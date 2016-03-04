(ns shadow.cljs.build.resource.common
  (:require [cljs.tagged-literals :as tags]
            [clojure.edn :as edn]
            [clojure.string :as str]
            [clojure.tools.reader :as reader]
            [clojure.tools.reader.reader-types :as readers]
            [shadow.cljs.build.internal :as internal
             :refer [compiler-state?]]
            [shadow.cljs.log :as log :refer [log-warning
                                             log-progress
                                             log-time-start
                                             log-time-end
                                             with-logged-time]]
            [shadow.cljs.query :as query]
            [shadow.cljs.util :as util])
  (:import [java.io
            File
            StringReader
            PushbackReader]
           [com.google.javascript.jscomp.deps
            JsFileParser]))

;; Resource Predicates

(defn valid-resource? [{:keys [type input name provides requires require-order last-modified] :as src}]
  (and (contains? #{:js :cljs} type)
       (instance? clojure.lang.IDeref input)
       (string? name)
       (set? provides)
       (set? requires)
       (vector? require-order)
       (number? last-modified)
       ))

(defn should-ignore-resource?
  [{:keys [ignore-patterns] :as state} name]
  (loop [patterns ignore-patterns]
    (if-let [pattern (first patterns)]
      (if (re-find pattern name)
        true
        (recur (rest patterns)))
      false
      )))

;; Name Normalization

(def ^{:doc "windows filenames need to be normalized because they contain backslashes which browsers don't understand"}
normalize-resource-name
  (if (= File/separatorChar \/)
    identity
    (fn [^String name]
      (str/replace name File/separatorChar \/))))

;; Goog Dependency

(defn add-goog-dependencies [state {:keys [name input] :as rc}]
  {:pre [(compiler-state? state)]}
  (if (= "goog/base.js" name)
    (assoc rc
      :requires #{}
      :require-order []
      :provides #{'goog})
    ;; parse any other js
    (let [deps (-> (JsFileParser. (.getErrorManager (internal/get-closure-compiler state)))
                   (.parseFile name name @input))]
      (assoc rc
        :requires (into #{} (map internal/munge-goog-ns) (.getRequires deps))
        :require-order (into [] (map internal/munge-goog-ns) (.getRequires deps))
        :provides (into #{} (map internal/munge-goog-ns) (.getProvides deps))))))

;; Peek Pass

(defn macros-from-ns-ast [state {:keys [require-macros use-macros]}]
  {:pre [(compiler-state? state)]}
  (into #{} (concat (vals require-macros) (vals use-macros))))

(defn update-rc-from-ns
  [state rc {:keys [name require-order] :as ast}]
  {:pre [(compiler-state? state)]}
  (let [require-order
        (if (= 'cljs.core name)
          require-order
          ;; inject implicit deps
          (into '[cljs.core runtime-setup] require-order))]  ; consider eliding runtime-setup
    (assoc rc
      :ns name
      :ns-info (dissoc ast :env)
      :provides #{name}
      :macros (macros-from-ns-ast state ast)
      :requires (into #{} require-order)
      :require-order require-order)))

(defn peek-into-cljs-resource
  "looks at the first form in a .cljs file, analyzes it if (ns ...) and returns the updated resource
   with ns-related infos"
  [{:keys [logger] :as state} {:keys [^String name input] :as rc}]
  {:pre [(compiler-state? state)]}
  (let [eof-sentinel (Object.)
        cljc? (.endsWith name ".cljc")
        opts (merge
               {:eof eof-sentinel}
               (when cljc?
                 {:read-cond :allow :features #{:cljs}}))
        rdr (StringReader. @input)
        in (readers/indexing-push-back-reader (PushbackReader. rdr) 1 name)]
    (binding [reader/*data-readers* tags/*cljs-data-readers*]
      (try
        (let [peek (reader/read opts in)]
          (if (identical? peek eof-sentinel)
            (throw (ex-info "file is empty" {:name name}))
            (let [ast (util/parse-ns peek)]
              (-> state
                  (update-rc-from-ns rc ast)
                  (assoc :cljc cljc?)))))
        (catch Exception e
          ;; could not parse NS
          ;; be silent about it until we actually require and attempt to compile the file
          ;; make best estimate guess what the file might provide based on name
          (let [guessed-ns (util/cljs-file->ns name)]
            (assoc rc
              :ns guessed-ns
              :requires #{'cljs.core}
              :require-order ['cljs.core]
              :provides #{guessed-ns}
              :type :cljs
              )))))))

(defn inspect-resource
  [state {:keys [name] :as rc}]
  {:pre [(compiler-state? state)]}
  (cond
    (util/js-file? name)
    (->> (assoc rc :type :js :js-name name)
         (add-goog-dependencies state))

    (util/cljs-or-cljc-file? name)
    (let [rc (assoc rc :type :cljs :js-name (str/replace name #"\.clj(s|c)$" ".js"))]
      (if (= name "deps.cljs")
        rc
        (peek-into-cljs-resource state rc)))

    :else
    (throw (ex-info "cannot identify as cljs resource" rc))))

;; deps.cljs Handling

(defn extract-foreign-libs
  [{:keys [foreign-libs externs] :as deps} source-path]
  (let [foreign-libs (cond
                       (nil? foreign-libs)
                       []
                       (vector? foreign-libs)
                       foreign-libs
                       (map? foreign-libs)
                       [foreign-libs]
                       (list? foreign-libs)
                       (into [] foreign-libs)
                       :else
                       (throw (ex-info (format "invalid :foreign-libs in deps.cljs of %s" source-path) {:deps deps})))]
    (if (seq externs)
      ;; FIXME: :externs at top level
      (update-in foreign-libs [0 :externs] #(into (or % []) externs))
      foreign-libs)))

(defn process-deps-cljs
  [{:keys [use-file-min] :as state} manifest source-path]
  {:pre [(compiler-state? state)
         (map? manifest)]}
  (let [deps (get manifest "deps.cljs")]
    (if (nil? deps)
      manifest
      (let [foreign-libs (-> @(:input deps)
                             (edn/read-string)
                             (extract-foreign-libs source-path))]

        (reduce
          (fn [result {:keys [externs provides requires] :as foreign-lib}]
            (if-not (or (contains? foreign-lib :file)
                        (contains? foreign-lib :file-min))
              ;; {:externs ["om/externs.js"]}
              ;; doesn't contain any foreign, only externs.
              ;; this really doesn't make sense, currently on the case because of a buggy externs
              ;; in cljsjs/react (pending https://github.com/cljsjs/packages/pull/287)
              result
              (let [[lib-key lib-other] (cond
                                          (and use-file-min (contains? foreign-lib :file-min))
                                          [:file-min :file]
                                          (:file foreign-lib)
                                          [:file :file-min])
                    lib-name (get foreign-lib lib-key)
                    rc (get result lib-name)]
                (when (nil? rc)
                  (throw (ex-info "deps.cljs refers to file not in jar" {:foreign-lib foreign-lib})))

                (let [dissoc-all (fn [m list]
                                   (apply dissoc m list))
                      ;; mark rc as foreign and merge with externs instead of leaving externs as seperate rc
                      rc (assoc rc
                           :foreign true
                           :requires (set (map symbol requires))
                           :provides (set (map symbol provides))
                           :externs externs
                           :externs-source (->> externs
                                                (map #(get result %))
                                                (map :input)
                                                (map deref)
                                                (str/join "\n")))]
                  (-> result
                      (dissoc-all externs)
                      ;; remove :file or :file-min
                      (dissoc (get foreign-lib lib-other))
                      (assoc lib-name rc))))))
          (dissoc manifest "deps.cljs")
          foreign-libs)))))

;; Resource Integration - Remove

(defn unmerge-provides [state provides]
  (reduce
    (fn [state provide]
      (update-in state [:provide->source] dissoc provide))
    state
    provides))

(defn unmerge-resource [state name]
  (if-let [{:keys [provides] :as current} (get-in state [:sources name])]
    (-> state
        (unmerge-provides provides)
        (update-in [:sources] dissoc name))
    ;; else: not present
    state))

;; Resource Integration - Add

(defn merge-provides [state provided-by provides]
  (reduce
    (fn [state provide]
      (assoc-in state [:provide->source provide] provided-by))
    state
    provides))

(defn merge-resource
  [{:keys [logger] :as state} {:keys [name provides url] :as src}]
  (cond
    (not (valid-resource? src))
    (do (log-warning logger (format "ERROR in resource: %s via %s" name url))
        state)

    ;; no not merge files that don't have the expected path for their ns
    ;; not really needed but cljs does this, so we should enforce it as well
    (and (= :cljs (:type src))
         (symbol? (:ns src))
         (let [expected-name (util/ns->cljs-file (:ns src))
               expected-cljc (str/replace expected-name #".cljs$" ".cljc")]
           (not (or (= name expected-name)
                    (= name expected-cljc)
                    ))))

   (do (log-warning
        logger
        (format "NS \"%s\" did not match expected file-path, expected A got B%nURL: %s%nA: %s%nB: %s"
                (:ns src)
                url
                (str (util/ns->cljs-file (:ns src)) " (or .cljc)")
                name
                ))
        ;; still want to remember the resource so it doesn't get detected as new all the time
        ;; remove all provides, otherwise it might end up being used despite the invalid name
        ;; enforce this behavior since the warning might get overlooked easily
        (let [invalid-src (assoc src
                            :provides #{}
                            :requires #{}
                            :require-order [])]
          (assoc-in state [:sources name] invalid-src)))

    ;; do not merge files that are already present from a different source path
    (let [existing (get-in state [:sources name])]
      (and existing
           (or (not= (:source-path existing)
                     (:source-path src))
               (not= (:url existing)
                     (:url src)))))
    (do (log-warning logger (format
                              "duplicate file on classpath \"%s\" (using A)%nA: %s%nB: %s"
                              name
                              (get-in state [:sources name :source-path])
                              (:source-path src)))
        state)

    ;; now we need to handle conflicts for cljc/cljs files
    ;; only use cljs if both exist
    :valid-resource
    (let [cljc? (util/cljc-file? name)
          cljc-name (when (util/cljs-file? name)
                      (str/replace name #"cljs$" "cljc"))
          cljs-name (when cljc?
                      (str/replace name #"cljc$" "cljs"))]
      (cond
        ;; don't merge .cljc file if a .cljs of the same name exists
        (and cljc? (contains? (:sources state) cljs-name))
        (do (log-warning logger (format "File conflict: \"%s\" -> \"%s\" (using \"%s\")" name cljs-name cljs-name))
            state)

        ;; if a .cljc exists for a .cljs file unmerge the .cljc and merge the .cljs
        (and (util/cljs-file? name) (contains? (:sources state) cljc-name))
        (do (log-warning logger (format "File conflict: \"%s\" -> \"%s\" (using \"%s\")" name cljc-name name))
            (-> state
                (assoc-in [:sources name] src)
                (merge-provides name provides)))

        :no-conflict
        (-> state
            (assoc-in [:sources name] src)
            (merge-provides name provides))))))

(defn merge-resources [state srcs]
  (reduce merge-resource state srcs))

(defn reset-resource
  [state {:keys [^File file url] :as resource}]
  (inspect-resource
   state
   (-> resource
       (dissoc :ns :ns-info :requires :require-order :provides :output :compiled :compiled-at)
       (assoc :input (delay (slurp url)))
       (assoc :last-modified (.lastModified file)))))

(defn reset-resource-by-name [state name]
  (let [{:keys [file] :as rc} (get-in state [:sources name])]
    ;; only resource that have a file associated with them can be reloaded (?)
    (if (nil? file)
      state
      (-> state
          (unmerge-resource name)
          (merge-resource (reset-resource state rc))))
    ))

(defn reset-resources-using-macro [state macro-ns]
  (let [names (query/get-resources-using-macro state macro-ns)]
    (reduce reset-resource-by-name state names)
    ))

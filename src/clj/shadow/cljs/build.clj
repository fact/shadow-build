(ns shadow.cljs.build
  (:import [java.io
            File
            FileOutputStream
            FileInputStream
            StringReader
            PushbackReader]
           [java.net URL]
           [com.google.javascript.jscomp
            JSModule
            SourceFile
            JSModuleGraph]
           [java.util.concurrent Executors Future])
  (:require [clojure.data.json :as json]
            [clojure.java.io :as io]
            [clojure.set :as set]
            [clojure.string :as str]
            [cljs.analyzer :as ana]
            [cljs.compiler :as comp]
            [cljs.source-map :as sm]
            [cljs.env :as env]
            [cljs.tagged-literals :as tags]
            [cljs.util :as cljs-util]
            [clojure.pprint :refer (pprint)]
            [clojure.repl :refer (pst)]
            [clojure.tools.reader :as reader]
            [clojure.tools.reader.reader-types :as readers]
            [loom.graph :as lg]
            [loom.alg :as la]
            [shadow.cljs.build.cache :as cache]
            [shadow.cljs.build.closure :as closure]
            [shadow.cljs.build.macro :as macro]
            [shadow.cljs.build.resource.common :as common]
            [shadow.cljs.build.resource.file :as file]
            [shadow.cljs.build.resource.jar :as jar]
            [shadow.cljs.build.internal :as internal]
            [shadow.cljs.log :as log]
            [shadow.cljs.query :as query]
            [shadow.cljs.util :as util]
            ))

;; (set! *warn-on-reflection* true)

(comment
  ;; maybe add some kind of type info later
  (def a-resource
    '{:input deref
      :output string
      :type (either :js :cljs)
      :from-jar boolean
      :last-modified long
      :requires #{name}
      :provides #{name}
      ;; only :cljs
      :ns name
      :ns-info ns-info
      }))

(defn error-report
  ([state e]
   (.flush *out*)
   (.write *err* "====== ERROR ==============\n")
   (pst e)
   (.write *err* "===========================\n")
   (.flush *err*))
  ([state e rc]
   (error-report state e)))


(defn post-analyze-ns [{:keys [name] :as ast} opts]
  (let [ast (-> ast
                (util/load-macros)
                (util/infer-macro-require)
                (util/infer-macro-use))]
    (util/check-uses! (:env ast) (:uses ast))
    (swap! env/*compiler* assoc-in [::ana/namespaces name] (dissoc ast :env :op :form))
    ast))

(defn post-analyze [{:keys [op] :as ast} opts]
  (case op
    :ns (post-analyze-ns ast opts)
    ast))

(defn hijacked-parse-ns [env form name opts]
  (assoc (util/parse-ns form)
    :env env
    :form form
    :op :ns))

(def default-parse ana/parse)

(defn shadow-parse [op env form name opts]
  (condp = op
    ;; the default ana/parse 'ns has way too many side effects we don't need or want
    ;; don't want analyze-deps -> never needed
    ;; don't want require or macro ns -> post-analyze
    ;; don't want check-uses -> doesn't recognize macros
    ;; don't want check-use-macros -> doesnt handle (:require [some-ns :refer (a-macro)])
    ;; don't want swap into compiler env -> post-analyze
    'ns (hijacked-parse-ns env form name opts)
    (default-parse op env form name opts)))

(defn analyze
  ([state compile-state form]
   (analyze state compile-state form :statement))
  ([state {:keys [ns name] :as compile-state} form context]
   {:pre [(map? compile-state)
          (symbol? ns)
          (string? name)
          (seq name)]}
    ;; (defmulti parse (fn [op & rest] op))
   (let [default-parse ana/parse]
     (binding [*ns* (create-ns ns)
               ana/*passes* [ana/infer-type]
               ;; [infer-type ns-side-effects] is default, we don't want the side effects
               ;; altough it is great that the side effects are now optional
               ;; the default still doesn't handle macros properly
               ;; so we keep hijacking
               ana/*cljs-ns* ns
               ana/*cljs-file* name]

       (-> (ana/empty-env) ;; this is anything but empty! requires *cljs-ns*, env/*compiler*
           (assoc :context context)
           (ana/analyze form ns state)
           (post-analyze state))))))

(defn do-compile-cljs-string
  [{:keys [name] :as init} reduce-fn cljs-source cljc?]
  (let [eof-sentinel (Object.)
        opts (merge
               {:eof eof-sentinel}
               (when cljc?
                 {:read-cond :allow :features #{:cljs}}))
        in (readers/indexing-push-back-reader (PushbackReader. (StringReader. cljs-source)) 1 name)]

    (binding [comp/*source-map-data* (atom {:source-map (sorted-map)
                                            :gen-col 0
                                            :gen-line 0})]

      (let [result
            (loop [{:keys [ns ns-info] :as compile-state} (assoc init :js "")]
              (let [form (binding [*ns* (create-ns ns)
                                   ana/*cljs-ns* ns
                                   ana/*cljs-file* name
                                   reader/*data-readers* tags/*cljs-data-readers*
                                   reader/*alias-map* (merge reader/*alias-map*
                                                        (:requires ns-info)
                                                        (:require-macros ns-info))]
                           (reader/read opts in))]

                (if (identical? form eof-sentinel)
                  ;; eof
                  compile-state
                  (recur (reduce-fn compile-state form)))))]

        (assoc result :source-map (:source-map @comp/*source-map-data*))
        ))))

(defn default-compile-cljs
  [state compile-state form]
  (let [ast (analyze state compile-state form)
        ast-js (with-out-str
                 (comp/emit ast))

        compile-state (if (= :ns (:op ast))
                        (common/update-rc-from-ns state compile-state ast)
                        compile-state)]
    (update-in compile-state [:js] str ast-js)
    ))


(defn warning-collector [warnings warning-type env extra]
  (swap! warnings conj {:warning-type warning-type
                        :env env
                        :extra extra}))

(defn warning->msg [{:keys [warning-type env extra] :as warning}]
  (when (contains? ana/*cljs-warnings* warning-type)
    (when-let [s (ana/error-message warning-type extra)]
      (ana/message env s)
      )))

(defmacro with-warnings
  "given a body that produces a compilation result, collect all warnings and assoc into :warnings"
  [& body]
  `(let [warnings# (atom [])
         result# (ana/with-warning-handlers
                   [(partial warning-collector warnings#)]
                   ~@body)]
     (assoc result# :warnings (mapv warning->msg @warnings#))))

(defn compile-cljs-string
  [state cljs-source name cljc?]
  (with-warnings
    (do-compile-cljs-string
      {:name name :ns 'cljs.user}
      (partial default-compile-cljs state)
      cljs-source
      cljc?)))

(defn compile-cljs-seq
  [state cljs-forms name]
  (with-warnings
    (reduce
      (partial default-compile-cljs state)
      {:name name :ns 'cljs.user}
      cljs-forms)))

(defn do-compile-cljs-resource
  "given the compiler state and a cljs resource, compile it and return the updated resource
   should not touch global state"
  [{:keys [static-fns] :as state} {:keys [name input cljc] :as rc}]

  (binding [ana/*cljs-static-fns* static-fns]
    (let [source @input]
      (log/with-logged-time
        [(:logger state) (format "Compile CLJS: \"%s\"" name)]
        (let [{:keys [js ns requires require-order source-map warnings]}
              (cond
                (string? source)
                (compile-cljs-string state source name cljc)
                (vector? source)
                (compile-cljs-seq state source name)
                :else
                (throw (ex-info "invalid cljs source type" {:name name :source source})))]

          (when-not ns
            (throw (ex-info "cljs file did not provide a namespace" {:file name})))

          (assoc rc
            :output js
            :requires requires
            :require-order require-order
            :compiled-at (System/currentTimeMillis)
            :provides #{ns}
            :compiled true
            :warnings warnings
            :source-map source-map))))))

(defn maybe-compile-cljs
  "take current state and cljs resource to compile
   make sure you are in with-compiler-env"
  [{:keys [cache-dir cache-level] :as state} {:keys [from-jar file] :as src}]
  (let [cache? (and cache-dir
                    ;; even with :all only cache resources that are in jars or have a file
                    ;; cljs.user (from repl) or runtime-setup should never be cached
                    (or (and (= cache-level :all)
                             (or from-jar file))
                        (and (= cache-level :jars)
                             from-jar)))]
    (or (when cache?
          (cache/load-cached-cljs-resource! state src))
        (let [src (do-compile-cljs-resource state src)]
          (when cache?
            (cache/write-cached-cljs-resource! state src))
          src))))





;;; COMPILE STEPS

(defn do-find-resources-in-path [state path]
  {:pre [(internal/compiler-state? state)]}
  (if (util/jar? path)
    (jar/find-jar-resources state path)
    (file/find-fs-resources state path)))

(defn merge-resources-in-path
  ([state path]
   (merge-resources-in-path state path {:reloadable true}))
  ([state path path-opts]
   (let [file (.getCanonicalFile (io/file path))
         abs-path (.getCanonicalPath file)]
     ;; checkout deps with a lot of symlinks can cause duplicates on classpath
     (if (contains? (:source-paths state) abs-path)
       state
       (let [resources (do-find-resources-in-path state abs-path)
             state
             (if (.isDirectory file)
               (assoc-in state [:source-paths abs-path] (assoc path-opts
                                                          :file file
                                                          :path abs-path))
               state)]
         (common/merge-resources state resources))))))

(defn find-resources
  "finds cljs resources in the given path"
  ([state path]
   (find-resources state path {:reloadable true}))
  ([{:keys [logger] :as state} path opts]
   (log/with-logged-time
     [(:logger state) (format "Find cljs resources in path: \"%s\"" path)]
     (let [file (io/file path)
           abs-path (.getCanonicalPath file)]
       (when-not (.exists file)
         (throw (ex-info (format "\"%s\" does not exist" path) {:path path})))

       (if (contains? (:source-paths state) abs-path)
         (do (log/log-progress logger (format "path \"%s\" already on classpath, skipped" path))
             state)
         (merge-resources-in-path state path opts))
       ))))

(defn should-exclude-classpath [exclude path]
  (boolean (some #(re-find % path) exclude)))

(defn find-resources-in-classpath
  "finds all cljs resources in the classpath (ignores resources)"
  ([state]
   (find-resources-in-classpath state {:exclude [#"resources(/?)$"
                                                 #"classes(/?)$"
                                                 #"java(/?)$"]}))
  ([state {:keys [classpath exclude]}]
   (log/with-logged-time
     [(:logger state) "Find cljs resources in classpath"]
     (let [paths
           (->> (or classpath (util/get-classpath))
                (util/classpath-entries)
                (remove #(should-exclude-classpath exclude %)))]
       (reduce merge-resources-in-path state paths)
       ))))

;; deprecate the weird naming stuff
(def step-find-resources-in-jars find-resources-in-classpath)
(def step-find-resources find-resources)

(def cljs-core-name "cljs/core.cljs")

(def ^:dynamic *in-compiler-env* false)

(defmacro with-compiler-env
  "compiler env is a rather big piece of dynamic state
   so we take it out when needed and put the updated version back when done
   doesn't carry the atom arround cause the compiler state itself should be persistent
   thus it should provide safe points

   the body should yield the updated compiler state and not touch the compiler env

   I don't touch the compiler env itself yet at all, might do for some metadata later"
  [state & body]
  `(do (when *in-compiler-env*
         (throw (ex-info "already in compiler env" {})))
       (let [dyn-env# (atom (:compiler-env ~state))
             new-state# (binding [env/*compiler* dyn-env#
                                  *in-compiler-env* true]
                          ~@body)]
         (assoc new-state# :compiler-env @dyn-env#))))

(defn swap-compiler-env!
  [state update-fn & args]
  (if *in-compiler-env*
    (do (swap! env/*compiler* (fn [current] (apply update-fn current args)))
        state)
    (update state :compiler-env (fn [current] (apply update-fn current args)))))

(defn ^:deprecated step-compile-core [state]
  ;; honestly not sure why this was ever here
  ;; since we compile in dep order 'cljs.core will always be compiled before any other CLJS
  state)

(defn finalize-config
  "should be called AFTER all resources have been discovers (ie. after find-resources...)"
  [state]
  (-> state
      (macro/discover-macros)
      (assoc :configured true
             :unoptimizable (when-let [imul (io/resource "cljs/imul.js")]
                              (slurp imul))
             ;; populate index with known sources
             :provide->source (into {} (for [{:keys [name provides]} (vals (:sources state))
                                             provide provides]
                                         [provide name]
                                         )))))

(def step-finalize-config finalize-config)

(defn reset-modules [state]
  (-> state
      (assoc :modules {})
      (dissoc :default-module :build-modules)
      ))

(defn configure-module
  ([state module-name module-mains depends-on]
   (configure-module state module-name module-mains depends-on {}))
  ([state module-name module-mains depends-on mod-attrs]
   (when-not (keyword? module-name)
     (throw (ex-info "module name should be a keyword" {:module-name module-name})))
   (when-not (every? keyword? depends-on)
     (throw (ex-info "module deps should be keywords" {:module-deps depends-on})))

   (let [is-default? (not (seq depends-on))

         _ (when is-default?
             (when-let [default (:default-module state)]
               (throw (ex-info "default module already defined, are you missing deps?"
                        {:default default :wants-to-be-default module-name}))))

         mod (merge mod-attrs
               {:name module-name
                :js-name (str (name module-name) ".js")
                :mains module-mains
                :depends-on depends-on
                :default is-default?})

         state (assoc-in state [:modules module-name] mod)
         state (if is-default?
                 (assoc state :default-module module-name)
                 state)]
     state)))

(def step-configure-module configure-module)

(defn flush-to-disk
  "flush all generated sources to disk, not terribly useful, use flush-unoptimized to include source maps"
  [{:keys [work-dir sources] :as state}]
  (log/with-logged-time
    [(:logger state) (format "Flushing to disk")]
    (doseq [{:keys [type name compiled] :as src} (vals sources)
            :when (and (= :cljs type)
                       compiled)]

      (let [{:keys [js-name output]} src
            target (io/file work-dir js-name)]
        (io/make-parents target)
        (spit target output)))
    state))

;; module related stuff

(defn module-graph [modules]
  (let [module-set (set (keys modules))]
    (doseq [{:keys [name depends-on]} (vals modules)
            :when (seq depends-on)]
      (when-not (set/subset? depends-on module-set)
        (throw (ex-info "module contains dependency on unknown modules"
                 {:module name
                  :unknown (set/difference depends-on module-set)})))))

  (apply lg/digraph
    (for [{:keys [name depends-on]} (vals modules)
          dep depends-on]
      [name dep])))

(defn dump-js-modules [modules]
  (doseq [js-mod modules]
    (prn [:js-mod (.getThisAndAllDependencies js-mod)])
    (doseq [input (.getInputs js-mod)]
      (prn [:js-mod input]))))

(defn sort-and-compact-modules
  "sorts modules in dependency order and remove sources provided by parent deps"
  [{:keys [logger modules] :as state}]
  (when-not (seq modules)
    (throw (ex-info "no modules defined" {})))

  ;; if only one module is defined we dont need all this work
  (if (= 1 (count modules))
    (vals modules)
    ;; else: multiple modules must be sorted in dependency order
    (let [module-graph (module-graph modules)
          module-order (reverse (la/topsort module-graph))

          js-mods (reduce
                    (fn [js-mods module-key]
                      (let [{:keys [js-name name depends-on sources]} (get modules module-key)
                            js-mod (JSModule. js-name)]

                        (doseq [name sources]
                          ;; we don't actually need code yet
                          (.add js-mod (SourceFile. name)))

                        (doseq [other-mod-name depends-on
                                :let [other-mod (get js-mods other-mod-name)]]
                          (when-not other-mod
                            (throw (ex-info "module depends on undefined module" {:mod name :other other-mod-name})))
                          (.addDependency js-mod other-mod))

                        (assoc js-mods module-key js-mod)))
                    {}
                    module-order)]

      ;; eek mutable code
      ;; this will move duplicate files from each module to the closest common ancestor
      (doto (JSModuleGraph. (into-array (for [module-key module-order]
                                          (get js-mods module-key))))
        (.coalesceDuplicateFiles))

      (->> module-order
           (map (fn [module-key]
                  (let [module (get modules module-key)
                        ;; enough with the mutable stuff
                        sources (->> (get js-mods module-key)
                                     (.getInputs)
                                     (map #(.getName %))
                                     (vec))]
                    (assoc module :sources sources))))
           (vec)))))

(defn do-print-warnings
  "print warnings after building modules, repeat warnings for files that weren't recompiled!"
  [{:keys [logger] :as state}]
  (doseq [{:keys [name warnings] :as src}
          (->> (:sources state)
               vals
               (sort-by :name)
               (filter #(seq (:warnings %))))]
    (log/log-warning logger (format "WARNINGS: %s (%d)" name (count warnings)))
    (doseq [warning warnings]
      (log/log-warning logger warning)
      ))
  state)

(defn do-analyze-module
  "resolve all deps for a given module, based on specified :mains
   will update state for each module with :sources, a list of sources needed to compile this module "
  [state {:keys [name mains] :as module}]
  (assoc-in state [:modules name :sources] (query/get-deps-for-mains state mains)))

(defn add-foreign
  [state name provides requires js-source externs-source]
  {:pre [(string? name)
         (set? provides)
         (seq provides)
         (set? requires)
         (string? js-source)
         (seq js-source)
         (string? externs-source)
         (seq externs-source)]}

  (common/merge-resource state
                         {:type :js
                          :foreign true
                          :name name
                          :js-name name
                          :provides provides
                          :requires requires
                          ;; FIXME: should allow getting a vector as provides instead
                          :require-order (into [] requires)
                          :output js-source
                          :input (atom js-source)
                          :externs-source externs-source
                          :last-modified 0
                          }))

(defn make-runtime-setup [{:keys [runtime] :as state}]
  (let [src (str/join "\n" [(case (:print-fn runtime)
                              ;; Browser
                              :console "cljs.core.enable_console_print_BANG_();"
                              ;; Node.JS
                              :print "cljs.core._STAR_print_fn_STAR_ = require(\"util\").print;")])]
    {:type :js
     :name "runtime_setup.js"
     :js-name "runtime_setup.js"
     :provides #{'runtime-setup}
     :requires #{'cljs.core}
     :require-order ['cljs.core]
     :input (atom src)
     :last-modified 0 ;; this file should never cause recompiles
     }))


(defn generate-output-for-source [state {:keys [name type output warnings] :as src}]
  {:pre [(common/valid-resource? src)]}
  (if (and (seq output)
           ;; always recompile files with warnings
           (not (seq warnings)))
    src
    (case type
      :js
      (assoc src :output @(:input src))
      :cljs
      (maybe-compile-cljs state src))))

(defn compile-sources
  "compile a list of sources by name,
   requires that the names are in dependency order
   requires that ALL of the dependencies NOT in source names are already compiled
   eg. you cannot just compile [\"clojure/string.cljs\"] as it requires other files to be compiled first"
  [state source-names]
  (with-redefs [ana/parse shadow-parse]
    (with-compiler-env state
      (ana/load-core)
      (reduce
        (fn [state source-name]
          (let [src (get-in state [:sources source-name])
                compiled-src (generate-output-for-source state src)]
            (-> state
                (assoc-in [:sources source-name] compiled-src)
                (cond->
                  (not= (:compiled-at src)
                        (:compiled-at compiled-src))
                  (update :compiled conj source-name)
                  ))))
        (assoc state :compiled [])
        source-names))))

(defn par-compile-one [state ready compiled errors source-name]
  (let [{:keys [requires] :as src} (get-in state [:sources source-name])]
    (loop []
      (cond
        ;; skip work if errors occured
        (seq @errors)
        src

        ;; only compile once all dependencies are compiled
        ;; FIXME: sleep is not great, cljs.core takes a couple of sec to compile
        ;; this will spin a couple hundred times, doing additional work
        ;; don't increase the sleep time since many files compile in the 5-10 range
        (not (set/superset? @ready requires))
        (do (Thread/sleep 5)
            (recur))

        :ready-to-compile
        (try
          (let [{:keys [provides] :as compiled-src}
                (generate-output-for-source state src)]

            (when (not= (:compiled-at src)
                        (:compiled-at compiled-src))
              (swap! compiled conj source-name))

            (swap! ready set/union provides)
            compiled-src)
          (catch Exception e
            (swap! errors assoc source-name e)
            src
            ))))))

(defn par-compile-sources
  "compile files in parallel, files MUST be in dependency order and ALL dependencies must be present
   this cannot do a partial incremental compile"
  [{:keys [n-compile-threads logger] :as state} source-names]
  (log/log-progress logger (format "Compiling with %d threads" n-compile-threads))
  (let [exec (Executors/newFixedThreadPool n-compile-threads)]
    (try
      (with-redefs [ana/parse shadow-parse]
        (with-compiler-env state
          (ana/load-core)
          (let [ready (atom #{}) ;; namespaces that are ready to be used
                compiled (atom []) ;; files that were actually compiled (not recycled)
                errors (atom {}) ;; source-name -> exception

                tasks
                (->> (for [source-name source-names]
                       ;; bound-fn for with-compiler-state
                       (let [task-fn (bound-fn [] (par-compile-one state ready compiled errors source-name))]
                         (.submit exec ^Callable task-fn)))
                     (doall) ;; force submit all, then deref
                     (mapv deref))]

            ;; unlikely to encounter 2 concurrent errors
            ;; so unpack for a single error for better stacktrace
            (let [errs @errors]
              (case (count errs)
                0 nil
                1 (let [[name err] (first errs)]
                    (throw (ex-info (format "compilation of \"%s\" failed" name) {} err)))
                (throw (ex-info "compilation failed" errs))))

            (-> state
                (update :sources (fn [sources]
                                   (reduce
                                    (fn [sources {:keys [name] :as src}]
                                      (assoc sources name src))
                                    sources
                                    tasks)))
                (assoc :compiled @compiled)))))
      (finally
       ;; FIXME: might deadlock here if any of the derefs fail
       (.shutdown exec)))))


(defn- prepare-compile [state]
  (let [runtime-setup (make-runtime-setup state)]
    (-> (finalize-config state)
        (common/merge-resource runtime-setup)
        )))

(defn compile-modules
  [{:keys [n-compile-threads] :as state}]
  (log/with-logged-time
    [(:logger state) "Compiling Modules ..."]
    (let [state (prepare-compile state)
          state (reduce do-analyze-module state (-> state :modules (vals)))
          modules (sort-and-compact-modules state)
          source-names (mapcat :sources modules)
          state (if (> n-compile-threads 1)
                  (par-compile-sources state source-names)
                  (compile-sources state source-names))]

      (-> state
          (assoc :build-modules modules)
          (do-print-warnings)
          ))))

(defn compile-all-for-ns [state ns]
  (let [deps (query/get-deps-for-ns state ns)]
    (-> state
        (prepare-compile)
        (compile-sources deps))
    ))

(def step-compile-modules compile-modules)


;; Flush

(defn- ns-list-string [coll]
  (->> coll
       (map #(str "'" (comp/munge %) "'"))
       (str/join ",")))

(defn closure-goog-deps [state]
  (->> (:sources state)
       (vals)
       (map (fn [{:keys [js-name require-order provides]}]
              (str "goog.addDependency(\"" js-name "\","
                   "[" (ns-list-string provides) "],"
                   "[" (ns-list-string require-order) "]);")))
       (str/join "\n")))

(defn flush-sources-by-name
  [{:keys [public-dir cljs-runtime-path] :as state} source-names]
  (doseq [{:keys [type name input last-modified] :as src}
          (->> source-names
               (map #(get-in state [:sources %])))
          :let [target (io/file public-dir cljs-runtime-path name)]

          ;; skip files we already have since source maps are kinda expensive to generate
          :when (or (not (.exists target))
                    (zero? last-modified)
                    (> (or (:compiled-at src) ;; js is not compiled but maybe modified
                           last-modified)
                      (.lastModified target)))]

    (io/make-parents target)

    (case type
      ;; cljs needs to flush the generated .js, for source-maps also the .cljs and a .map
      :cljs
      (do (let [{:keys [source-map js-name output]} src
                js-target (io/file public-dir cljs-runtime-path js-name)]

            (when (nil? output)
              (throw (ex-info (format "no output for resource: %s" js-name) src)))

            (spit js-target output)

            (when source-map
              (let [source-map-name (str js-name ".map")]
                (spit (io/file public-dir cljs-runtime-path source-map-name)
                  (sm/encode {name source-map} {:file js-name}))
                (spit js-target (str "//# sourceMappingURL=" (util/file-basename source-map-name) "?r=" (rand)) :append true))))

          ;; spit original source, cljs needed for source maps
          (spit target @input))

      ;; js just needs itself
      ;; FIXME: needs to flush more when js processing is added
      :js
      (do (spit target (:output src))
          ;; foreign libs should play nice with goog require/import and tell what they provide
          (when (:foreign src)
            (spit target (closure/make-foreign-js-source src) :append true)
            ))

      (throw (ex-info "cannot flush" (dissoc src :input :output)))
      ))

  state)

(defn flush-unoptimized
  [{:keys [build-modules public-dir unoptimizable] :as state}]
  {:pre [(util/directory? public-dir)]}

  (when-not (seq build-modules)
    (throw (ex-info "flush before compile?" {})))
  (log/with-logged-time
    [(:logger state) "Flushing sources"]

    (flush-sources-by-name state (mapcat :sources build-modules)))

  (log/with-logged-time
    [(:logger state) "Flushing unoptimized modules"]

    (closure/flush-manifest public-dir build-modules)

    ;; flush fake modules
    (doseq [{:keys [default js-name name prepend prepend-js append-js sources web-worker] :as mod} build-modules]
      (let [provided-ns (mapcat #(reverse (get-in state [:sources % :provides]))
                          sources)
            target (io/file public-dir js-name)

            out (->> provided-ns
                     (map (fn [ns]
                            (str "goog.require('" (comp/munge ns) "');")))
                     (str/join "\n"))
            out (str prepend prepend-js out append-js)
            out (if (or default web-worker)
                  ;; default mod needs closure related setup and goog.addDependency stuff
                  (str unoptimizable
                       "var SHADOW_MODULES = {};\n"
                       (when web-worker
                         "\nvar CLOSURE_IMPORT_SCRIPT = function(src) { importScripts(src); };\n")
                       (closure/closure-defines-and-base state)
                       (closure-goog-deps state)
                       "\n\n"
                       out)
                  ;; else
                  out)

            out (str out "\n\nSHADOW_MODULES[" (pr-str (str name)) "] = true;\n")]

        (spit target out))))
  ;; return unmodified state
  state)

(defn line-count [text]
  (with-open [rdr (io/reader (StringReader. text))]
    (count (line-seq rdr))))

(defn create-index-map
  [{:keys [public-dir cljs-runtime-path] :as state} out-file init-offset {:keys [sources js-name] :as mod}]
  (let [index-map
        (reduce
          (fn [src-map src-name]
            (let [{:keys [type output js-name] :as rc} (get-in state [:sources src-name])
                  source-map-file (io/file public-dir cljs-runtime-path (str js-name ".map"))
                  lc (line-count output)
                  start-line (:current-offset src-map)

                  ;; extra 2 lines per file
                  ;; // SOURCE comment
                  ;; goog.dependencies_.written[src] = true;
                  src-map (update src-map :current-offset + lc 2)]

              (if (and (= :cljs type)
                       (.exists source-map-file))
                (update src-map :sections conj {:offset {:line (+ start-line 3) :column 0}
                                                ;; :url (str js-name ".map")
                                                ;; chrome doesn't support :url
                                                ;; see https://code.google.com/p/chromium/issues/detail?id=552455
                                                ;; FIXME: inlining the source-map is expensive due to excessive parsing
                                                ;; could try to insert MARKER instead and str/replace
                                                ;; 300ms is acceptable for now, but might not be on bigger projects
                                                ;; flushing the unoptmized version should not exceed 100ms
                                                :map (let [sm (json/read-str (slurp source-map-file))]
                                                       ;; must set sources and file to complete relative paths
                                                       ;; as the source map only contains local references without path
                                                       (assoc sm
                                                         "sources" [src-name]
                                                         "file" js-name))
                                                })
                ;; only have source-maps for cljs
                src-map)
              ))
          {:current-offset init-offset
           :version 3
           :file (str "../" js-name)
           :sections []}
          sources)

        index-map (dissoc index-map :current-offset)]

    ;; (pprint index-map)
    (spit out-file (json/write-str index-map))
    ))

(defn flush-unoptimized-compact
  [{:keys [build-modules public-dir unoptimizable cljs-runtime-path] :as state}]
  {:pre [(util/directory? public-dir)]}

  (when-not (seq build-modules)
    (throw (ex-info "flush before compile?" {})))
  (log/with-logged-time
    [(:logger state) "Flushing sources"]

    (flush-sources-by-name state (mapcat :sources build-modules)))

  (log/with-logged-time
    [(:logger state) "Flushing unoptimized compact modules"]

    (closure/flush-manifest public-dir build-modules)

    ;; flush fake modules
    (doseq [{:keys [default js-name name prepend prepend-js append-js sources web-worker] :as mod} build-modules]
      (let [target (io/file public-dir js-name)
            append-to-target
            (fn [text]
              (spit target text :append true))]

        (spit target (str prepend prepend-js))
        (when (or default web-worker)
          (append-to-target
            (str unoptimizable
                 "var SHADOW_MODULES = {};\n"
                 (if web-worker
                   "\nvar CLOSURE_IMPORT_SCRIPT = function(src) { importScripts(src); };\n"
                   ;; FIXME: should probably throw an error because we NEVER want to import anything this way
                   "\nvar CLOSURE_IMPORT_SCRIPT = function(src, opt_sourceText) { console.log(\"BROKEN IMPORT\", src); };\n"
                   )
                 (closure/closure-defines-and-base state)
                 (closure-goog-deps state)
                 "\n\n"
                 )))

        ;; at least line-count must be captured here
        ;; since it is the initial offset before we actually have a source map
        (create-index-map
          state
          (io/file public-dir cljs-runtime-path (str (clojure.core/name name) "-index.js.map"))
          (line-count (slurp target))
          mod)

        (doseq [src-name sources
                :let [{:keys [output name js-name] :as rc} (get-in state [:sources src-name])]]
          (append-to-target (str "// SOURCE=" name "\n"))
          ;; pretend we actually loaded a separate file, live-reload needs this
          (append-to-target (str "goog.dependencies_.written[" (pr-str js-name) "] = true;\n"))
          (append-to-target (str (str/trim output) "\n")))

        (append-to-target append-js)
        (append-to-target (str "\n\nSHADOW_MODULES[" (pr-str (str name)) "] = true;\n"))

        (append-to-target (str "//# sourceMappingURL=" cljs-runtime-path "/" (clojure.core/name name) "-index.js.map?r=" (rand)))
        )))

  ;; return unmodified state
  state)

(defn scan-for-new-files
  "scans the reloadable paths for new files

   returns a seq of resource maps with a {:scan :new} value"
  [{:keys [sources] :as state}]
  (let [reloadable-paths (query/get-reloadable-source-paths state)
        known-files (->> sources
                         (vals)
                         (map (fn [{:keys [source-path name]}]
                                [source-path name]))
                         (into #{}))]
    (->> reloadable-paths
         (mapcat #(file/find-fs-resources state %))
         (remove (fn [{:keys [source-path name]}]
                   (contains? known-files [source-path name])))
         (map #(assoc % :scan :new))
         (into []))))

(defn scan-for-modified-files
  "scans known sources for modified or deleted files

  returns a seq of resource maps with a :scan key which is either :modified :delete

  modified macros will cause all files using to to be returned as well
  although the files weren't modified physically the macro output may have changed"
  [{:keys [sources macros] :as state}]
  (let [reloadable-paths (query/get-reloadable-source-paths state)]

    ;; FIXME: separate macro scanning from normal scanning
    (let [modified-macros
          (->> macros
               (vals)
               (filter :file)
               (reduce
                 (fn [result {:keys [ns file last-modified] :as macro}]
                   (let [new-mod (.lastModified file)]
                     (if (<= new-mod last-modified)
                       result
                       (let [macro (assoc macro
                                     :scan :macro
                                     :last-modified new-mod)]

                         (conj result macro)))))
                 []))

          affected-by-macros
          (->> modified-macros
               (map :ns)
               (map #(query/get-resources-using-macro state %))
               (reduce set/union))]

      (->> (vals sources)
           (filter #(contains? reloadable-paths (:source-path %)))
           (filter :file)
           (reduce
             (fn [result {:keys [name ^File file last-modified] :as rc}]
               (cond
                 (not (.exists file))
                 (conj result (assoc rc :scan :delete))

                 (contains? affected-by-macros name)
                 (conj result (assoc rc :scan :modified))

                 (> (.lastModified file) last-modified)
                 (conj result (assoc rc :scan :modified))

                 :else
                 result))
             modified-macros)))))

(defn scan-files
  "scans for new and modified files
   returns resources maps with a :scan key with is either :new :modified :delete"
  [state]
  (concat (scan-for-modified-files state)
    (scan-for-new-files state)))

(defn reload-modified-resource
  [{:keys [logger] :as state} {:keys [scan name file ns] :as rc}]
  (case scan
    :macro
    (do (log/log-progress logger (format "[RELOAD] macro: %s" ns))
        (try
          ;; FIXME: :reload enough probably?
          (require ns :reload-all)
          (catch Exception e
            (let [st (with-out-str (pst e))]
              (log/log-warning logger
                (format "MACRO-RELOAD FAILED %s!%n%s" name st)))))
        (assoc-in state [:macros ns] (dissoc rc :scan)))

    :delete
    (do (log/log-progress logger (format "[RELOAD] del: %s" file))
        (common/unmerge-resource state (:name rc)))

    :new
    (do (log/log-progress logger (format "[RELOAD] new: %s" file))
        (common/merge-resource state (common/inspect-resource state (dissoc rc :scan))))

    :modified
    (do (log/log-progress logger (format "[RELOAD] mod: %s" file))
        (let [dependents (query/get-dependent-names state ns)]
          ;; modified files also trigger recompile of all its dependents
          (reduce common/reset-resource-by-name state (cons name dependents))
          ))))

(defn reload-modified-files!
  [state scan-results]
  (as-> state $state
    (reduce reload-modified-resource $state scan-results)
    ;; FIXME: this is kinda ugly but need a way to discover newly required macros
    (macro/discover-macros $state)
    ))

;;-------------------------------------------------------------------

;; configuration stuff
(defn ^{:deprecated "moved to a closure pass, always done on closure optimize"}
enable-emit-constants [state]
  state)

(defn enable-source-maps [state]
  (assoc state :source-map "cljs.closure/make-options expects a string but we dont use it"))

(defn set-build-options [state opts]
  (merge state opts))

(def base-configuration
  {:compiler-env {} ;; will become env/*compiler*

   :ignore-patterns #{#"^node_modules/"
                      #"^goog/demos/"
                      #".aot.js$"
                      #"_test.js$"}

   internal/compiler-state true

   :runtime {:print-fn :console}
   :macros-loaded #{}
   :use-file-min true

   :static-fns true
   :elide-asserts false

   :closure-configurators []

   ;; :none supprt files are placed into <public-dir>/<cljs-runtime-path>/cljs/core.js
   ;; this used to be just "src" but that is too generic and easily breaks something
   ;; if public-dir is equal to the current working directory
   :cljs-runtime-path "cljs-runtime"

   :manifest-cache-dir "target/shadow-build/jar-manifest/v3"
   :cache-dir "target/shadow-build/cljs-cache"
   :cache-level :all

   :public-dir "public/js"
   :public-path "js"

   :optimizations :none
   :n-compile-threads (.. Runtime getRuntime availableProcessors)

   :source-paths {}
   :closure-defines {"goog.DEBUG" false
                     "goog.LOCALE" "en"}})

(defn configure [overrides]
  (with-meta (merge base-configuration overrides) (meta overrides)))

(defn- ->file [path]
  (cond
   (instance? java.io.File path) path
   (string? path) (io/file path)
   :else
   (throw (ex-info "Path must be a string or instance of java.io.File"
                   {:path path}))))

(defn- ->file-with-parents [path]
  (let [file (->file path)]
    (io/make-parents file)
    file))

(defn init-state!
  ([] (init-state! nil))
  ([overrides]
   (-> (configure overrides)
       (update :cache-dir ->file)
       (update :public-dir ->file)
       (update :manifest-cache-dir ->file-with-parents)
       (update :logger #(or % (log/logger)))
       (assoc internal/closure-compiler (closure/make-closure-compiler))
       (closure/add-closure-configurator
        closure/closure-add-replace-constants-pass))))

(def init-state init-state!)

(defn has-tests? [{:keys [requires] :as rc}]
  (contains? requires 'cljs.test))

;;-------------------------------------------------------------------
;; Moved vars

;; Query

(def get-max-last-modified-for-source
  query/get-max-last-modified-for-source)

(def find-resource-by-js-name query/get-resource-by-js-name)

(def find-dependent-names query/get-dependent-names)

(def find-dependents-for-names query/get-dependents-for-names)

(def find-resources-using-macro query/get-resources-using-macro)

(def get-resource-for-provide query/get-resource-for-provide)

(def get-deps-for-src query/get-deps-for-src)

(def get-deps-for-ns query/get-deps-for-ns)

(def get-deps-for-mains query/get-deps-for-mains)

(def get-reloadable-source-paths query/get-reloadable-source-paths)

;; Util

(def is-cljc? util/cljc-file?)

(def is-cljs? util/cljs-file?)

(def directory? util/directory?)

(def read-cache util/read-transit)

(def write-cache util/write-transit)

(def classpath-entries util/classpath-entries)

;; Internal

(def get-closure-compiler internal/get-closure-compiler)


;; Resource

(def inspect-resource common/inspect-resource)

(def merge-resource common/merge-resource)

(def merge-resources common/merge-resources)

(def reset-resource-by-name common/reset-resource-by-name)

(def should-ignore-resource? common/should-ignore-resource?)

(def unmerge-resource common/unmerge-resource)

;; File

(def make-fs-resource file/make-fs-resource)

;; Jar Manifest

(def read-jar-manifest jar/read-jar-manifest)


(def write-jar-manifest jar/write-jar-manifest)

;; Macros

(def discover-macros macro/discover-macros)

;; Cache

(def get-cache-file-for-rc cache/get-cache-file-for-rc)

(def make-age-map cache/make-age-map)

(def load-cached-cljs-resource cache/load-cached-cljs-resource!)

(def write-cached-cljs-resource cache/write-cached-cljs-resource!)

;; Closure

(def goog-base-name closure/goog-base-name)

(def make-closure-compiler closure/make-closure-compiler)

(def closure-add-replace-constants-pass
  closure/closure-add-replace-constants-pass)

(def add-closure-configurator closure/add-closure-configurator)

(def make-closure-modules closure/make-closure-modules)

(def cljs-source-map-for-module closure/cljs-source-map-for-module)

(def closure-optimize closure/closure-optimize)

(def foreign-js-source-for-mod closure/foreign-js-source-for-mod)

(def flush-modules-to-disk closure/flush-optimized-modules-to-disk!)

;; Log

(def BuildLog log/BuildLog)

(def log-warning log/log-warning)

(def log-progress log/log-progress)

(def log-time-start log/log-time-start)

(def log-time-end log/log-time-end)

(def logger log/logger)

(def version 1)

;;-------------------------------------------------------------------
;; Watch

(defn wait-for-modified-files!
  "blocks current thread waiting for modified files
  return resource maps with a :scan key which is either :new :modified :delete"
  [{:keys [logger sources] :as initial-state}]
  (log/log-progress logger "Waiting for modified files ...")
  (loop [state initial-state
         i 0]

    ;; don't scan for new files too frequently
    ;; quite a bit more expensive than just checking a known file

    (let [modified (scan-for-modified-files state)
          modified (if (zero? (mod i 5))
                     (concat modified (scan-for-new-files state))
                     modified)]
      (if (seq modified)
        modified
        (do (Thread/sleep 500)
            (recur state
              (inc i)))))))

(defn wait-and-reload!
  "wait for modified files, reload them and return reloaded state"
  [state]
  (->> (wait-for-modified-files! state)
       (reload-modified-files! state)))

(defn watch-and-repeat! [state callback]
  (loop [state (callback state [])]
    (let [modified (wait-for-modified-files! state)
          state (reload-modified-files! state modified)]
      (recur (try
               (callback state (mapv :name modified))
               (catch Exception e
                 (println (str "COMPILATION FAILED: " e))
                 (.printStackTrace e)
                 state))))))

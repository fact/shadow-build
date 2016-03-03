(ns shadow.cljs.build.closure
  (:require [clojure.data.json :as json]
            [clojure.java.io :as io]
            [clojure.string :as str]
            [cljs.closure :as closure]
            [cljs.source-map :as sm]
            [shadow.cljs.build.internal :as internal]
            [shadow.cljs.log :as log :refer [log-warning
                                             log-progress
                                             log-time-start
                                             log-time-end
                                             with-logged-time]]
            [shadow.cljs.util :as util])
  (:import [com.google.javascript.jscomp
            JSModule
            SourceFile
            SourceFile$Generated
            SourceFile$Generator
            SourceFile$Builder
            JSModuleGraph
            CustomPassExecutionTime
            CommandLineRunner
            CompilerOptions
            ReplaceCLJSConstants]
           [java.io StringWriter]
           [java.util.logging Level]))

(def goog-base-name "goog/base.js")

;; Compiler

(defn ^com.google.javascript.jscomp.Compiler make-closure-compiler []
  (com.google.javascript.jscomp.Compiler/setLoggingLevel Level/WARNING)
  (doto (com.google.javascript.jscomp.Compiler.)
    ;; the thread lingers and prevents the JVM from exiting
    ;; haven't found a clean way to shut it down otherwise
    ;; but given that only one thread is used to compile anyways there
    ;; is really no gain to running in another thread?
    (.disableThreads)))

;; Configuration

(defn closure-add-replace-constants-pass [cc ^CompilerOptions co]
  (.addCustomPass co CustomPassExecutionTime/BEFORE_CHECKS (ReplaceCLJSConstants. cc)))

(defn add-closure-configurator
  "adds a closure configurator 2-arity function that will be called before the compiler is invoked
   signature of the callback is (fn [compiler compiler-options])

   Compiler and CompilerOptions are mutable objects, the return value of the callback is ignored

   CLJS default configuration is done first, all configurators are applied later and may override
   any options.

   See:
   com.google.javascript.jscomp.Compiler
   com.google.javascript.jscomp.CompilerOptions"
  [state callback]
  (update state :closure-configurators conj callback))

;; Module

(defn closure-defines-and-base [{:keys [public-path cljs-runtime-path] :as state}]
  (let [goog-rc (get-in state [:sources goog-base-name])
        goog-base @(:input goog-rc)]

    (when-not (seq goog-base)
      (throw (ex-info "no goog/base.js" {})))

    ;; FIXME: work arround for older cljs versions that used broked closure release, remove.
    (when (< (count goog-base) 500)
      (throw (ex-info "probably not the goog/base.js you were expecting"
               (get-in state [:sources goog-base-name]))))

    (str "var CLOSURE_NO_DEPS = true;\n"
         ;; goog.findBasePath_() requires a base.js which we dont have
         ;; this is usually only needed for unoptimized builds anyways
         "var CLOSURE_BASE_PATH = '" public-path "/" cljs-runtime-path "/';\n"
         "var CLOSURE_DEFINES = "
         (json/write-str (:closure-defines state {}))
         ";\n"
         goog-base
         "\n")))

(defn make-foreign-js-source
  "only need this because we can't control which goog.require gets emitted"
  [{:keys [provides require-order]}]
  (let [sb (StringBuilder.)]
    (doseq [provide provides]
      (doto sb
        (.append "goog.provide(\"")
        (.append (internal/munge-goog-ns provide))
        (.append "\");\n")))
    (doseq [require require-order]
      (doto sb
        (.append "goog.require(\"")
        (.append (internal/munge-goog-ns require))
        (.append "\");\n")))
    (.toString sb)
    ))

(defn make-closure-modules
  "make a list of modules (already in dependency order) and create the closure JSModules"
  [state modules]

  (let [js-mods
        (reduce
          (fn [js-mods {:keys [js-name name depends-on sources prepend-js append-js] :as mod}]
            (let [js-mod (JSModule. js-name)]
              (when (:default mod)
                (.add js-mod (SourceFile/fromCode "closure_setup.js" (closure-defines-and-base state))))
              (when (seq prepend-js)
                (.add js-mod (SourceFile/fromCode (str "mod_" name "_prepend.js") prepend-js)))

              (doseq [{:keys [name type js-name output] :as src} (map #(get-in state [:sources %]) sources)]
                ;; throws hard to track NPE otherwise
                (when-not (and js-name output (seq output))
                  (throw (ex-info "missing output for source" {:js-name js-name :name (:name src)})))

                (if (:foreign src)
                  (.add js-mod (SourceFile/fromCode js-name (make-foreign-js-source src)))
                  (let [input-name (if (= :cljs type) (str "CLJS/" js-name) js-name)]
                    (.add js-mod (SourceFile/fromCode input-name output))
                    )))

              (when (seq append-js)
                (.add js-mod (SourceFile/fromCode (str "mod_" name "_append.js") append-js)))

              (doseq [other-mod-name depends-on
                      :let [other-mod (get js-mods other-mod-name)]]
                (when-not other-mod
                  (throw (ex-info "module depends on undefined module" {:mod name :other other-mod-name})))
                (.addDependency js-mod other-mod))

              (assoc js-mods name js-mod)))
          {}
          modules)]
    (for [{:keys [name] :as mod} modules]
      (assoc mod :js-module (get js-mods name))
      )))

;; Source Maps

(defn cljs-source-map-for-module [sm-text sources opts]
  (let [sm-json (json/read-str sm-text :key-fn keyword)
        closure-source-map (sm/decode sm-json)]
    (loop [sources (seq sources)
           merged (sorted-map-by (sm/source-compare (map :name sources)))]
      (if sources
        (let [{:keys [name js-name] :as source} (first sources)]
          (recur
            (next sources)
            (assoc merged name (sm/merge-source-maps (:source-map source)
                                 (get closure-source-map js-name)))))

        ;; FIXME: sm/encode relativizes paths but we already have relative paths
        ;; there is a bunch of work done over there that we simply dont need
        ;; unfortunatly there is no "simple" workarround
        ;; if that ever changes return result of sm/encode instead of reparsing it
        (-> (sm/encode merged
              {:lines (+ (:lineCount sm-json) 2)
               :file (:file sm-json)})
            (json/read-str)
            (assoc "sources" (keys merged))
            ;; sm/encode pprints
            (json/write-str))))))

;; Optimize

(defn load-externs [{:keys [logger externs build-modules] :as state}]
  (let [default-externs
        (CommandLineRunner/getDefaultExterns)

        manual-externs
        (when (seq externs)
          (log-progress logger "Using externs from options:")
          (->> externs
               (map
                 (fn [ext]
                   (if-let [rc (or (io/resource ext)
                                   (let [file (io/file ext)]
                                     (when (.exists file)
                                       file)))]
                     (do (log-progress logger (format "\t%s" ext))
                         (SourceFile/fromCode (str "EXTERNS/" ext) (slurp rc)))
                     (do (log-warning logger (format "EXTERN missing: %s (file or resource not found)" ext))
                         nil))))
               (remove nil?)
               ;; just to force the logging
               (into [])))

        foreign-externs
        (->> build-modules
             (mapcat :sources)
             (map #(get-in state [:sources %]))
             (filter :foreign)
             (filter :externs-source)
             (map (fn [{:keys [js-name externs externs-source] :as foreign-src}]
                    (log-progress logger (format "Using externs for: %s" js-name))
                    (doseq [ext externs]
                      (log-progress logger (format "\t%s" ext)))
                    (SourceFile/fromCode (str "EXTERNS/" js-name) externs-source)))
             ;; just to force the logging
             (into []))]

    (->> (concat default-externs foreign-externs manual-externs)
         (into []))
    ))

(defn closure-optimize
  "takes the current defined modules and runs it through the closure optimizer

   will return the state with :optimized a list of module which now have a js-source and optionally source maps
   nothing is written to disk, use flush-optimized to write"
  ([state optimizations]
   (-> state
       (assoc :optimizations optimizations)
       (closure-optimize)))
  ([{:keys [logger build-modules closure-configurators] :as state}]
   (when-not (seq build-modules)
     (throw (ex-info "optimize before compile?" {})))

   (with-logged-time
     [logger "Closure optimize"]

     (let [modules (make-closure-modules state build-modules)
           ;; can't use the shared one, that only allows one compile
           cc (make-closure-compiler)
           co (closure/make-options state)

           ;; (fn [closure-compiler compiler-options])
           _ (doseq [cfg closure-configurators]
               (cfg cc co))

           source-map? (boolean (:source-map state))

           externs (load-externs state)

           result (.compileModules cc externs (map :js-module modules) co)]

       (let [errors (.errors result)
             warnings (.warnings result)]
         (doseq [next (seq errors)]
           (log-warning logger (format "CLOSURE-ERROR: %s" (.toString next))))
         (doseq [next (seq warnings)]
           (log-warning logger (format "CLOSURE-WARNING: %s" (.toString next)))))

       (assoc state
         :optimized
         (when (.success result)
           (let [source-map (when source-map?
                              (.getSourceMap cc))]

             (vec (for [{:keys [js-name js-module sources] :as m} modules
                        ;; reset has to be called before .toSource
                        :let [_ (when source-map?
                                  (.reset source-map))
                              output (.toSource cc js-module)]]
                    (-> m
                        (dissoc :js-module)
                        (merge {:output output}
                               (when source-map?
                                 (let [sw (StringWriter.)
                                       sources (map #(get-in state [:sources %]) sources)
                                       source-map-name (str js-name ".map")]
                                   (.appendTo source-map sw source-map-name)
                                   {:source-map-json (cljs-source-map-for-module (.toString sw) sources state)
                                    :source-map-name source-map-name})
                                 ))))))))))))

;; Flush Optimized

(defn foreign-js-source-for-mod [state {:keys [sources] :as mod}]
  (->> sources
       (map #(get-in state [:sources %]))
       (filter :foreign)
       (map :output)
       (str/join "\n")))

;; FIXME: manifest should be custom step
(defn flush-manifest [public-dir modules]
  (spit (io/file public-dir "manifest.json")
    (json/write-str (map #(select-keys % [:name :js-name :mains :depends-on :default :sources]) modules))))

(defn- flush-source-maps [{modules :optimized :keys [^File public-dir cljs-runtime-path] :as state}]
  (with-logged-time
    [(:logger state) "Flushing source maps"]

    (when-not (seq modules)
      (throw (ex-info "flush before optimize?" {})))

    (when-not public-dir
      (throw (ex-info "missing :public-dir" {})))

    (doseq [{:keys [source-map-name source-map-json sources] :as mod} modules]
      (let [target (io/file public-dir cljs-runtime-path source-map-name)]
        (io/make-parents target)
        (spit target source-map-json))

      ;; flush all sources used by this module
      ;; FIXME: flushes all files always, should skip if files already exist and are current
      (doseq [{:keys [type name input] :as src} (map #(get-in state [:sources %]) sources)]
        (let [target (io/file public-dir cljs-runtime-path name)]
          (io/make-parents target)
          (spit target @input))))
    state))

(defn flush-optimized-modules-to-disk!
  [{modules :optimized
    :keys [unoptimizable
           ^File public-dir
           cljs-runtime-path
           logger]
    :as state}]
  (with-logged-time
    [(:logger state) "Flushing modules to disk"]

    (when-not (seq modules)
      (throw (ex-info "flush before optimize?" {})))

    (when-not public-dir
      (throw (ex-info "missing :public-dir" {})))

    (doseq [{:keys [default
                    output
                    prepend
                    source-map-name
                    name
                    js-name] :as mod} modules]
      (let [target (io/file public-dir js-name)
            out (if default
                  (str unoptimizable output)
                  output)
            out (if (:web-worker mod)
                  (let [deps (:depends-on mod)]
                    (str (str/join "\n" (for [other modules
                                              :when (contains? deps (:name other))]
                                          (str "importScripts('" (:js-name other) "');")))
                         "\n\n"
                         out))
                  out)
            out (str prepend (foreign-js-source-for-mod state mod) out)]

        (io/make-parents target)
        (spit target out)

        (log-progress logger (format "Wrote module \"%s\" (size: %d)" js-name (count out)))

        (when source-map-name
          (spit target (str "\n//# sourceMappingURL=" cljs-runtime-path "/" (util/file-basename source-map-name) "\n")
            :append true)))))

  (flush-manifest public-dir modules)

  (when (:source-map state)
    (flush-source-maps state))

  state)

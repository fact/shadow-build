(ns shadow.cljs.build.cache
  (:require [clojure.java.io :as io]
            [cljs.analyzer :as ana]
            [cljs.env :as env]
            [shadow.cljs.log :as log :refer [log-warning
                                             log-progress
                                             log-time-start
                                             log-time-end
                                             with-logged-time]]
            [shadow.cljs.query :as query]
            [shadow.cljs.util :as util])
  (:import [java.io File]))


;; FIXME: must manually bump if anything cache related changes
;; use something similar to clojurescript-version
(def cache-file-version "v4")

(defn- cache-file-name [name]
  (str name "." cache-file-version ".cache.transit.json"))

(defn get-cache-file-for-rc
  ^File [{:keys [cache-dir] :as state} {:keys [name] :as rc}]
  (io/file cache-dir "ana" (cache-file-name name)))

(def cache-affecting-options [:static-fns :elide-asserts])

(defn make-age-map
  "procudes a map of {source-name last-modified} for caching to identify
   whether a cache is safe to use (if any last-modifieds to not match if is safer to recompile)"
  [state ns]
  (reduce
    (fn [age-map source-name]
      (let [last-modified (query/get-max-last-modified-for-source state source-name)]
        ;; zero? is a pretty ugly indicator for deps that should not affect cache
        ;; eg. runtime-setup
        (if (pos? last-modified)
          (assoc age-map source-name last-modified)
          age-map)))
    {}
    (query/get-deps-for-ns state ns)))

(defn load-cached-cljs-resource!
  [{:keys [logger cache-dir cljs-runtime-path] :as state}
   {:keys [ns js-name name last-modified] :as rc}]
  (let [cache-file (get-cache-file-for-rc state rc)
        cache-js (io/file cache-dir cljs-runtime-path js-name)]

    (when (and (.exists cache-file)
               (> (.lastModified cache-file) last-modified)
               (.exists cache-js)
               (> (.lastModified cache-js) last-modified))

      (let [cache-data (util/read-transit cache-file)
            age-of-deps (make-age-map state ns)]

        ;; just checking the "maximum" last-modified of all dependencies is not enough
        ;; must check times of all deps, mostly to guard against jar changes
        ;; lib-A v1 was released 3 days ago
        ;; lib-A v2 was released 1 day ago
        ;; we depend on lib-A and compile against v1 today
        ;; realize that a new version exists and update deps
        ;; compile again .. since we were compiled today the min-age is today
        ;; which is larger than v2 release date thereby using cache if only checking one timestamp

        (when (and (= (:source-path cache-data) (:source-path rc))
                   (= age-of-deps (:age-of-deps cache-data))
                   (every? #(= (get state %) (get cache-data %)) cache-affecting-options))
          (log-progress logger (format "[CACHE] read: \"%s\"" name))

          ;; restore analysis data
          (let [ana-data (:analyzer cache-data)]

            (swap! env/*compiler* assoc-in [::ana/namespaces (:ns cache-data)] ana-data)
            (util/load-macros ana-data))

          ;; merge resource data & return it
          (-> (merge rc cache-data)
              (dissoc :analyzer)
              (assoc :output (slurp cache-js))))))))

(defn write-cached-cljs-resource!
  [{:keys [logger cache-dir cljs-runtime-path] :as state}
   {:keys [ns name js-name] :as rc}]

  ;; only cache files that don't have warnings!
  (when-not (seq (:warnings rc))

    (let [cache-file (get-cache-file-for-rc state rc)
          cache-data (-> rc
                         (dissoc :file :output :input :url)
                         (assoc :age-of-deps (make-age-map state ns)
                                :analyzer (get-in @env/*compiler* [::ana/namespaces ns])))
          cache-data (reduce
                       (fn [cache-data option-key]
                         (assoc cache-data option-key (get state option-key)))
                       cache-data
                       cache-affecting-options)
          cache-js (io/file cache-dir cljs-runtime-path js-name)]

      (io/make-parents cache-file)
      (util/write-transit cache-file cache-data)

      (io/make-parents cache-js)
      (spit cache-js (:output rc))

      (log-progress logger (format "[CACHE] write: \"%s\"" name)))))

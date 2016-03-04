(ns shadow.cljs.build.resource.file
  (:require [clojure.java.io :as io]
            [shadow.cljs.build.internal :refer [compiler-state?]]
            [shadow.cljs.build.resource.common :as common]
            [shadow.cljs.query :as query]
            [shadow.cljs.util :as util])
  (:import [java.io
            File]))

(defn make-fs-resource [state source-path rc-name ^File rc-file]
  (common/inspect-resource
    state
    {:name rc-name
     :file rc-file
     :source-path source-path
     :last-modified (.lastModified rc-file)
     :url (.toURL (.toURI rc-file))
     :input (delay (slurp rc-file))}))

(defn find-fs-resources
  [state ^String path]
  {:pre [(compiler-state? state)
         (seq path)]}
  (let [root (io/file path)
        root-path (.getCanonicalPath root)
        root-len (inc (count root-path))

        manifest
        (->> (for [^File file (file-seq root)
                   :let [file (.getCanonicalFile file)
                         abs-path (.getCanonicalPath file)]
                   :when (and (util/cljs-resource? abs-path)
                              (not (.isHidden file)))
                   :let [name (-> abs-path
                                  (.substring root-len)
                                  (common/normalize-resource-name))]
                   :when (not (common/should-ignore-resource? state name))]

               (make-fs-resource state path name file))
             (map (juxt :name identity))
             (into {}))]

    (-> (common/process-deps-cljs state manifest path)
        (vals))))

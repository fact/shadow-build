(ns shadow.cljs.build.resource.jar
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [shadow.cljs.build.internal :refer [compiler-state?]]
            [shadow.cljs.build.resource.common :as common]
            [shadow.cljs.util :as util])
  (:import [java.io
            File]
           [java.net
            URL]
           [java.util.jar
            JarEntry
            JarFile]))


;; Jar Manifest

(defn create-jar-manifest
  "returns a map of {source-name resource-info}"
  [state path]
  {:pre [(compiler-state? state)]}
  (let [file (io/file path)
        abs-path (.getCanonicalPath file)
        jar-file (JarFile. file)
        last-modified (.lastModified file)
        entries (.entries jar-file)
        slurp-entry (fn [entry]
                      (with-open [in (.getInputStream jar-file entry)]
                        (slurp in)))]
    (loop [result (transient {})]
      (if (not (.hasMoreElements entries))
        (persistent! result)
        (let [^JarEntry jar-entry (.nextElement entries)
              name (.getName jar-entry)]
          (if (or (not (util/cljs-resource? name))
                  (common/should-ignore-resource? state name))
            (recur result)
            (let [url (URL. (str "jar:file:" abs-path "!/" name))
                  rc (common/inspect-resource state
                       {:name (common/normalize-resource-name name)
                        :from-jar true
                        :source-path path
                        :last-modified last-modified
                        :url url
                        :input (atom (slurp-entry jar-entry))})]
              (recur (assoc! result name rc))
              )))))))

(defn read-jar-manifest [file]
  (let [entries (util/read-transit file)]
    (reduce
      (fn [m {:keys [name url] :as v}]
        (assoc m name (assoc v :input (delay (slurp url)))))
      {}
      entries)))

(defn write-jar-manifest [file manifest]
  (let [data (->> (vals manifest)
                  ;; :input is non serializable deref, don't want to store actual content
                  ;; might not need it, just a performance issue
                  ;; reading closure jar with js contents 300ms without content 5ms
                  ;; since we are only using a small percentage of those file we delay reading
                  (map #(dissoc % :input))
                  (into []))]
    (util/write-transit file data)
    ))

(defn find-jar-resources
  [{:keys [manifest-cache-dir] :as state} path]
  {:pre [(compiler-state? state)]}
  ;; FIXME: assuming a jar with the same name and same last modified is always identical, probably not. should md5 the full path?
  (let [manifest-name (let [jar (io/file path)]
                        (str (.lastModified jar) "-" (.getName jar) ".manifest"))
        mfile (io/file manifest-cache-dir manifest-name)
        jar-file (io/file path)
        manifest (if (and (.exists mfile)
                          (>= (.lastModified mfile) (.lastModified jar-file)))
                   (read-jar-manifest mfile)
                   (let [manifest (create-jar-manifest state path)]
                     (io/make-parents mfile)
                     (write-jar-manifest mfile manifest)
                     manifest))]
    (-> (common/process-deps-cljs state manifest path)
        (vals))))

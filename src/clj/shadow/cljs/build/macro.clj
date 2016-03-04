(ns shadow.cljs.build.macro
  (:require [clojure.java.io :as io]
            [shadow.cljs.log :as log]
            [shadow.cljs.util :as util])
  (:import [java.net URL]))

(defn set-conj [x y]
  (if x
    (conj x y)
    #{y}))

(defn macros-used-by
  [state]
  (reduce-kv
   (fn [macro-info _ {:keys [macros name]}]
     (reduce (fn [macro-info macro-ns]
               (update-in macro-info [macro-ns] set-conj name))
             macro-info
             macros))
   {}
   (:sources state)))

(defn discover-macros [{:keys [logger] :as state}]
  ;; build {macro-ns #{used-by-source-by-name ...}}
  (let [macro-info
        (->> (macros-used-by state)
             (map (fn [[macro-ns used-by]]
                    (let [name (str (util/ns->path macro-ns) ".clj")
                          url (io/resource name)
                          ;; FIXME: clean this up, must look for .clj and .cljc
                          [name url] (if url
                                       [name url]
                                       (let [name (str name "c")]
                                         [name (io/resource name)]))]

                      ;; SDB - uncomment this warning?
                      #_(when-not url (log/log-warning logger (format "Macro namespace: %s not found, required by %s" macro-ns used-by)))
                      {:ns macro-ns
                       :used-by used-by
                       :name name
                       :url url})))
             ;; always get last modified for macro source
             (map (fn [{:keys [url] :as info}]
                    (if (nil? url)
                      info
                      (let [con (.openConnection ^URL url)]
                        (assoc info :last-modified (.getLastModified con)))
                      )))
             ;; get file (if not in jar)
             (map (fn [{:keys [^URL url] :as info}]
                    (if (nil? url)
                      info
                      (if (not= "file" (.getProtocol url))
                        info
                        (let [file (io/file (.getPath url))]
                          (assoc info :file file))))))
             (map (juxt :ns identity))
             (into {}))]
    (assoc state :macros macro-info)
    ))

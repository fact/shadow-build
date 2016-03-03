(ns shadow.cljs.build.resource.jar
  (:require [shadow.cljs.util :as util]))


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

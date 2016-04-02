(ns shadow.cljs.test
  (:require [shadow.cljs.build :as cljs]
            [shadow.cljs.query :as query]
            [shadow.cljs.schemas :as schemas]
            [clojure.string :as str]))

(def has-tests?-xf
  (filter cljs/has-tests?))

(defn test-namespace-xf []
  (comp query/remove-jar-xf
        has-tests?-xf
        query/namespace-xf
        (distinct)))

(defn find-affected-test-namespaces-from-sources
  [state changed-sources]
  (let [dependents (query/sources->dependents state changed-sources)]
    (vec (sequence (test-namespace-xf)
                   (concat changed-sources dependents)))))

(defn find-all-test-namespaces
  [state]
  (vec (sequence (comp (query/source-name->source-xf state) (test-namespace-xf))
                 (query/source-names state))))

(defn find-affected-test-namespaces
  [state changed-source-names]
  (let [dependents (cljs/find-dependents-for-names state changed-source-names)]
    (vec (sequence (comp (query/source-name->source-xf state) (test-namespace-xf))
                   (concat changed-source-names dependents)))))

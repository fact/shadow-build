(ns shadow.cljs.build.internal
  (:require [clojure.string :as str]))

(def compiler-state ::is-compiler-state)

(defn compiler-state? [state]
  (true? (compiler-state state)))

(def closure-compiler ::cc)

(defn get-closure-compiler [state]
  (closure-compiler state))

(defn munge-goog-ns [s]
  (-> s
      (str/replace #"_" "-")
      (symbol)))

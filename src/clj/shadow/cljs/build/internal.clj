(ns shadow.cljs.build.internal)

(def compiler-state ::is-compiler-state)

(defn compiler-state? [state]
  (true? (compiler-state state)))

(def closure-compiler ::cc)

(defn get-closure-compiler [state]
  (closure-compiler state))

(ns shadow.cljs.query
  (:require [clojure.set :as set]
            [clojure.string :as str]
            [shadow.cljs.build.internal :refer [compiler-state?]]))


;;-------------------------------------------------------------------
;; Accessors

(defn sources
  [state]
  (vals (:sources state)))

(defn source-names
  [state]
  (keys (:sources state)))

(defn source-paths
  [state]
  (vals (:source-paths state)))

;;-------------------------------------------------------------------
;; Query Modifiers and Relations

(def remove-jar-xf
  (remove :from-jar))

(def namespace-xf
  (map :ns))

(def name-xf
  (map :name))

(defn source-name->source
  [state source-name]
  (get-in state [:sources source-name]))

(defn source-name->ns-symbol
  [state source-name]
  (get-in state [:sources source-name :provides]))

;;-------------------------------------------------------------------
;; Joins

(defn source-name->ns-symbol-xf
  [state]
  (map (partial source-name->ns-symbol state)))

(defn source-name->source-xf
  [state]
  (map (partial source-name->source state)))

(defn dependents-xf
  [ns-symbol]
  (filter (fn [{:keys [requires]}] (requires ns-symbol))))

(defn source->dependents-xf
  [state source]
  (dependents-xf (source-name->ns-symbol state source)))

(defn source->dependent-names-xf
  [state source]
  (comp (source->dependents-xf state source) name-xf))

;;-------------------------------------------------------------------
;; Queries

(defn source->dependents
  [state source]
  (set (sequence (source->dependents-xf state source) (sources state))))

(defn source-name->dependents
  [state source-name]
  (source->dependents state (source-name->source state source-name)))

(defn source-name->dependent-names
  [state source-name]
  (let [xf (source->dependent-names-xf state
                                       (source-name->source state source-name))]
    (set (sequence xf (sources state)))))

(defn source-symbol->dependent-names
  [state source-symbol]
  (set (sequence (comp (dependents-xf source-symbol) name-xf)
                 (sources state))))

(defn sources->dependents
  [state sources]
  (->> sources
       (mapcat (partial source->dependents state))
       (into #{})))

(defn conj-in [m k v]
  (update-in m k (fn [old] (conj old v))))

(defn get-reloadable-source-paths [state]
  (->> state
       (source-paths)
       (filter :reloadable)
       (map :path)
       (set)))

(defn get-max-last-modified-for-source [state source-name]
  (let [{:keys [last-modified macros] :as rc} (get-in state [:sources source-name])]

    (transduce
      (map #(get-in state [:macros % :last-modified]))
      (completing
        (fn [a b]
          (Math/max ^long a ^long b)))
      last-modified
      macros
      )))

(defn get-resource-by-js-name [state js-name]
  {:pre [(compiler-state? state)
         (string? js-name)]}
  (let [rcs (filterv #(= js-name (:js-name %)) (sources state))]
    (when (not= 1 (count rcs))
      ;; FIXME: this should be checked when scanning for resources
      (throw (ex-info (format "multiple resources for js-name:%s" js-name)
               {:js-name js-name
                :resources rcs})))
    (first rcs)))

(defn get-dependent-names
  [state ns-sym]
  (->> state
       (sources)
       (filter (fn [{:keys [requires]}]
                 (contains? requires ns-sym)))
       (map :name)
       (into #{})
       ))

(defn get-dependents-for-names [state source-names]
  (->> source-names
       (map #(get-in state [:sources % :provides]))
       (reduce set/union)
       (map #(get-dependent-names state %))
       (reduce set/union)
       (into #{})))

(defn get-resource-for-provide [state ns-sym]
  {:pre [(compiler-state? state)
         (symbol? ns-sym)]}
  (when-let [name (get-in state [:provide->source ns-sym])]
    (get-in state [:sources name])))

(defn get-resources-using-macro
  "returns a set of names using the macro ns"
  [state macro-ns]
  (let [direct-dependents (->> state
                               (sources)
                               (filter (fn [{:keys [macros] :as rc}]
                                         (contains? macros macro-ns)))
                               (map :name)
                               (into #{}))]

    ;; macro has a companion .cljs file
    ;; FIXME: should check if that file actually self references
    (if (get-resource-for-provide state macro-ns)
      (-> (get-dependent-names state macro-ns)
          (set/union direct-dependents))
      direct-dependents
      )))

(defn- get-deps-for-src* [{:keys [deps-stack] :as state} name]
  {:pre [(compiler-state? state)]}
  (when-not (string? name)
    (throw (ex-info (format "trying to get deps for \"%s\"" (pr-str name)) {})))

  (cond
    ;; don't run in circles
    (some #(= name %) deps-stack)
    (let [path (->> (conj deps-stack name)
                    (drop-while #(not= name %))
                    (str/join " -> "))]
      (throw (ex-info (format "circular dependency: %s" path) {:name name :stack deps-stack})))

    ;; don't revisit
    (contains? (:deps-visited state) name)
    state

    :else
    (let [requires (get-in state [:sources name :require-order])]
      (when-not (and requires (vector? requires))
        (throw (ex-info (format "cannot find required deps for \"%s\"" name) {:name name})))

      (let [state (-> state
                      (conj-in [:deps-visited] name)
                      (conj-in [:deps-stack] name))
            state (->> requires
                       (map (fn [require-sym]
                              (let [src-name (get-in state [:provide->source require-sym])]
                                (when-not src-name
                                  (throw
                                    (ex-info
                                      (format "ns \"%s\" not available, required by %s" require-sym name)
                                      {:ns require-sym
                                       :src name})))
                                src-name
                                )))
                       (into [] (distinct))
                       (reduce get-deps-for-src* state))
            state (update state :deps-stack (fn [stack] (into [] (butlast stack))))]
        (conj-in state [:deps-ordered] name)
        ))))

(defn get-deps-for-src
  "returns names of all required sources for a given resource by name (in dependency order), does include self
   (eg. [\"goog/string/string.js\" \"cljs/core.cljs\" \"my-ns.cljs\"])"
  [state src-name]
  {:pre [(compiler-state? state)
         (string? src-name)]}
  (-> state
      (assoc :deps-stack []
             :deps-ordered []
             :deps-visited #{})
      (get-deps-for-src* src-name)
      :deps-ordered))

(defn get-deps-for-ns
  "returns names of all required sources for a given ns (in dependency order), does include self
   (eg. [\"goog/string/string.js\" \"cljs/core.cljs\" \"my-ns.cljs\"])"
  [state ns-sym]
  {:pre [(compiler-state? state)
         (symbol? ns-sym)]}
  (let [name (get-in state [:provide->source ns-sym])]
    (when-not name
      (let [reqs (->> state
                      (sources)
                      (filter #(contains? (:requires %) ns-sym))
                      (map :name)
                      (into #{}))]
        (throw (ex-info (format "ns \"%s\" not available, required by %s" ns-sym reqs) {:ns ns-sym :required-by reqs}))))

    (get-deps-for-src state name)
    ))

(defn get-deps-for-mains [state mains]
  (->> mains
       (mapcat #(get-deps-for-ns state %))
       (distinct)
       (into [])))

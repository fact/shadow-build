(ns shadow.cljs.log)

;; Protocol

(defprotocol BuildLog
  (log-warning [this log-string])
  (log-progress [this log-string])
  (log-time-start [this log-string])
  (log-time-end [this log-string time-in-ms]))

;; Logger

(defn logger []
  (let [log-lock (Object.)]
    (reify BuildLog
      (log-warning [_ msg]
                   (locking log-lock
                     (println (str "WARN: " msg))))
      (log-time-start [_ msg]
                      (locking log-lock
                        (println (format "-> %s" msg))))
      (log-time-end [_ msg ms]
                    (locking log-lock
                      (println (format "<- %s (%dms)" msg ms))))
      (log-progress [_ msg]
                    (locking log-lock
                      (println msg))))))

(def ^{:dynamic true} *time-depth* 0)

(defmacro with-logged-time
  [[logger msg] & body]
  `(let [msg# ~msg]
     (log-time-start ~logger msg#)
     (let [start# (System/currentTimeMillis)
           result# (binding [*time-depth* (inc *time-depth*)]
                     ~@body)]
       (log-time-end ~logger msg# (- (System/currentTimeMillis) start#))
       result#)))

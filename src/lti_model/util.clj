(ns lti-model.util
  )

; Poly -> (Vec '{:op ':F})
(defn Poly-frees [p]
  {:pre [(= :Poly (:op p))]}
  (mapv (fn [s]
          {:pre [(symbol? s)]}
          {:op :F :name (with-meta (gensym s) {:original-name s})
           :original-name s})
        (:syms p)))

(def -Int {:op :Base :name 'Int})
(def -Num {:op :Base :name 'Num})
(def -any {:op :Intersection :types #{}})
(def -nothing {:op :Union :types #{}})
(defn IFn? [t] (= :IFn (:op t)))
(defn Base? [t] (= :Base (:op t)))
(defn Poly? [t] (= :Poly (:op t)))
(defn Fn? [t] (= :Fn (:op t)))


(defn make-U [ts]
  (let [ts (set
             (mapcat (fn [t]
                       (if (= :Union (:op t))
                         (:types t)
                         [t]))
                     ts))
        _ (assert (not (ts -nothing)))
        ts (if (contains? ts -Num)
             (disj ts -Int)
             ts)]
    (cond
      (contains? ts -any) -any
      (= (count ts) 1) (first ts)
      :else {:op :Union
             :types ts})))

(defn make-I [ts]
  (let [ts (mapcat (fn [t]
                     (if (= :Intersection (:op t))
                       (:types t)
                       [t]))
                   ts)
        ts (disj (set ts)
                 -any)]
    (cond
      (contains? ts -nothing) -nothing
      (= (count ts) 1) (first ts)
      :else {:op :Intersection
             :types ts})))

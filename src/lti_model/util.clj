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

; Name T [[Integer T -> T] Integer T -> (U nil T)] -> Scope
(defn abstract-by [n t f]
  (letfn [; Integer T -> T
          (name-to [outer t]
            {:pre [(:op t)
                   (integer? outer)]}
            (let [nt #(name-to outer %)
                  ntv #(mapv nt %)]
              (or (f name-to outer t)
                  (case (:op t)
                    (:B :Base) t
                    :Union (make-U (map nt (:types t)))
                    :Intersection (make-I (map nt (:types t)))
                    :Seq (update t :type nt)
                    :F (if (= n (:name t))
                         {:op :B
                          :index outer}
                         t)
                    :Poly (-> t
                              (update :type nt)
                              (update :constraints (fn [cs]
                                                     (mapv #(-> %
                                                                (update :lower nt)
                                                                (update :upper nt))
                                                           cs)))
                              (update :bounds (fn [bs]
                                                (mapv #(-> %
                                                           (update :lower nt)
                                                           (update :upper nt))
                                                      bs))))
                    :Fn (-> t
                            (update :dom ntv)
                            (update :rng nt))
                    :IFn (update t :methods ntv)
                    :Scope (update t :scope #(name-to (inc outer) %))))))]
    {:op :Scope
     :scope (name-to 0 t)}))

; (Vec Name) T [Name T -> Scope] -> Scope
(defn abstract-all-by [syms t ab]
  {:pre [(vector? syms)]}
  (reduce (fn [t sym]
            (ab sym t))
          t
          (rseq syms)))

; [T -> T] T [T -> (U nil T)] -> T
(defn walk-type-by [f t custom-walk]
  (let [wlk #(f %)]
    (or (custom-walk t)
        (case (:op t)
          (:F :Base :B) t
          :Union (make-U (map wlk (:types t)))
          :Intersection (make-I (map wlk (:types t)))
          :Seq (update t :type wlk)
          :Poly (-> t
                    (update :type wlk)
                    (update :constraints (fn [cs]
                                           (mapv #(-> %
                                                      (update :lower wlk)
                                                      (update :upper wlk))
                                                 cs)))
                    (update :bounds (fn [bs]
                                      (mapv #(-> %
                                                 (update :lower wlk)
                                                 (update :upper wlk))
                                            bs))))
          :Fn (-> t
                  (update :dom #(mapv wlk %))
                  (update :rng wlk))
          :IFn (update t :methods #(mapv wlk %))
          :Scope (update t :scope wlk)))))

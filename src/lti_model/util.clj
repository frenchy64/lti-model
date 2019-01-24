(ns lti-model.util
  )

(def type-error-kw ::type-error)

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

; T Scope [[Int T -> T] Int T -> (U nil T)] -> T
(defn instantiate-by [image t f]
  {:pre [(= :Scope (:op t))
         (:op image)]
   :post [(:op %)]}
  (letfn [; Integer T -> T
          (replace [outer t]
            {:pre [(integer? outer)]
             :post [(:op %)]}
            (let [rp #(replace outer %)
                  rpv #(mapv rp %)]
              (or (f replace outer t)
                  (case (:op t)
                    (:F :Base) t
                    :Union (make-U (map rp (:types t)))
                    :Intersection (make-I (map rp (:types t)))
                    :Seq (update t :type rp)
                    :Poly (-> t
                              (update :type rp)
                              (update :constraints (fn [cs]
                                                     (mapv #(-> %
                                                                (update :lower rp)
                                                                (update :upper rp))
                                                           cs)))
                              (update :bounds (fn [bs]
                                                (mapv #(-> %
                                                           (update :lower rp)
                                                           (update :upper rp))
                                                      bs))))
                    :B (if (= outer (:index t))
                         image
                         t)
                    :Fn (-> t
                            (update :dom rpv)
                            (update :rng rp))
                    :IFn (update t :methods rpv)
                    :Scope (update t :scope #(replace (inc outer) %))))))]
    (replace 0 (:scope t))))

; (Seqable T) Scope [T Scope -> T] -> T
(defn instantiate-all-by [images t ins]
  (reduce (fn [t image]
            (ins image t))
          t
          images))

; Poly (Seqable Type) [(Seqable T) Scope -> T] -> Type
(defn Poly-body-by [p images instantiate-all-fn]
  {:pre [(= :Poly (:op p))
         (= (count images) (count (:syms p)))]
   :post [(:op %)]}
  (instantiate-all-fn images (:type p)))

; (Seqable Sym) Type -> Poly
(defn Poly*-by [syms t abstract-all-fn & {:keys [constraints original-names bounds]}]
  {:pre [(every? symbol? syms)
         (apply distinct? syms)
         (vector? syms)
         (:op t)
         (or (nil? original-names)
             (and (= (count syms) (count original-names))
                  (every? symbol? original-names)
                  (apply distinct? original-names)))
         (or (nil? bounds)
             (= (count syms) (count bounds)))
         ]}
  (let [ab (abstract-all-fn syms t)
        constraints (mapv (fn [c]
                            (-> c
                                (select-keys [:lower :upper])
                                (update :lower #(abstract-all-fn syms %))
                                (update :upper #(abstract-all-fn syms %))))
                          constraints)
        bounds (mapv (fn [b]
                       (-> b
                           (update :lower #(abstract-all-fn syms %))
                           (update :upper #(abstract-all-fn syms %))))
                     (or bounds
                         (repeat (count syms) {:lower -nothing :upper -any})))]
    {:op :Poly
     :syms (or original-names (vec syms))
     :bounds bounds
     :constraints constraints
     :type ab}))

(def ^:dynamic *tvar* #{})

(defn parse-type-by [t {:keys [Poly* parse-type]}]
  (let [parse-fn-arity (fn [t]
                         {:pre [(vector? t)]}
                         (let [[args [_ ret & more]] (split-with (complement #{:->}) t)]
                           (when more
                             (throw (ex-info (str "Extra arguments after :-> in function type: " more)
                                             {type-error-kw true})))
                           {:op :Fn
                            :dom (mapv parse-type args)
                            :rng (parse-type ret)}))]
    (cond
      (vector? t) {:op :IFn
                   :methods [(parse-fn-arity t)]}
      (seq? t) (case (first t)
                 U (make-U (map parse-type (rest t)))
                 I (make-I (map parse-type (rest t)))
                 Seq {:op :Seq
                      :type (parse-type (second t))}
                 All (let [[syms t] (rest t)]
                       (binding [*tvar* (into *tvar* syms)]
                         (Poly* syms (parse-type t))))
                 IFn (let [methods (mapv parse-fn-arity (rest t))]
                       (assert (seq methods))
                       {:op :IFn
                        :methods methods}))
      ('#{Int} t) -Int
      ('#{Num} t) -Num
      ('#{Any} t) -any
      ('#{Nothing} t) -nothing
      ((every-pred symbol? *tvar*) t) {:op :F :name t}
      :else (assert false (str "Error parsing type: " t)))))

(def ^:dynamic *verbose-types* nil)

(defn unparse-type-by [t {:keys [Poly-frees
                                 Poly-body
                                 Poly-constraints
                                 unparse-env
                                 Poly-bounds
                                 unparse-type]}]
  (case (:op t)
    ; TODO move out the constraint/bounds logic
    :Poly (let [gs (Poly-frees t)
                body (unparse-type (Poly-body t gs))
                constraints (mapv (fn [{:keys [lower upper]}]
                                    [(unparse-type lower) :< (unparse-type upper)])
                                  (Poly-constraints t gs))]
            (list 'All
                  (into (mapv (fn [v b]
                                (let [n ((some-fn #(when-not *verbose-types*
                                                     (:original-name %))
                                                  :name) v)]
                                  (cond
                                    (and (= -any (:upper b))
                                         (= -nothing (:lower b)))
                                    n
                                    (= -any (:upper b))
                                    [n :lower (unparse-type (:lower b))]
                                    (= -nothing (:lower b))
                                    [n :upper (unparse-type (:upper b))]
                                    :else 
                                    [n :lower (unparse-type (:lower b)) :upper (unparse-type (:upper b))])))
                              gs (Poly-bounds t gs))
                        (when (seq constraints)
                          [:constraints (set constraints)]))
                  body))
    :F (or (when (not *verbose-types*)
             (:original-name t))
           (:name t))
    :B (:index t)
    :Union (if (empty? (:types t))
             'Nothing
             (list* 'U (mapv unparse-type (:types t))))
    :Intersection (if (empty? (:types t))
                    'Any
                    (list* 'I (mapv unparse-type (:types t))))
    :Seq (list 'Seq (unparse-type (:type t)))
    :Base (:name t)
    :Fn (let [dom (mapv unparse-type (:dom t))
              rng (unparse-type (:rng t))]
          (vec (concat dom [:-> rng])))
    :IFn (let [methods (mapv unparse-type (:methods t))]
           (if (= 1 (count methods))
             (first methods)
             (doall (list* 'IFn methods))))
    (assert nil (str "Cannot unparse type: " (pr-str t)))))

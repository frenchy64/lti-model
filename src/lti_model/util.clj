(ns lti-model.util
  (:require [clojure.string :as str]))

(def type-error-kw ::type-error)

(defmacro handle-type-error [f & body]
  `(try (do ~@body)
        (catch clojure.lang.ExceptionInfo e# 
          (if (type-error-kw (ex-data e#))
            (~f e#)
            (throw e#)))))

(defmacro throws-type-error? [e]
  `(handle-type-error (fn [^Exception e#]
                        ;(println (.getMessage e#))
                        true)
     (do ~e
         false)))

(defn Type? [t] (and (map? t) (keyword? (:op t))))

#_
(t/defalias Result
  '{:e E
    :t T})

(defn Result? [r]
  (and (map? r)
       (contains? r :e)
       (Type? (:t r))))

(defn ->Result [e t]
  {:post [(Result? %)]}
  {:e e
   :t t})

(defn ret-t [r]
  {:pre [(Result? r)]
   :post [(Type? %)]}
  (:t r))

(defn ret-e [r]
  {:pre [(Result? r)]}
  (:e r))

(def -Int {:op :Base :name 'Int})
(def -Str {:op :Base :name 'Str})
(def -Num {:op :Base :name 'Num})
(def -any {:op :Intersection :types #{}})
(def -nothing {:op :Union :types #{}})
(def -anyfunction {:op :IFn :methods []})

(defmacro ^:private make-op-predicate [nme]
  `(defn ~(symbol (str nme "?")) [t#]
     (= ~(keyword nme)
        (:op t#))))
(make-op-predicate IFn)
(make-op-predicate Base)
(make-op-predicate Poly)
(make-op-predicate Fn)
(make-op-predicate Seq)
(make-op-predicate Intersection)
(make-op-predicate Union)
(make-op-predicate Mu)
(make-op-predicate F)
(make-op-predicate PApp)
(make-op-predicate Scope)
(make-op-predicate EnclosingFnCase)

; Poly -> (Vec F)
(defn Poly-frees [p]
  {:pre [(Poly? p)]
   :post [(vector? %)
          (< 0 (count %))
          (every? F? %)]}
  (mapv (fn [s]
          {:pre [(symbol? s)]}
          {:op :F :name (with-meta (gensym s) {:original-name s})
           :original-name s})
        (:syms p)))

; Mu -> F
(defn Mu-free [p]
  {:pre [(Mu? p)]
   :post [(F? %)]}
  (let [s (:sym p)]
    (assert (symbol? s))
    {:op :F :name (with-meta (gensym s) {:original-name s})
     :original-name s}))

; (Seqable T) -> T
(defn make-U [ts]
  {:pre [(every? Type? ts)]
   :post [(Type? %)]}
  (let [ts (set
             (mapcat (fn [t]
                       (if (Union? t)
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

; (Seqable T) -> T
(defn make-I [ts]
  {:pre [(every? Type? ts)]
   :post [(Type? %)]}
  (let [ts (mapcat (fn [t]
                     (if (Intersection? t)
                       (:types t)
                       [t]))
                   ts)
        ; (I Any t) => t
        ts (disj (set ts)
                 -any)
        ; (I (IFn) (IFn <arities>)) => (IFn <arities>)
        ts (if (and (contains? ts -anyfunction)
                    (some (fn [t]
                            (and (IFn? t)
                                 (seq (:methods t))))
                          ts))
             (disj ts -anyfunction)
             ts)]
    (cond
      ; (I Nothing t) => Nothing
      (contains? ts -nothing) -nothing
      ; (I t) => t
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
                    :Mu (-> t
                            (update :type nt))
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
  (let [wlk #(f %)
        wlkv #(do
                (assert (vector? %))
                (mapv f %))]
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
                  (update :dom wlkv)
                  (update :rng wlk))
          :IFn (update t :methods wlkv)
          :PApp (-> t
                    (update :poly wlk)
                    (update :args wlkv))
          :Scope (update t :scope wlk)))))

; T Scope [[Int T -> T] Int T -> (U nil T)] -> T
(defn instantiate-by [image t f]
  {:pre [(Type? image)
         (= :Scope (:op t))]
   :post [(Type? %)]}
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
                    :Mu (-> t
                            (update :type rp))
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

(defn Poly-constraints-by [p images instantiate-all]
  {:pre [(= :Poly (:op p))
         (= (count images) (count (:syms p)))]}
  (mapv (fn [c]
          (-> c
              (update :lower #(instantiate-all images %))
              (update :upper #(instantiate-all images %))))
        (:constraints p)))

(defn Poly-bounds-by [p images instantiate-all]
  {:pre [(= :Poly (:op p))
         (= (count images) (count (:bounds p)))]}
  (mapv (fn [b]
          (-> b
              (update :lower #(instantiate-all images %))
              (update :upper #(instantiate-all images %))))
        (:bounds p)))

; F Mu [T Scope -> T] -> Type
(defn Mu-body-by [image p instantiate-fn]
  {:pre [(Type? image)
         (Mu? p)]
   :post [(Type? %)]}
  (instantiate-fn image (:type p)))

(defn subst-by [sb t {:keys [abstract-all instantiate-all]}]
  {:pre [(map? sb)
         (Type? t)]
   :post [(Type? %)]}
  (->> t
       (abstract-all (vec (keys sb)))
       (instantiate-all (vec (vals sb)))))

; Mu -> Type
(defn unfold-by [m {:keys [Mu-body subst]}]
  {:pre [(Mu? m)]
   :post [(Type? %)]}
  (let [sym (Mu-free m)
        body (Mu-body sym m)]
    (subst {(:name sym) m} body)))

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

(defn validate-Mu-body [m]
  (case (:op m)
    :IFn nil
    (throw (ex-info (str "Not allowed in Rec body: " (:op m))
                    {type-error-kw true}))))

; Sym Type [Sym Scope -> Type] -> Type
(defn Mu*-by [sym t abstract-fn & {:keys [original-name]}]
  {:pre [(symbol? sym)
         (Type? t)
         ((some-fn nil? symbol?) original-name)]}
  (let [_ (validate-Mu-body t)
        ab (abstract-fn sym t)]
    {:op :Mu
     :sym (or original-name sym)
     :type ab}))

(def ^:dynamic *tvar* #{})

(defn parse-type-by [t {:keys [Poly* Mu* parse-type]}]
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
                 Rec (let [[syms t] (rest t)]
                       (assert (= 1 (count syms)))
                       (binding [*tvar* (into *tvar* syms)]
                         (Mu* (first syms) (parse-type t))))
                 IFn (let [methods (mapv parse-fn-arity (rest t))]
                       ;(assert (seq methods)) ; (IFn) <=> AnyFunction
                       {:op :IFn
                        :methods methods}))
      ('#{Int} t) -Int
      ('#{Num} t) -Num
      ('#{Str} t) -Str
      ('#{Any} t) -any
      ('#{Nothing} t) -nothing
      ((every-pred symbol? *tvar*) t) {:op :F :name t}
      :else (assert false (str "Error parsing type: " t)))))

(def ^:dynamic *verbose-types* nil)

(defn unparse-type-by [t {:keys [Poly-frees
                                 Poly-body
                                 Poly-constraints
                                 Poly-bounds
                                 Mu-body
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
    :Mu (let [g (Mu-free t)
              body (unparse-type (Mu-body g t))]
          (list 'Rec [(unparse-type g)] body))
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
    :PApp (list* 'PApp (unparse-type (:poly t))
                 (map unparse-type (:args t)))
    (assert nil (str "Cannot unparse type: " (pr-str t)))))

(defn variance? [v]
  (contains? #{:covariant :contravariant :invariant} v))

(defn merge-fv-variances [& vs]
  (letfn [(combine-variances [v1 v2]
            {:pre [(variance? v1)
                   (variance? v2)]
             :post [(variance? %)]}
            (if (= v1 v2)
              v1
              :invariant))]
    (apply merge-with combine-variances vs)))

(defn flip-variances [v]
  {:pre [(variance? v)]
   :post [(variance? %)]}
  ({:covariant :contravariant
    :contravariant :covariant
    :invariant :invariant}
   v))

(defn fv-variances-by [t {:keys [fv-variances]}]
  (let []
    (case (:op t)
      (:B :Base) {}
      :F {(with-meta (:name t) (select-keys t [:original-name]))
          :covariant}
      :Scope (fv-variances (:scope t))
      (:Intersection :Union) (apply merge-fv-variances (map fv-variances (:types t)))
      :Seq (fv-variances (:type t))
      :Fn (let [dom (apply merge-fv-variances
                           (map (fn [t]
                                  (let [vs (fv-variances t)]
                                    (zipmap (keys vs)
                                            (map flip-variances (vals vs)))))
                                (:dom t)))
                rng (fv-variances (:rng t))]
            (merge-fv-variances dom rng))
      :IFn (apply merge-fv-variances (map fv-variances (:methods t)))
      (assert nil (str "Cannot find fv for type: " (pr-str t))))))

(defn fv-by [t {:keys [fv-variances]}]
  (set (keys (fv-variances t))))

(defn constant-type-fn [parse-type]
  {'app (parse-type '(All [a b] [[a :-> b] a :-> b]))
   'appid (parse-type '(All [a] [[a :-> a] a :-> a]))
   'map (parse-type '(All [a b] [[a :-> b] (Seq a) :-> (Seq b)]))
   'app0 (parse-type '(All [a b] [[a :-> b] :-> [a :-> b]]))
   'app2 (parse-type '(All [a b c] [[a b :-> c] a b :-> c]))
   'id (parse-type '(All [a] [a :-> a]))
   '+ (parse-type '[Int Int :-> Int])
   '+' (parse-type '(IFn [Int Int :-> Int]
                         [Num Num :-> Num]))
   'inc (parse-type '[Int :-> Int])
   'inc' (parse-type '(IFn [Int :-> Int]
                           [Num :-> Num]))
   'comp (parse-type '(All [a b c] [[b :-> c] [a :-> b] :-> [a :-> c]]))
   'every-pred (parse-type '(All [a] [[a :-> Any] [a :-> Any] :-> [a :-> Any]]))
   'partial (parse-type '(All [a b c] [[a b :-> c] a :-> [b :-> c]]))
   'reduce (parse-type '(All [a c] [[a c :-> a] a (Seq c) :-> a]))
   'mapT (parse-type '(All [a b] [[a :-> b] :-> (All [r] [[r b :-> r] :-> [r a :-> r]])]))
   'intoT (parse-type '(All [a b] [(Seq b) (All [r] [[r b :-> r] :-> [r a :-> r]]) (Seq a) :-> (Seq b)]))
   })

(defn type-for-symbol-with [env e constant-type]
  {:post [(Type? %)]}
  (or (get env e)
      (constant-type e)
      (throw (Exception. (str "Bad symbol: " e)))))

(defn type-for-value [e]
  {:post [(Type? %)]}
  (cond
    (integer? e) -Int
    (string? e) -Str
    :else (throw (Exception. (str "Bad value: " e)))))

(defn expected-error-with [msg t P e unparse-type]
  (throw (ex-info
           (str msg "\nActual:\n\t" (print-str (unparse-type t)) "\nExpected:\n\t" (print-str (unparse-type P))
                "\nin:\n\t" e)
           {type-error-kw true})))

(defn indent-str-by [ind s]
  (apply str
         (interpose (str "\n" ind)
                    (str/split-lines s))))

(defn subtype-Seq?-with [s t subtype?]
  {:pre [(Seq? s)
         (Seq? t)]
   :post [(boolean? %)]}
  (subtype? (:type s) (:type t)))

(defn base-supers [t]
  {:pre [(Base? t)]
   :post [((some-fn nil? (every-pred set? seq)) %)
          (not (contains? % t))]}
  ({'Int #{-Num}}
   (:name t)))

(defn subtype-Base-left?-with [s t subtype?]
  {:pre [(Base? s)]
   :post [(boolean? %)]}
  (boolean
    (when-let [s (base-supers s)]
      (subtype? (make-U s) t))))

(defn subtype-Union-Intersection?-with [s t subtype?]
  {:pre [((some-fn Intersection? Union?) s t)]
   :post [(boolean? %)]}
  (cond
    (Intersection? t) (every? #(subtype? s %) (:types t))
    (Union? s)        (every? #(subtype? % t) (:types s))
    (Intersection? s) (boolean (some #(subtype? % t) (:types s)))
    (Union? t)        (boolean (some #(subtype? s %) (:types t)))
    :else (throw (Exception. "impossible"))))

(defn subtype-Fn?-with [s t subtype?]
  {:pre [(Fn? s)
         (Fn? t)]
   :post [(boolean? %)]}
  (and (= (count (:dom s))
          (count (:dom t)))
       (every? identity
               (map subtype?
                    (:dom t)
                    (:dom s)))
       (subtype? (:rng s)
                 (:rng t))))

(defn subtype-IFn?-with [s t subtype-Fn?]
  {:pre [((every-pred IFn?) s t)]
   :post [(boolean? %)]}
  (let [ms (:methods t)
        _ (assert (vector? ms))]
    (every? #(boolean
               (some (fn [s] (subtype-Fn? s %))
                     (:methods s)))
            ms)))

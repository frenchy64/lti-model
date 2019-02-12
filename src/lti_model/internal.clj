(ns lti-model.internal
  (:require [lti-model.util :as u]
            [clojure.pprint :as pp]
            [lti-model.internal-eval]))

; Expressions
; e ::= 
;       c                    ; constant functions
;     | n                    ; integers
;     | sym                  ; locals
;     | (ann (fn [x *] e) t) ; annotated functions
;     | (ann e t)            ; type ascription
;     | [e *]                ; sequences

;Types
; t ::= 
;       (IFn [t * :-> t]+) ;ordered intersection function types
;     | [t * :-> t]        ;function type
;     | a                  ;type variables
;     | Int                ;integers
;     | Num                ;numbers
;     | (U t *)            ;unions
;     | (I t *)            ;intersections
;     | (Seq t)            ;sequences
;     | (PApp t t *)       ;instantiation of polymorphic types

; Type Abbreviations
;  Any = (I)
;  Nothing = (U)

; Name T -> Scope
(defn abstract [n t]
  (u/abstract-by n t (fn [name-to outer t]
                       (case (:op t)
                         nil))))

; (Vec Name) T -> Scope
(defn abstract-all [syms t]
  (u/abstract-all-by syms t abstract))

; [T -> T] T -> T
(defn walk-type [f t]
  (u/walk-type-by f t
                  (fn [t]
                    (case (:op t)
                      nil))))

; T Scope -> T
(defn instantiate [image t]
  {:pre [(u/Scope? t)
         (u/Type? image)]
   :post [(u/Type? %)]}
  (u/instantiate-by image t
                    (fn [replace outer t]
                      (case (:op t)
                        nil))))

; (Seqable T) Scope -> T
(defn instantiate-all [images t]
  (u/instantiate-all-by images t instantiate))

; Poly (Seqable Type) -> Type
(defn Poly-body [p images]
  (u/Poly-body-by p images instantiate-all))
; Sym Mu -> Type
(defn Mu-body [sym p]
  (u/Mu-body-by sym p instantiate))

(defn Poly* [syms t & args]
  (apply u/Poly*-by syms t abstract-all args))
(defn Mu* [sym t & args]
  (apply u/Mu*-by sym t abstract args))

(declare unparse-type)

; Any -> T
(defn parse-type [t]
  (cond
    (and (seq? t)
         ('#{PApp} (first t))
         (next t))
    (let [[_ psyn & targssyn] t
          p (parse-type psyn)
          _ (assert (u/Poly? p) (unparse-type p))
          targs (mapv parse-type targssyn)]
      {:op :PApp
       :poly p
       :args targs})
    :else (u/parse-type-by t {:Poly* Poly*
                              :Mu* Mu*
                              :parse-type parse-type})))

(defn Poly-constraints [p images]
  {:pre [(= :Poly (:op p))
         (= (count images) (count (:syms p)))]}
  (u/Poly-constraints-by p images instantiate-all))

(defn Poly-bounds [p images]
  {:pre [(u/Poly? p)
         (= (count images) (count (:bounds p)))]}
  (u/Poly-bounds-by p images instantiate-all))

; T -> Any
(defn unparse-type [t]
  (case (:op t)
    (u/unparse-type-by t 
                       {:Poly-frees u/Poly-frees
                        :Poly-body Poly-body
                        :Poly-constraints Poly-constraints
                        :Poly-bounds Poly-bounds
                        :Mu-body Mu-body
                        :unparse-type unparse-type})))

(declare fv-variances)

(defn Poly-bounds-fv-variances [bounds]
  (apply u/merge-fv-variances 
         (map (fn [{:keys [lower upper]}]
                (u/merge-fv-variances (fv-variances lower)
                                      (fv-variances upper)))
              bounds)))

(defn Poly-bounds-fv [bounds]
  (set (keys (Poly-bounds-fv-variances bounds))))

(defn Poly-constraints-fv-variances [constraints]
  (apply u/merge-fv-variances 
         (map (fn [{:keys [lower upper]}]
                (u/merge-fv-variances (fv-variances lower)
                                      (fv-variances upper)))
              constraints)))

(defn Poly-constraints-fv [constraints]
  (set (keys (Poly-constraints-fv-variances constraints))))

(defn fv-variances [t]
  (case (:op t)
    ; FIXME :constraints variances?
    :Poly (u/merge-fv-variances (fv-variances (:type t))
                                (Poly-bounds-fv-variances (:bounds t))
                                (Poly-constraints-fv-variances (:constraints t)))
    (u/fv-variances-by t {:fv-variances fv-variances})))

(defn fv [t]
  (u/fv-by t {:fv-variances fv-variances}))

(def constant-type (u/constant-type-fn parse-type))

(defn type-for-symbol [env e]
  (u/type-for-symbol-with env e constant-type))

(declare subtype?)

(defn subtype-Seq? [s t]
  {:pre [(u/Seq? s)
         (u/Seq? t)]
   :post [(boolean? %)]}
  (u/subtype-Seq?-with s t subtype?))

(defn subtype-Base-left? [s t]
  {:pre [(u/Base? s)]
   :post [(boolean? %)]}
  (u/subtype-Base-left?-with s t subtype?))

(defn subtype-Union-Intersection? [s t]
  {:pre [((some-fn u/Intersection? u/Union?) s t)]
   :post [(boolean? %)]}
  (u/subtype-Union-Intersection?-with s t subtype?))

(defn subtype-Fn? [s t]
  {:pre [(u/Fn? s)
         (u/Fn? t)]
   :post [(boolean? %)]}
  (u/subtype-Fn?-with s t subtype?))

(defn subtype-IFn? [s t]
  {:pre [((every-pred u/IFn?) s t)]
   :post [(boolean? %)]}
  (u/subtype-IFn?-with s t subtype-Fn?))

(defn subst [sb t]
  {:pre [(map? sb)
         (u/Type? t)]
   :post [(u/Type? %)]}
  (u/subst-by sb t {:abstract-all abstract-all
                    :instantiate-all instantiate-all}))

(defn unfold [m]
  (u/unfold-by m {:Mu-body Mu-body
                  :subst subst}))

(def resolvable? (some-fn u/Mu? u/PApp?))

(defn apply-PApp [p]
  {:pre [(u/PApp? p)]
   :post [(u/Type? %)]}
  (let [poly (:poly p)
        args (:args p)
        _ (assert (u/Poly? poly))
        _ (assert (vector args))]
    (Poly-body poly args)))

(defn resolve-type [t]
  {:pre [(u/Type? t)]
   :post [(u/Type? %)]}
  (case (:op t)
    :Mu (unfold t)
    :PApp (apply-PApp t)))

(defn fully-resolve-type
  ([t] (fully-resolve-type t #{}))
  ([t seen]
   (let [_ (when (seen t)
             (throw (Exception. (str "Infinite type detected: "
                                     (unparse-type t)))))]
     (if (resolvable? t)
       (recur (resolve-type t) (conj seen t))
       t))))

(def ^:dynamic *subtype-seen* #{})

(defn subtype? [s t]
  {:pre [(u/Type? s)
         (u/Type? t)]
   :post [(boolean? %)]}
  (if (or (*subtype-seen* [s t])
          (= s t))
    true
    (binding [*subtype-seen* (conj *subtype-seen* [s t])]
      (cond
        ((some-fn u/Intersection? u/Union?) s t) (subtype-Union-Intersection? s t)

        (u/Mu? s) (subtype? (unfold s) t)
        (u/Mu? t) (subtype? s (unfold t))

        (and (u/Poly? s)
             (u/PApp? t))
        (subtype? s (:poly t))

        ((every-pred u/IFn?) s t) (subtype-IFn? s t)

        ((every-pred u/Seq?) s t) (subtype-Seq? s t)

        (u/Base? s) (subtype-Base-left? s t)

        :else false))))

(defn expected-error [msg actual expected  e]
  (u/expected-error-with msg actual expected e unparse-type))

(defn check-app [cop cargs]
  {:pre [(u/Type? cop)
         (every? u/Type? cargs)]
   :post [((some-fn nil? u/Type?) %)]}
  (let [cop (fully-resolve-type cop)]
    (case (:op cop)
      ; unordered intersections
      :IFn (let [as (keep (fn [m]
                            {:pre [(u/Fn? m)]
                             :post [((some-fn nil? u/Type?) %)]}
                            (when (= (count cargs)
                                     (count (:dom m)))
                              (when (every? identity (map subtype? cargs (:dom m)))
                                (:rng m))))
                          (:methods cop))]
             (when (seq as)
               (u/make-I as)))
      :Poly (throw (ex-info (str "Cannot invoke polymorphic function, must instantiate: "
                                 (unparse-type cop))
                            {u/type-error-kw true})))))

(declare check)

(def reserved-symbols '#{ann fn fn*})

(defn check-fn [env e exp]
  {:pre [(map? env)
         ((every-pred seq? seq) e)
         (u/Type? exp)]
   :post [(u/Result? %)]}
  (let [args (next e)
        [plist body & more] args
        _ (when more
            (throw (ex-info (str "Extra arguments to 'fn': " more)
                            {u/type-error-kw true})))
        _ (assert (= 2 (count args)) "Not enough arguments to 'fn'")
        _ (assert (and (vector? plist)
                       (every? symbol? plist))
                  (str "'fn' takes a vector of arguments, found " plist))
        _ (assert (not-any? reserved-symbols plist)
                  (str "Cannot use reserved symbol: "
                       (some reserved-symbols plist)))
        ; check body. no use for return type because entire interface is provided
        ; for each function, so it's thrown away.
        _ (let [exp (fully-resolve-type exp)]
            (case (:op exp)
              :IFn (let [_ (mapv (fn [m]
                                   {:pre [(u/Fn? m)]}
                                   (let [dom (:dom m)
                                         _ (when-not (= (count plist) (count dom))
                                             (throw (ex-info (str "Function does not match expected number of parameters"
                                                                  "\nActual:\n\t" (count plist)
                                                                  "\nExpected:\n\t" (count dom)
                                                                  "\nExpected type:\n\t" (unparse-type m)
                                                                  "\nin:\n\t" e)
                                                             {u/type-error-kw true})))
                                         env (merge env (zipmap plist dom))
                                         rng (check env body)
                                         rng-t (u/ret-t rng)
                                         exp (:rng m)
                                         _ (when-not (subtype? rng-t exp)
                                             (expected-error "Unexpected function body"
                                                             rng-t
                                                             exp
                                                             body))]
                                     nil))
                                 (:methods exp))]
                     nil)
              ))
        ]
    (u/->Result (list 'ann e (unparse-type exp))
                exp)))

(defn check [env e]
  {:pre [(map? env)]
   :post [(u/Result? %)]}
  (cond
    ; locals shadow globals, except when used as a special form like (ann ...)
    (symbol? e) (u/->Result e (type-for-symbol env e))
    ((some-fn integer? string?) e) (u/->Result e (u/type-for-value e))
    (vector? e) (let [rs (mapv #(check env %) e)]
                  (u/->Result (mapv u/ret-e rs)
                              {:op :Seq
                               :type (u/make-U (map u/ret-t rs))}))
    ((every-pred seq? seq) e)
             (let [[op & args] e]
               (case op
                 fn (throw (Exception. (str "Function requires annotation: " e)))
                 ann (let [[e' at & more] args
                           _ (when more
                               (throw (ex-info (str "Extra arguments to 'ann': " more)
                                               {u/type-error-kw true})))
                           _ (assert (= 2 (count args)) "Not enough arguments to 'ann'")
                           exp (parse-type at)]
                       (cond
                         ; (ann (fn ...) t)
                         (and ((every-pred seq? seq) e')
                              ('#{fn fn*} (first e')))
                         (check-fn env e' exp)

                         ; (ann e t)
                         :else (let [r (check env e')
                                     _ (when-not (subtype? (u/ret-t r) exp)
                                         (expected-error "Incorrect annotation for 'ann'"
                                                         (u/ret-t r)
                                                         exp
                                                         e))]
                                 ;(prn "ann")
                                 (u/->Result (list 'ann (u/ret-e r) (unparse-type exp))
                                             exp))))
                 (let [rcop (check env op)
                       cop (u/ret-t rcop)
                       rcargs (mapv #(check env %) args)
                       cargs (mapv u/ret-t rcargs)]
                   (if-let [t (check-app cop cargs)]
                     (u/->Result (map u/ret-e (cons rcop rcargs))
                                 t)
                     (throw (ex-info (str "Could not apply function: "
                                          "\nFunction:\n\t"
                                          (u/indent-str-by "\t" (with-out-str (pp/pprint (unparse-type cop))))
                                          "\nArguments:\n" (apply str (map #(println-str (str "\t" %)) (map unparse-type cargs)))
                                          "\n\nin:\n\t" e)
                                     {u/type-error-kw true}))))))
    :else (assert nil (str "Bad expression in check: " (pr-str e)))))

(defn check-form [env e]
  (check env e))

;assumes form is well-typed
(defn eval-form [form]
  (binding [*ns* (the-ns 'lti-model.internal-eval)]
    (eval form)))

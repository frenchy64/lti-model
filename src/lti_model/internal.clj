(ns lti-model.internal
  (:require [lti-model.util :as u]))

; e ::=                    ; Expressions
;       c                  ; constant functions
;     | n                  ; integers
;     | (fn {:interface t} ; functions
;         [x *]
;         e)
;     | [e *]              ; sequences
;     | (inst-case e (case (enclosing-fn-arity n) t [t *] *))       ; polymorphic type instantiation

#_
(fn {:interface (IFn [-> [Int -> [Int -> Int]]]
                     [-> [Bool -> [Bool -> Bool]]])}
  []
  (fn {:interface (case (enclosing-fn-arity 0)
                    [-> [Int -> [Int -> Int]]] [Int -> [Int -> Int]]
                    [-> [Bool -> [Bool -> Bool]]] [Bool -> [Bool -> Bool]])}
    [x]
    (fn {:interface (case (enclosing-fn-arity 0)
                      [Int -> [Int -> Int]] [Int -> Int]
                      [Bool -> [Bool -> Bool]] [Bool -> Bool])}
      [y] y)))

; foo : (U (All [a] [a -> a]) (All [b] [b -> b]))

; ((inst foo) 1)
; ((ann-poly foo  ;required that foo must be of the below type, but with PInst+type arguments erased
;            (U (PInst (All [a] [a -> a]) Int)
;               (PInst (All [b] [b -> b]) Int)))
;  1)

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
  {:pre [(= :Scope (:op t))
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

; Any -> T
(defn parse-type [t]
  (cond
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

(defn subtype? [s t]
  {:pre [(u/Type? s)
         (u/Type? t)]
   :post [(boolean? %)]}
  (= s t))

(defn expected-error [msg actual expected  e]
  (u/expected-error-with msg actual expected e unparse-type))

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
                 ann (let [[e' at & more] args
                           _ (when more
                               (throw (ex-info (str "Extra arguments to 'ann': " more)
                                               {u/type-error-kw true})))
                           _ (assert (= 2 (count args)) "Not enough arguments to 'ann'")
                           exp (parse-type at)
                           r (check env e')
                           _ (when-not (subtype? (u/ret-t r) exp)
                               (expected-error "Incorrect annotation for 'ann'"
                                               (u/ret-t r)
                                               exp
                                               e))]
                       ;(prn "ann")
                       (u/->Result (list 'ann (u/ret-e r) (unparse-type exp))
                                   exp))))
    :else (assert nil (str "Bad expression in check: " (pr-str e)))))

(defn check-form [env e]
  (check env e))

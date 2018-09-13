(ns lti-model.core)

; e ::=              ; Expressions
;     | c            ; constant functions
;     | n            ; integers
;     | (fn [x *] e) ; functions
;     | [e *]        ; sequences
; t ::=                    ; Types
;     | (IFn [t * :-> t]+) ;ordered intersection function types
;     | [t * :-> t]        ;function type
;     | a                  ;type variables
;     | Int                ;integers
;     | (U t *)            ;unions
;     | (I t *)            ;intersections
;     | (Seq t)            ;sequences
;     | (Closure Env e)    ;delayed untyped functions
; P ::=                    ; Prototypes
;     | ?                  ;wildcard
;     | (IFn [P * :-> P]+) ;ordered intersection function types
;     | [P * :-> P]        ;function type
;     | a                  ;type variables
;     | Int                ;integers
;     | (U P *)            ;unions
;     | (I P *)            ;intersections
;     | (Seq t)            ;sequences
; s ::= (All [x+] (IFn [t * :-> t]+)) ;type schemes
; Any = (I)
; Nothing = (U)

(declare T)

#_
(t/defalias Scope
  "Scopes for deBruijn indices"
  (t/U {:op ':Scope
        :scope Scope}
       T))

#_
(t/defalias T
  "AST representation for types"
  (t/U '{:op ':IFn
         :methods (t/Vec '{:op :Fn
                           :dom (t/Vec T)
                           :rng T})}
       '{:op ':Int}
       '{:op ':Seq
         :type T}
       '{:op ':Poly
         :syms (t/Vec t/Sym)
         :type Scope}
       '{:op ':F
         :sym t/Sym}
       '{:op ':B
         :index t/Sym}
       '{:op ':Closure
         :env Env
         :expr E}
       '{:op ':Union
         :types (t/Set T)}
       '{:op ':Intersection
         :types (t/Set T)}))

#_
(t/defalias P
  "AST representation for Prototypes"
  (t/U '{:op ':Wild}
       '{:op ':IFn
         :methods (t/Vec '{:op :Fn
                           :dom (t/Vec P)
                           :rng P})}
       '{:op ':Poly
         :gsyms (t/Vec t/Sym)
         :type P}
       '{:op ':Int}
       '{:op ':Union
         :types (t/Vec P)}
       '{:op ':Intersection
         :types (t/Vec P)}))

#_
(t/defalias Env
  "Representation for type environments"
  (t/Map t/Sym T))

(def ^:dynamic *tvar* #{})

; Name Expr -> Scope
(defn abstract [n t]
  (letfn [(name-to [outer t]
            {:pre [(:op t)
                   (integer? outer)]}
            (case (:op t)
              :F (if (= n (:sym t))
                   {:op :B
                    :index outer}
                   t)
              :Fn (-> t
                      (update :dom #(mapv (fn [t]
                                            (name-to outer t))
                                          %))
                      (update :rng #(name-to outer %)))
              :IFn (update t :methods #(mapv (fn [t]
                                               (name-to outer t))
                                             %))
              :Scope (update t :scope #(name-to (inc outer) %))
              t))]
    {:op :Scope
     :scope (name-to 0 t)}))

(defn abstract-all [syms t]
  (reduce (fn [t sym]
            (abstract sym t))
          t
          syms))

; Expr Scope -> Expr
(defn instantiate [image t]
  {:pre [(= :Scope (:op t))
         (:op image)]
   :post [(:op %)]}
  (letfn [(replace [outer t]
            {:pre [(integer? outer)]
             :post [(:op %)]}
            (case (:op t)
              :B (if (= outer (:index t))
                   image
                   t)
              :Fn (-> t
                      (update :dom #(mapv (fn [t]
                                            (replace outer t))
                                          %))
                      (update :rng #(replace outer %)))
              :IFn (update t :methods #(mapv (fn [t]
                                               (replace outer t))
                                             %))
              :Scope (update t :scope #(replace (inc outer) %))
              t))]
    (replace 0 (:scope t))))

(defn instantiate-all [images t]
  (reduce (fn [t image]
            (instantiate image t))
          t
          images))

; Poly (Seqable Type) -> Type
(defn Poly-body [p images]
  {:pre [(= :Poly (:op p))
         (= (count images) (count (:syms p)))]
   :post [(:op %)]}
  (instantiate-all images (:type p)))

(declare parse-type)

; (Seqable Sym) Type -> Poly
(defn Poly* [syms t]
  {:pre [(every? symbol? syms)
         (:op t)]}
  (let [ab (abstract-all syms t)]
    {:op :Poly
     :syms syms
     :type ab}))

(defn make-U [ts]
  (let [ts (set ts)]
    (case (count ts)
      1 (first ts)
      {:op :Union
       :types ts})))

(def -wild {:op :Wild})
(def -any {:op :Intersection :types #{}})
(def -nothing {:op :Union :types #{}})
(defn IFn? [t] (= :IFn (:op t)))
(defn Fn? [t] (= :Fn (:op t)))

; Any -> T
(defn parse-type [t]
  (let [parse-fn-arity (fn [t]
                         {:pre [(vector? t)]}
                         (let [[args [_ ret]] (split-with (complement #{:->}) t)]
                           {:op :Fn
                            :dom (mapv parse-type args)
                            :rng (parse-type ret)}))]
    (cond
      (vector? t) {:op :IFn
                   :methods [(parse-fn-arity t)]}
      (seq? t) (case (first t)
                 U {:op :Union
                    :types (into #{} (map parse-type) (rest t))}
                 I {:op :Intersection
                    :types (into #{} (map parse-type) (rest t))}
                 Seq {:op :Seq
                      :types (parse-type (second t))}
                 All (let [[syms t] (rest t)]
                       (binding [*tvar* (into *tvar* syms)]
                         (Poly* syms (parse-type t))))
                 IFn (let [methods (mapv parse-fn-arity (rest t))]
                       (assert (seq methods))
                       {:op :IFn
                        :methods methods}))
      ('#{Int} t) {:op :Int}
      ('#{Any} t) {:op :Intersection :types #{}}
      (symbol? t) {:op :F :sym t}
      :else (assert false t))))

(def constant-type
  {'app (parse-type '(All [a b] [[a :-> b] a :-> b]))})

(declare subtype?)

(defn subtype-Fn? [s t]
  {:pre [(= :Fn (:op s))
         (= :Fn (:op t))]
   :post [(boolean? %)]}
  (and (= (count (:dom s))
          (count (:dom t)))
       (every? identity
               (map subtype? (:dom t) (:dom s)))
       (subtype? (:rng s) (:rng t))))


(defn subtype [s t]
  {:pre [(:op s)
         (:op t)]
   :post [(boolean? %)]}
  (cond
    (or (= s t) 
        (= -any t)
        (= -nothing s))
    true
    (= :Intersection (:op t)) (every? #(subtype? s %) (:types t))
    (= :Intersection (:op s)) (boolean (some #(subtype? % t) (:types s)))
    (= :Union (:op t)) (some #(subtype? % t) (:types s))
    (= :Union (:op s)) (every? #(subtype? % t) (:types s))
    (and (= :IFn (:op s))
         (= :IFn (:op t)))
    (every? #(boolean
               (some (fn [s] (subtype-Fn? s %))
                     (:types s)))
            (:types t))
    :else false))

(declare match-dir)

(defn flip-dir [dir]
  {:post [(#{:up :down} %)]}
  ({:up :down :down :up} dir))

(defn match-dir-Fn [dir t P]
  {:pre [(Fn? t)
         (Fn? P)]
   :post [((some-fn nil? :op) %)]}
  (when (= (count (:dom t))
           (count (:dom P)))
    (let [dom (mapv #(match-dir (flip-dir dir) %1 %2)
                    (:dom P)
                    (:dom t))
          rng (match-dir dir (:rng t) (:rng P))]
      (when (every? :op dom)
        (when rng
          {:op :Fn
           :dom dom
           :rng rng})))))

(defn match-for-prototype [dir P]
  (let [[small large] (if (= :up dir)
                        [-nothing -any]
                        [-any -nothing])]
    (case (:op P)
      :Seq {:op :Seq :type small}
      :IFn {:op :IFn
            :methods (mapv (fn [m]
                             (-> m
                                 (update :dom #(repeat (count %) large))
                                 (assoc :rng small)))
                           (:types P))})))

; T P -> T
(defn match-dir
  "Returns smallest supertype of t that matches P if direction is :up.
   Returns largest subtype of t that matches P if direction is :down.
  Returns nil if undefined."
  [dir t P]
  {:post [((some-fn nil? :op) %)]}
  (cond
    (or (= t P)
        (= -wild P))
    t
    (and (IFn? t)
         (IFn? P))
    (let [matches (mapv #(some
                           (fn [t]
                             (match-dir-Fn dir t %))
                           (:methods t))
                        (:methods P))]
      (when (every? :op matches)
        {:op :IFn
         :methods matches}))

    (and (or (and (= :up dir)
                  (= -nothing t))
             (and (= :down dir)
                  (= -any t)))
        (and (IFn? P)
             (= :Seq (:op P))))
    (match-dir dir (match-for-prototype dir P) P)

    (= :Intersection (:op P))
    (let [matches (mapv #(match-dir dir t %) (:types P))]
      (when (every? :op matches)
        {:op :Intersection
         :types (set matches)}))
    (= :Union (:op P))
    (let [matches (mapv #(match-dir dir t %) (:types P))]
      (when (some :op matches)
        (make-U (set (remove nil? matches)))))


    ; (Seq Int) ^ (Seq ?) => (Seq Int)
    ; (Seq Any) ^ (Seq ?) => (Seq Any)
    ; Int ^ (Seq ?) => FAIL
    ; ----------------------------------------------------------------
    ; (I Int (Seq Int) (Seq Any)) ^ (Seq ?) => (I (Seq Int) (Seq Any))
    (= :Intersection (:op t))
    (let [matches (mapv #(match-dir dir % P) (:types t))]
      (when (some :op matches)
        {:op :Intersection
         :types (set (remove nil? matches))}))

    ; (Seq Int) ^ (Seq ?) => (Seq Int)
    ; (Seq Any) ^ (Seq ?) => (Seq Any)
    ; ------------------------------------------------------------
    ; (U (Seq Int) (Seq Any)) ^ (Seq ?) => (U (Seq Int) (Seq Any))
    (= :Union (:op t))
    (let [matches (mapv #(match-dir dir % P) (:types t))]
      (when (every? :op matches)
        (make-U (set matches))))

    :else nil))

#_
(t/ann check [P Env E :-> T])
(defn check [P env e]
  {:pre [(:op P)
         (map? env)]
   :post [(:op %)]}
  (prn "e" e)
  (cond
    (symbol? e) (or (constant-type e)
                    (get env e)
                    (assert nil "Bad symbol"))
    (vector? e) {:op :Seq
                 :type (make-U (mapv #(check -wild env %) e))}
    (seq? e) (let [[op & args] e
                   _ (assert (seq e))]
               (case op
                 fn (let [[plist body] args]
                      (cond
                        (= -wild P) {:op :Closure
                                     :env env
                                     :expr e}
                        :else (assert nil "TODO fn check")))
                 (let [cop (check -wild env op)
                       cargs (mapv #(check -wild env %) args)]
                   (assert nil "TODO app check"))))
    (integer? e) {:op :Int}
    :else (assert nil (str "Bad check: " e))))

(comment
  (check -wild {} 1)
  (check -wild {} [1 2])
  (check -wild {} '(fn [x] [1 2]))
  (check -wild {} '(app (fn [x] [1 2]) 1))
)

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
                 (let[cop (check -wild env op)
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

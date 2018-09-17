(ns lti-model.core
  (:require [clojure.set :as set]
            [clojure.string :as str]
            [lti-model.topo :as topo]
            [clojure.pprint :refer [pprint]]))

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
         :constraints (t/Vec '{:lower Scope :upper Scope})
         :type Scope}
       '{:op ':F
         :name t/Sym}
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
         :syms (t/Vec t/Sym)
         :constraints (t/Vec '{:lower Scope :upper Scope})
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
            (let [nt #(name-to outer %)
                  ntv #(mapv nt %)]
              (case (:op t)
                (:Wild :Closure :B :Int) t
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
                :Scope (update t :scope #(name-to (inc outer) %)))))]
    {:op :Scope
     :scope (name-to 0 t)}))

(defn abstract-all [syms t]
  (reduce (fn [t sym]
            (abstract sym t))
          t
          (rseq syms)))

; Expr Scope -> Expr
(defn instantiate [image t]
  {:pre [(= :Scope (:op t))
         (:op image)]
   :post [(:op %)]}
  (letfn [(replace [outer t]
            {:pre [(integer? outer)]
             :post [(:op %)]}
            (let [rp #(replace outer %)
                  rpv #(mapv rp %)]
              (case (:op t)
                (:Wild :Closure :F :Int) t
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
                :Scope (update t :scope #(replace (inc outer) %)))))]
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

(defn Poly-constraints [p images]
  {:pre [(= :Poly (:op p))
         (= (count images) (count (:syms p)))]}
  (mapv (fn [c]
          (-> c
              (update :lower #(instantiate-all images %))
              (update :upper #(instantiate-all images %))))
        (:constraints p)))

(defn Poly-bounds [p images]
  {:pre [(= :Poly (:op p))
         (= (count images) (count (:bounds p)))]}
  (mapv (fn [b]
          (-> b
              (update :lower #(instantiate-all images %))
              (update :upper #(instantiate-all images %))))
        (:bounds p)))

; Poly -> (Vec '{:op ':F})
(defn Poly-frees [p]
  {:pre [(= :Poly (:op p))]}
  (mapv (fn [s]
          {:pre [(symbol? s)]}
          {:op :F :name (gensym s)
           :original-name s})
        (:syms p)))

(declare parse-type)

; (Seqable Sym) Type -> Poly
(defn Poly* [syms t & {:keys [constraints original-names bounds]}]
  {:pre [(every? symbol? syms)
         (apply distinct? syms)
         (vector? syms)
         (:op t)
         (or (nil? original-names)
             (= (count syms) (count original-names)))
         (or (nil? bounds)
             (= (count syms) (count bounds)))
         ]}
  (let [ab (abstract-all syms t)
        constraints (mapv (fn [c]
                            (-> c
                                (select-keys [:lower :upper])
                                (update :lower #(abstract-all syms %))
                                (update :upper #(abstract-all syms %))))
                          constraints)
        bounds (mapv (fn [b]
                       (-> b
                           (update :lower #(abstract-all syms %))
                           (update :upper #(abstract-all syms %))))
                     (or bounds
                         (repeat (count syms) {:lower -nothing :upper -any})))]
    {:op :Poly
     :syms (or original-names (vec syms))
     :bounds bounds
     :constraints constraints
     :type ab}))

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

(defn make-U [ts]
  (let [ts (mapcat (fn [t]
                     (if (= :Union (:op t))
                       (:types t)
                       [t]))
                   ts)
        ts (disj (set ts)
                 -nothing)]
    (cond
      (contains? ts -any) -any
      (= (count ts) 1) (first ts)
      :else {:op :Union
             :types ts})))

(def -wild {:op :Wild})
(def -Int {:op :Int})
(def -any {:op :Intersection :types #{}})
(def -nothing {:op :Union :types #{}})
(defn IFn? [t] (= :IFn (:op t)))
(defn Poly? [t] (= :Poly (:op t)))
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
      ('#{Int} t) {:op :Int}
      ('#{Any} t) -any
      ('#{Nothing} t) -nothing
      ('#{?} t) {:op :Wild}
      ((every-pred symbol? *tvar*) t) {:op :F :name t}
      :else (assert false (str "Error parsing type: " t)))))

(declare unparse-type)

(defn unparse-env [env]
  (into {}
        (map (fn [[k v]]
               [k (unparse-type v)]))
        env))

; T -> Any
(defn unparse-type [t]
  (case (:op t)
    :Wild '?
    :Poly (let [gs (Poly-frees t)
                body (unparse-type (Poly-body t gs))
                constraints (mapv (fn [{:keys [lower upper]}]
                                    [(unparse-type lower) :< (unparse-type upper)])
                                  (Poly-constraints t gs))]
            (list 'All
                  (into (mapv (fn [v b]
                                (let [n ((some-fn :original-name :name) v)]
                                  (cond
                                    (and (= -any (:upper b))
                                         (= -nothing (:lower b)))
                                    n
                                    (= -any (:upper b))
                                    [n :> (unparse-type (:lower b))]
                                    (= -nothing (:lower b))
                                    [n :< (unparse-type (:upper b))]
                                    :else 
                                    [n :> (unparse-type (:lower b)) :< (unparse-type (:upper b))])))
                              gs (Poly-bounds t gs))
                        (when (seq constraints)
                          (into [:constraints] constraints)))
                  body))
    :F (or (:original-name t)
           (:name t))
    :B (:index t)
    :Union (if (empty? (:types t))
             'Nothing
             (list* 'U (mapv unparse-type (:types t))))
    :Intersection (if (empty? (:types t))
                    'Any
                    (list* 'I (mapv unparse-type (:types t))))
    :Closure (list 'Closure (unparse-env (:env t)) (:expr t))
    :Seq (list 'Seq (unparse-type (:type t)))
    :Int 'Int
    :Fn (let [dom (mapv unparse-type (:dom t))
              rng (unparse-type (:rng t))]
          (vec (concat dom [:-> rng])))
    :IFn (let [methods (mapv unparse-type (:methods t))]
           (if (= 1 (count methods))
             (first methods)
             (doall (list* 'IFn methods))))
    (assert nil (str "Cannot unparse type: " (pr-str t)))))

(defn variance? [v]
  (contains? #{:covariant :contravariant :invariant} v))

(defn fv-variances [t]
  (let [combine-variances (fn [v1 v2]
                            {:pre [(variance? v1)
                                   (variance? v2)]
                             :post [(variance? %)]}
                            (if (= v1 v2)
                              v1
                              :invariant))
        flip-variances (fn [v]
                        {:pre [(variance? v)]
                         :post [(variance? %)]}
                        ({:covariant :contravariant
                          :contravariant :covariant
                          :invariant :invariant}
                         v))]
    (case (:op t)
      (:Wild :Closure :B :Int) {}
      ; FIXME :constraints variances?
      :Poly (fv-variances (:type t))
      :F {(:name t) :covariant}
      :Scope (fv-variances (:scope t))
      (:Intersection :Union) (apply merge-with combine-variances (map fv-variances (:types t)))
      :Seq (fv-variances (:type t))
      :Fn (let [dom (apply merge-with combine-variances
                           (map (fn [t]
                                  (let [vs (fv-variances t)]
                                    (zipmap (keys vs)
                                            (map flip-variances (vals vs)))))
                                (:dom t)))
                rng (fv-variances (:rng t))]
            (merge-with combine-variances dom rng))
      :IFn (apply merge-with combine-variances (map fv-variances (:methods t)))
      (assert nil (str "Cannot find fv for type: " (pr-str t))))))

(defn fv [t]
  (set (keys (fv-variances t))))

(def constant-type
  {'app (parse-type '(All [a b] [[a :-> b] a :-> b]))
   'app0 (parse-type '(All [a b] [[a :-> b] :-> [a :-> b]]))
   'id (parse-type '(All [a] [a :-> a]))
   '+ (parse-type '[Int Int :-> Int])
   'inc (parse-type '[Int :-> Int])
   'comp (parse-type '(All [a b c] [[b :-> c] [a :-> b] :-> [a :-> c]]))
   'every-pred (parse-type '(All [a] [[a :-> Any] [a :-> Any] :-> [a :-> Any]]))
   'partial (parse-type '(All [a b c] [[a b :-> c] a :-> [b :-> c]]))
   'reduce (parse-type '(All [a b c] [[a c :-> a] a (Seq c) :-> a]))
   'mapT (parse-type '(All [a b] [[a :-> b] :-> (All [r] [[r b :-> r] :-> [r a :-> r]])]))
   'intoT (parse-type '(All [a b] [(Seq b) (All [r] [[r b :-> r] :-> [r a :-> r]]) (Seq a) :-> (Seq b)]))
   })

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


(defn subtype? [s t]
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

    (#{[:down -any]
       [:up -nothing]}
      [dir t])
    (promote-demote (flip-dir dir) #{} P)

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

    (= :Intersection (:op P))
    (let [matches (mapv #(match-dir dir t %) (:types P))]
      (when (every? :op matches)
        (make-I (set matches))))
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
        (make-I (remove nil? matches))))

    ; (Seq Int) ^ (Seq ?) => (Seq Int)
    ; (Seq Any) ^ (Seq ?) => (Seq Any)
    ; ------------------------------------------------------------
    ; (U (Seq Int) (Seq Any)) ^ (Seq ?) => (U (Seq Int) (Seq Any))
    (= :Union (:op t))
    (let [matches (mapv #(match-dir dir % P) (:types t))]
      (when (every? :op matches)
        (make-U (set matches))))

    :else nil))

(defn smallest-matching-super [t P]
  (match-dir :up t P))
(defn largest-matching-sub [t P]
  (match-dir :down t P))

(defn expected-error [msg t P e]
  (throw (ex-info
           (str msg "\nActual:\n\t" (print-str (unparse-type t)) "\nExpected:\n\t" (print-str (unparse-type P))
                "\nin:\n\t" e)
           {::type-error true})))

(defn check-match [t P m e]
  {:pre [(:op t)
         (:op P)
         ((some-fn :op nil?) m)]
   :post [(:op %)]}
  (or m
      (expected-error "Did not match:" t P e)))

#_
(defalias ConstraintSet
  (U nil
     {:xs (t/Set t/Sym)
      :cs (t/Map t/Sym '{:lower T
                         :upper T})
      :delay (t/Set '{:lower T, :upper T, :depends (Set Sym), :provides (Set Sym)
                      :V (Set Sym), :X (Set Sym)})}))

(defn delays->graph [delays]
  (apply merge-with into
         (map (fn [{:keys [depends provides]}]
                (into {}
                      (map (fn [s]
                             [s (set provides)]))
                      depends))
              delays)))

(defn unparse-delay [d]
  {:lower (unparse-type (:lower d))
   :upper (unparse-type (:upper d))
   :depends (:depends d)
   :provides (:provides d)})

(defn unparse-delays [ds]
  (into #{} (map unparse-delay) ds))

;ConstraintSet -> Any
(defn unparse-cset [cs]
  (when cs
    {:xs (:xs cs)
     :cs (zipmap (keys (:cs cs))
                 (map (fn [v]
                        {:lower (unparse-type (:lower v))
                         :upper (unparse-type (:upper v))})
                      (vals (:cs cs))))
     :delay (unparse-delays (:delay cs))}))


; (Set Sym) -> C
(defn trivial-constraint [X]
  {:pre [(set? X)]}
  {:xs X
   :cs {}
   :delay #{}})
; (Set Sym) -> C
(defn impossible-constraint [X]
  {:pre [(set? X)]}
  nil)
; (Set Sym) T Sym T -> C
(defn constraint-entry [X s x t]
  {:pre [(set? X)
         (symbol? x)]}
  {:xs (set X)
   :cs {x {:lower s :upper t}}
   :delay #{}})
; (Set Sym) (Set Sym) T T -> C
(defn delay-constraint [V X s t]
  {:pre [(set? V)
         (set? X)
         (#{:IFn :Poly :Closure} (:op s))
         (empty? (set/intersection (fv s) X))
         (= :IFn (:op t))
         (= 1 (count (:methods t)))]}
  (let [m (first (:methods t))
        domv (set/intersection X (into #{} (mapcat fv (:dom m))))
        rngv (set/intersection X (fv (:rng m)))]
    {:xs X
     :cs {}
     :delay #{{:V V :X X :lower s :upper t
               :depends domv :provides rngv}}}))

; (Seqable C) -> C
(defn intersect-constraints [cs]
  (when (every? map? cs)
    (prn "intersect-constraints delay" (apply set/union (map :delay cs)))
    (let [imp? (atom nil)
          c {:xs (apply set/union (map :xs cs))
             :cs (apply merge-with
                        (fn [c1 c2]
                          (let [l (make-U [(:lower c1) (:lower c2)])
                                u (make-I [(:upper c1) (:upper c2)])]
                            (when-not (subtype? l u)
                              (reset! imp? true))
                            {:lower l
                             :upper u}))
                        {}
                        (map :cs cs))
             :delay (apply set/union (map :delay cs))}]
      (when-not @imp?
        c))))

(defn promote-demote [dir V t]
  {:pre [(#{:up :down} dir)
         (set? V)
         (:op t)]
   :post [(:op t)]}
  (case (:op t)
    :Union (make-U (mapv #(promote-demote dir V %) (:types t)))
    :Intersection (make-I (mapv #(promote-demote dir V %) (:types t)))
    ;; handy for match-dir
    :Wild (if (= :up dir)
            -any
            -nothing)
    :F (if (V (:name t))
         ; FIXME use bounds
         (if (= :up dir)
           -any
           -nothing)
         t)
    :Int t
    :Seq (update t :type #(promote-demote dir V %))
    :Poly (let [gs (Poly-frees t)
                body (Poly-body t gs)
                constraints (Poly-constraints t gs)
                bounds (Poly-bounds t gs)
                pbody (promote-demote dir V body)
                pconstraints (mapv (fn [c]
                                     ;; FIXME which directions for constraints?
                                     (-> c
                                         (update :lower #(promote-demote dir V %))
                                         (update :upper #(promote-demote dir V %))))
                                   constraints)
                pbounds (mapv (fn [b]
                                ;; FIXME which directions for bounds?
                                (-> b
                                    (update :lower #(promote-demote dir V %))
                                    (update :upper #(promote-demote dir V %))))
                              bounds)]
            (Poly* (mapv :name gs) pbody
                   :original-names (mapv :original-name gs)
                   :constraints pconstraints
                   :bounds bounds))
    :IFn (update t :methods (fn [ms]
                              (mapv #(promote-demote dir V %) ms)))
    :Fn (-> t
            (update :dom (fn [dom]
                           (mapv #(promote-demote (flip-dir dir) V %)
                                 dom)))
            (update :rng #(promote-demote dir V %)))))

(defn subst [sb t]
  {:pre [(map? sb)
         (:op t)]
   :post [(:op t)]}
  (->> t
       (abstract-all (vec (keys sb)))
       (instantiate-all (vec (vals sb)))))

(defn promote [V t]
  (promote-demote :up V t))
(defn demote [V t]
  (promote-demote :down V t))

(declare check)

; FIXME V should carry its bounds for promote/demote
; (Set Sym) (Set Sym) T T -> C
(defn gen-constraint [V X s t]
  {:pre [(set? V)
         (set? X)
         (:op s)
         (:op t)]
   :post [((some-fn map? nil?) %)]}
  (prn "gen-constraint")
  (prn "s" (unparse-type s))
  (prn "t" (unparse-type t))
  (cond
    (= s t) (trivial-constraint X)
    ; CG-Top
    (= -any t) (trivial-constraint X)
    ; CG-Bot
    (= -nothing s) (trivial-constraint X)
    ; CG-Upper
    (= :F (:op s))
    (when (contains? X (:name s))
      (let [T (demote V t)]
        (constraint-entry X -nothing (:name s) T)))
    ; CG-Lower
    (= :F (:op t))
    (when (contains? X (:name t))
      (let [S (promote V s)]
        (constraint-entry X S (:name t) -any)))
    ; CG-Fun
    (IFn? t)
    (cond
      (and (IFn? s)
           (= 1
              (count (:methods s))
              (count (:methods t))))
      (let [sm (first (:methods s))
            tm (first (:methods t))]
        (when (= (count (:dom sm))
                 (count (:dom tm)))
          (let [cdoms (mapv #(gen-constraint V X %1 %2)
                            (:dom tm)
                            (:dom sm))
                crng (gen-constraint V X (:rng sm) (:rng tm))]
            (intersect-constraints (cons crng cdoms)))))
      (and (#{:IFn :Poly :Closure} (:op s))
           (= 1 (count (:methods t))))
      (delay-constraint V X s t)
      :else nil)
    :else (impossible-constraint X)))

(defn subst-with-constraint [X c t]
  (let [variances (merge (zipmap X (repeat :constant))
                         (select-keys (fv-variances t) X))
        sbt (into {}
                  (map (fn [[n variance]]
                         [n (case variance
                              (:contravariant) (get-in c [:cs n :upper] -any)
                              (get-in c [:cs n :lower] -nothing))]))
                  variances)]
    (subst sbt t)))

(defn order-delays [delays]
  {:pre [(every? (comp set? :depends) delays)
         (every? (comp set? :provides) delays)]}
  (prn "order-delays" delays)
  (when-let [order (topo/kahn-sort (delays->graph delays))]
    (let [delay-order (mapv
                        (fn [sym]
                          (set (filter #(contains? (:depends %) sym) delays)))
                        order)]
      (vec (apply concat delay-order)))))

(defn indent-str-by [ind s]
  (apply str
         (interpose (str "\n" ind)
                    (str/split-lines s))))

(defn scoped-pred [pred t]
  {:pre [(:op t)]}
  (if (= :Scope (:op t))
    (recur pred (:scope t))
    (pred t)))

#_
(t/ann check [P Env E :-> T])
(defn check [P env e]
  {:pre [(:op P)
         (map? env)]
   :post [(:op %)]}
  (cond
    (symbol? e) (let [t (or (constant-type e)
                            (get env e)
                            (assert nil (str "Bad symbol" e)))
                      m (smallest-matching-super t P)]
                  (check-match t P m e))
    (vector? e) (let [t {:op :Seq
                         :type (make-U (mapv #(check -wild env %) e))}
                      m (smallest-matching-super t P)]
                  (check-match t P m e))
    (seq? e) (let [[op & args] e
                   _ (assert (seq e))]
               (case op
                 fn (let [[plist body] args
                          t (cond
                              (= -wild P) {:op :Closure
                                           :env env
                                           :expr e}
                              ;; TODO unions of functions
                              (IFn? P) {:op :IFn
                                        :methods (mapv (fn [m]
                                                         {:pre [(Fn? m)]
                                                          :post [(Fn? %)]}
                                                         (when-not (= (count plist) (count (:dom m)))
                                                           (throw (ex-info (str "Function does not match expected number of parameters")
                                                                           {::type-error true})))
                                                         (prn "checking lambda" e)
                                                         (prn "method" (unparse-type m))
                                                         (let [env (merge env (zipmap plist 
                                                                                      ;TODO demote wildcards
                                                                                      (:dom m)))
                                                               rng (check (:rng m) env body)]
                                                           ;; TODO demote wildcards in dom
                                                           (assoc m :rng rng)))
                                                       (:methods P))}
                              (= -any P) -any
                              :else (throw (ex-info (str "Function does not match expected type:"
                                                         "\nExpected:\n\t" (unparse-type P)
                                                         "\nin:\n\t" e)
                                                    {::type-error true})))]
                      t)
                 (let [solve-method (fn solve-method [P cop cargs]
                                      (prn "solve-method"  (:op cop))
                                      (case (:op cop)
                                        ;; TODO unions of functions
                                        :Closure (let [ifn (check {:op :IFn
                                                                   :methods [{:op :Fn
                                                                              :dom cargs
                                                                              :rng P}]}
                                                                  (:env cop)
                                                                  (:expr cop))
                                                       _ (assert (and (IFn? ifn)
                                                                      (= 1 (count (:methods ifn)))))
                                                       m (first (:methods ifn))]
                                                   (:rng m))
                                        :IFn (some (fn [m]
                                                     {:pre [(Fn? m)]}
                                                     (when (= (count cargs)
                                                              (count (:dom m)))
                                                       (when (every? identity (map subtype? cargs (:dom m)))
                                                         (smallest-matching-super (:rng m) P))))
                                                   (:methods cop))
                                        :Poly (let [gs (Poly-frees cop)
                                                    V #{}
                                                    X (set (map :name gs))
                                                    body (Poly-body cop gs)
                                                    existing-c (intersect-constraints
                                                                 (concat
                                                                   (map #(delay-constraint V X (:lower %) (:upper %))
                                                                        (Poly-constraints cop gs))
                                                                   (map (fn [{:keys [lower upper]}]
                                                                          (gen-constraint V X lower upper))
                                                                        (Poly-bounds cop gs))))
                                                    solve-pmethod
                                                    (fn [m]
                                                      (prn "solve-pmethod" (unparse-type m))
                                                      (when (= (count (:dom m))
                                                               (count cargs))
                                                        (let [cdom (mapv #(gen-constraint V X %1 %2) cargs (:dom m))
                                                              rng (:rng m)]
                                                          (when-let [exp (largest-matching-sub -any P)]
                                                            (let [crng (gen-constraint V X rng exp)]
                                                              (prn "crng" (some? crng))
                                                              (when-let [c (intersect-constraints
                                                                             (concat [crng existing-c] cdom))]
                                                                ; true if X's in delays are acyclic
                                                                (when-let [order (order-delays (:delay c))]
                                                                  (prn "order" order)
                                                                  (when-let [c (reduce (fn [c {:keys [V X lower upper] :as dly}]
                                                                                         {:pre [(IFn? upper)
                                                                                                (= 1 (count (:methods upper)))]}
                                                                                         (let [m (first (:methods upper))
                                                                                               ddom (mapv #(subst-with-constraint X c %)
                                                                                                          (:dom m))
                                                                                               rng (:rng m)
                                                                                               wrng (subst (zipmap X (repeat -wild))
                                                                                                           rng)
                                                                                               sol (solve-method wrng lower ddom)
                                                                                               c' (gen-constraint V X sol rng)]
                                                                                           (if (seq (:delay c'))
                                                                                             (do
                                                                                               (prn "TODO inner cset delay")
                                                                                               (reduced nil))
                                                                                             (intersect-constraints
                                                                                               [c c']))))
                                                                                       c
                                                                                       order)]
                                                                    (cond
                                                                      (IFn? rng)
                                                                      (Poly* (mapv :name gs) rng
                                                                             :bounds (let [v->b (merge (zipmap X (repeat {:lower -nothing
                                                                                                                          :upper -any}))
                                                                                                       (select-keys (:cs c) X))]
                                                                                       (mapv (comp #(select-keys % [:lower :upper])
                                                                                                   v->b)
                                                                                             X))
                                                                             :constraints order
                                                                             :original-names (mapv :original-name gs))
                                                                      (and (Poly? rng)
                                                                           (scoped-pred IFn? (:type rng)))
                                                                      (let [rng-gs (Poly-frees rng)
                                                                            rng-body (Poly-body rng rng-gs)
                                                                            rng-cs (Poly-constraints rng rng-gs)
                                                                            rng-bounds (Poly-bounds rng rng-gs)
                                                                            uniquify-onames (fn [names]
                                                                                              (let [fqs (frequencies names)]
                                                                                                (mapv (fn [sym]
                                                                                                        {:pre [(contains? fqs sym)]}
                                                                                                        (if (= 1 (fqs sym))
                                                                                                          sym
                                                                                                          (loop [sym (symbol (str sym "'"))]
                                                                                                            (if (contains? fqs sym)
                                                                                                              (recur (symbol (str sym "'")))
                                                                                                              sym))))
                                                                                                      names)))
                                                                            names (into (mapv :name gs)
                                                                                        (map :name rng-gs))]
                                                                        (Poly* names
                                                                               rng-body
                                                                               :constraints (into order rng-cs)
                                                                               :bounds (let [v->b (merge (zipmap X (repeat {:lower -nothing
                                                                                                                            :upper -any}))
                                                                                                         (select-keys (:cs c) X))]
                                                                                         (into (mapv (comp #(select-keys % [:lower :upper])
                                                                                                           v->b)
                                                                                                     X)
                                                                                               rng-bounds))
                                                                               :original-names (uniquify-onames
                                                                                                 (into (mapv :original-name gs)
                                                                                                       (map :original-name rng-gs)))))
                                                                      (not (#{:Union :Intersection :Poly} (:op rng)))
                                                                      (subst-with-constraint X c rng)
                                                                      :else (do (prn "TODO return too complex" (:op rng) (:op (:type rng)))
                                                                                nil))))))))))]
                                                (case (:op body)
                                                  :IFn (some solve-pmethod (:methods body))
                                                  nil))))
                       cop (check -wild env op)
                       cargs (mapv #(check -wild env %) args)
                       rt (solve-method P cop cargs)]
                   (or rt
                       (throw (ex-info (str "Could not apply function: "
                                            "\nFunction:\n\t"
                                            (indent-str-by "\t" (with-out-str (pprint (unparse-type cop))))
                                            "\nArguments:\n\t" (apply println-str (mapv unparse-type cargs))
                                            "Expected:\n\t" (unparse-type P)
                                            "\n\nin:\n\t" e)
                                       {::type-error true}))))))
    (integer? e) (let [t {:op :Int}
                       m (smallest-matching-super t P)]
                   (check-match t P m e))
    :else (assert nil (str "Bad expression in check: " e))))

(comment
  (check -Int {} 1)
  (check -wild {} 1)
  (check -wild {} [1 2])
  (check -Int {} [1 2])
  (check -wild {} '(fn [x] [1 2]))
  (check -wild {} '(app (fn [x] [1 2]) 1))
)

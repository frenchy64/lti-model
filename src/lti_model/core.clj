(ns lti-model.core
  (:require [clojure.set :as set]
            [clojure.string :as str]
            [clojure.walk :as walk]
            [lti-model.topo :as topo]
            [lti-model.util :refer [Poly-frees -Int -Num -any -nothing
                                    IFn? Base? Poly? Fn? make-U make-I
                                    type-error-kw]
             :as u]
            [lti-model.external-eval]
            [clojure.pprint :refer [pprint]]))

; Expressions
; e ::=               
;       c             ; constant functions
;     | n             ; integers
;     | sym           ; locals
;     | (fn [x *] e)  ; functions
;     | (let [x e] e) ; let
;     | (ann e t)     ; type ascription
;     | [e *]         ; sequences

; Types
; t ::=     
;       (IFn [t * :-> t]+) ;ordered intersection function types
;     | [t * :-> t]        ;function type
;     | a                  ;type variables
;     | Int                ;integers
;     | Num                ;numbers
;     | (U t *)            ;unions
;     | (I t *)            ;intersections
;     | (Seq t)            ;sequences
;     | (Closure Env e)    ;symbolic closures
;     | (PApp t t *)       ;instantiation of polymorphic types
;     | (All [x+] t)       ;polymorphic types

; Type Abbreviations
;  Any = (I)
;  Nothing = (U)

; Prototypes
; P ::=
;       ?                  ;wildcard
;     | (IFn [P * :-> P]+) ;ordered intersection function types
;     | [P * :-> P]        ;function type
;     | a                  ;type variables
;     | Int                ;integers
;     | (U P *)            ;unions
;     | (I P *)            ;intersections
;     | (Seq t)            ;sequences


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
       ; base types
       '{:op ':Base :name Sym}
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
         :types (t/Set T)}
       '{:op ':PApp
         :poly T
         :args (t/Vec T)}))

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
       '{:op ':Base :name Sym}
       '{:op ':Union
         :types (t/Vec P)}
       '{:op ':Intersection
         :types (t/Vec P)}))

#_
(t/defalias Env
  "Representation for type environments"
  (t/Map t/Sym T))

(def -wild {:op :Wild})
(defn Closure? [t] (= :Closure (:op t)))

; Name T -> Scope
(defn abstract [n t]
  (u/abstract-by n t
                 (fn [name-to outer t]
                   (case (:op t)
                     (:Wild :Closure) t
                     nil))))

; (Vec Name) T -> Scope
(defn abstract-all [syms t]
  (u/abstract-all-by syms t abstract))

; [T -> T] T -> T
(defn walk-type [f t]
  (u/walk-type-by f t
                  (fn [t]
                    (case (:op t)
                      (:Wild :Closure) t
                      nil))))

; T Scope -> T
(defn instantiate [image t]
  {:pre [(= :Scope (:op t))
         (u/Type? image)]
   :post [(u/Type? %)]}
  (u/instantiate-by image t
                    (fn [replace outer t]
                      (case (:op t)
                        (:Wild :Closure) t
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

(defn Poly-constraints [p images]
  {:pre [(u/Poly? p)
         (= (count images) (count (:syms p)))]}
  (u/Poly-constraints-by p images instantiate-all))

(defn Poly-bounds [p images]
  {:pre [(u/Poly? p)
         (= (count images) (count (:bounds p)))]}
  (u/Poly-bounds-by p images instantiate-all))

(defn Poly* [syms t & args]
  (apply u/Poly*-by syms t abstract-all args))
(defn Mu* [sym t & args]
  (apply u/Mu*-by sym t abstract args))

; Any -> T
(defn parse-type [t]
  (cond
    ('#{?} t) -wild
    :else (u/parse-type-by t {:Poly* Poly*
                              :Mu* Mu*
                              :parse-type parse-type})))

(declare unparse-type)

(defn unparse-env [env]
  (into {}
        (map (fn [[k v]]
               [k (unparse-type v)]))
        env))

(defn unparse-type-verbose [t]
  (binding [u/*verbose-types* true]
    (unparse-type t)))

(def ^:dynamic *unparse-closure-by-id* nil)
(def ^:dynamic *unparse-disallow-wildcard* nil)
(def ^:dynamic *unparse-disallow-closure* nil)

; T -> Any
(defn unparse-type [t]
  (case (:op t)
    :Wild (do (assert (not *unparse-disallow-wildcard*))
              '?)
    :Closure (do
               (assert (not *unparse-disallow-closure*))
               (if *unparse-closure-by-id*
                 (list ::ClosureByID (:id t))
                 (list 'Closure (unparse-env (:env t)) (:expr t))))
    (u/unparse-type-by t 
                       {:Poly-frees Poly-frees
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
    (:Wild :Closure) {}
    (u/fv-variances-by t {:fv-variances fv-variances})))

(defn fv [t]
  (u/fv-by t {:fv-variances fv-variances}))

(declare subtype? check check-or-nil)

(defn subtype-Fn? [s t]
  {:pre [(u/Fn? s)
         (u/Fn? t)]
   :post [(boolean? %)]}
  (u/subtype-Fn?-with s t subtype?))

(declare substitution-for-variances)

(defn upcast-Poly [t]
  {:pre [(Poly? t)]}
  (let [gs (Poly-frees t)
        gs-names (map :name gs)
        bounds (Poly-bounds t gs)
        constraints (Poly-constraints t gs)
        body (Poly-body t gs)
        gs-variances (merge
                       (zipmap gs-names (repeat :constant))
                       (select-keys
                         (u/merge-fv-variances
                           (Poly-bounds-fv-variances bounds)
                           (Poly-constraints-fv-variances constraints)
                           (fv-variances body))
                         gs-names))
        sbt (substitution-for-variances gs-variances bounds)]
    (assert nil "TODO")
    ))


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

(defn subtype-IFn? [s t]
  {:pre [((every-pred IFn?) s t)]
   :post [(boolean? %)]}
  (u/subtype-IFn?-with s t subtype-Fn?))

(defn subtype? [s t]
  {:pre [(:op s)
         (:op t)
         (not= -wild s)
         (not= -wild t)]
   :post [(boolean? %)]}
  ;(prn "subtype?")
  ;(prn "s" (unparse-type s))
  ;(prn "t" (unparse-type t))
  (cond
    (= s t) true

    ((some-fn u/Intersection? u/Union?) s t) (subtype-Union-Intersection? s t)

    ((every-pred IFn?) s t) (subtype-IFn? s t)

    ((every-pred u/Seq?) s t) (subtype-Seq? s t)

    (u/Base? s) (subtype-Base-left? s t)

    ; This case is pretty weird because it can trigger side effects
    ; in the *closure-cache* that might end up being irrelevant.
    ; Perhaps the Closure is called with a wrong number of arguments,
    ; and then we suggest an annotation with the wrong number of args.
    ;FIXME need unit tests that pass even though a Closure failed to check
    (Closure? s) (boolean (check-or-nil t (:env s) (:expr s)))
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

(declare promote-demote solve-app
         smallest-matching-super demote)

; T P -> (U nil T)
(defn match-dir
  "Returns smallest supertype of t that matches P if direction is :up.
   Returns largest subtype of t that matches P if direction is :down.
  Returns nil if undefined."
  [dir t P]
  {:pre [(#{:up :down} dir)
         (u/Type? t)
         (u/Type? P)]
   :post [((some-fn nil? u/Type?) %)]}
  ;(prn "match-dir" dir)
  ;(prn "t" (unparse-type t))
  ;(prn "P" (unparse-type P))
  (cond
    (or (= t P)
        (= -wild P))
    t

    (#{[:down -any]
       [:up -nothing]}
      [dir t])
    ;; erase wildcards, flip direction so we're closer to t
    (promote-demote (flip-dir dir) #{} P)

    (= :Intersection (:op P))
    (let [matches (mapv #(match-dir dir t %) (:types P))]
      (when (every? :op matches)
        (make-I (set matches))))
    (= :Union (:op P))
    (let [matches (mapv #(match-dir dir t %) (:types P))]
      (when (some :op matches)
        (make-U (set (remove nil? matches)))))

    ;FIXME intersection and union could (should?) fold result so it looks like P.
    ; is that closer, or further from the smallest super/largest sub we're looking for?

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

    (Base? t)
    (when-let [s (u/base-supers t)]
      (match-dir dir (make-U s) P))

    (and (IFn? t)
         (IFn? P))
    (let [mths (:methods P)
          _ (assert (vector? P))
          matches (mapv #(some
                           (fn [t]
                             (match-dir-Fn dir t %))
                           (:methods t))
                        mths)]
      (when (every? :op matches)
        {:op :IFn
         :methods matches}))

    (and (Poly? t)
         (IFn? P))
    (let [sols (mapv (fn [m]
                       (let [dom (:dom m)
                             rng (:rng m)
                             ;_ (prn "Poly IFn match")
                             ;_ (prn "dom" (mapv unparse-type dom))
                             ;_ (prn "rng" (unparse-type rng))
                             sol (solve-app rng t dom)]
                         ;(prn "sol Poly IFn match" (some-> sol unparse-type))
                         ; FIXME is "smallest" correct here?
                         (when-let [ret (and sol
                                             (smallest-matching-super (:rng-t sol) rng))]
                           (assoc m
                                  ; erase wildcards
                                  :dom (mapv #(demote #{} %) dom)
                                  :rng ret))))
                     (:methods P))]
      (when (every? identity sols)
        (assoc P :methods sols)))

    (and (Poly? t)
         (Poly? P))
    (let [P-gs (Poly-frees P)
          P-bounds (Poly-bounds P P-gs)
          P-constraints (Poly-constraints P P-gs)
          P-body (Poly-body P P-gs)]
      (when (and (every? #{{:lower -nothing :upper -any}} P-bounds)
                 (empty? P-constraints))
        (when-let [sol (match-dir dir t P-body)]
          (Poly* (mapv :name P-gs)
                 sol
                 :original-names (mapv :original-name P-gs)))))

    ;FIXME need unit tests that pass even though a Closure failed to check
    ;FIXME need to update the closure-cache to make this an explicit subtyping check in internal language
    (Closure? t)
    (some-> (check-or-nil P (:env t) (:expr t))
            u/ret-t)

    (and (= :Seq (:op t))
         (= :Seq (:op P)))
    (update t :type #(match-dir dir % (:type P)))

    :else nil))

; T P -> (U nil T)
(defn smallest-matching-super [t P] (match-dir :up t P))
; T P -> (U nil T)
(defn largest-matching-sub [t P] (match-dir :down t P))

(defn expected-error [msg t P e]
  (u/expected-error-with msg t P e unparse-type))

(defn check-match [t P m e]
  {:pre [(u/Type? t)
         (u/Type? P)
         ((some-fn u/Type? nil?) m)]
   :post [(u/Type? %)]}
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

(defn unparse-free-name [s]
  (or (when-not u/*verbose-types*
        (-> s meta :original-name))
      s))

;ConstraintSet -> Any
(defn unparse-cset [cs]
  (when cs
    (let [onames-seq (map unparse-free-name (:xs cs))
          use-onames? (or (empty? onames-seq)
                          (apply distinct? onames-seq))
          onames (if use-onames?
                   (set onames-seq)
                   (:xs cs))]
    {:xs onames
     :cs (zipmap (if use-onames?
                   onames-seq
                   (keys (:cs cs)))
                 (map (fn [v]
                        {:lower (unparse-type-verbose (:lower v))
                         :upper (unparse-type-verbose (:upper v))})
                      (vals (:cs cs))))
     :delay (unparse-delays (:delay cs))})))


; (Set Sym) -> C
(defn trivial-constraint [X]
  {:pre [(set? X)]}
  {:xs X
   :cs {}
   :delay #{}})
; (Set Sym) -> C
(defn impossible-constraint [X]
  {:pre [(set? X)]}
  (prn "impossible")
  nil)
; (Set Sym) T Sym T -> C
(defn constraint-entry [X s x t]
  {:pre [(set? X)
         (symbol? x)]}
  (assert (empty? (set/intersection X (set/union (fv s) (fv t))))
          (set/intersection X (set/union (fv s) (fv t))))
  {:xs (set X)
   :cs {x {:lower s :upper t}}
   :delay #{}})
; (Set Sym) (Set Sym) T T -> C
(defn delay-constraint [V X s t]
  {:pre [(set? V)
         (set? X)
         (or (empty? (set/intersection (fv s) X))
             (empty? (set/intersection (fv t) X)))]}
  (prn "delay-constraint" (unparse-type s) (unparse-type t))
  (let [m (cond
            (IFn? t) (do
                             (assert (= 1 (count (:methods t))))
                             (first (:methods t)))
            (Poly? t) (let [gs (Poly-frees t)
                            body (Poly-body t gs)]
                        (assert (= 1 (count (:methods body))))
                        (first (:methods body)))
            :else (assert nil (str "What is this" (:op t))))
        _ (assert (Fn? m))
        sfv (set/intersection (fv s) X)
        {:keys [depends provides]} (if (empty? sfv)
                                     ; FIXME this doesn't seem to "depend" on a
                                     ; eg. [Int :-> Int] <: [a :-> b]
                                     ; depends #{a}, provides #{b}
                                     ; eg. Closure <: [a :-> b]
                                     {:depends (set/intersection X (into #{} (mapcat fv (:dom m))))
                                      :provides (set/intersection X (fv (:rng m)))}
                                     ; eg. [a :-> b] <: [Int :-> Int]
                                     ; provides #{a b}
                                     ; helps for tranducers, eg.
                                     ; (All [r1] [[r1 b :-> r1] :-> [r1 a :-> r1]])
                                     ; <:
                                     ; (All [r1] [[r1 Int :-> r1] :-> [r1 Int :-> r1]])
                                     {:depends #{}
                                      :provides sfv})]
    {:xs X
     :cs {}
     :delay #{{:V V :X X :lower s :upper t
               :depends depends :provides provides}}}))

; (Seqable C) -> C
(defn intersect-constraints [cs]
  ;(prn "intersect-constraints")
  (when (every? map? cs)
    ;(prn "intersect-constraints delay" (apply set/union (map :delay cs)))
    (let [imp? (atom nil)
          xs (apply set/union (map :xs cs))
          c {:xs xs
             :cs (apply merge-with
                        (fn [c1 c2]
                          (let [l (make-U [(:lower c1) (:lower c2)])
                                u (make-I [(:upper c1) (:upper c2)])]
                            (assert (empty? (set/intersection xs (set/union (fv l) (fv u))))
                                    (set/intersection xs (set/union (fv l) (fv u))))
                            (when-not (subtype? l u)
                              (prn "impossible (in intersect-constraints)"
                                   (unparse-type l)
                                   (unparse-type u))
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
    (:Base :Closure) t
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
         (u/Type? t)]
   :post [(u/Type? %)]}
  (u/subst-by sb t {:abstract-all abstract-all
                    :instantiate-all instantiate-all}))

(defn unfold [m]
  (u/unfold-by m {:Mu-body Mu-body
                  :subst subst}))

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
  ;(prn "gen-constraint")
  ;(prn "s" (unparse-type s))
  ;(prn "t" (unparse-type t))
  ;(assert (not= -wild s) s)
  ;(assert (not= -wild t) t)
  (cond
    (or (= s t)
        ;FIXME not sure if these are good ideas
        (= s -wild)
        (= t -wild))
    (trivial-constraint X)
    ; CG-Top
    (= -any t) (trivial-constraint X)
    ; CG-Bot
    (= -nothing s) (trivial-constraint X)
    ; CG-Upper
    (and (= :F (:op s))
         (contains? X (:name s)))
    (let [T (demote V t)]
      (constraint-entry X -nothing (:name s) T))
    ; CG-Lower
    (and (= :F (:op t))
         (contains? X (:name t)))
    (let [S (promote V s)]
      (constraint-entry X S (:name t) -any))
    (or (= :F (:op s))
        (= :F (:op t)))
    (impossible-constraint X)
    (and (= :Seq (:op s))
         (= :Seq (:op t)))
    (gen-constraint V X (:type s) (:type t))
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
    (Poly? t) 
    (cond
      (#{:IFn :Poly :Closure} (:op s)) (delay-constraint V X s t)
      :else nil)
    :else (impossible-constraint X)))

(defn substitution-for-variances [variances bounds]
  (into {}
        (map (fn [[n variance]]
               {:pre [(symbol? n)]
                :post [(:op (second %))]}
               [n (case variance
                    (:contravariant) (get-in bounds [n :upper])
                    (get-in bounds [n :lower]))]))
        variances))

(defn substitution-for-constraint [X c t]
  (let [variances (merge (zipmap X (repeat :constant))
                         (select-keys (fv-variances t) X))
        bounds (into {}
                     (map (fn [x]
                            [x {:lower (get-in c [:cs x :lower] -nothing)
                                :upper (get-in c [:cs x :upper] -any)}]))
                     X)]
    (substitution-for-variances variances bounds)))

(defn subst-with-constraint [X c t]
  (let [sbt (substitution-for-constraint X c t)]
    (subst sbt t)))

(defn order-delays [delays]
  {:pre [(every? (comp set? :depends) delays)
         (every? (comp set? :provides) delays)]}
  ;(prn "order-delays" (unparse-delays delays))
  ;(prn "graph" (delays->graph delays))
  (when-let [order (topo/kahn-sort (delays->graph delays))]
    ;(prn "sorted order" order)
    (let [delay-order (mapv
                        (fn [sym]
                          (set (filter #(or (contains? (:depends %) sym)
                                            ; for delays where variables are on the left
                                            ; eg. [a :-> b] <: [Int :-> Int]
                                            (and (empty? (:depends %))
                                                 (contains? (:provides %) sym)))
                                       delays)))
                        order)]
      (into [] (distinct) (apply concat delay-order)))))

(defn scoped-pred [pred t]
  {:pre [(:op t)]}
  (if (= :Scope (:op t))
    (recur pred (:scope t))
    (pred t)))

(defn uniquify-onames [names used-onames]
  (let [fqs (atom (frequencies names))]
    (mapv (fn [sym]
            {:pre [(contains? @fqs sym)]}
            (let [osym sym]
              (if (and (= 1 (@fqs sym))
                       (not (used-onames sym)))
                sym
                (loop [sym (symbol (str sym "'"))]
                  (if (or (contains? @fqs sym)
                          (used-onames sym))
                    (recur (symbol (str sym "'")))
                    (do (swap! fqs 
                               #(-> %
                                    (assoc sym 1)
                                    (update osym dec)))
                        sym))))))
          names)))

(defn process-delays [c]
  {:pre [c]}
  (let [process-delay (fn [c {:keys [V X lower upper] :as dly}]
                        {:pre [c
                               (or (empty? (set/intersection (fv lower) X))
                                   (empty? (set/intersection (fv upper) X)))]}
                        (prn "process delay")
                        (prn "X" (into #{} (map unparse-free-name) X))
                        (prn "lower" (unparse-type lower) (set/intersection (fv lower) X))
                        (prn "upper" (unparse-type upper) (set/intersection (fv upper) X))
                        (let [m (cond
                                  (IFn? upper) (do
                                                 (assert (= 1 (count (:methods upper))))
                                                 (first (:methods upper)))
                                  (Poly? upper) (let [gs (Poly-frees upper)
                                                      body (Poly-body upper gs)]
                                                  (assert (= 1 (count (:methods body))))
                                                  (first (:methods body)))
                                  :else (assert nil (str "What is this" (:op upper))))
                              ddom (mapv #(subst-with-constraint X c %)
                                         (:dom m))
                              _ (prn "dom" (mapv unparse-type (:dom m)))
                              _ (prn "ddom" (mapv unparse-type ddom))
                              rng (:rng m)
                              wrng (subst (zipmap X (repeat -wild))
                                          rng)
                              ]
                          (prn "rng" (unparse-type rng))
                          (prn "wrng" (unparse-type wrng))
                          (when-let [sol (solve-app wrng (demote X lower) ddom)]
                            (let [sol (:rng-t sol)
                                  _ (prn "sol" (unparse-type sol))
                                  c' (gen-constraint V X sol rng)]
                              (if (or (nil? c')
                                      (seq (:delay c')))
                                (do
                                  (prn "TODO inner cset delay")
                                  nil)
                                (do
                                  (prn "c'" (unparse-cset c'))
                                  (intersect-constraints
                                    [c c'])))))))
        order (order-delays (:delay c))]
    (cond
      ; true if X's in delays are acyclic
      order (when-let [c' (reduce (fn [c dly]
                                    (or (process-delay c dly)
                                        (reduced nil)))
                                  c
                                  order)]
              ;;FIXME this should be done in intersect-constraints?
              (update c' :delay #(into (or % #{}) (:delay c))))
      ;FIXME very rough, find fixpoint
      :else (loop [fuel 100
                   c c]
              (assert (pos? fuel) "Out of fuel")
              (prn "cycle detected")
              (when-let [c' (reduce (fn [c dly]
                                      (or (process-delay c dly)
                                          (reduced nil)))
                                    c
                                    (:delay c))]
                (let [;;FIXME this should be done in intersect-constraints?]
                      c' (update c' :delay #(into (or % #{}) (:delay c)))]
                  (if (= c c')
                    c
                    (recur (dec fuel) c'))))))))

(defn synthesize-result [X {constraints :delay :as c} rng gs]
  {:pre [c]}
  (let [gs-names (map :name gs)]
    (cond
      (IFn? rng)
      (let [bounds (let [v->b (merge (zipmap gs-names (repeat {:lower -nothing
                                                               :upper -any}))
                                     (select-keys (:cs c) gs-names))]
                     (mapv (comp #(select-keys % [:lower :upper])
                                 v->b)
                           gs-names))
            ; avoid reusing these original names, otherwise they will appear to
            ; be captured by inner bindings in pretty printed types
            used-onames (set (keep (comp :original-name meta)
                                   (set/difference
                                     (set/union (fv rng)
                                                (Poly-bounds-fv bounds)
                                                (Poly-constraints-fv constraints))
                                     ;; we're capturing these intentionally, don't rename
                                     (set (map :name gs)))))]
        (prn "rng" (unparse-type rng))
        (prn "used-onames" used-onames)
        (Poly* (mapv :name gs)
               rng
               :bounds bounds
               :constraints constraints
               :original-names (uniquify-onames
                                 (map :original-name gs)
                                 used-onames)))
      (Poly? rng)
      (let [
            rng-gs (Poly-frees rng)
            rng-body (Poly-body rng rng-gs)
            _ (assert (IFn? rng-body))
            rng-cs (Poly-constraints rng rng-gs)
            rng-bounds (Poly-bounds rng rng-gs)
            names (into (mapv :name gs)
                        (map :name rng-gs))
            ; avoid reusing these original names, otherwise they will appear to
            ; be captured by inner bindings in pretty printed types
            used-onames (set (keep (comp :original-name meta)
                                   (set/difference
                                     (fv rng)
                                     ;; we're capturing these intentionally, don't rename
                                     (set names))))
            _ (prn "rng" (unparse-type rng))
            _ (prn "used-onames" used-onames)
            ]
        (Poly* names
               rng-body
               :constraints (into constraints rng-cs)
               :bounds (let [v->b (merge (zipmap gs-names
                                                 (repeat {:lower -nothing
                                                          :upper -any}))
                                         (select-keys (:cs c) gs-names))]
                         (into (mapv (comp #(select-keys % [:lower :upper])
                                           v->b)
                                     gs-names)
                               rng-bounds))
               :original-names (uniquify-onames
                                 (into (mapv :original-name gs)
                                       (map :original-name rng-gs))
                                 used-onames)))
      (not (#{:Union :Intersection :Poly} (:op rng)))
      (subst-with-constraint X c rng)
      :else (do (prn "TODO return too complex" (:op rng) (:op (:type rng)))
                nil))))

; V; X; P; c |- m; cargs => T
(defn solve-pmethod [V X m P cargs gs existing-c]
  {:pre [(set? V)
         (set? X)
         (u/Type? P)
         (vector? cargs)
         (every? u/Type? cargs)
         (Fn? m)
         (vector? gs)
         ((some-fn nil? map?) existing-c)]
   :post [(or (nil? %)
              (and (map? %)
                   (u/Type? (:rng-t %))
                   (map? (:subst %))))]}
  ;(prn "solve-pmethod" (unparse-type m) (unparse-type P) (mapv unparse-type cargs))
  (when (= (count (:dom m))
           (count cargs))
    (let [cdom (mapv #(gen-constraint V X %1 %2) cargs (:dom m))
          ;_ (prn "cdom" (map unparse-cset cdom))
          rng (:rng m)]
      (when-let [exp (largest-matching-sub -any P)]
        ;(prn "rng" (unparse-type rng))
        ;(prn "expected return" (unparse-type exp))
        (let [crng (gen-constraint V X rng exp)]
          ;(prn "crng" (unparse-cset crng))
          ;(prn "existing-c" (unparse-cset existing-c))
          (when-let [c (intersect-constraints
                         (concat [crng existing-c] cdom))]
            ;(prn "intersected" (unparse-cset c))
            (when-let [c (process-delays c)]
              ;(prn "c delays" (unparse-delays (:delay c)))
              (when-let [synth-res (synthesize-result X c rng gs)]
                ;(prn "synth-res" (unparse-type synth-res))
                (when-let [smret (smallest-matching-super synth-res P)]
                  {:rng-t smret
                   :interface m
                   :subst (substitution-for-constraint X c m)})))))))))

; (defalias CExpected '{:args (Vec T) :ret T})

; (Atom (Map Symbol (HMap :mandatory {:reduction-count Int,
;                                     :expecteds (Map CExpected Int)}
;                         ; if the closure didn't type check, these might not be added
;                         :optional  {:forms (Vec Any)
;                                     :actual-rngs (Map CExpected (Set T))})))
(def ^:dynamic *closure-cache* nil)
(def ^:dynamic *reduction-limit* 20)
(def ^:dynamic *global-reduction-counter* nil)
(def ^:dynamic *global-reduction-limit* 100)

(declare suggest-annotation)

(def ^:dynamic *currently-elaborating-closures* {})

(declare elaborated-type)

;returns the full elaborated type for closure id
(defn elaborated-closure-type [closure-cache cop]
  {:pre [(map? closure-cache)
         (symbol? cop)]
   :post [(u/Type? %)]}
  (let [{:keys [expecteds actual-rngs original-form] :as entry} (get closure-cache cop)
        ;_ (prn "elaborated-closure-type" cop (count expecteds) (count actual-rngs))
        ;_ (binding [*print-length* nil
        ;            *print-level* nil]
        ;    (prn original-form))

        ; nil `entry` implies `(IFn)` annotation (dead code), because the symbolic closure
        ; was never symbolically invoked
        _ (assert ((some-fn nil? map?) entry))
        ; flag is true if this type should be recursive
        this-flag (atom nil) 
        this-rec-sym (gensym "rec")
        fn-type-from-expected (fn [{:keys [args] :as expected}]
                                (let [actuals (get actual-rngs expected)
                                      _ (assert (seq actuals))
                                      t {:op :Fn
                                         :dom args
                                         :rng (make-U actuals)}]
                                  (cond
                                    (*currently-elaborating-closures* cop)
                                    (let [{:keys [flag rec-sym]} (*currently-elaborating-closures* cop)
                                          _ (reset! flag true)]
                                      {:op :F :name rec-sym})

                                    :else (binding [*currently-elaborating-closures*
                                                      (assoc *currently-elaborating-closures*
                                                             cop
                                                             {:rec-sym this-rec-sym
                                                              :flag this-flag})]
                                              (elaborated-type closure-cache t)))))
        t {:op :IFn
           :methods (into []
                          (comp ; resolve an arity for this symbolic closure
                                (map (comp fn-type-from-expected key))
                                ; now resolve duplicates, crucially after all symbolic closures are resolved.
                                (distinct))
                          expecteds)}
        t (cond
            @this-flag (Mu* this-rec-sym t)
            :else t)]
    ;(prn "computed" cop)
    t))

(def ^:dynamic *currently-suggesting-closures* #{})

(defn elaborated-type [closure-cache t]
  {:pre [(map? closure-cache)]
   :post [(u/Type? %)]}
  (let [elab #(elaborated-type closure-cache %)]
    (case (:op t)
      :Closure (elaborated-closure-type closure-cache (:id t))
      (walk-type elab t))))

; The :Closure case in `subtype?` might cause irrelevant side effects
; to the closure-cache, so it might cause us to give bad suggestions sometimes.
; Of course, the type system will catch the errors if the users take our advice
; and actually use our suggested annotations.

; Symbol -> Type
(defn suggested-annotation-for-closure [closure-cache cop]
  {:pre [(map? closure-cache)
         (symbol? cop)]
   :post [(u/Type? %)]}
  (let [{:keys [reduction-count expecteds actual-rngs] :as entry} (get closure-cache cop)]
    (if (contains? *currently-suggesting-closures* cop)
      -any ; probably in an infinite loop
      (binding [*currently-suggesting-closures* (conj *currently-suggesting-closures* cop)]
        ;(prn "expecteds" cop entry closure-cache)
        (cond
          ; likely this is a good annotation for arguments
          (= (count expecteds) 1)
          (let [{:keys [args] :as expected} (key (first expecteds))
                actuals (get actual-rngs expected)
                rng (if (= (count actuals) 1)
                      (first actuals)
                      -any)]
              (suggest-annotation
                closure-cache
                {:op :IFn
                 :methods [{:op :Fn
                            :dom args
                            :rng rng}]}))
          
          ; if argument count is always the same, just suggest a [Any_0 Any_1 ... Any_n :-> Any]
          ; annotation
          (and (seq expecteds)
               (apply = (map (comp count :args) (keys expecteds))))
          {:op :IFn
           :methods [{:op :Fn
                      :dom (repeat (-> expecteds keys first :args count) -any)
                      :rng -any}]}

          ;otherwise we have no idea. maybe `?` is better here, but users can't write `?`.
          :else -any)))))

(defn suggest-annotation [closure-cache t]
  {:pre [(map? closure-cache)]
   :post [(u/Type? %)]}
  (let [sg #(suggest-annotation closure-cache %)]
    (case (:op t)
      ;TODO handle free type variables, do they imply a polymorphic annotation, or perhaps just upcast to Any?
      :Closure (suggested-annotation-for-closure closure-cache (:id t))
      (walk-type sg t))))

(defn closure-report [closure-cache cop]
  {:pre [(map? closure-cache)
         (Closure? cop)]}
  ; if a local function happens to have equivalent source and environment,
  ; their reports will probably be conflated
  (when-let [{:keys [reduction-count expecteds actual-rngs] :as entry} (get closure-cache cop)]
    (str "\n=== Symbolic Closure report ===\n"
         "\tReductions: " (or reduction-count 0) "\n"
         "\tDistinct expecteds: " (count expecteds) "\n"
         "\tDistinct actual rngs: " (count (apply set/union (vals actual-rngs)))
         (when (= (count expecteds) 1)
           (let [{:keys [args] :as expected} (key (first expecteds))
                 actuals (get actual-rngs expected)]
             (str "\n\tSuggested argument annotations:\n"
                  (binding [*print-level* 10
                            *print-length* 10]
                    (apply str (mapv (fn [t]
                                       (let [t (suggest-annotation closure-cache t)]
                                         (str "\t\t" (prn-str (unparse-type t)))))
                                     args)))
                  (when (= (count actuals) 1)
                    (let [rng (suggest-annotation closure-cache (first actuals))]
                      (str "\n\tSuggested return annotation:\n"
                           (binding [*print-level* 10
                                     *print-length* 10]
                             (str "\t\t" (prn-str (unparse-type rng)))))))))))))

(def ^:dynamic *enclosing-fn-stack* [])

; T T (Seqable T) -> (U nil '{:rng-t T})
(defn solve-app [P cop cargs]
  {:pre [(u/Type? P)
         (u/Type? cop)
         (every? u/Type? cargs)]
   :post [(or (nil? %)
              (and (map? %)
                   (u/Type? (:rng-t %))
                   (u/Type? (:interface %))))]}
  ;(prn "solve-app" (:op cop))
  ;(prn "cop" (unparse-type cop))
  ;(prn "P" (unparse-type P))
  ;(prn "cargs" (mapv unparse-type cargs))
  (case (:op cop)
    :Intersection (let [successes (keep #(solve-app P % cargs) (:types cop))
                        _ (when (empty? successes)
                            (throw (ex-info (str "Cannot invoke " (unparse-type cop))
                                            {type-error-kw true})))]
                    {:rng-t (make-I (map :rng-t successes))
                     :interface (make-I (map :interface successes))})
    :Union (let [sols (map #(solve-app P % cargs) (:types cop))
                 rng-ts (map :rng-t sols)]
             {:rng-t (make-U rng-ts)
              :interface (make-I (map :interface sols))})
    :Base (throw (ex-info (str "Cannot invoke " (unparse-type cop))
                          {type-error-kw true}))
    :Closure (let [_ (assert *closure-cache*)
                   id (:id cop)
                   enclosing-fn-stack (:enclosing-fn-stack cop)
                   ;_ (prn "checking closure" id)
                   _ (assert (symbol? id))
                   _ (some-> *closure-cache*
                       (swap! (fn [closure-cache]
                                (update closure-cache id
                                  (fn [{i :reduction-count :as m}]
                                    (let [i ((fnil inc 0) i)]
                                      (if (some-> *reduction-limit*
                                                  (< i))
                                        (throw (ex-info (str "Exceeded 'fn' checking limit, consider annotating: " (:expr cop)
                                                             (closure-report closure-cache cop)
                                                             ;"\n" (mapv unparse-type cargs)
                                                             )
                                                        {type-error-kw true}))
                                        (-> m
                                            (assoc :reduction-count i)
                                            (update :expecteds update {:args cargs :ret P} (fnil inc 0))))))))))
                   _ (some-> *global-reduction-counter*
                             (swap! (fn [i]
                                      (let [i (inc i)]
                                        (if (some-> *global-reduction-limit*
                                                    (< i))
                                          (throw (ex-info (str "Exceeded 'fn' global checking limit, consider annotating: " (:expr cop)
                                                               (some-> *closure-cache* deref (closure-report cop))
                                                               ;"\n" (mapv unparse-type cargs)
                                                               )
                                                          {type-error-kw true}))
                                          i)))))

                   rifn (binding [*enclosing-fn-stack* enclosing-fn-stack]
                          (check {:op :IFn
                                  :methods [{:op :Fn
                                             :dom cargs
                                             :rng P}]}
                                 (:env cop)
                                 (:expr cop)))
                   ifn (u/ret-t rifn)
                   eifn (u/ret-e rifn)
                   _ (assert (and (IFn? ifn)
                                  (= 1 (count (:methods ifn)))))
                   m (first (:methods ifn))
                   actual-rng (:rng m)
                   _ (assert (u/Type? actual-rng))
                   _ (some-> *closure-cache*
                       (swap! assoc-in [id :original-form] (:expr cop)))
                   _ (some-> *closure-cache*
                       (swap! update-in [id :forms] (fnil conj []) eifn))
                   _ (some-> *closure-cache*
                       (swap! update-in [id :actual-rngs {:args cargs :ret P}]
                              (fn [actual-rngs]
                                (conj (or actual-rngs #{}) actual-rng))))]
               ;(prn "intermediate cache" @*closure-cache*)
               {:interface {:op :IFn
                            :methods [{:op :Fn
                                       :dom cargs
                                       :rng actual-rng}]}
                :rng-t actual-rng})
    :IFn (some (fn [m]
                 {:pre [(Fn? m)]}
                 (when (= (count cargs)
                          (count (:dom m)))
                   (when (every? identity (map subtype? cargs (:dom m)))
                     (when-let [rng-t (smallest-matching-super (:rng m) P)]
                       {:rng-t rng-t
                        :interface {:op :IFn
                                    :methods [m]}}))))
               (:methods cop))
    :Poly (let [gs (Poly-frees cop)
                gs-names (map :name gs)
                V #{}
                X (set gs-names)
                body (Poly-body cop gs)
                pbounds (Poly-bounds cop gs)
                pconstraints (Poly-constraints cop gs)
                existing-c (intersect-constraints
                             (concat
                               (map #(delay-constraint V X (:lower %) (:upper %))
                                    pconstraints)
                               (map (fn [{:keys [lower upper]}]
                                      (gen-constraint V X lower upper))
                                    pbounds)))
                ;_ (prn "existing-c" (unparse-cset existing-c))
                ]
            (case (:op body)
              :IFn (when-let [{:keys [rng-t interface subst]} (some #(solve-pmethod V X % P cargs gs existing-c) (:methods body))]
                     (assert (Fn? interface))
                     {:rng-t rng-t
                      :interface {:op :PApp
                                  :poly (Poly* (mapv :name gs)
                                               {:op :IFn
                                                :methods [interface]}
                                               :original-names (mapv :original-name gs)
                                               :constraints pconstraints
                                               :bounds pbounds)
                                  :args (mapv (fn [g-name]
                                                {:pre [(symbol? g-name)]
                                                 :post [(u/Type? %)]}
                                                (get subst g-name))
                                              (map :name gs))}})
              nil))))

(declare check resolve-symbolic-closures)

(def ^:dynamic *simplify-EnclosingFnCase* nil)
(def ^:dynamic *disable-elaboration* nil)

(defn check-form [P env e]
  (assert (not *closure-cache*) "Recursive check-form not allowed")
  (binding [*closure-cache* (atom {}
                                  :validator #(and (map? %)
                                                   (every? symbol? (keys %))))
            *global-reduction-counter* (atom 0 :validator int?)]
    (let [e (check P env e)]
      (if *disable-elaboration*
        e
        (let [r (resolve-symbolic-closures @*closure-cache* e)
              ; prematurely simplifies EnclosingFnCase if enabled above
              r (binding [*simplify-EnclosingFnCase* true]
                  (resolve-symbolic-closures @*closure-cache* r))]
          r)))))

; T Env E -> (U nil Result)
(defn check-or-nil [P env e]
  {:post [((some-fn nil? u/Result?) %)]}
  (u/handle-type-error (constantly nil)
    (check P env e)))

(declare merge-enclosing-fn-cases)

; dirty-tree-walk expression e and resolve symbolic closures
(defn resolve-symbolic-closures [closure-cache e]
  {:pre [(map? closure-cache)]}
  ;postwalk because suggested-annotation-for-closure already traverses its result
  ; to resolve closures, and so we can also simplify EnclosingFnCase types
  (walk/postwalk (fn [e]
                   (cond
                     ;expand symbolic closure bodies
                     (and (seq? e)
                          (= ::ClosureFormsByID (first e))
                          (= 2 (count e)))
                     (let [{:keys [ids original-form] :as opt} (second e)
                           _ (assert (map? opt))
                           ffrms (map #(get-in closure-cache [% :forms]) ids)]
                       (if (every? nil? ffrms)
                         ;dead code, equivalent to checking the function as Any (or maybe `(IFn)`?)
                         original-form
                         (let [_ (assert (every? (every-pred vector? seq) ffrms)
                                         (vec ffrms))
                               frms (mapv #(resolve-symbolic-closures closure-cache %)
                                          (apply concat ffrms))]
                           (merge-enclosing-fn-cases frms))))

                     ;expand symbolic closure types
                     (and (seq? e)
                          (= ::ClosureByID (first e))
                          (symbol? (second e)))
                     (let [[_ id] e
                           _ (assert (symbol? id))
                           ; resolve this closure type
                           t (elaborated-closure-type closure-cache id)
                           ; convert back to syntax
                           e (binding [*unparse-disallow-closure* true]
                               (unparse-type t))]
                       ; recur
                       #_(resolve-symbolic-closures closure-cache e)
                       e)

                     ;simplify EnclosingFnCase types
                     (and *simplify-EnclosingFnCase*
                          (seq? e)
                          (= 'EnclosingFnCase (first e))
                          (integer? (second e)))
                     (let [[_ _ & fn-cases] e
                           _ (assert (even? (count fn-cases)))
                           cases-paired (partition 2 fn-cases)]
                       ; rhs never changes
                       (if (apply = (map second cases-paired))
                         (second fn-cases)
                         ;TODO group cases keyed via unions
                         e))

                     :else e))
                 e))

(defn count-papps [t]
  {:pre [(u/Type? t)]
   :post [(int? %)]}
  (let [cnt (atom 0)]
    (walk-type (fn [t]
                 (if (= :PApp (:op t))
                   (swap! cnt inc)
                   t))
               t)
    @cnt))

; Type -> Any
(defn wrap-enclosing-fn-cases [t]
  {:pre [(u/Type? t)]}
  (let [; Nat (Vec T) Any -> Any
        wrap1 (fn [n stack t]
                (if (seq stack)
                  (recur (inc n)
                         (pop stack)
                         (list 'EnclosingFnCase n
                               (binding [*unparse-disallow-wildcard* true]
                                 (unparse-type (peek stack)))
                               t))
                  t))]
    (wrap1 0 *enclosing-fn-stack*
           (binding [*unparse-disallow-wildcard* true]
             (unparse-type t)))))

(defn ann-form? [e]
  (and (seq? e)
       (= 'ann (first e))
       (= 3 (count e))))
(defn EnclosingFnCase-form? [e]
  (and (seq? e)
       (= 'EnclosingFnCase (first e))
       (integer? (second e))
       (<= 4 (count e))))

(defn ClosureFormsByID-form? [e]
  (and (seq? e)
       (= ::ClosureFormsByID (first e))
       (= (count e) 2)
       (map? (second e))))

; (Seqable Any) -> Any
; dirty-tree-walk to merge EnclosingFnCase forms in arbitrary expressions/types
; depends on: 
; 1. (list 'ann e1 e2) only ever is an ann form
;    - local bindings cannot shadow first-order usages of 'ann
;    - I don't think it can appear in a type
; 2. (list ::ClosureFormsByID {:original-form f, :ids [syms ...]}) only ever is a placeholder for a symbolic closure form
; 3. (list 'EnclosingFnCase i c1-q c1-a, c2-q c2-a ...) is always an EnclosingFnCase type
(defn merge-enclosing-fn-cases [es]
  {:pre [(seq es)]}
  (let [add-ann-left (fn [e1 e2]
                       {:pre [(ann-form? e1)]}
                       (let [[ann e t] e1]
                         (list ann
                               (merge-enclosing-fn-cases [e e2])
                               t)))]
    (reduce (fn [e1 e2]
              ;(prn "e1" e1)
              ;(prn "e2" e2)
              (cond
                (= e1 e2) e1

                ;extra 'ann on the left
                (and (ann-form? e1) (not (ann-form? e2))) (add-ann-left e1 e2)

                ;extra 'ann on the right
                (and (ann-form? e2) (not (ann-form? e1))) (add-ann-left e2 e1)

                (and ((every-pred EnclosingFnCase-form?) e1 e2)
                     (apply = (map second [e1 e2])))
                (let [[_ _ & e2-cases] e2]
                  (concat e1 e2-cases))

                ((every-pred ClosureFormsByID-form?) e1 e2)
                (let [e1-opt (second e1)
                      e2-opt (second e2)]
                  (assert ((every-pred map?) e1-opt e2-opt)
                          [e1 e2])
                  (assert (apply = (map :original-form [e1-opt e2-opt])))
                  (list (first e1)
                        (merge (select-keys e1-opt [:original-form])
                               {:ids (into (:ids e1-opt) (:ids e2-opt))})))

                (and (vector? e1)
                     (vector? e2)
                     (= (count e1)
                        (count e2)))
                (mapv #(merge-enclosing-fn-cases %&) e1 e2)

                (and (seq? e1)
                     (seq? e2)
                     (= (count e1)
                        (count e2)))
                (doall (map #(merge-enclosing-fn-cases %&) e1 e2))

                :else (throw (Exception. (str "Cannot unify fn cases: " e1 " " e2)))
                ))
            es)))

(def constant-type (u/constant-type-fn parse-type))

(defn type-for-symbol [env e]
  (u/type-for-symbol-with env e constant-type))

(def reserved-symbols '#{ann let fn fn*})

#_
(t/ann check [P Env E :-> T])
(defn check [P env e]
  {:pre [(u/Type? P)
         (map? env)]
   :post [(u/Result? %)]}
  (cond
    ; locals shadow globals
    (symbol? e) (let [t (type-for-symbol env e)
                      m (smallest-matching-super t P)]
                  (u/->Result e (check-match t P m e)))
    (vector? e) (let [rs (mapv #(check -wild env %) e)
                      t {:op :Seq
                         :type (make-U (map u/ret-t rs))}
                      m (smallest-matching-super t P)]
                  (u/->Result (mapv u/ret-e rs)
                              (check-match t P m e)))
    ((every-pred seq? seq) e)
             (let [[op & args] e]
               (case op
                 ann (let [[e' at & more] args
                           _ (when more
                               (throw (ex-info (str "Extra arguments to 'ann': " more)
                                               {type-error-kw true})))
                           _ (assert (= 2 (count args)) "Not enough arguments to 'ann'")
                           r (check (parse-type at) env e')
                           t (u/ret-t r)
                           m (smallest-matching-super t P)
                           mtc (check-match t P m e)]
                       ;(prn "ann")
                       (u/->Result (list 'ann (u/ret-e r) (unparse-type mtc))
                                   mtc))
                 let (let [[b body & more] args
                           _ (when more
                               (throw (ex-info (str "Extra arguments to 'let': " more)
                                               {type-error-kw true})))
                           _ (assert (= 2 (count args)))
                           _ (assert (even? (count b)))
                           _ (assert (vector? b))
                           b (partition 2 b)]
                       (check P env
                              (reduce (fn [e b]
                                        (list (list 'fn [(first b)] e)
                                              (second b)))
                                      body
                                      (reverse b))))
                 (fn fn*)
                    (let [[plist body & more] args
                          _ (when more
                              (throw (ex-info (str "Extra arguments to 'fn': " more)
                                              {type-error-kw true})))
                          _ (assert (= 2 (count args)) "Not enough arguments to 'fn'")
                          _ (assert (and (vector? plist)
                                         (every? symbol? plist))
                                    (str "'fn' takes a vector of arguments, found " plist))
                          _ (assert (not-any? reserved-symbols plist)
                                    (str "Cannot use reserved symbol: "
                                         (some reserved-symbols plist)))
                          r (cond
                              (= -wild P) (let [t {:op :Closure
                                                   :id (gensym 'closure)
                                                   :enclosing-fn-stack *enclosing-fn-stack*
                                                   :env env
                                                   :expr e}]
                                            (u/->Result (list 'ann
                                                              (list ::ClosureFormsByID
                                                                    {:original-form e
                                                                     :ids [(:id t)]})
                                                              ; FIXME e needs to be updated with static info
                                                              (binding [*unparse-closure-by-id* true]
                                                                (wrap-enclosing-fn-cases t)))
                                                        t))
                              (IFn? P) (let [methodrs (mapv (fn [m]
                                                              {:pre [(Fn? m)]
                                                               :post [(u/Result? %)
                                                                      (Fn? (u/ret-t %))]}
                                                              (when-not (= (count plist) (count (:dom m)))
                                                                (throw (ex-info (str "Function does not match expected number of parameters"
                                                                                     "\nActual:\n\t" (count plist)
                                                                                     "\nExpected:\n\t" (count (:dom m))
                                                                                     "\nExpected type:\n\t" (unparse-type m)
                                                                                     "\nin:\n\t" e)
                                                                                {type-error-kw true})))
                                                              ;(prn "checking lambda" e)
                                                              ;(prn "method" (unparse-type m))
                                                              (let [;demote wildcards
                                                                    ; FIXME if we have wildcards in the domain, it might be more useful to return
                                                                    ; a Closure type after verifying this arity matches. But what if
                                                                    ; we want to attach some information to the Closure type?
                                                                    ddom (mapv #(demote #{} %) (:dom m))
                                                                    env (merge env (zipmap plist ddom))
                                                                    rrng (binding [*enclosing-fn-stack*
                                                                                   (conj *enclosing-fn-stack*
                                                                                         ; erase wildcards to prevent them appearing
                                                                                         ; in elaboration
                                                                                         ; eg. [Int -> ?] => [Int -> Any]
                                                                                         ; eg. [? -> Int] => [Nothing -> Int]
                                                                                         (promote #{} m))]
                                                                           (check (:rng m) env body))
                                                                    rng (u/ret-t rrng)]
                                                                (u/->Result
                                                                  (list 'fn plist (u/ret-e rrng))
                                                                  (assoc m
                                                                         :dom ddom
                                                                         :rng rng))))
                                                            (:methods P))
                                             _ (assert (seq methodrs))
                                             t {:op :IFn
                                                :methods (mapv u/ret-t methodrs)}
                                             es (map u/ret-e methodrs)
                                             _ (assert (seq es))
                                             ;_ (do (prn "merging") (mapv prn es))
                                             e (merge-enclosing-fn-cases es)]
                                         ;(prn "=>")
                                         ;(prn e)
                                         (u/->Result e t))
                              ; TODO unit tests for polymorphically annotated fn's
                              (Poly? P) (let [gs (Poly-frees P)
                                              gs-names (mapv :name gs)
                                              t (Poly-body P gs)
                                              r (check t env e)]
                                          (update r :t
                                                  #(Poly* gs-names %
                                                          :original-names (mapv :original-name gs))))
                              (= -any P) (u/->Result e -any)
                              ;; TODO unions of functions
                              :else (throw (ex-info (str "Function does not match expected type:"
                                                         "\nExpected:\n\t" (unparse-type P)
                                                         "\nin:\n\t" e)
                                                    {type-error-kw true})))]
                      r)
                 (let [rcop (check -wild env op)
                       cop (u/ret-t rcop)
                       rcargs (mapv #(check -wild env %) args)
                       cargs (mapv u/ret-t rcargs)]
                   (if-let [{:keys [interface] :as sol} (solve-app P cop cargs)]
                     (let [eop (u/ret-e rcop)
                           previous-papps (count-papps cop)
                           new-papps (count-papps cop)]
                       ;(prn "eop" eop)
                       (u/->Result (list* (if (or (= cop interface)
                                                  (= previous-papps new-papps))
                                            eop
                                            (list 'ann eop (binding [*unparse-closure-by-id* true]
                                                             (wrap-enclosing-fn-cases
                                                               interface))))
                                          (map u/ret-e rcargs))
                                   (:rng-t sol)))
                     (throw (ex-info (str "Could not apply function: "
                                          "\nFunction:\n\t"
                                          (u/indent-str-by "\t" (with-out-str (pprint (unparse-type cop))))
                                          "\nArguments:\n" (apply str (map #(println-str (str "\t" %)) (map unparse-type cargs)))
                                          "Expected:\n\t" (unparse-type P)
                                          "\n\nin:\n\t" e)
                                     {type-error-kw true}))))))
    ((some-fn integer? string?) e) (let [t (u/type-for-value e)
                                         m (smallest-matching-super t P)]
                                     (u/->Result e
                                                 (check-match t P m e)))
    :else (assert nil (str "Bad expression in check: " (pr-str e)))))

;assumes form is well-typed
(defn eval-form [form]
  (binding [*ns* (the-ns 'lti-model.external-eval)]
    (eval form)))

(comment
  (check-form -Int {} 1)
  (check-form -wild {} 1)
  (check-form -wild {} [1 2])
  (check-form -Int {} [1 2])
  (check-form -wild {} '(fn [x] [1 2]))
  (check-form -wild {} '(app (fn [x] [1 2]) 1))
)

(ns lti-model.core
  (:require [clojure.set :as set]
            [clojure.string :as str]
            [lti-model.topo :as topo]
            [clojure.pprint :refer [pprint]]))

; e ::=              ; Expressions
;     | c            ; constant functions
;     | n            ; integers
;     | (fn [x *] e) ; functions
;     | (let [x e *] e) ; let
;     | (ann e t)    ; type ascription
;     | [e *]        ; sequences
; t ::=                    ; Types
;     | (IFn [t * :-> t]+) ;ordered intersection function types
;     | [t * :-> t]        ;function type
;     | a                  ;type variables
;     | Int                ;integers
;     | Num                ;numbers
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
       '{:op ':Base :name Sym}
       '{:op ':Union
         :types (t/Vec P)}
       '{:op ':Intersection
         :types (t/Vec P)}))

#_
(t/defalias Env
  "Representation for type environments"
  (t/Map t/Sym T))

(def ^:dynamic *tvar* #{})

(declare make-U make-I)

(def -wild {:op :Wild})
(def -Int {:op :Base :name 'Int})
(def -Num {:op :Base :name 'Num})
(def -any {:op :Intersection :types #{}})
(def -nothing {:op :Union :types #{}})
(defn IFn? [t] (= :IFn (:op t)))
(defn Base? [t] (= :Base (:op t)))
(defn Poly? [t] (= :Poly (:op t)))
(defn Fn? [t] (= :Fn (:op t)))

; Name Expr -> Scope
(defn abstract [n t]
  (letfn [(name-to [outer t]
            {:pre [(:op t)
                   (integer? outer)]}
            (let [nt #(name-to outer %)
                  ntv #(mapv nt %)]
              (case (:op t)
                (:Wild :Closure :B :Base) t
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
                (:Wild :Closure :F :Base) t
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
          {:op :F :name (with-meta (gensym s) {:original-name s})
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
             (and (= (count syms) (count original-names))
                  (every? symbol? original-names)
                  (apply distinct? original-names)))
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
      ('#{Int} t) -Int
      ('#{Num} t) -Num
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

(def ^:dynamic *verbose-types* nil)

(defn unparse-type-verbose [t]
  (binding [*verbose-types* true]
    (unparse-type t)))

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
    :Closure (list 'Closure (unparse-env (:env t)) (:expr t))
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

(declare fv-variances)

(defn Poly-bounds-fv-variances [bounds]
  (apply merge-fv-variances 
         (map (fn [{:keys [lower upper]}]
                (merge-fv-variances (fv-variances lower)
                                    (fv-variances upper)))
              bounds)))

(defn Poly-bounds-fv [bounds]
  (set (keys (Poly-bounds-fv-variances bounds))))

(defn Poly-constraints-fv-variances [constraints]
  (apply merge-fv-variances 
         (map (fn [{:keys [lower upper]}]
                (merge-fv-variances (fv-variances lower)
                                    (fv-variances upper)))
              constraints)))

(defn Poly-constraints-fv [constraints]
  (set (keys (Poly-constraints-fv-variances constraints))))

(defn fv-variances [t]
  (let [flip-variances (fn [v]
                        {:pre [(variance? v)]
                         :post [(variance? %)]}
                        ({:covariant :contravariant
                          :contravariant :covariant
                          :invariant :invariant}
                         v))]
    (case (:op t)
      (:Wild :Closure :B :Base) {}
      ; FIXME :constraints variances?
      :Poly (merge-fv-variances (fv-variances (:type t))
                                (Poly-bounds-fv-variances (:bounds t))
                                (Poly-constraints-fv-variances (:constraints t)))
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

(defn fv [t]
  (set (keys (fv-variances t))))

(def constant-type
  {'app (parse-type '(All [a b] [[a :-> b] a :-> b]))
   'appid (parse-type '(All [a] [[a :-> a] a :-> a]))
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
                         (merge-fv-variances
                           (Poly-bounds-fv-variances bounds)
                           (Poly-constraints-fv-variances constraints)
                           (fv-variances body))
                         gs-names))
        sbt (substitution-for-variances gs-variances bounds)]
    ))

(defn base-supers [t]
  {:pre [(Base? t)]
   :post [((some-fn nil? (every-pred set? seq)) %)
          (not (contains? % t))]}
  ({'Int #{-Num}}
   (:name t)))

(defn subtype? [s t]
  {:pre [(:op s)
         (:op t)
         (not= -wild s)
         (not= -wild t)]
   :post [(boolean? %)]}
  (cond
    (or (= s t) 
        (= -any t)
        (= -nothing s))
    true
    (= :Intersection (:op t)) (every? #(subtype? s %) (:types t))
    (= :Intersection (:op s)) (boolean (some #(subtype? % t) (:types s)))
    (= :Union (:op t)) (boolean (some #(subtype? % t) (:types s)))
    (= :Union (:op s)) (every? #(subtype? % t) (:types s))
    (and (IFn? s)
         (IFn? t))
    (every? #(boolean
               (some (fn [s] (subtype-Fn? s %))
                     (:types s)))
            (:types t))
    (and (= :Seq (:op s))
         (= :Seq (:op t)))
    (subtype? (:type s) (:type t))
    (= :Base (:op s))
    (boolean
      (when-let [s (base-supers s)]
        (subtype? (make-U s) t)))
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

; T P -> T
(defn match-dir
  "Returns smallest supertype of t that matches P if direction is :up.
   Returns largest subtype of t that matches P if direction is :down.
  Returns nil if undefined."
  [dir t P]
  {:post [((some-fn nil? :op) %)]}
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
    (when-let [s (base-supers t)]
      (match-dir dir (make-U s) P))

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

    (and (Poly? t)
         (IFn? P))
    (let [sols (mapv (fn [m]
                       (let [dom (:dom m)
                             rng (:rng m)
                             _ (prn "Poly IFn match")
                             _ (prn "dom" (mapv unparse-type dom))
                             _ (prn "rng" (unparse-type rng))
                             sol (solve-app rng t dom)]
                         (prn "sol Poly IFn match" (some-> sol unparse-type))
                         ; FIXME is "smallest" correct here?
                         (when-let [ret (and sol
                                             (smallest-matching-super sol rng))]
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

    (and (= :Seq (:op t))
         (= :Seq (:op P)))
    (update t :type #(match-dir dir % (:type P)))

    :else nil))

(defn smallest-matching-super [t P]
  ;(prn "smallest-matching-super" (unparse-type t) (unparse-type P))
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

(defn unparse-free-name [s]
  (or (when-not *verbose-types*
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

(defn subst-with-constraint [X c t]
  (let [variances (merge (zipmap X (repeat :constant))
                         (select-keys (fv-variances t) X))
        bounds (into {}
                     (map (fn [x]
                            [x {:lower (get-in c [:cs x :lower] -nothing)
                                :upper (get-in c [:cs x :upper] -any)}]))
                     X)
        sbt (substitution-for-variances variances bounds)]
    (subst sbt t)))

(defn order-delays [delays]
  {:pre [(every? (comp set? :depends) delays)
         (every? (comp set? :provides) delays)]}
  (prn "order-delays" (unparse-delays delays))
  (prn "graph" (delays->graph delays))
  (when-let [order (topo/kahn-sort (delays->graph delays))]
    (prn "sorted order" order)
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

(defn indent-str-by [ind s]
  (apply str
         (interpose (str "\n" ind)
                    (str/split-lines s))))

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
                            (let [_ (prn "sol" (unparse-type sol))
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
         (:op P)
         (vector? cargs)
         (Fn? m)
         (vector? gs)
         ((some-fn nil? map?) existing-c)]}
  (prn "solve-pmethod" (unparse-type m) (unparse-type P) (mapv unparse-type cargs))
  (when (= (count (:dom m))
           (count cargs))
    (let [cdom (mapv #(gen-constraint V X %1 %2) cargs (:dom m))
          _ (prn "cdom" (map unparse-cset cdom))
          rng (:rng m)]
      (when-let [exp (largest-matching-sub -any P)]
        (prn "rng" (unparse-type rng))
        (prn "expected return" (unparse-type exp))
        (let [crng (gen-constraint V X rng exp)]
          ;(prn "crng" (unparse-cset crng))
          ;(prn "existing-c" (unparse-cset existing-c))
          (when-let [c (intersect-constraints
                         (concat [crng existing-c] cdom))]
            (prn "intersected" (unparse-cset c))
            (when-let [c (process-delays c)]
              (prn "c delays" (unparse-delays (:delay c)))
              (when-let [synth-res (synthesize-result X c rng gs)]
                (prn "synth-res" (unparse-type synth-res))
                (when-let [smret (smallest-matching-super synth-res P)]
                  smret)))))))))

(defn solve-app [P cop cargs]
  (prn "solve-app" (:op cop))
  (prn "cop" (unparse-type cop))
  (prn "P" (unparse-type P))
  (prn "cargs" (mapv unparse-type cargs))
  (case (:op cop)
    :Union (make-U (map #(solve-app P % cargs) (:types cop)))
    :Base (throw (ex-info (str "Cannot invoke " (unparse-type cop))
                          {::type-error true}))
    :Closure (let [_ (assert *closure-cache*)
                   _ (when *closure-cache*
                       (swap! *closure-cache* update cop
                              (fn [i]
                                (let [i ((fnil inc 0) i)]
                                  (if (< 20 i)
                                    (throw (ex-info (str "Exceeded 'fn' checking limit, consider annotating: " (:expr cop)
                                                         ;"\n" (mapv unparse-type cargs)
                                                         )
                                                    {::type-error true}))
                                    i)))))
                   ifn (check {:op :IFn
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
                gs-names (map :name gs)
                V #{}
                X (set gs-names)
                body (Poly-body cop gs)
                existing-c (intersect-constraints
                             (concat
                               (map #(delay-constraint V X (:lower %) (:upper %))
                                    (Poly-constraints cop gs))
                               (map (fn [{:keys [lower upper]}]
                                      (gen-constraint V X lower upper))
                                    (Poly-bounds cop gs))))
                ;_ (prn "existing-c" (unparse-cset existing-c))
                ]
            (case (:op body)
              :IFn (some #(solve-pmethod V X % P cargs gs existing-c) (:methods body))
              nil))))

(declare check)

(def ^:dynamic *closure-cache* nil)

(defn check-form [P env e]
  (binding [*closure-cache* (atom {})]
    (check P env e)))

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
                 ann (let [[e' at] args
                           _ (assert (= 2 (count args)))
                           t (check (parse-type at) env e')
                           m (smallest-matching-super t P)]
                       (prn "ann")
                       (check-match t P m e))
                 let (let [[b body] args
                           _ (assert (= 2 (count args)))
                           _ (assert (even? (count b)))
                           _ (assert (vector? b))
                           b (partition 2 b)]
                       (check P env
                              (list* (list 'fn (mapv first b) body)
                                     (map second b))))
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
                                                         (let [;demote wildcards
                                                               ; FIXME if we have wildcards in the domain, it might be more useful to return
                                                               ; a Closure type after verifying this arity matches. But what if
                                                               ; we want to attach some information to the Closure type?
                                                               ddom (mapv #(demote #{} %) (:dom m))
                                                               env (merge env (zipmap plist ddom))
                                                               rng (check (:rng m) env body)]
                                                           (assoc m
                                                                  :dom ddom
                                                                  :rng rng)))
                                                       (:methods P))}
                              ;; TODO Poly
                              (= -any P) -any
                              :else (throw (ex-info (str "Function does not match expected type:"
                                                         "\nExpected:\n\t" (unparse-type P)
                                                         "\nin:\n\t" e)
                                                    {::type-error true})))]
                      t)
                 (let [cop (check -wild env op)
                       cargs (mapv #(check -wild env %) args)
                       rt (solve-app P cop cargs)]
                   (or rt
                       (throw (ex-info (str "Could not apply function: "
                                            "\nFunction:\n\t"
                                            (indent-str-by "\t" (with-out-str (pprint (unparse-type cop))))
                                            "\nArguments:\n" (apply str (map #(println-str (str "\t" %)) (map unparse-type cargs)))
                                            "Expected:\n\t" (unparse-type P)
                                            "\n\nin:\n\t" e)
                                       {::type-error true}))))))
    (integer? e) (let [t -Int
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

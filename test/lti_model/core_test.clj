(ns lti-model.core-test
  (:require [clojure.test :refer :all]
            [clojure.pprint :refer [pprint]]
            [clojure.walk :as walk]
            [lti-model.core :refer :all :as lti]
            [lti-model.internal :as in]
            [lti-model.util :as u]))

(defmacro prs [s] `(parse-type '~s))

(defmacro tc [P e]
  `(unparse-type (u/ret-t (check-form (prs ~P) {} '~e))))

(defmacro tc-exp [P e]
  `(u/ret-e (check-form (prs ~P) {} '~e)))

(defmacro tc-err [P e]
  `(u/handle-type-error (fn [^Exception e#]
                          (println (.getMessage e#))
                          true)
     (do (tc ~P ~e)
         false)))

(defn compatible? [v1 v2]
  (cond
    (= v1 v2) true
    ((every-pred fn?) v1 v2) true
    ((every-pred coll?) v1 v2) (and (= (count v1) (count v2))
                                    (every? identity
                                            (map compatible?
                                                 v1
                                                 v2)))
    :else false))

(defmacro tc+elab [P e]
  `(let [e# '~e
         P# '~P
         r-ex# (check-form (parse-type P#) {} e#)
         e-val# (eval-form e#)
         r-in# (in/check-form {} (u/ret-e r-ex#))
         i-val# (in/eval-form (u/ret-e r-ex#))]
     (assert (compatible? e-val# i-val#)
             (str "Not compatible results: "
                  i-val# " <=> " e-val#))
     (u/ret-e r-ex#)))

(defmacro sub? [s t]
  `(subtype? (parse-type '~s)
             (parse-type '~t)))

(defn pprint' [e]
  (binding [*print-length* nil
            *print-level* nil]
    (pprint e)))

(defmacro spit-pprint [out e]
  `(spit ~out
         (with-out-str
           (pprint' ~e))))

(defmacro evl [e]
  `(eval-form '~e))

; dummy to evaluate code in this ns
(defmacro ann [e t] e)

(deftest Mu-test
  (is (= '(Rec [x] [x :-> x])
         (unparse-type (parse-type '(Rec [x] [x :-> x])))))
  ;infinite
  (is (u/throws-type-error? (parse-type '(Rec [x] x))))
  (is (= (parse-type '[(Rec [x] [x :-> x]) :-> (Rec [x] [x :-> x])])
         (unfold (parse-type '(Rec [x] [x :-> x]))))))

(deftest subtype-test
  (is (not (sub? [:-> Any] [:-> Nothing]))))

(deftest check-test
  (is (= 'Int
         (tc Int 1)))
  (is (= 'Int
         (tc ? 1)))
  (is (= '(Seq Int)
         (tc ? [1 2])))
  (is (tc-err Int [1 2]))
  (is (= '(Seq Int)
         (tc (Seq ?) [1 2])))
  (is (= '(Closure {} (fn [x] [1 2]))
         (tc ? (fn [x] [1 2]))))
  ;; FIXME
  ; perhaps could be more helpful? need a Nothing to invoke this...
  (is (= '[Nothing :-> Int]
         (tc [? :-> Int] (fn [x] 1))))
  ; again: sort of weird but I don't think this is unsound,
  ; because you need to provide an [Int -> Nothing]
  ; function to invoke it
  (is (= '[[Int :-> Nothing] :-> Int]
         (tc [[Int :-> ?] :-> Int] (fn [f] (f 1)))))
  (is (= '[Int :-> Int]
         (tc [Int :-> Int] (fn [x] x))))
  (is (tc-err [Int :-> Nothing] (fn [x] x)))
  (is (tc-err [? :-> Int] (fn [x] [1 2])))
  (is (= '[Nothing :-> (Seq Int)]
         (tc [? :-> (Seq Int)] (fn [x] [1 2]))))
  (is (tc-err [Int :-> Int] (fn [x] [1 2])))
  (is (= '(Seq Int)
         (tc ? ((fn [x] [1 2]) 1))))
  (is (= 'Int
         (tc ? (+ 1 2))))
  (is (tc-err ? (+ (fn [x] 1) 2)))
  (is (tc-err Int ((fn [x] [x]) 2)))
  (is (= 'Int
         (tc Int ((fn [x] x) 2))))
  ; ?, {} |-w app => (All [a b] [[a :-> b] a :-> b])
  ; ?, {} |-w (fn [x] [1 2]) => (Closure {} (fn [x] [1 2]))
  ; ?, {} |-w 1 => Int
  ; {} |-{a,b} (Closure {} (fn [x] [1 2])) <: [a :-> b] => 
  ; {} |-{a,b} Int <: a => {Int <: a <: Any}
  ; {} |-{a,b} b <: Any => {Nothing <: b <: Any}
  ; -------------------------------------
  ; ?, {} |-w (app (fn [x] [1 2]) 1) => ?
  (is (= '(Seq Int)
         (tc ? (app (fn [x] [1 2]) 1))))
  (is (= '(Seq Int)
         (tc (Seq ?) (app (fn [x] [1 2]) 1))))
  (is (= 'Int
         (tc ? (id 1))))
  (is (= 'Int
         (tc Int (id 1))))
  (is (tc-err (Seq Int) (id 1)))
  (is (= 'Int
         (tc ? (app id 1))))
  (is (= 'Int
         (tc Int (app id 1))))
  (is (tc-err (Seq Int) (app id 1)))
  (is (= 'Int
         (tc ? (app (fn [x] x) 1))))
  (is (= 'Int
         (tc Int (app (fn [x] x) 1))))
  (is (tc-err (Seq Int) (app (fn [x] x) 1)))
  (is (= '(All [[a :upper Int] [b :lower Int :upper Int] [c :lower Int]]
            [a :-> c])
         (tc ? (comp inc inc))))
  (is (= '[Int :-> Int]
         (tc [Int :-> Int]
             (comp inc inc))))
  (is (= '(All [a b :constraints #{[(Closure {} (fn [x] x)) :< [a :-> b]]}]
            [a :-> b])
         (tc ? (app0 (fn [x] x)))))
  (is (= '[Int :-> Int]
         (tc [Int :-> Int]
             (app0 (fn [x] x)))))
  (is (= '[Num :-> Num]
         (tc [Num :-> Num]
             (app0 (fn [x] x)))))
  (is (= '[Int :-> Int]
         (tc [Int :-> ?]
             (app0 (fn [x] x)))))
  (is (= '(All [a b c :constraints #{[(Closure {} (fn [x] x)) :< [a :-> b]]
                                     [(Closure {} (fn [x] x)) :< [b :-> c]]}]
            [a :-> c])
         (tc ?
             (comp (fn [x] x)
                   (fn [x] x)))))
  (is (= '[Int :-> Int]
         (tc [Int :-> Int]
             (comp (fn [x] x)
                   (fn [x] x)))))
  (is (= '(All [a b c :constraints #{[(Closure {} (fn [x] (x x))) :< [a :-> b]]
                                     [(Closure {} (fn [x] x)) :< [b :-> c]]}]
            [a :-> c])
         (tc ?
             (comp (fn [x] x)
                   (fn [x] (x x))))))
  (is (tc-err [Int :-> (Seq Int)]
              (comp (fn [x] x)
                    (fn [x] x))))
  (is (= 'Int
         (tc ?
             ((comp (fn [x] x)
                    (fn [x] x))
              1))))
  (is (= 'Int
         (tc Int
             ((comp (fn [x] x)
                    (fn [x] x))
              1))))
  (is (tc-err (Seq Int)
              ((comp (fn [x] x)
                     (fn [x] x))
               1)))
  ; [Int :-> Int]
  ;FIXME
  (is (= '[Nothing :-> Any]
         (tc [? :-> Any]
             (comp (fn [x] x)
                   (fn [x] x)))))
  ; FIXME
  (is (= '[Nothing :-> Int]
         (tc [? :-> Int]
             (comp (fn [x] x)
                   (fn [x] x)))))
  ; Transducers
  (is (= '(All [[a :upper Int] [b :lower Int] r]
            [[r b :-> r] :-> [r a :-> r]])
         (tc ?
             (mapT inc))))
  (is (= '(All [a [b :lower Int] r
                :constraints #{[(IFn [Int :-> Int] [Num :-> Num]) :< [a :-> b]]}]
            [[r b :-> r] :-> [r a :-> r]])
         (tc ?
             (mapT inc'))))
  (is (tc-err [Int :-> Int :-> Int]
              (fn [a b c] c)))
  )

(deftest reserved-symbol-test
  (is (thrown? AssertionError (tc ? (fn [let] let))))
  (is (thrown? AssertionError (tc ? (fn [fn] fn))))
  (is (thrown? AssertionError (tc ? (fn [fn*] fn*))))
  (is (thrown? AssertionError (tc ? (fn [ann] ann))))
  (is (thrown? AssertionError (tc ? (let [let 1] let))))
  (is (thrown? AssertionError (tc ? (let [fn 1] fn))))
  (is (thrown? AssertionError (tc ? (let [fn* 1] fn*))))
  (is (thrown? AssertionError (tc ? (let [ann 1] ann)))))

(deftest eval-test
  (is (= 1 (evl 1)))
  (is (= 2 (evl (inc 1))))
  (is (= 2 (evl (+ 1 1))))
  (is (= 1 (evl (app id 1))))
  (is (= 1 (evl ((ann (fn [x] x)
                      [Any :-> Any])
                 1))))
  ;closures
  (is (= 1 (evl ((let [a 1]
                   (ann (fn [x] a)
                        [Any :-> Any]))
                 2))))
  )

(deftest id-cast-test
  (is (= '(All [a] [a :-> a])
         (tc (All [a] [a :-> a])
             (fn [x] x))))
  (is (= '(All [a b c] [a :-> a])
         (tc (All [a b c] [a :-> a])
             id)))
  (is (tc [Nothing :-> Any]
          id))
  (is (tc [Nothing :-> Nothing]
          id))
  (is (tc [Any :-> Any]
          id))
  (is (tc-err [Any :-> Nothing]
              id))
  (is (tc-err [Int :-> Nothing]
              id))
  (is (tc [Nothing :-> Int]
          id))
  (is (tc (All [a b] [(U a b) :-> (U a b)])
          id))
  (is (tc (All [a b] [(I a b) :-> (I a b)])
          id))
  (is (tc (All [a b] [(I a b) :-> (I b a)])
          id))
  (is (tc (All [a b] [(Seq (I a b)) :-> (Seq (I b a))])
          id))
  ; eg. [(I Int Bool) :-> Bool]
  ; eg. [(I Int Bool) :-> Int]
  (is (tc (All [a b] [(I a b) :-> a])
          id))
  (is (tc (All [a b c] [(I a b c) :-> (I a c)])
          id))
  ; eg. [Int :-> (I Bool Int)]
  ; eg. [Bool :-> (I Bool Int)]
  (is (tc-err (All [a b] [a :-> (I a b)])
              id))
  (is (tc-err (All [a b c] [(I a c) :-> (I a b)])
              id))
  (is (tc-err (All [a b c] [(Seq (I a c)) :-> (Seq (I a b))])
              id))
  (is (tc (All [a b] [(U a b) :-> (U a b)])
          id))
  (is (tc-err (All [a b c] [(U a b) :-> (U a c)])
              id))
  (is (tc ?
          (let [f (ann id (All [a] [a :-> a]))]
            (f 1)
            )))
  (is (= 'Int
         (tc ?
             (let [f (fn [x] x)]
               (f 1)))))
  ;recursive function type
  (is (= 'Int
         (tc ?
             (let [f (fn [x] x)]
               ((f f) 1)))))
  ; not exponential like let-polymorphism: https://cs.stackexchange.com/questions/6617/concise-example-of-exponential-cost-of-ml-type-inference
; # let pair x f = f x x;;
; # let f1 x = pair x in
;   let f2 x = f1 (f1 x) in
;   let f3 x = f2 (f2 x) in
;   fun z -> f3 (fun x -> x) z;;
  (is
    (= 'Int
       (tc ?
           ((let [pair (fn [f] ; flipped f and x
                         (fn [x]
                           ((f x) x)))]
              (let [f1 (fn [x] (pair x))]
                (let [f2 (fn [x] (f1 (f1 x)))]
                  (let [f3 (fn [x] (f2 (f2 x)))]
                    (let [f4 (fn [x] (f3 (f3 x)))]
                      (fn [z] ((f4 (fn [x] x)) z)))))))
            ;this is apparently given a recursive type, (Rec [a] [a -> ?]).
            (fn [x]
              (fn [y]
                (fn [x']
                  (fn [y']
                    (fn [x]
                      (fn [y]
                        (fn [x']
                          (fn [y']
                            ;return 1
                            1))))))))))))
  ; smallest case of recursive function type
  (is (= '(Closure {} (fn [f] f))
         (tc ? (let [f (fn [f] f)]
                 (f f)))))
  ; features a recursive type
  (is (= 'Int
         (tc ?
            ((let [pair (fn [f] ; flipped f and x
                          (fn [x]
                            ((f x) x)))]
               (let [f1 (fn [x] (pair x))]
                 (let [f2 (fn [x] (f1 (f1 x)))]
                   (let [f3 (fn [x] (f2 (f2 x)))]
                     (let [f4 (fn [x] (f3 (f3 x)))]
                       (fn [z] ((f4 (fn [x] x)) z)))))))
             ;this is apparently given a recursive type, (Rec [a] [a -> ?]).
             (fn [x]
               (fn [y]
                 (fn [x']
                   (fn [y']
                     (fn [x]
                       (fn [y]
                         (fn [x']
                           (fn [y']
                             ;return 1
                             1))))))))))))
  ; exponential growth in size of printed type
  (is
    (= (read-string (slurp "huge_type.edn"))
       (tc ?
           ((let [pair (fn [x] ; original f and x ordering
                         (fn [f]
                           ((f x) x)))]
              (let [f1 (fn [x] (pair x))]
                (let [f2 (fn [x] (f1 (f1 x)))]
                  (let [f3 (fn [x] (f2 (f2 x)))]
                    (let [f4 (fn [x] (f3 (f3 x)))]
                      (fn [z] ((f4 (fn [x] x)) z)))))))
            (fn [x]
              (fn [y]
                (fn [x']
                  (fn [y']
                    (fn [x]
                      (fn [y]
                        (fn [x']
                          (fn [y']
                            ;return id
                            (fn [i] i)))))))))))))
  ; add expected type to the expression above, and the huge type goes away.
  ; Challenge: how to suggest user what to write and where to get rid of exponential printed type size
  ; Also: what is the type of the operator here? Needs more investigation
  (is
    (= '[Int :-> [Int :-> [Int :-> [Int :-> [Int :-> [Int :-> [Int :-> Int]]]]]]]
       (tc [Int :-> [Int :-> [Int :-> [Int :-> [Int :-> [Int :-> [Int :-> Int]]]]]]]
           ((let [pair (fn [x] ; original f and x ordering
                         (fn [f]
                           ((f x) x)))]
              (let [f1 (fn [x] (pair x))]
                (let [f2 (fn [x] (f1 (f1 x)))]
                  (let [f3 (fn [x] (f2 (f2 x)))]
                    (let [f4 (fn [x] (f3 (f3 x)))]
                      (fn [z] ((f4 (fn [x] x)) z)))))))
            (fn [x]
              (fn [y]
                (fn [x']
                  (fn [y']
                    (fn [x]
                      (fn [y]
                        (fn [x']
                          (fn [y']
                            ;return id
                            (fn [i] i)))))))))))))
  ; invoke f3
  (is
    (=    '[Int :-> [Int :-> [Int :-> [Int :-> [Int :-> Int]]]]]
       (tc [Int :-> [Int :-> [Int :-> [Int :-> [Int :-> Int]]]]]
           ((let [pair (fn [x] ; original f and x ordering
                         (fn [f]
                           ((f x) x)))]
              (let [f1 (fn [x] (pair x))]
                (let [f2 (fn [x] (f1 (f1 x)))]
                  (let [f3 (fn [x] (f2 (f2 x)))]
                    (fn [z] ((f3 (fn [x] x)) z))))))
            (fn [x']
              (fn [y']
                (fn [x]
                  (fn [y]
                    (fn [x']
                      (fn [y']
                        ;return id
                        (fn [i] i)))))))))))
  ; invoke f2
  (is
    (=    '[Int :-> [Int :-> [Int :-> Int]]]
       (tc [Int :-> [Int :-> [Int :-> Int]]]
           ((let [pair (fn [x] ; original f and x ordering
                         (fn [f]
                           ((f x) x)))]
              (let [f1 (fn [x] (pair x))]
                (let [f2 (fn [x] (f1 (f1 x)))]
                  (fn [z] ((f2 (fn [x] x)) z)))))
            (fn [x]
              (fn [y]
                (fn [x']
                  (fn [y']
                    ;return id
                    (fn [i] i)))))))))
  (is (= '[Int :-> Int]
         (tc [Int :-> Int]
             (let [id (fn [a] a)]
               id))))
  (is (= '[Int :-> [Int :-> Int]]
         (tc [Int :-> [Int :-> Int]]
             (let [id (fn [a] (fn [b] b))]
               id))))
  ; invoke f1
  (is
    (=    '[Int :-> Int]
       (tc [Int :-> Int]
           ((let [pair (fn [x]
                         (fn [sel]
                           ((sel x) x)))]
              (let [p1 (fn [x] (pair x))
                    zero (fn [x] x)]
                (fn [sel] ((p1 zero) sel))))
            (fn [fst]
              (fn [snd]
                fst))))))
  (is (= '[[Int :-> Any] :-> Any]
         (tc [[Int :-> Any] :-> Any]
             (fn [f]
               (f 1)))))
  (is (= '[[[Int :-> Int] :-> Any]
           :-> Any]
         (tc [[[Int :-> Int] :-> Any]
              :-> Any]
             (fn [f]
               (f (fn [a] a))))))
  ; ascribe type f1
  (is
    (=    '[[[Int :-> Int] :-> [[Int :-> Int] :-> [Int :-> Int]]] :-> [Int :-> Int]]
       (tc [[[Int :-> Int] :-> [[Int :-> Int] :-> [Int :-> Int]]] :-> [Int :-> Int]]
           (let [pair (fn [x]
                        (fn [sel]
                          ((sel x) x)))]
             (let [p1 (fn [x] (pair x))
                   zero (fn [x] x)]
               (fn [sel] ((p1 zero) sel)))))))
  ; invoke type p2
  (is
    (=    '[Int :-> Int]
       (tc [Int :-> Int]
           ((let [pair (fn [x]
                         (fn [sel]
                           ((sel x) x)))]
              (let [p1 (fn [x] (pair x))]
                (let [p2 (fn [x] (p1 (p1 x)))]
                  (let [zero (fn [x] x)]
                    (fn [sel] ((p2 zero) sel))))))
            (fn [x]
              (fn [x]
                (fn [i] i)))))))
  ; ascribe type x1 (from Mairson 1989)
  (is
    (=    '[[[Int :-> Int] :-> [[Int :-> Int] :-> [Int :-> Int]]] :-> [Int :-> Int]]
       (tc [[[Int :-> Int] :-> [[Int :-> Int] :-> [Int :-> Int]]] :-> [Int :-> Int]]
           (let [pair (fn [x]
                        (fn [y]
                          (fn [z]
                            ((z x) y))))]
             (let [x1 (fn [y] ((pair y) y))]
               (x1 (fn [y] y)))))))
  ; ascribe type x1 (from Mairson 1989), but more Clojurey
  (is
    (=    '[[Int Int :-> Any] :-> Any]
       (tc [[Int Int :-> Any] :-> Any]
          ;< Int,Int                 >
           ; <a,b> is [[a b :-> c] :-> c]
           (let [pair (fn [x y]
                        (fn [z]
                          (z x y)))
                 fst (fn [p]
                       (p (fn [x y]
                            x)))
                 snd (fn [p]
                       (p (fn [x y]
                            y)))]
             (let [x1 #(pair % %)]
               (x1 1))))))
  ; ascribe type x2 (from Mairson 1989), but more Clojurey
  (is
    (=    '[[[[Int Int :-> Any] :-> Any] [[Int Int :-> Any] :-> Any] :-> Any] :-> Any]
       (tc [[[[Int Int :-> Any] :-> Any] [[Int Int :-> Any] :-> Any] :-> Any] :-> Any]
          ;< < Int,Int                 >,< Int,Int                 >                 >
           ; Pair is [x y :-> [x y :-> Any]]
           (let [pair (fn [x y]
                        (fn [z]
                          (z x y)))
                 fst (fn [p]
                       (p (fn [x y]
                            x)))
                 snd (fn [p]
                       (p (fn [x y]
                            y)))]
             (let [x1 #(pair % %)]
               (let [x2 #(x1 (x1 %))]
                 ; <<1,1>,<1,1>>
                 (x2 1)))))))
  ;checks (x4)
  (is
    ;slow
     (tc Any
         (let [pair (fn [x y]
                      (fn [z]
                        (z x y)))]
           (let [x1 #(pair % %)]
           (let [x2 #(x1 (x1 %))]
           (let [x3 #(x2 (x2 %))]
           (let [x4 #(x3 (x3 %))]
             (x4 1))))))))
  ;checks (x4 with 9 fst's)
  (is
    ;FIXME slow but unsure if it will ever return!
    (binding [*disable-elaboration* true]
      (= 'Int
         (tc ?
             (let [pair (fn [x y]
                          (fn [z]
                            (z x y)))
                   fst (fn [p]
                         (p (fn [x y]
                              x)))
                   snd (fn [p]
                         (p (fn [x y]
                              y)))]
               (let [x1 #(pair % %)]
               (let [x2 #(x1 (x1 %))]
               (let [x3 #(x2 (x2 %))]
               (let [x4 #(x3 (x3 %))]
                 (fst
                   (fst
                     (fst
                       (fst
                         (fst
                           (fst
                             (fst
                               (fst
                                 (x4 1))))))))))))))))))
  ;checks (x4 with 8 fst's)
  (is
    (=    '[[Int Int :-> Int] :-> Int]
      ;FIXME slow but unsure if it will ever return!
      (binding [*disable-elaboration* true]
       (tc [[Int Int :-> Int] :-> Int]
           (let [pair (fn [x y]
                        (fn [z]
                          (z x y)))
                 fst (fn [p]
                       (p (fn [x y]
                            x)))
                 snd (fn [p]
                       (p (fn [x y]
                            y)))]
             (let [x1 #(pair % %)]
             (let [x2 #(x1 (x1 %))]
             (let [x3 #(x2 (x2 %))]
             (let [x4 #(x3 (x3 %))]
               (fst
                 (fst
                   (fst
                     (fst
                       (fst
                         (fst
                           (fst
                             (x4 1)))))))))))))))))
  ; FIXME BUG! returns Nothing
; x4 with 9 fst's, but with polymorphic annotation on 'pair'
#_
  (is
    (= 'Int
       (tc ?
           (let [pair (ann (fn [x y]
                             (fn [z]
                               (z x y)))
                           (All [a b c]
                             [a b :-> [[a b :-> c] :-> c]]))
                 fst (fn [p]
                       (p (fn [x y]
                            x)))
                 snd (fn [p]
                       (p (fn [x y]
                            y)))]
             (let [x1 #(pair % %)]
             (let [x2 #(x1 (x1 %))]
             (let [x3 #(x2 (x2 %))]
             (let [x4 #(x3 (x3 %))]
               (fst
                 (fst
                   (fst
                     (fst
                       (fst
                         (fst
                           (fst
                             (fst
                               (x4 1)))))))))))))))))
  ;checks (x5)
  (is
     (tc Any
         (let [pair (fn [x y]
                      (fn [z]
                        (z x y)))
               fst (fn [p]
                     (p (fn [x y]
                          x)))
               snd (fn [p]
                     (p (fn [x y]
                          y)))]
           (let [x1 #(pair % %)]
             (let [x2 #(x1 (x1 %))]
             (let [x3 #(x2 (x2 %))]
             (let [x4 #(x3 (x3 %))]
             (let [x5 #(x4 (x4 %))]
             (let [x6 #(x5 (x5 %))]
             (let [x7 #(x6 (x6 %))]
             (let [x8 #(x7 (x7 %))]
             (let [x9 #(x8 (x8 %))]
             (let [x10 #(x9 (x9 %))]
               (x5 1))))))))))))))
  ;checks (x6)
  (is
     (tc Any
         (let [pair (fn [x y]
                      (fn [z]
                        (z x y)))
               fst (fn [p]
                     (p (fn [x y]
                          x)))
               snd (fn [p]
                     (p (fn [x y]
                          y)))]
           (let [x1 #(pair % %)]
             (let [x2 #(x1 (x1 %))]
             (let [x3 #(x2 (x2 %))]
             (let [x4 #(x3 (x3 %))]
             (let [x5 #(x4 (x4 %))]
             (let [x6 #(x5 (x5 %))]
             (let [x7 #(x6 (x6 %))]
             (let [x8 #(x7 (x7 %))]
             (let [x9 #(x8 (x8 %))]
             (let [x10 #(x9 (x9 %))]
               (x6 1))))))))))))))
  ;hits fn checking limit (x8)
  (is
     (tc-err Any
         (let [pair (fn [x y]
                      (fn [z]
                        (z x y)))
               fst (fn [p]
                     (p (fn [x y]
                          x)))
               snd (fn [p]
                     (p (fn [x y]
                          y)))]
           (let [x1 #(pair % %)]
             (let [x2 #(x1 (x1 %))]
             (let [x3 #(x2 (x2 %))]
             (let [x4 #(x3 (x3 %))]
             (let [x5 #(x4 (x4 %))]
             (let [x6 #(x5 (x5 %))]
             (let [x7 #(x6 (x6 %))]
             (let [x8 #(x7 (x7 %))]
             (let [x9 #(x8 (x8 %))]
             (let [x10 #(x9 (x9 %))]
               (x8 1))))))))))))))
  ;hits fn checking limit (x10)
  (is
     (tc-err Any
         (let [pair (fn [x y]
                      (fn [z]
                        (z x y)))
               fst (fn [p]
                     (p (fn [x y]
                          x)))
               snd (fn [p]
                     (p (fn [x y]
                          y)))]
           (let [x1 #(pair % %)]
             (let [x2 #(x1 (x1 %))]
             (let [x3 #(x2 (x2 %))]
             (let [x4 #(x3 (x3 %))]
             (let [x5 #(x4 (x4 %))]
             (let [x6 #(x5 (x5 %))]
             (let [x7 #(x6 (x6 %))]
             (let [x8 #(x7 (x7 %))]
             (let [x9 #(x8 (x8 %))]
             (let [x10 #(x9 (x9 %))]
               (x10 1))))))))))))))
  ;hit global checking limit
  (is
    (binding [*reduction-limit* nil
              *global-reduction-limit* 1000]
     (tc-err ?
         (let [pair (fn [x y]
                      (fn [z]
                        (z x y)))
               fst (fn [p]
                     (p (fn [x y]
                          x)))
               snd (fn [p]
                     (p (fn [x y]
                          y)))]
           (let [x1 #(pair % %)]
             (let [x2 #(x1 (x1 %))]
             (let [x3 #(x2 (x2 %))]
             (let [x4 #(x3 (x3 %))]
             (let [x5 #(x4 (x4 %))]
             (let [x6 #(x5 (x5 %))]
             (let [x7 #(x6 (x6 %))]
             (let [x8 #(x7 (x7 %))]
             (let [x9 #(x8 (x8 %))]
             (let [x10 #(x9 (x9 %))]
               (x10 1)))))))))))))))
;Notes on lambda encoding of pairs
;           (let [; a Pair is [Int :-> [Int :-> Int]]
;                 ; [Int :-> [Int :-> Pair]]
;                 pair (fn [x]
;                        (fn [y]
;                          (fn [z]
;                            ((z x) y))))
;                 ; [Pair :-> Int]
;                 fst (fn [p]
;                       (p (fn [x]
;                            (fn [y]
;                              x))))
;                 ; [Pair :-> Int]
;                 snd (fn [p]
;                       (p (fn [x]
;                            (fn [y]
;                              y))))]
;             (let [; x1 creates a pair <y,y>
;                   x1 (fn [y] ((pair y) y))]
;               (let [; x2 creates the pair <<y,y>,<y,y>>
;                     x2 (fn [y] (x1 (x1 y)))]
;                 (x2 1))))

; TODO another terrible error message
#_
  (is
     (tc [[Int :-> [Int :-> [Int :-> [Int :-> [Int :-> [Int :-> [Int :-> [Int :-> [Int :-> Int]]]]]]]]]
          :->
          [Int :-> [Int :-> [Int :-> [Int :-> [Int :-> [Int :-> [Int :-> Int]]]]]]]]
         (let [pair (fn [x]
                       (fn [f]
                         ((f x) x)))]
            (let [f1 (fn [x] (pair x))]
              (let [f2 (fn [x] (f1 (f1 x)))]
                (let [f3 (fn [x] (f2 (f2 x)))]
                  (let [f4 (fn [x] (f3 (f3 x)))]
                    (fn [z] ((f4 (fn [x] x)) z)))))))))
  ; pair
  (is (= '(All [a b c]
               [a b :-> [[a b :-> c] :-> c]])
         (tc (All [a b c]
                  [a b :-> [[a b :-> c] :-> c]])
             (fn [x y]
               (fn [z]
                 (z x y))))))
  (is (= '(All [a b c]
               [a b :-> [[a b :-> c] :-> c]])
         (tc ?
             (let [pair (ann (fn [x y]
                               (fn [z]
                                 (z x y)))
                             (All [a b c]
                                  [a b :-> [[a b :-> c] :-> c]]))]
               pair))))
  ; pair+f1
; FIXME good example of a terrible error message
;  (is
;    (= '[[[Int :-> Int] :-> Int]
;         :-> Int]
;       (tc [[[Int :-> Int] :-> Int]
;            :-> Int]
;           (let [pair (ann (fn [x y]
;                             (fn [z]
;                               (z x y)))
;                           (All [a b c]
;                             [a b :-> [[a b :-> c] :-> c]]))]
;             (let [f1 (fn [x] (pair x))]
;               (fn [z] ((f1 (fn [x] x)) z)))))))

  ; inferring pair+f1
  (is
    (= '(All [[a :lower (Closure {pair (All [a b c]
                                         [a b :-> [[a b :-> c] :-> c]]),
                                  x1 (Closure {pair (All [a b c] [a b :-> [[a b :-> c] :-> c]])}
                                              (fn [y] (pair y y)))}
                                 (fn [x] x))]
              [b :lower (Closure {pair (All [a b c]
                                         [a b :-> [[a b :-> c] :-> c]]),
                                  x1 (Closure {pair (All [a b c] [a b :-> [[a b :-> c] :-> c]])}
                                              (fn [y] (pair y y)))}
                                 (fn [x] x))]
              c]
             [[a b :-> c] :-> c])
       (tc ?
           (let [pair (ann (fn [x y]
                             (fn [z]
                               (z x y)))
                           (All [a b c]
                                [a b :-> [[a b :-> c] :-> c]]))]
             (let [x1 (fn [y] (pair y y))]
               (x1 (fn [x] x)))))))
  ; evaluating pair+f1
  (is
    ((let [pair (ann (fn [x y]
                       (fn [z]
                         (z x y)))
                     (All [a b c]
                          [a b :-> [[a b :-> c] :-> c]]))]
       (let [x1 (fn [y] (pair y y))]
         (x1 (fn [x] x))))
     (fn [x y]
       (prn "(x 1)" (x 1))
       (prn "(y 1)" (y 1))
       x)))
;; attempting to annotate pair+f1
#_
  (is
    (tc [[[Int :-> Int] [Int :-> Int] :-> [Int :-> Int]] :-> [Int :-> Int]]
        (let [pair (ann (fn [x y]
                          (fn [z]
                            (z x y)))
                        (All [a b c]
                             [a b :-> [[a b :-> c] :-> c]]))]
          (let [x1 (fn [y] (pair y y))]
            (x1 (fn [x] x))))))
;; checking an applied pair+f1
;FIXME BUG! this type checks as Nothing!
#_
  (is
    (not= 'Nothing
          (tc ?
              ((let [pair (ann (fn [x y]
                                 (fn [z]
                                   (z x y)))
                               (All [a b c]
                                    [a b :-> [[a b :-> c] :-> c]]))]
                 (let [x1 (fn [y] (pair y y))]
                   (x1 (fn [x] x))))
               (fn [x y]
                 x)))))

  ; f1 + f2
  (is (tc-err ?
              (let [f (ann id (All [a b] [a :-> b]))]
                (f 1))))
  ; out of scope?
  #_
  (is (tc ?
          (let [f (ann id (All [a b] [(I a b) :-> (I a b)]))]
            (f 1))))
  )

;; mainly hofs and transducers
(deftest fancy-polymorphic-upcast
  (is (= '(All [c a b]
            [[b :-> c] [a :-> b] :-> [a :-> c]])
         (tc (All [c a b]
               [[b :-> c] [a :-> b] :-> [a :-> c]])
             comp)))
  (is (= '(All [a]
               [[a :-> a] [a :-> a] :-> [a :-> a]])
         (tc (All [a]
               [[a :-> a] [a :-> a] :-> [a :-> a]])
             comp)))
  (is (= '(All [a b]
               [[b :-> a] [a :-> b] :-> [a :-> a]])
         (tc (All [a b]
               [[b :-> a] [a :-> b] :-> [a :-> a]])
             comp)))
  (is (= '(All [a1] [a1 :-> a1])
         (tc (All [a1] [a1 :-> a1])
             (comp (fn [x] x)
                   (fn [x] x)))))
  ; like annotating (Transducer Int Int)
  (is (tc (All [r1] [[r1 Int :-> r1] :-> [r1 Int :-> r1]])
          (mapT inc)))
  (is (tc-err (All [r1 r2] [[r1 Int :-> r1] :-> [r2 Int :-> r2]])
              (mapT inc)))
  (is (= '(All [r1 r2] [[r1 Int :-> r1] :-> [r1 Int :-> r1]])
         (tc (All [r1 r2] [[r1 Int :-> r1] :-> [r1 Int :-> r1]])
             (mapT inc))))
  (is (= '(All [a b r :constraints #{[(Closure {} (fn [x] x)) :< [a :-> b]]}]
            [[r b :-> r] :-> [r a :-> r]])
         (tc ?
             (mapT (fn [x] x)))))
  ;; FIXME `r` occurs both sides
  ;; FIXME accidental shadowing of type variables?
  #_
  (is (= false
         '(All [a 
                [b :lower (All [a b r]
                            [r a :-> r])]
                [c :lower (All [a b r
                                :constraints #{[(All [a b r] [r a :-> r]) :< [r b :-> r]]}]
                            [r a :-> r])]
                :constraints #{[(All [[a :upper Int] [b :lower Int] r] [[r b :-> r] :-> [r a :-> r]]) :< [b :-> c]]
                               [(All [[a :upper Int] [b :lower Int] r] [[r b :-> r] :-> [r a :-> r]]) :< [a :-> b]]}]
             [a :-> c])
         (tc ?
             (comp
               (mapT inc)
               (mapT inc)))))
  ;TODO
  #_
  (is (tc ?
          (comp
            (mapT inc')
            (mapT inc'))))
  (is (= '(All [r1] [[r1 Int :-> r1] :-> [r1 Int :-> r1]])
         (tc (All [r1] [[r1 Int :-> r1] :-> [r1 Int :-> r1]])
             (mapT (fn [x] x)))))
  (is (tc (All [r1] [[r1 Num :-> r1] :-> [r1 Int :-> r1]])
          (mapT inc)))
  ;FIXME
  #_
  (is (tc-err (All [r1] [[r1 (Seq Int) :-> r1] :-> [r1 Int :-> r1]])
              (mapT inc)))
  ;FIXME
  #_
  (is (= '(All [r1] [[r1 Num :-> r1] :-> [r1 Int :-> r1]])
         (tc (All [r1] [[r1 Num :-> r1] :-> [r1 Int :-> r1]])
             (mapT (fn [x] x)))))
  (is (= '(All [r1] [[r1 Any :-> r1] :-> [r1 Int :-> r1]])
         (tc (All [r1] [[r1 ? :-> r1] :-> [r1 Int :-> r1]])
             (mapT (fn [x] x)))))
  ;FIXME
  #_
  (is (= '(Seq Int)
         (tc ?
             (intoT []
                    (mapT inc)
                    [1 2 3]))))
  ;FIXME
  #_
  (is (= '(Seq Int)
         (tc ?
             (intoT []
                    (mapT (fn [x] x))
                    [1 2 3]))))
  )

(deftest reduce-test
  (is (= '[[Int :-> Int] Int :-> Int]
         (tc [[Int :-> Int] Int :-> Int]
             appid)))
  (is (= 'Int
         (tc ?
             (appid id 0))))
  (is (= 'Int
         (tc ?
             (reduce (ann (fn [x y] x)
                          [Int Int :-> Int])
                     0
                     [1 2 3]))))
  (is (= 'Int
         (tc ?
             (reduce (ann (fn [x y] x)
                          (IFn [Int Int :-> Int]
                               [Num Num :-> Num]))
                     0
                     [1 2 3]))))
  (is (= 'Num
         (tc ?
             (reduce (ann (fn [x y] x)
                          (IFn [Int Int :-> Int]
                               [Num Num :-> Num]))
                     0
                     [(ann 1 Num) 2 3]))))
  (is (= 'Num
         (tc ?
             (reduce (fn [x y] (ann x Num))
                     0
                     [1 2 3]))))
  (is (= 'Int
         (tc ?
             (reduce (fn [x y] (ann x Int))
                     0
                     [1 2 3]))))
  (is (= 'Int
         (tc ?
             (reduce (fn [x y] x)
                     0
                     [1 2 3]))))
  (is (tc-err (Seq Int)
              (reduce (fn [x y] x)
                      0
                      [1 2 3]))))

; let Y = fun f -> (fun g -> fun x -> f (g g) x)
;                  (fun g -> fun x -> f (g g) x) in
; let compute = Y (fun f -> fun x -> plus 1 (f x)) in
; compute 1
(deftest ycomb
  ; hits checking limit
  (is (tc-err ?
              (let [Y (fn [f]
                        ((fn [g] (fn [x] (f (g g) x)))
                         (fn [g] (fn [x] (f (g g) x)))))]
                (let [compute (Y (fn [f x] (+ 1 (f x))))]
                  (compute 1)))))
  ; hits checking limit
  (is (tc-err ?
              (let [Y (fn [f]
                        ((fn [g] (fn [x] (f (g g) x)))
                         (fn [g] (fn [x] (f (g g) x)))))]
                (let [compute (Y (fn [f x] (+ 1 (f x))))]
                  (compute 1)))))
  )

(deftest self-application
  (is (tc-err ?
              ((fn [f] (f f)) (fn [f] (f f)))))
  (is (tc-err ?
              (let [f (fn [f] (f f))]
                (f f))))
  )

(deftest closure-suggestions
  ; suggests Int -> Int
  (is (binding [*reduction-limit* 5]
        (tc-err ?
                (let [f (fn [x] x)]
                  (f (f (f (f (f (f 1))))))))))
  ; following the suggestion fixes the problem
  (is (binding [*reduction-limit* 5]
        (tc ?
            (let [f (ann (fn [x] x) [Int :-> Int])]
              (f (f (f (f (f (f 1))))))))))
  ; suggestion with 1 level of nested Closures
  (is (binding [*global-reduction-limit* 10]
        (tc-err ?
                (let [g (fn [x] x)]
                (let [f (fn [g x] (g x))]
                  (f g (f g (f g (f g (f g (f g 1)))))))))))
  ; following the suggestion fixes the problem
  (is (binding [*global-reduction-limit* 10]
        (tc ?
            (let [g (fn [x] x)]
              (let [f (ann (fn [g x] (g x))
                           [[Int :-> Int] Int :-> Int])]
                (f g (f g (f g (f g (f g (f g 1)))))))))))
  ; suggestion with 2 levels of nested Closures
  (is (binding [*reduction-limit* 5]
        (tc-err ?
                (let [h (fn [x] x)]
                (let [g (fn [h x] (h x))]
                (let [f (fn [g x] (g h x))]
                  (f g (f g (f g (f g (f g (f g 1))))))))))))
  ; suggestion with 3 levels of nested Closures
  (is (binding [*reduction-limit* 5]
        (tc-err ?
                (let [i (fn [x] x)]
                (let [h (fn [i x] (i x))]
                (let [g (fn [h x] (h i x))]
                (let [f (fn [g x] (g h x))]
                  (f g (f g (f g (f g (f g (f g 1)))))))))))))
  ; suggestion with unexercised Closures
  (is (binding [*global-reduction-limit* 2]
        (tc-err ?
                (let [j (fn [x] x)
                      i (fn [j x] x)]
                  (i j (i j 1))))))
  )

(defn symbol-count [d]
  (when (some? d)
    (let [a (atom 0)]
      (walk/postwalk
        #(when (symbol? %)
           (swap! a inc))
        d)
      @a)))

(defn closure-count [d]
  (when (some? d)
    (let [a (atom 0)]
      (walk/postwalk
        #(when (= 'Closure %)
           (swap! a inc))
        d)
      @a)))

(defn node-count [d]
  (when (some? d)
    (let [a (atom 0)]
      (walk/postwalk
        (fn [_] (swap! a inc))
        d)
      @a)))

;from Kanellakis & Mitchell [POPL 1989]
; Example 3.1 - composing (lambda encoded) pairs, let-free
; Observation here:
; - symbolic closure types grow linearly
;   - actually, their environments grow linearly
(deftest kami89-3.1
  (is
    (symbol-count
      (tc ?
          (fn [x]
            (fn [z]
              (z x x))))))
  (is (symbol-count
        (tc ?
            (let [P (fn [x]
                      (fn [z]
                        (z x x)))]
              P))))
  (is (symbol-count
        (tc ?
            (let [P (fn [x]
                      (fn [z]
                        (z x x)))]
              (P 1)))))
  (is (symbol-count
        (tc ?
            (let [P (fn [x]
                      (fn [z]
                        (z x x)))]
              (P (P 1))))))
  (is (symbol-count
        (tc ?
            (let [P (fn [x]
                      (fn [z]
                        (z x x)))]
              (P (P (P 1)))))))
  (is (symbol-count
        (tc ?
            (let [P (fn [x]
                      (fn [z]
                        (z x x)))]
              (P (P (P (P 1))))))))
  (is (symbol-count
        (tc ?
            ((fn [x]
               (fn [z]
                 (z x x))) 1))))
  (is (symbol-count
        (tc ?
            ((fn [x]
               (fn [z]
                 (z x x)))
             ((fn [x]
                (fn [z]
                  (z x x))) 1)))))
  (is (symbol-count
        (tc ?
            ((fn [x]
               (fn [z]
                 (z x x)))
             ((fn [x]
                (fn [z]
                  (z x x)))
              ((fn [x]
                 (fn [z]
                   (z x x))) 1))))))
  (is (symbol-count
        (tc ?
            ((fn [x]
               (fn [z]
                 (z x x)))
             ((fn [x]
                (fn [z]
                  (z x x)))
              ((fn [x]
                 (fn [z]
                   (z x x)))
               ((fn [x]
                  (fn [z]
                    (z x x))) 1)))))))
  (is (symbol-count
        (tc ?
            ((fn [x]
               (fn [z]
                 (z x x)))
             ((fn [x]
                (fn [z]
                  (z x x)))
              ((fn [x]
                 (fn [z]
                   (z x x)))
               ((fn [x]
                  (fn [z]
                    (z x x)))
                ((fn [x]
                   (fn [z]
                     (z x x))) 1))))))))
  (is (symbol-count
        (tc ?
            (let [comp (fn [f g]
                         (fn [x]
                           (f (g x))))]
              (let [P (fn [x]
                         (fn [z]
                           (z x x)))]
                (comp P P))))))
  (is (symbol-count
        (tc ?
            (let [comp (fn [f g]
                         (fn [x]
                           (f (g x))))]
              (let [P (fn [x]
                         (fn [z]
                           (z x x)))]
                (comp (comp P P) P))))))
  (is (symbol-count
        (tc ?
            (let [comp (fn [f g]
                         (fn [x]
                           (f (g x))))]
              (let [P (fn [x]
                         (fn [z]
                           (z x x)))]
                (comp (comp (comp P P) P) P))))))
  (is (symbol-count
        (tc ?
            (let [comp (fn [f g]
                         (fn [x]
                           (f (g x))))]
              (let [P (fn [x]
                         (fn [z]
                           (z x x)))]
                (comp (comp (comp (comp P P) P) P) P))))))
  )

;from Kanellakis & Mitchell [POPL 1989]
; Example 3.4 - composing (lambda encoded) pairs using let
; Observation here:
; - linear increase in type size from nested symbolic closure environments
; - constant size of symbolic closure's expression: (fn [z] (z x x))
(deftest kami89-3.4
  (is ((juxt last symbol-count)
        (tc ?
            (let [P (fn [x]
                      (fn [z]
                        (z x x)))]
              (let [x0 (fn [x] x)]
                x0)))))
  (is ((juxt last symbol-count)
        (tc ?
            (let [P (fn [x]
                      (fn [z]
                        (z x x)))]
              (let [x0 (fn [x] x)]
                (let [x1 (P x0)]
                  x1))))))
  (is ((juxt last symbol-count)
        (tc ?
            (let [P (fn [x]
                      (fn [z]
                        (z x x)))]
              (let [x0 (fn [x] x)]
                (let [x1 (P x0)]
                  (let [x2 (P x1)]
                    x2)))))))
  (is ((juxt last symbol-count)
        (tc ?
            (let [P (fn [x]
                      (fn [z]
                        (z x x)))]
              (let [x0 (fn [x] x)]
                (let [x1 (P x0)]
                  (let [x2 (P x1)]
                    (let [x3 (P x2)]
                      x3))))))))
  (is ((juxt last symbol-count)
        (tc ?
            (let [P (fn [x]
                      (fn [z]
                        (z x x)))]
              (let [x0 (fn [x] x)]
                (let [x1 (P x0)]
                  (let [x2 (P x1)]
                    (let [x3 (P x2)]
                      (let [x4 (P x3)]
                        x4)))))))))
  ;inline P
  (is ((juxt last symbol-count)
       (walk/postwalk
         (fn [f]
           ('{} f f))
         (tc ?
             (let [x0 1]
               (let [x1 ((fn [x]
                           (fn [z]
                             (z x x))) x0)]
                 x1))))))
  (is ((juxt last symbol-count closure-count)
       (walk/postwalk
         identity
         #_
         (fn [f]
           ('{(Closure {x0 Int, x Int} (fn [z] (z x x))) Pc1} f f))
         (tc ?
             (let [x0 1]
               (let [
                     x1 ((fn [x]
                           (fn [z]
                             (z x x))) x0)
                     x2 ((fn [x]
                           (fn [z]
                             (z x x))) x1)
                     ]
                 x2))))))
  (is ((juxt last symbol-count closure-count)
       (walk/postwalk
         identity
         #_
         (fn [f]
           ('{
              (Closure {x0 Int, x Int} (fn [z] (z x x))) Pc1
              (Closure {x0 Int, x1 Pc1, x Pc1} (fn [z] (z x x))) Pc2
              }
                       f f))
        (tc ?
            (let [x0 1]
              (let [
                    x1 ((fn [x]
                          (fn [z]
                            (z x x))) x0)
                    x2 ((fn [x]
                          (fn [z]
                            (z x x))) x1)
                    x3 ((fn [x]
                          (fn [z]
                            (z x x))) x2)
                    ]
                x3))))))
  (is ((juxt last symbol-count closure-count)
       (walk/postwalk
         identity
         #_
         (fn [f]
           ('{(Closure {x0 Int, x Int} (fn [z] (z x x))) Pc1
              (Closure {x0 Int, x1 Pc1, x Pc1} (fn [z] (z x x))) Pc2
              (Closure {x0 Int, x1 Pc1, x2 Pc2, x Pc2} (fn [z] (z x x))) Pc3
              }
                       f f))

         (tc ?
             (let [x0 1]
               (let [
                     x1 ((fn [x]
                           (fn [z]
                             (z x x))) x0)
                     x2 ((fn [x]
                           (fn [z]
                             (z x x))) x1)
                     x3 ((fn [x]
                           (fn [z]
                             (z x x))) x2)
                     x4 ((fn [x]
                           (fn [z]
                             (z x x))) x3)
                     ]
                 x4))))))
  )

;from Kanellakis & Mitchell [POPL 1989]
; Example 3.5 - composing (lambda encoded) pairs using let
; Observation here:
; - exponential increase in type size!
;   - nested symbolic closure environments are increasing
;   - however, the closure's expression is constant (the return of P)
;     - (fn [z] (z x x))
; - note that the printed types are _doubly_ exponential in ML
;   - symbolic closure environments seem to give us a DAG for free
;     (eliminating one level of exponential?)
;   - eg., the type of (let [P (fn [x] (fn [z] (z x x)))] (P (fn [y] y)))
;     - in ML:
;       ((('a -> 'a) -> ('a -> 'a) -> 'b) -> 'b)
;     - symbolic closures:
;       (Closure {x (Closure {P (Closure {} (fn [x] (fn [z] (z x x))))}
;                            (fn [y] y))}
;                (fn [z] (z x x)))
;       - note that `x` is already abbreviated!
;         - like the following ML type:
;           ((W -> W -> 'b) -> 'b)
;           where W = ('a -> 'a)
; - seems clear that symbolic closure environments should rarely
;   be displayed to the user
(deftest kami89-3.5
  ;some tests for the above notes
  (is ((juxt last symbol-count)
        (tc ?
            (let [P (fn [x]
                      (fn [z]
                        (z x x)))]
              (P (fn [y] y))))))
  (is ((juxt last symbol-count)
        (tc ?
            (let [P (fn [x]
                      (fn [z]
                        (z x x)))]
              (P (P (fn [y] y)))))))
  (is ((juxt last symbol-count)
        (tc ?
            (let [P (fn [x]
                      (fn [z]
                        (z x x)))]
              (P (P (P (fn [y] y))))))))
  ; example 3.5 starts here
  (is ((juxt last symbol-count closure-count)
       (walk/postwalk
         identity
         #_(fn [f]
           ('{(fn [z] (z x x)) Pz} f f))
         (tc ?
             (let [P (fn [x]
                       (fn [z]
                         (z x x)))]
               (let [x1 (fn [x] (P x))]
                 (x1 1)))))))
  (is ((juxt last symbol-count closure-count)
       (walk/postwalk
         identity
         #_
         (fn [f]
           ('{(fn [z] (z x x)) Pz
              (Closure {x Int} Pz) Pc1} f f))
         (tc ?
             (let [P (fn [x]
                       (fn [z]
                         (z x x)))]
               (let [x1 (fn [x] (P x))]
                 (let [x2 (fn [y] (x1 (x1 y)))]
                   (x2 1))))))))
  (is ((juxt last symbol-count closure-count)
       (walk/postwalk
         identity
         #_
         (fn [f]
           ('{(fn [z] (z x x)) Pz
              (Closure {x Int} Pz) Pc1
              (Closure {x Pc1} Pz) Pc2} f f))
         (tc ?
             (let [P (fn [x]
                       (fn [z]
                         (z x x)))]
               (let [x1 (fn [x] (P x))]
                 (let [x2 (fn [y] (x1 (x1 y)))]
                   (let [x3 (fn [y] (x2 (x2 y)))]
                     (x3 1)))))))))
  (is ((juxt last symbol-count closure-count)
       (walk/postwalk
         identity
         #_
         (fn [f]
           ('{(fn [z] (z x x)) Pz
              (Closure {x Int} Pz) Pc1
              (Closure {x Pc1} Pz) Pc2
              (Closure {x Pc2} Pz) Pc3} f f))
         (tc ?
             (let [P (fn [x]
                       (fn [z]
                         (z x x)))]
               (let [x1 (fn [x] (P x))]
                 (let [x2 (fn [y] (x1 (x1 y)))]
                   (let [x3 (fn [y] (x2 (x2 y)))]
                     (let [x4 (fn [y] (x3 (x3 y)))]
                       (x4 1))))))))))
  (is ((juxt last symbol-count closure-count)
       (walk/postwalk
         (fn [f]
           ('{(fn [z] (z x x)) Pz
              (Closure {x Int} Pz) Pc1
              (Closure {x Pc1} Pz) Pc2
              (Closure {x Pc2} Pz) Pc3
              (Closure {x Pc3} Pz) Pc4
              } f f))
         (binding [*disable-elaboration* true] ;FIXME slow! unsure if elaborates
           (tc ?
               (let [P (fn [x]
                         (fn [z]
                           (z x x)))]
                 (let [x1 (fn [x] (P x))]
                   (let [x2 (fn [y] (x1 (x1 y)))]
                     (let [x3 (fn [y] (x2 (x2 y)))]
                       (let [x4 (fn [y] (x3 (x3 y)))]
                         (let [x5 (fn [y] (x4 (x4 y)))]
                           (x5 1))))))))))))
  (is ((juxt last symbol-count closure-count)
       (walk/postwalk
         (fn [f]
           ('{(fn [z] (z x x)) Pz
              (Closure {x Int} Pz) Pc1
              (Closure {x (Closure {x Pc1} Pz)} Pz) Pz2
              (Closure {x (Closure {x (Closure {x (Closure {x Pz2} Pz)} Pz)} Pz)} Pz) Pz3
              } f f))
         (binding [*disable-elaboration* true] ;FIXME slow! unsure if elaborates
           (tc ?
               (let [P (fn [x]
                         (fn [z]
                           (z x x)))]
                 (let [x1 (fn [x] (P x))]
                   (let [x2 (fn [y] (x1 (x1 y)))]
                     (let [x3 (fn [y] (x2 (x2 y)))]
                       (let [x4 (fn [y] (x3 (x3 y)))]
                         (let [x5 (fn [y] (x4 (x4 y)))]
                           (let [x6 (fn [y] (x5 (x5 y)))]
                             (x6 1)))))))))))))
)

; From "Characterization of typings in polymorphic type discipline" - Giannini and Rocca
; a term without higher-order polymorphic type
(deftest giannini-rocca-term
  (is (let [r (tc ? 
                  (let [I (fn [a] a)
                        K (fn [b]
                            (fn [c]
                              b))
                        D (fn [d]
                            (d d))]
                    ((fn [x]
                       (fn [y]
                         ((y (x I))
                          (x K))))
                     D)))]
        #_
        (binding [*print-level* nil
                  *print-length* nil]
          (pprint
            (walk/prewalk 
              (fn [f]
                  ('{(fn [a] a) I
                     (fn [b] (fn [c] b)) K
                     (fn [d] (d d)) D}
                         f
                         f))
              r)))
        r))
  (is (tc-err [Any :-> ?]
              (let [I (fn [a] a)
                    K (fn [b]
                        (fn [c]
                          b))
                    D (fn [d]
                        (d d))]
                ((fn [x]
                   (fn [y]
                     ((y (x I))
                      (x K))))
                 D))))
  (is (tc-err [[Any :-> Any] :-> ?]
              (let [I (fn [a] a)
                    K (fn [b]
                        (fn [c]
                          b))
                    D (fn [d]
                        (d d))]
                ((fn [x]
                   (fn [y]
                     ((y (x I))
                      (x K))))
                 D))))
  (is (= '[[Any :-> [Any :-> Nothing]] :-> Nothing]
         (tc [[? :-> [? :-> ?]] :-> ?]
             (let [I (fn [a] a)
                   K (fn [b]
                       (fn [c]
                         b))
                   D (fn [d]
                       (d d))]
               ((fn [x]
                  (fn [y]
                    ((y (x I))
                     (x K))))
                D)))))
  (is (= '[[Any :-> [Any :-> Int]] :-> Int]
         (tc [[? :-> [? :-> Int]] :-> ?]
             (let [I (fn [a] a)
                   K (fn [b]
                       (fn [c]
                         b))
                   D (fn [d]
                       (d d))]
               ((fn [x]
                  (fn [y]
                    ((y (x I))
                     (x K))))
                D)))))
  (is (= '(All [a] [[Any :-> [Any :-> a]] :-> a])
         (tc (All [a] [[? :-> [? :-> a]] :-> ?])
             (let [I (fn [a] a)
                   K (fn [b]
                       (fn [c]
                         b))
                   D (fn [d]
                       (d d))]
               ((fn [x]
                  (fn [y]
                    ((y (x I))
                     (x K))))
                D)))))
  (is (= '(All [a] [a :-> a])
         (tc (All [a] [a :-> a])
             (fn [i]
               ((let [I (fn [a] a)
                      K (fn [b]
                          (fn [c]
                            b))
                      D (fn [d]
                          (d d))]
                  ((fn [x]
                     (fn [y]
                       ((y (x I))
                        (x K))))
                   D))
                (fn [_]
                  (fn [_]
                    i)))))))
  (is (= '[[Any :-> [Any :-> Any]] :-> Any]
         (tc [[Any :-> [Any :-> Any]] :-> ?]
             (let [I (fn [a] a)
                   K (fn [b]
                       (fn [c]
                         b))
                   D (fn [d]
                       (d d))]
               ((fn [x]
                  (fn [y]
                    ((y (x I))
                     (x K))))
                D)))))
  (is (= '[[Any :-> [Any :-> Int]] :-> Int]
         (tc [[Any :-> [Any :-> Int]] :-> ?]
             (let [I (fn [a] a)
                   K (fn [b]
                       (fn [c]
                         b))
                   D (fn [d]
                       (d d))]
               ((fn [x]
                  (fn [y]
                    ((y (x I))
                     (x K))))
                D)))))
  (is (tc [[Any :-> [Any :-> Int]] :-> Int]
          (let [I (fn [a] a)
                K (fn [b]
                    (fn [c]
                      b))
                D (fn [d]
                    (d d))]
            ((fn [x]
               (fn [y]
                 ((y (x I))
                  (x K))))
             D))))
  (is (tc [[[Int :-> Int] :-> [Any :-> Int]] :-> Int]
          (let [I (fn [a] a)
                K (fn [b]
                    (fn [c]
                      b))
                D (fn [d]
                    (d d))]
            ((fn [x]
               (fn [y]
                 ((y (x I))
                  (x K))))
             D))))
  (is (tc [[[Int :-> Int] :-> [[Any :-> [Int :-> [Int :-> Int]]] :-> Int]] :-> Int]
          (let [I (fn [a] a)
                K (fn [b]
                    (fn [c]
                      b))
                D (fn [d]
                    (d d))]
            ((fn [x]
               (fn [y]
                 ((y (x I))
                  (x K))))
             D))))
  (is (= 'Int
         (tc ?
             (let [I (fn [a] a)
                   K (fn [b]
                       (fn [c]
                         b))
                   D (fn [d]
                       (d d))]
               (let [GR ((fn [x]
                           (fn [y]
                             ((y (x I))
                              (x K))))
                         D)]
                 (GR (fn [f]                  ;f  : [Int :-> Int]
                       (fn [g]                ;g  : [Any :-> [Int :-> [Int :-> Int]]]
                         (let [g1 (g 1)]      ;g1 : [Int :-> [Int :-> Int]]
                           (let [g2 (g1 1)]   ;g2 : [Int :-> Int]
                             (inc (g2 (inc (f 1))))))))))))))
  (is (= 'Int
         (tc ?
             (let [I (fn [a] a)
                   K (fn [b]
                       (fn [c]
                         b))
                   D (fn [d]
                       (d d))]
               (let [GR ((fn [x]
                           (fn [y]
                             ((y (x I))
                              (x K))))
                         D)]
                 (GR (fn [_]
                       (fn [_]
                         42))))))))
  )

(deftest polymorphic-upcast
  (is (= '(All [b a] [[a :-> b] a :-> b])
         (tc (All [b a] [[a :-> b] a :-> b])
             app)))
  (is (= '(All [a] [[a :-> a] a :-> a])
         (tc (All [a] [[a :-> a] a :-> a])
             app)))
  (is (tc-err (All [a1 b1] [[a1 :-> b1] b1 :-> a1])
              app))
  (is (tc-err (All [a1 b1] [[b1 :-> a1] b1 :-> b1])
              app))
  (is (= '(All [b] [[Int :-> b] Int :-> b])
         (tc (All [b] [[Int :-> b] Int :-> b])
             app)))
  (is (= '(All [a] [[a :-> Int] a :-> Int])
         (tc (All [a] [[a :-> Int] a :-> Int])
             app)))
  (is (tc-err (All [a] [[a :-> Int] Int :-> Int])
              app))
  (is (tc-err (All [a b] [[a :-> Int] a :-> b])
              app))
  (is (tc-err (All [a b] [[a :-> Int] a :-> b])
              app))
  (is (tc-err (All [a b] [a :-> b])
              (comp (fn [x] x)
                    (fn [x] x))))
)

(deftest overload-first-order
  (is (= 'Int
         (tc ? (+' 1 2))))
  (is (= 'Num
         (tc Num (+ 1 2))))
  (is (tc-err ? (+ (ann 1 Num)
                   (ann 2 Num))))
  (is (= 'Num
         (tc ? (+' (ann 1 Num)
                   (ann 2 Num)))))
  (is (= 'Num
         (tc ? (+' (ann 1 Num)
                   2))))
  (is (= 'Num
         (tc ? (+' 1
                   (ann 2 Num)))))
  (is (= 'Num
         (tc Num (+' 1
                     2))))
)

(deftest overload-higher-order
  (is (= 'Int
         (tc ? (app (fn [x] (+' 1 x)) 2))))
  (is (= 'Num
         (tc ? (app (fn [x] (+' 1 x)) (ann 2 Num)))))
  (is (= 'Int
         (tc ? (app inc' 1))))
  (is (= 'Num
         (tc ? (app inc' (ann 1 Num)))))
  (is (= '(All [a [b :lower Int]
                :constraints #{[(IFn [Int :-> Int]
                                     [Num :-> Num])
                                :<
                                [a :-> b]]}]
           [a :-> b])
         (tc ? (app0 inc'))))
  (is (= 'Int
         (tc ? (app2 +' 1 2))))
  (is (= 'Num
         (tc ? (app2 +' 1 (ann 2 Num)))))
)

(deftest elaboration-test
  (is (= 1 (tc+elab ? 1)))
  (is (= 'inc (tc+elab ? inc)))
  (is (= '(ann (fn [a] a) (IFn))
         (tc+elab ? (fn [a] a))))
  (is (= '((ann (fn [a] a)
                [Int :-> Int])
           1)
         (tc+elab ? (let [a 1] a))))
  (is (= '[1 ((ann (fn [a] a)
                   [Int :-> Int])
              1)]
         (tc+elab ? [1 (let [a 1] a)])))
  (is (= '[1 ((ann (fn [a] ((ann (fn [b] a)
                                 [Int :-> Int])
                            2))
                   [Int :-> Int])
              1)]
         (tc+elab ? [1 (let [a 1 b 2] a)])))
  (is (= '(ann ((ann (fn [a] a)
                     [Int :-> Int])
                1)
               Int)
         (tc+elab ? (ann (let [a 1] a) Int))))
  (is (= '(ann (fn [a] ((ann (fn [a] a)
                             [Int :-> Int]) 1))
               [Int :-> Int])
         (tc+elab ? (ann (fn [a] (let [a 1] a))
                         [Int :-> Int]))))
  (is (= '((ann (fn [f] [(f 1) (f "a")])
                [(IFn [Int :-> Int]
                      [Str :-> Str])
                 :-> (Seq (U Int Str))])
           (ann (fn [x] x)
                (IFn [Int :-> Int]
                     [Str :-> Str])))
         (tc+elab ? (let [f (fn [x] x)]
                      [(f 1) (f "a")]))))
  (is (= '((ann (fn [f] [((f 1) 2) ((f "a") "b")])
                [(IFn [Int :-> [Int :-> Int]]
                      [Str :-> [Str :-> Str]])
                 :-> (Seq (U Int Str))])
           (ann (fn [x]
                  (ann (fn [y] x)
                       (TypeCase (EnclosingFn 0)
                         [Int :-> Any] [Int :-> Int]
                         [Str :-> Any] [Str :-> Str])))
                (IFn [Int :-> [Int :-> Int]]
                     [Str :-> [Str :-> Str]])))
         (tc+elab ? (let [f (fn [x] (fn [y] x))]
                      [((f 1) 2) ((f "a") "b")]))))
  (is (= '(ann (fn [a] ((ann (fn [a] a)
                             [Int :-> Int])
                        1))
               (IFn [Int :-> Int]
                    [Str :-> Int]))
         (tc+elab ? (ann (fn [a] (let [a 1] a))
                         (IFn [Int :-> Int]
                              [Str :-> Int])))))
  (is (= '(ann (fn [a]
                 ((ann (fn [a]
                         ((ann (fn [b] a)
                               [Int :-> Int])
                          2))
                       [Int :-> Int])
                  1))
               (IFn [Int :-> Int]
                    [Str :-> Int]))
         (tc+elab ? (ann (fn [a] (let [a 1 b 2] a))
                         (IFn [Int :-> Int]
                              [Str :-> Int])))))
  ; smallest case of recursive function type, with elaboration
  (is (tc+elab ? (let [f (fn [f] f)]
                   (f f))))
  ; nested recursive function types (but references are not nested)
  (is (tc+elab ? (let [f (fn [f] f)
                       g (fn [g] g)]
                   ((f f) (g g)))))
  ; interestingly nested recursive types (like `(Rec [x] [:-> (Rec [y] [x -> y])])`)
  (is (tc+elab ? (let [f (fn [f]
                           (fn [g]
                             (f g)))]
                   (f f))))
  ;FIXME elaboration does not type check
  (is (tc-exp ? (let [f (fn [f]
                          (fn [g]
                            (f g)))]
                  ((f f) f))))
  ; the following elaborations exhibit exponential growth in the annotations
  (is ((juxt pprint' node-count)
        (tc+elab ? (let [call (fn [f]
                                (fn [g]
                                  (f g)))]
                     (call call)))))
  (is ((juxt pprint' node-count)
       (tc+elab ? (let [call (fn [f]
                               (fn [g]
                                 (f g)))]
                    ((call call) call)))))
  (is (node-count 
        (tc+elab ? (let [f (fn [f]
                             (fn [g]
                               (f g)))]
                     (((f f) f) f)))))
  (is (node-count
        ;slow!
        (tc+elab ? (let [f (fn [f]
                             (fn [g]
                               (f g)))]
                     ((((f f) f) f) f)))))
  (is (node-count
        ;FIXME too slow to elaborate
        (tc-exp ? (let [f (fn [f]
                            (fn [g]
                              (f g)))]
                    (((((f f) f) f) f) f)))))
  (is (node-count
        ;FIXME too slow to elaborate
        (tc-exp ? (let [f (fn [f]
                            (fn [g]
                              (f g)))]
                    ((((((f f) f) f) f) f) f)))))
  ;each of the following elaborations have identical annotation
  ; for `f`: (Rec [r] [r :-> r])
  (is (node-count
        (tc+elab ? (let [f (fn [g] g)]
                     (f f)))))
  (is (node-count
        (tc+elab ? (let [f (fn [g] g)]
                     ((f f) f)))))
  (is (node-count
        (tc+elab ? (let [f (fn [g] g)]
                     (((f f) f) f)))))
  (is (node-count
        (tc+elab ? (let [f (fn [g] g)]
                     ((((f f) f) f) f)))))
  (is (node-count
        (tc+elab ? (let [f (fn [f] f)]
                     (((((f f) f) f) f) f)))))
  ; recursive function type intersected with [Int -> Int]
  ; Note that [Int -> Int] is part of the recursive type. Is this correct?
  (is (tc-exp ?
              (let [f (fn [x] x)]
                ((f f) 1))))
  ; FIXME does this type check in the internal language?
  (is
       (tc-exp ?
           ((let [pair (fn [f] ; flipped f and x
                         (fn [x]
                           ((f x) x)))]
              (let [f1 (fn [x] (pair x))]
                (let [f2 (fn [x] (f1 (f1 x)))]
                  (let [f3 (fn [x] (f2 (f2 x)))]
                    (let [f4 (fn [x] (f3 (f3 x)))]
                      (fn [z] ((f4 (fn [x] x)) z)))))))
            ;this is apparently given a recursive type, (Rec [a] [a -> ?]).
            (fn [x]
              (fn [y]
                (fn [x']
                  (fn [y']
                    (fn [x]
                      (fn [y]
                        (fn [x']
                          (fn [y']
                            ;return 1
                            1)))))))))))
;TODO
#_
  (is (= '((ann map (PApp (All [a b] [[a :-> b] (Seq a) :-> (Seq b)]) Int Int)) inc [1 2 3])
         (tc-exp ? (map inc [1 2 3]))))
#_
  (is (= '?
         (tc-exp ? (let [; f is exercised with a polymorphic function
                         ; and a symbolic closure. in the former, an instantiation
                         ; is needed in (f x y), in the latter it is not.
                         ; therefore, type instantiation must be nested in a TypeCase,
                         ; and so an `inst` term is not sufficient.
                         a (fn [f x y] (f x y))
                         mp-id (fn [x y] y)]
                     [(a map inc [1 2 3])
                      (a mp-id inc [1 2 3])]))))
  )

; sometimes a function is nested in such a way that makes the
; an internal closure unreachable. this seems bad since we need
; to add unannotated functions to the internal language.
; Consider: always checking an unannotated function at Bot -> ? upon discovery
; in the external language. That way, all functions are annotated in internal lang.
; Once I added this, the checking limit had to be 10x higher for the let-polymorphism
; stress tests. Probably because it exponentially increased the number of times closures had to be
; checked, wrt to their nested depth. (OTOH, in the same commit I let subtyping participate
; in decreasing the checking limit (bug fix), so that might have also increased the limit needed).
;
; The lambda-encoding for let's now seems very expensive:
; eg. (let [a 1 b 2 c 3] ...)
;     will first check
;      a : Nothing                           |- (let [b 2 c 3] ...)
;      a : Nothing, b : Nothing              |- (let [c 3] ...)
;      a : Nothing, b : Nothing, c : Nothing |- (let [] ...)
;     before checking `1`, then checks
;      a : Int                           |- (let [b 2 c 3] ...)
;      a : Int, b : Nothing              |- (let [c 3] ...)
;      a : Int, b : Nothing, c : Nothing |- (let [] ...)
;     before checking `2`, then checks,
;      a : Int, b : Int              |- (let [c 3] ...)
;      a : Int, b : Int, c : Nothing |- (let [] ...)
;     before checking `3`, then checks,
;      a : Int, b : Int, c : Int |- (let [] ...)
;
; Looks exponential in the number of nested let's.
(deftest unreachable-closure-test
  ;unexercised symbolic closures
  ;TODO should be: (ann (fn [a] a) [Nothing :-> Nothing])
  (is (= '(ann (fn [a] a) (IFn))
         (tc+elab ? (fn [a] a))))
  ; unreachable unannotated function in elaboration
  ;TODO
  ;should be: (ann (fn [a]
  ;                (ann (fn [b] a)
  ;                     [Nothing :-> Nothing]))
  ;                [Nothing :-> [Nothing :-> Nothing]])
  (is (= '(ann (fn [a] (fn [b] a))
               (IFn))
         (tc+elab ? (fn [a] (fn [b] a))))))

;http://web.cs.ucla.edu/~palsberg/tba/papers/banerjee-icfp97.pdf
; A modular, polyvariant and type-based closure analysis - Banerjee
(deftest banerjee-test
  (is (= '(Closure {f (Closure {} (fn [v] v)), x Int} (fn [u] u))
         (tc ?
             ((fn [f] ((fn [x]
                         (f (fn [u] u)))
                       (f 0)))
              (fn [v] v))))))


(comment
  ;Error messages
  ;Unicode Arrows: ↘ ⟶ ⟵ ↙  
  ;
  ; The return type of `app` is Int, but the surrounding expression expected (Seq Int).
  ;
  ; 5|   (app id 1)
  ;      ^^^^^^^^^^
  ;
  ; From the type of `app`, 
  ; The result of that application flows to the return of `app` (3 -> 4), but
  ; the result type did not agree with the expected type of the surrounding
  ; context.
  ;
  ; In: (app id ; [2 -> 3]
  ;          1  ; 1
  ;          )  ;=> 4
  ; # Function
  ;         app : (All [a b] [[a -> b] a -> b])
  ;         app :            [[2 -> 3] 1 -> 4]
  ;
  ; # Arguments
  ;                         2    3
  ;         id  : (All [a] [a -> a])
  ;
  ;               1
  ;         1   : Int
  ;
  ; # Expected type
  ;
  ;               4
  ; _exp  =     : (Seq Int)
  ;
  ; # Data flow diagram
  ;                            +    -  -    +
  ;         app : (All [a b] [[a -> b] a -> b])
  ;
  ;         +    -  -    +
  ; app : [[2 -> 5] 1 -> 6]
  ; id  : [3 -> 4]
  ;
  ;      [[2 -> 5] 1 -> 6] [3 -> 4]
  ;                        
  ;                1 : Int         Int <: a <: Any
  ;         /-----/
  ;        2 : a[Int/a]
  ;         \--------------\   
  ;                         3 : a[Int/a]
  ;                          \--\
  ;                              4 : Int 
  ;              /--------------/   
  ;             5 : Int            Int <: b <: Any
  ;              \-----\
  ;                     6 : b[Int/b]
  ;
  (is (tc-err (Seq Int) (app id 1)))

  ; The return type of this expression is Int, but the surrounding expression expected (Seq Int).
  ;
  ; 5|   ((comp (fn [x] x)
  ; 6|          (fn [x] x))
  ; 7|    1)
  ;      ^^^^^^^^^^^^^^^^^^
  ;
  ;  _fn   : (All [a b c :constraints #{[(Closure {} (fn [x] x)) :< [a :-> b]]
  ;                                     [(Closure {} (fn [x] x)) :< [b :-> c]]}]
  ;            [a :-> c])
  ;  _arg1 : Int
  ;
  ; # Data flow
  ;
  ; 5|   ((comp (fn [x] x)
  ; 6|          (fn [x] x))
  ; 7|    42)
  ;
  ;  (comp ...) : [1 -> 6]
  ;  (fn [x] x) : [2 -> 3]
  ;  (fn [x] x) : [4 -> 5]
  ;
  ;    [1 -> 6] [2 -> 3] [4 -> 5]
  ;
  ;     1 : Int
  ;      \------\
  ;              2 : Int
  ;               \--\
  ;                   3 : Int
  ;                    \-\
  ;                       4 : Int
  ;                        \--\
  ;                            5 : Int
  ;           /---------------/
  ;          6 : Int

  (is (tc-err (Seq Int)
              ((comp (fn [x] x)
                     (fn [x] x))
               1)))
  ; 2| (f f)      : [1 -> 4]
  ; 1| (fn [x] x) : [2 -> 3]
  ;
  ;    [1 -> 4] [2 -> 3]
  ;
  ;     1 : Int
  ;      \------\
  ;              2 : Int
  ;               \--\
  ;                   3 : Int
  ;           /------/
  ;          4 : Int

  (is (= 'Int
         (tc ?
             (let [f (fn [x] x)]
               ((f f) 42)))))
  (is (tc ?
          (let [f (fn [x] x)]
            (f f))))
  ; 1| (mapT inc) : [[1 2 -> 3] -> [4 5 -> 6]]
  ; 1|       inc  : [7 -> 8]
  ;
  ;      + +    -      - -    +    +    -
  ;      r b    r      r a    r    a    b
  ;    [[1 2 -> 3] -> [4 5 -> 6]] [7 -> 8]
  ;
  ;      1 : r1                            r1 <: r <: Any
  ;      \ 2 : Int                        Int <: b <: Any
  ;       \-\--\
  ;             3 : r1                     r1 <: r <: Any
  ;
  ;                    4 : r1
  ;                    \ 5 : Int          Int <: a <: Any
  ;                     \-\--\
  ;                           6 : r1       r1 <: r <: Any
  ;
  ;                                7 : Int
  ;                                 \--\
  ;                                     8 : Int   Int <: b <: Any
  ; 
  ;
  ; r = r1
  ; a = Int
  ; b = Int
  (is (tc (All [r1] [[r1 Int :-> r1] :-> [r1 Int :-> r1]])
          (mapT inc)))

  ; Goal: generate substitution for LHS
  ; This says, for every instantiation of the LHS, there exists
  ; a substitution for the right hand side that makes it a supertype.
  ; (All [a] [a :-> a]) <: (All [b] [b :-> b])
  ; [Nothing -> Nothing] <: [Any -> Any]
  ;
  ; 1| id : [1 -> 2]
  ;
  ;    [1 -> 2]
  ;     1 : b                            b <: a <: Any
  ;          2 : b                            b <: a <: Any
  ;
  (is (= '(All [b] [b :-> b])
         (tc (All [b] [b :-> b])
             id)))

  ; (All [a] [a :-> a]) <: [Int -> Int]
  ;
  ; 1| id : [1 -> 2]
  ;
  ;    [1 -> 2]
  ;     1 : Int                            Int <: a <: Any
  ;          2 : Int                       Int <: a <: Any
  (is (= '[Int :-> Int]
         (tc [Int :-> Int]
             id)))

  ;  (mapT (fn [x] x)) : (All [a b r :constraints #{[(Closure {} (fn [x] x)) :< [a :-> b]]}]
  ;                        [[r b :-> r] :-> [r a :-> r]])
  ;
  ; (All [a b r :constraints #{[(Closure {} (fn [x] x)) :< [a :-> b]]}]
  ;   [[r b :-> r] :-> [r a :-> r]])
  ; <:
  ; (All [r1]
  ;   [[r1 ? :-> r1] :-> [r1 Int :-> r1]])
  ;
  ;  arg1: [r1 ? :-> r1] <: [r b :-> r]
  ;   => b <: ?
  ;   => r <: r1
  ;   => r1 <: r
  ;  ret: [r a :-> r] <: [r1 Int :-> r1]
  ;   => Int <: a
  ;   => r1 <: r
  ;   => r <: r1
  ;  constraint1: (Closure {} (fn [x] x)) :< [a :-> b]
  ;
  ; 1| (mapT (fn [x] x)) : [[1 2 -> 3] -> [4 5 -> 6]]
  ; 1|       (fn [x] x)  : [7 -> 8]
  ;
  ;      + +    -      - -    +    +    -
  ;      r b    r      r a    r    a    b
  ;    [[1 2 -> 3] -> [4 5 -> 6]] [7 -> 8]
  ;
  ;      1 : r1                            r1 <: r <: Any
  ;      \ 2 : ?                          Bot <: b <: Any
  ;       \-\--\
  ;             3 : r1                    
  ;
  ;                    4 : r1
  ;                    \ 5 : Int          Int <: a <: Any
  ;                     \-\--\
  ;                           6 : r1       
  ;
  ;                                7 : Int
  ;                                 \--\
  ;                                     8 : Int   Int <: b <: Any
  ; 
  ;      1 : r1                            
  ;      \ 2 : Int                        
  ;       \-\--\
  ;             3 : r1                     
  ;
  ; r = r1
  ; a = Int
  ; b = Int
  (is (tc (All [r1] [[r1 ? :-> r1] :-> [r1 Int :-> r1]])
          (mapT (fn [x] x))))

  ; 1| (reduce ...) : [[1 2 :-> 3] 4 (Seq 5) :-> 6]
  ; 2| 0            : Int
  ; 3| [1 2 3]      : (Seq Int)
  ;
  ;    [[1 2 :-> 3] 4 (Seq 5) :-> 6]
  ;
  ;                 4 : Int
  ;       /--------/       5 : Int
  ;      /  /-------------/
  ;      1 : Int
  ;      \ 2 : Int
  ;       \-\---\
  ;              3 : Int
  ;               \--------------\
  ;                               6 : Int
  (is (= 'Int
         (tc ?
             (reduce (fn [x y] x)
                     0
                     [1 2 3]))))

  ; 1| (reduce ...)       : [[1 2 :-> 3] 4 (Seq 5) :-> 6]
  ; 1| (fn [x y] (+ x y)) : [7 8 -> 9]
  ; 2| 0                  : Int
  ; 3| [1.0 2 3]          : (Seq Num)
  ;      
  ;      + +     -  -      -     +   + +    -
  ;      a c     a  a      c     a   a c    a
  ;    [[1 2 :-> 3] 4 (Seq 5) -> 6] [7 8 -> 9]
  ;
  ;                 4 : Int                         Int <: a <: Any
  ;       /--------/       5 : Num                  Num <: c <: Any
  ;      /                /
  ;      1 : Int         /                        
  ;      |  /-----------/
  ;      \ 2 : Num
  ;       \-\-----------------------\
  ;          \                       7 : Int
  ;           \                       \-------
  ;            \----------------------\       \
  ;                                    8 : Num \
  ;                                     \--\ /-/
  ;                                         9 : Num
  ;               /------------------------/
  ;              3 : Num                            Num <: a <: Any
  ;       /-----/
  ;      1 : Num
  ;       \-------------------------\
  ;                                  7 : Num
  ;                                   \----\ 
  ;                                         9 : Num 
  ;               /------------------------/
  ;              3 : Num 
  ;               \-------------\
  ;                              6 : Num 
  (is (= 'Num
         (tc ?
             (reduce (fn [x y] (+ x y))
                     0
                     [1.0 2 3]))))

  ; 1| appid : [[1 -> 2] 3 -> 4]
  ; 2| id    : [5 -> 6]
  ; 3| 0     : Int
  ;
  ;    [[1 -> 2] 3 -> 4] [5 -> 6]
  ;
  ;              3 : Int
  ;       /-----/
  ;      1 : Int
  ;       \--------------\
  ;                       5 : Int
  ;                        \--\
  ;                            6 : Int
  ;            /--------------/
  ;           2 : Int
  ;            \-----\
  ;                   4 : Int
  (is (= 'Int
         (tc ?
             (appid id 0))))

(tc ? 1)
Int

(tc [Int :-> Int] (fn [x] x))
[Int :-> Int]

(tc ? (fn [x] x))
(Closure {} (fn [x] x))

(tc ? ((fn [x] x) 1))
Int

(tc ? (map (fn [x] x) [1 2 3]))
(Seq Int)

(tc ? (map (comp (fn [x] x)
                 (fn [y] y))
           [1 2 3]))
(Seq Int)

             (let [I (fn [a] a)
                   K (fn [b]
                       (fn [c]
                         b))
                   D (fn [d]
                       (d d))]
               (let [GR ((fn [x]
                           (fn [y]
                             ((y (x I))
                              (x K))))
                         D)]
(GR
 (fn [_]
   (fn [_]
     42)))))
)

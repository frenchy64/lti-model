(ns lti-model.core-test
  (:require [clojure.test :refer :all]
            [clojure.pprint :refer [pprint]]
            [lti-model.core :refer :all :as lti]))

(defmacro tc [P e]
  `(unparse-type (check-form (parse-type '~P) {} '~e)))

(defmacro handle-type-error [f & body]
  `(try (do ~@body)
        (catch clojure.lang.ExceptionInfo e# 
          (if (::lti/type-error (ex-data e#))
            (~f e#)
            (throw e#)))))


(defmacro tc-err [P e]
  `(handle-type-error (fn [^Exception e#]
                        (println (.getMessage e#))
                        true)
     (do (tc ~P ~e)
         false)))

; dummy to evaluate code in this ns
(defmacro ann [e t] e)

(deftest check-test
  (is (= 'Int
         (tc Int 1)))
  (is (= 'Int
         (tc ? 1)))
  (is (= '(Seq Int)
         (tc ? [1 2])))
  (is (tc-err Int [1 2]))
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
  (is
    (= '[[[Int :-> Int] :-> Int]
         :-> Int]
       (tc [[[Int :-> Int] :-> Int]
            :-> Int]
           (let [pair (fn [f]
                        (fn [x]
                          ((f x) x)))]
             (let [f1 (fn [x] (pair x))]
               (let [f2 (fn [x] (f1 (f1 x)))]
                 (fn [z] ((f2 (fn [x] x)) z))))))))
  (is (tc-err ?
              (let [f (ann id (All [a b] [a :-> b]))]
                (f 1))))
  ; out of scope?
  #_
  (is (tc ?
          (let [f (ann id (All [a b] [(I a b) :-> (I a b)]))]
            (f 1))))
  )

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
  (is (tc-err (All [r1] [[r1 (Seq Int) :-> r1] :-> [r1 Int :-> r1]])
              (mapT inc)))
  (is (= '(All [r1] [[r1 Num :-> r1] :-> [r1 Int :-> r1]])
         (tc (All [r1] [[r1 Num :-> r1] :-> [r1 Int :-> r1]])
             (mapT (fn [x] x)))))
  (is (= '(All [r1] [[r1 Any :-> r1] :-> [r1 Int :-> r1]])
         (tc (All [r1] [[r1 ? :-> r1] :-> [r1 Int :-> r1]])
             (mapT (fn [x] x)))))
  ;FIXME
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
  (is (tc ?
            (let [Y (fn [f]
                      ((fn [g] (fn [x] (f (g g) x)))
                       (fn [g] (fn [x] (f (g g) x)))))]
              (let [compute (Y (ann (fn [f x] (+ 1 (f x)))
                                    [[Int :-> Int] Int :-> Int]))]
                (compute 1)))))
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
)

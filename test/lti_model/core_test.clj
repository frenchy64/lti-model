(ns lti-model.core-test
  (:require [clojure.test :refer :all]
            [lti-model.core :refer :all :as lti]))

(defmacro tc [P e]
  `(unparse-type (check (parse-type '~P) {} '~e)))

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
  (is (= '[Nothing :-> Int]
         (tc [? :-> Int] (fn [x] 1))))
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
  ; (All [a b c :constraints [[Closure#1 <: [b :-> c]]
  ;                           [Closure#2 <: [a :-> b]]]]
  ;   [a :-> c])
  (is (tc ?
          (comp (fn [x] x)
                (fn [x] x))))
  (is (= '[Int :-> Int]
         (tc [Int :-> Int]
             (comp (fn [x] x)
                   (fn [x] x)))))
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
  ; unsure why this errors
  (is (= '[Nothing :-> Int]
         (tc [? :-> Int]
             (comp (fn [x] x)
                   (fn [x] x)))))
  ; Transducers
  (is (= '(All [[a :upper Int] [b :lower Int] r]
            [[r b :-> r] :-> [r a :-> r]])
         (tc ?
             (mapT inc))))
  )

(deftest id-cast-test
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
            (f 1))))
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
  (is (tc ?
          (mapT (fn [x] x))))
  (is (= '(All [r1] [[r1 Int :-> r1] :-> [r1 Int :-> r1]])
         (tc (All [r1] [[r1 Int :-> r1] :-> [r1 Int :-> r1]])
             (mapT (fn [x] x)))))
  (is (= '(All [r1] [[r1 Any :-> r1] :-> [r1 Int :-> r1]])
         (tc (All [r1] [[r1 ? :-> r1] :-> [r1 Int :-> r1]])
             (mapT (fn [x] x)))))
  #_
  (is (tc ?
          (intoT []
                 (mapT (fn [x] x))
                 [1 2 3])))
  )

; let Y = fun f -> (fun g -> fun x -> f (g g) x)
;                  (fun g -> fun x -> f (g g) x) in
; let compute = Y (fun f -> fun x -> plus 1 (f x)) in
; compute 1
#_
(deftest ycomb
  (is (tc ?
          (let [Y (fn [f]
                    ((fn [g] (fn [x] (f (g g) x)))
                     (fn [g] (fn [x] (f (g g) x)))))]
            (let [compute (Y (fn [f x] (+ 1 (f x))))]
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
  ;FIXME
  (is (= 'Int
         (tc ? (app2 +' 1 2))))
  (is (= 'Num
         (tc ? (app2 +' 1 (ann 2 Num)))))
)

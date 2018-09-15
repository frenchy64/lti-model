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
  (is (tc Int 1))
  (is (tc ? 1))
  (is (tc ? [1 2]))
  (is (tc-err Int [1 2]))
  (is (tc Int [1 2]))
  (is (tc ? (fn [x] [1 2])))
  (is (tc [? :-> Int] (fn [x] 1)))
  (is (tc [Int :-> Int] (fn [x] x)))
  (is (tc-err [Int :-> Nothing] (fn [x] x)))
  (is (tc [? :-> Int] (fn [x] [1 2])))
  (is (tc [? :-> (Seq Int)] (fn [x] [1 2])))
  (is (tc [Int :-> Int] (fn [x] [1 2])))
  (is (tc ? ((fn [x] [1 2]) 1)))
  (is (tc ? (+ 1 2)))
  (is (tc-err ? (+ (fn [x] 1) 2)))
  (is (tc-err Int ((fn [x] [x]) 2)))
  (is (tc Int ((fn [x] x) 2)))
  ; ?, {} |-w app => (All [a b] [[a :-> b] a :-> b])
  ; ?, {} |-w (fn [x] [1 2]) => (Closure {} (fn [x] [1 2]))
  ; ?, {} |-w 1 => Int
  ; {} |-{a,b} (Closure {} (fn [x] [1 2])) <: [a :-> b] => 
  ; {} |-{a,b} Int <: a => {Int <: a <: Any}
  ; {} |-{a,b} b <: Any => {Nothing <: b <: Any}
  ; -------------------------------------
  ; ?, {} |-w (app (fn [x] [1 2]) 1) => ?
  (is (tc ? (app (fn [x] [1 2]) 1)))
  (is (tc ? (id 1)))
  (is (tc Int (id 1)))
  (is (tc-err (Seq Int) (id 1)))
  (is (tc ? (app id 1)))
  (is (tc Int (app id 1)))
  (is (tc-err (Seq Int) (app id 1)))
  (is (tc ? (app (fn [x] x) 1)))
  (is (tc Int (app (fn [x] x) 1)))
  (is (tc-err (Seq Int) (app (fn [x] x) 1)))
  ; FIXME fishy
  (is (tc ? (comp inc inc)))
  (is (tc [Int :-> Int] (comp inc inc)))
  ; (All [a b c :constraints [[Closure#1 <: [b :-> c]]
  ;                           [Closure#2 <: [a :-> b]]]]
  ;   [a :-> c])
  (is (tc ?
          (comp (fn [x] x)
                (fn [x] x))))
  (is (tc ?
          ((comp (fn [x] x)
                 (fn [x] x))
           1)))
  (is (tc Int
          ((comp (fn [x] x)
                 (fn [x] x))
           1)))
  (is (tc-err (Seq Int)
              ((comp (fn [x] x)
                     (fn [x] x))
               1)))
  ; [Int :-> Int]
  (is (tc [? :-> ?]
          (comp (fn [x] x)
                (fn [x] x))))
  (is (tc [Int :-> Int]
          (comp (fn [x] x)
                (fn [x] x))))
  )

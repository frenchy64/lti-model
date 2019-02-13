(ns lti-model.internal-test
  (:require [clojure.test :refer :all]
            [clojure.pprint :refer [pprint]]
            [clojure.walk :as walk]
            [lti-model.util :as u]
            [lti-model.internal :refer :all :as lti]))

(defmacro tc [e]
  `(unparse-type (u/ret-t (check-form {} '~e))))

(defmacro tc-err [e]
  `(u/handle-type-error (fn [^Exception e#]
                          (println (.getMessage e#))
                          true)
     (do (tc ~e)
         false)))

(defmacro sub? [s t]
  `(subtype? (parse-type '~s)
             (parse-type '~t)))

(defmacro evl [e]
  `(eval-form '~e))

(deftest tc-basics-test
  (is (= 'Int (tc 1)))
  (is (= 'Str (tc "a")))
  (is (= '(Seq Str) (tc ["a"])))
  (is (= '(Seq (U Int Str)) (tc ["a" 1])))
  (is (= '(Seq (U Int Str)) (tc [1 "a"])))
  (is (= '(Seq Int) (tc [1 2])))
  (is (= 'Int (tc (ann 1 Int))))
  (is (= 'Str (tc (ann "a" Str))))
  (is (tc-err (ann 1 Str)))
  (is (tc-err (ann "a" Int)))
  (is (tc-err (ann ["a" 1] Str)))
  ;ann
  (is (= 'Int (tc (ann 1 Int))))
  (is (= '[:-> Any] (tc (ann (ann (fn [] "a") [:-> Str])
                             [:-> Any]))))
  (is (tc-err (ann (ann (fn [] "a")
                        [:-> Str])
                   [:-> Nothing])))
  (is (tc (ann (fn [f] (f f))
               (Rec [r] [r :-> r]))))
  (is (= '[Nothing :-> Any]
         (tc (ann (ann (fn [f] (f f))
                       (Rec [r] [r :-> r]))
                  [Nothing :-> Any]))))
  (is (= 'Num (tc (ann 1 Num))))
  ; infinite Rec type
  (is (tc-err (ann 1 (Rec [r] r))))
  ;app
  (is (= 'Int (tc (inc 1))))
  (is (= 'Int (tc (+ 1 1))))
  (is (= 'Num (tc (+' (ann 1 Num) 1))))
  (is (tc-err (inc "a")))
  ;fn
  (is (tc (ann (fn [] "a") [:-> Str])))
  (is (tc-err (ann (fn [] "a") [:-> Int])))
  (is (tc-err (ann (fn [] ["a" 1]) [:-> Int])))
  (is (tc (ann (fn [x] x)
               (IFn [Int :-> Int]
                    [Str :-> Str]))))
  (is (tc-err (ann (fn [x] x)
                   (IFn [Int :-> Int]
                        [Str :-> Int]))))
  ; poly app
  (is (tc-err (map (ann (fn [e] e) [Int :-> Int])
                   [1 2])))
  (is (tc ((ann map
                (PApp (All [a b] [[a :-> b] (Seq a) :-> (Seq b)])
                      Int
                      Int))
           (ann (fn [e] e) [Int :-> Int])
           [1 2])))
  ; switched 'All' arguments
  (is (tc-err ((ann map
                    (PApp (All [b a] [[a :-> b] (Seq a) :-> (Seq b)])
                          Int
                          Int))
               (ann (fn [e] e) [Int :-> Int])
               [1 2])))
  ; EnclosingFnCase
  (is (tc (ann (fn [x]
                 (ann (fn [y] x)
                      (EnclosingFnCase 0
                        [Int :-> [Int :-> Int]] [Int :-> Int]
                        [Str :-> [Str :-> Str]] [Str :-> Str])))
               (IFn [Int :-> [Int :-> Int]]
                    [Str :-> [Str :-> Str]]))))
  )

(deftest eval-test
  (is (= 1 (evl 1)))
  (is (= 2 (evl (inc 1))))
  (is (= 2 (evl (+ 1 1))))
  (is (= 1 (evl (app id 1))))
  (is (= 1 (evl ((ann (fn [x] x)
                      [Any :-> Any])
                 1))))
  ;closures
  (is (= 1 (evl (((ann (fn [a]
                         (ann (fn [x] a)
                              [Any :-> Any]))
                       [Any :-> Any])
                  1)
                 2))))
  )

(deftest subtype-test
  (is (not (sub? Any Nothing)))
  (is (sub? Nothing Any))
  (is (sub? [:-> Nothing] [:-> Any]))
  (is (not (sub? [:-> Any] [:-> Nothing])))
  (is (sub? (Rec [a] [a :-> a])
            [(Rec [b] [b :-> b]) :-> (Rec [c] [c :-> c])]))
  (is (not (sub? (Rec [a] [a :-> a])
                 [Int :-> Int])))
  (is (u/throws-type-error? (sub? (Rec [a] a) (Rec [b] b))))
  (is (u/throws-type-error? (sub? Int (Rec [b] b))))
  (is (u/throws-type-error? (sub? (Rec [b] b) Int)))
  )

(deftest reserved-symbol-test
  (is (thrown? AssertionError (tc (ann (fn [fn] fn)
                                       [Any :-> Any]))))
  (is (thrown? AssertionError (tc (ann (fn [fn*] fn*)
                                       [Any :-> Any]))))
  (is (thrown? AssertionError (tc (ann (fn [ann] ann)
                                       [Any :-> Any])))))

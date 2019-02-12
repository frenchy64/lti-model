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
  ;TODO (is (= 'Num (tc (ann 1 Num))))
  ;app
  (is (= 'Int (tc (inc 1))))
  (is (= 'Int (tc (+ 1 1))))
  ;TODO
  ;(is (= 'Int (tc (+' (ann 1 Num) 1))))
  (is (tc-err (inc "a")))
  ;fn
  (is (tc (ann (fn [] "a") [:-> Str])))
  (is (tc-err (ann (fn [] "a") [:-> Int])))
  (is (tc-err (ann (fn [] ["a" 1]) [:-> Int])))
  ; poly app
  #_;TODO
  (is (tc-err (map (ann (fn [e] e) [Int :-> Int])
                   [1 2])))
  )

(deftest subtype-test
  (is (not (sub? Any Nothing)))
  (is (sub? Nothing Any))
  (is (sub? [:-> Nothing] [:-> Any]))
  (is (not (sub? [:-> Any] [:-> Nothing])))
  )

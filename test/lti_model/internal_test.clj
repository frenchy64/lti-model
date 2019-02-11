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

(deftest tc-basics
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
  ;app
  (is (= 'Int (tc (inc 1))))
  (is (tc-err (inc "a")))
  ;fn
  (is (tc (ann (fn [] "a") [:-> Str])))
  (is (tc-err (ann (fn [] "a") [:-> Int])))
  (is (tc-err (ann (fn [] ["a" 1]) [:-> Int])))
  )

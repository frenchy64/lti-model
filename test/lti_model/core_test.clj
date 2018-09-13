(ns lti-model.core-test
  (:require [clojure.test :refer :all]
            [lti-model.core :refer :all :as lti]))

(defmacro tc [P e]
  `(check (parse-type '~P) {} '~e))

(defmacro handle-type-error [v & body]
  `(try (do ~@body)
        (catch ExceptionInfo e# 
          (if (::lti/type-error (ex-data e#))
            v
            (throw e#)))))


(defmacro tc-err [P e]
  `(handle-type-error true
     (not (tc ~P ~e))))

(deftest check-test
  (is (tc Int 1))
  (is (tc ? 1))
  (is (tc ? [1 2]))
  (is (tc Int [1 2]))
  (is (tc ? (fn [x] [1 2])))
  ;; TODO
  (is (tc -wild (app (fn [x] [1 2]) 1)))
  )

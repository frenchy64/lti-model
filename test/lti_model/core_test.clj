(ns lti-model.core-test
  (:require [clojure.test :refer :all]
            [lti-model.core :refer :all :as lti]))

(defmacro tc [P e]
  `(check (parse-type '~P) {} '~e))

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
  ;; TODO
  (is (tc [Int :-> Int] (fn [x] [1 2])))
  (is (tc -wild (app (fn [x] [1 2]) 1)))
  )

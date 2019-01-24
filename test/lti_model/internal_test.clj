(ns lti-model.core-test
  (:require [clojure.test :refer :all]
            [clojure.pprint :refer [pprint]]
            [clojure.walk :as walk]
            [lti-model.internal :refer :all :as lti]))

(defmacro tc [P e]
  `(unparse-type (check-form (parse-type '~P) {} '~e)))

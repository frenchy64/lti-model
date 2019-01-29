(ns lti-model.walk
  (:require [clojure.walk :as cwalk]))

(defn trampoline-walk
  "Traverses form, an arbitrary data structure.  inner and outer are
  functions.  Applies inner to each element of form, building up a
  data structure of the same type, then applies outer to the result.
  Recognizes all Clojure data structures. Consumes seqs as with doall."

  {:added "1.1"}
  [inner outer form]
  (cond
   (list? form) #(outer (apply list (map inner form)))
   (instance? clojure.lang.IMapEntry form)
   #(outer (clojure.lang.MapEntry/create (inner (key form)) (inner (val form))))
   (seq? form) #(outer (doall (map inner form)))
   (instance? clojure.lang.IRecord form)
     #(outer (reduce (fn [r x] (conj r (inner x))) form form))
   (coll? form) #(outer (into (empty form) (map inner form)))
   :else (outer form)))

(defn trampoline-prewalk
  "Like postwalk, but does pre-order traversal."
  {:added "1.1"}
  [f form]
  (trampoline-walk (partial trampoline-prewalk f) identity (f form)))


(trampoline #(trampoline-prewalk (fn [x]
                                   (prn "inner" x)
                                   (if (integer? x) (inc x) x))
                                 %)
            [[1 2 3 4] [1 2 3 4]])

(cwalk/walk (fn [x]
              (prn "inner" x)
              (if (integer? x) (inc x) x))
            (fn [x]
              (prn "outer" x)
              (if (integer? x) (dec x) x))
            [[1 2 3 4] [1 2 3 4]])

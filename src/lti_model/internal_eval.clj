; dummy namespace to evaluate internal language forms in
(ns lti-model.internal-eval
  (:refer-clojure :only [fn + +' inc inc' comp every-pred
                         map partial reduce]))

(clojure.core/defmacro ann [e t] e)
(def app #(clojure.core/apply %1 [%2]))
(def appid app)
(def app0 #(%))
(def app2 #(clojure.core/apply %1 [%2 %3]))
(def id clojure.core/identity)
(def mapT #(map %))
(def intoT #(clojure.core/into %1 %2 %3))

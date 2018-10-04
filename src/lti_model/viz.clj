(ns lti-model.viz
  (:require [dorothy.core :as dot]
            [dorothy.jvm :as dotj #_#_:refer (render save! show!)]
            [hiccup.core :as html]))

(def g
  (dot/digraph [
    (dot/subgraph :cluster_0 [
      {:style :filled, :color :lightgrey, :label "process #1"}
      (dot/node-attrs {:style :filled, :color :white})

      [:a0 :> :a1 :> :a2 :> :a3]])

    (dot/subgraph :cluster_1 [
      {:color :blue, :label "process #2"}
      (dot/node-attrs {:style :filled})

      [:b0 :> :b1 :> :b2 :> :b3]])

    [:start :a0]
    [:start :b0]
    [:a1    :b3]
    [:b2    :a3]
    [:a3    :a0]
    [:a3    :end]
    [:b3    :end]

    [:start {:shape :Mdiamond}]
    [:end   {:shape :Msquare}]]))

(def g2
  (dot/digraph [
    (dot/node-attrs {:shape :Mrecord})
    [:fn {:label "<a0> a| <a1> a| <a2> a|<a3> a|"}]
    [:arg {:label "Int"}]
    [:arg :fn:a2]
    [:fn:a2 :fn:a0]
    [:fn:a0 :fn:a1]
    [:fn:a1 :fn:a0]
    [:fn:a1 :fn:a3]
    ]))

(comment
  (html/html [:table {:border 0, :cellborder 1 :cellspacing 0}
              [:tr
               [:td "left"]
               [:td {:port "f1"} "mid dle"]
               [:td {:port "f2"} "right"]]
              ])
  )

(def g3
  (dot/digraph [
    (dot/node-attrs {:shape :plaintext})
    [:struct1
     {:label (html/html
               [:table {:border 0, :cellborder 1 :cellspacing 0}
                [:tr
                 [:td "left"]
                 [:td {:port "f1"} "mid dle"]
                 [:td {:port "f2"} "right"]]])}]
    [:struct2
     {:label (html/html
               [:table {:border 0, :cellborder 1 :cellspacing 0}
                [:tr
                 [:td {:port "f0"} "one"]
                 [:td  "two"]]])}]
    [:struct3
     {:label (html/html
               [:table {:border 0, :cellborder 1 :cellspacing 0 :cellpadding 4}
                [:tr
                 [:td {:rowspan 3} "hello" [:br] "world"]
                 [:td {:colspan 3} "b"]
                 [:td {:rowspan 3} "g"]
                 [:td {:rowspan 3} "h"]]
                [:tr
                 [:td "c"]
                 [:td {:port "here"} "d"]
                 [:td "e"]]
                [:tr
                 [:td {:colspan 3} "f"]]
                ])}]
    [:struct1:f1 :struct2:f0]
    [:struct1:f2 :struct3:here]
    ]))

(def g4
  (dot/digraph [
    {:rankdir "LR"
     :fontsize 18
     :fontname "Anonymous Pro"}
    (dot/node-attrs
      {:fontname "Anonymous Pro"})
    (dot/subgraph :fn [
      {:style :filled, :color :lightgrey,
       :label "For All a"}
      ;(dot/node-attrs {:style :filled, :color :white})
      (dot/subgraph :fn0 [
        ["0a" "1a" {:style :dashed}]])
      ])
    ]))

(comment
(-> (dot/digraph [ [:a :b :c] [:b :d] ])
    dot/dot
    dotj/show!)

(-> g
    dot/dot
    dotj/show!)
(-> g3
    dot/dot
    dotj/show!)
(-> g4
    dot/dot
    dotj/show!)
)


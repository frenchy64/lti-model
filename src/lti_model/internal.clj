(ns lti-model.internal)

; e ::=                    ; Expressions
;       c                  ; constant functions
;     | n                  ; integers
;     | (fn {:interface t} ; functions
;         [x *]
;         e)
;     | [e *]              ; sequences
;     | (inst-case e (case (enclosing-fn-arity n) t [t *] *))       ; polymorphic type instantiation

#_
(fn {:interface (IFn [-> [Int -> [Int -> Int]]]
                     [-> [Bool -> [Bool -> Bool]]])}
  []
  (fn {:interface (case (enclosing-fn-arity 0)
                    [-> [Int -> [Int -> Int]]] [Int -> [Int -> Int]]
                    [-> [Bool -> [Bool -> Bool]]] [Bool -> [Bool -> Bool]])}
    [x]
    (fn {:interface (case (enclosing-fn-arity 0)
                      [Int -> [Int -> Int]] [Int -> Int]
                      [Bool -> [Bool -> Bool]] [Bool -> Bool])}
      [y] y)))

; foo : (U (All [a] [a -> a]) (All [b] [b -> b]))

; ((inst foo) 1)
; ((ann-poly foo  ;required that foo must be of the below type, but with PInst+type arguments erased
;            (U (PInst (All [a] [a -> a]) Int)
;               (PInst (All [b] [b -> b]) Int)))
;  1)

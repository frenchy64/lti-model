(ns lti-model.internal)

; e ::=                    ; Expressions
;       c                  ; constant functions
;     | n                  ; integers
;     | (fn {:interface t} ; functions
;         [x *]
;         e)
;     | [e *]              ; sequences
;     | (inst e t *)       ; polymorphic type instantiation

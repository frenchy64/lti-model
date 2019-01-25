(ns lti-model.internal)

; e ::=              ; Expressions
;     | c            ; constant functions
;     | n            ; integers
;     | (fn ^{:interface t} [x *] e) ; functions
;     | [e *]        ; sequences

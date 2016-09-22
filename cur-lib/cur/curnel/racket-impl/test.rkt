#lang s-exp "lang.rkt"

(Type 1)

(define x (Type 1))

x

(Π (x : (Type 1)) (Type 1))
(define id (λ (x : (Type 1)) x))


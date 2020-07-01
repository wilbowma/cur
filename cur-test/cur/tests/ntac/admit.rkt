#lang cur
(require cur/stdlib/axiom
         cur/stdlib/sugar
         cur/stdlib/prop
         cur/ntac/base
         cur/ntac/standard
         (only-in racket/base module))

(module check-output racket/base
  (provide check-output)
  (require rackunit racket/port)
  (define-syntax-rule (check-output expect body ...)
    (check-equal? (with-output-to-string (λ () body ...)) 'expect)))
(require 'check-output)


(define-theorem excluded-middle
  (∀ [P : Prop] (And P (Not P)))
  (admit ex-mid))
  
(check-output
 "Axioms used by \"excluded-middle\":\n - ex-mid : (Π (P : (Type 0)) (And P (Π (X37 : P) False)))\n"
 ;"Axioms used by \"excluded-middle\":\n - ex-mid : (Π (P : (Type 0)) (And P (→ P False)))\n"
 (print-assumptions excluded-middle))

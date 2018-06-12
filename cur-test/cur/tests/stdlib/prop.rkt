#lang cur
(require
 cur/stdlib/prop
 cur/stdlib/sugar
 cur/stdlib/bool
 cur/stdlib/nat
 "curunit.rkt")

(check-equal? And And)
(check-equal? True True)
(:: pf:anything-implies-true thm:anything-implies-true)
(:: pf:and-is-symmetric thm:and-is-symmetric)
(:: pf:proj1 thm:proj1)
(:: pf:proj2 thm:proj2)

(check-equal?
 (conj/i (conj/i T T) T)
 (conj (And True True) True (conj True True T T) T))

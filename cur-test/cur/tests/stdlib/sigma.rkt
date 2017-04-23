#lang cur
(require
 cur/stdlib/nat
 cur/stdlib/prop
 cur/stdlib/sugar
 cur/stdlib/sigma
 rackunit)

(define P (λ (x : Nat) (== Nat x 5)))
(define test-p (pair P 5 (refl Nat 5)))
(:: test-p (Σ Nat P))

(:: (fst test-p) Nat)
(:: (snd test-p) (== Nat (fst test-p) 5))

(check-equal?
 (fst test-p)
 5)

(check-equal?
 (snd test-p)
 (refl Nat 5))

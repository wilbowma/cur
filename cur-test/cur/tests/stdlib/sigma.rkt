#lang cur
(require
 cur/stdlib/nat
 cur/stdlib/equality
 cur/stdlib/sugar
 cur/stdlib/sigma
 rackunit)

(define P (λ (x : Nat) (ML-= Nat x 5)))
(define test-p (pair P 5 (ML-refl Nat 5)))
(:: test-p (Σ Nat P))

(:: (fst test-p) Nat)
(:: (snd test-p) (ML-= Nat (fst test-p) 5))

(check-equal?
 (fst test-p)
 5)

(check-equal?
 (snd test-p)
 (ML-refl Nat 5))

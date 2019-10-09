#lang cur
(require
 cur/stdlib/nat
 cur/stdlib/equality
 cur/stdlib/sugar
 cur/stdlib/sigma
 rackunit/turnstile+)

(define P (λ (x : Nat) (ML-= Nat x 5)))
(define test-p (pair P 5 (ML-refl Nat 5)))
(check-type test-p : (Σ Nat P))

(check-type (fst test-p) : Nat -> 5)
(check-type (snd test-p) : (ML-= Nat (fst test-p) 5) -> (ML-refl Nat 5))

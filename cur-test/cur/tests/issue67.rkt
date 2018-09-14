#lang cur
(require turnstile/rackunit-typechecking)

(define-datatype Nat : (Type 0)
  (z : Nat)
  (s : (Π (x : Nat) Nat)))

(define-datatype Nat2 : (Type 0)
  (zz : Nat2)
  (ss : (Π (x : Nat2) Nat2)))

(typecheck-fail
 (elim-Nat z
           (λ (x : Nat) Nat)
           zz
           (λ (x : Nat2) (λ (ih : Nat2) ih)))
 #:with-msg "expected.*Nat.*given.*Nat2")


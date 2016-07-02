#lang cur

(require
 rackunit
 cur/stdlib/nat
 cur/stdlib/bool
 cur/stdlib/prop
 cur/stdlib/sugar
 cur/stdlib/ntac/base
 cur/stdlib/ntac/standard)

;; Not quite and-proj1; need elim for that.
(define-theorem and-proj1
  (forall (A : Type) (B : Type) (c : (And A B)) Type)
  nop
  ;; XXX The use of fill is ugly. Perhaps could be infered
  (intro A)
  (intro)
  (intros c)
  nop
  ;interactive ; try (fill (exact 'A))
  ;; This works too
  (exact A)
  ;; And this
  #;(fill by-assumption))

(check-equal?
 (and-proj1 Nat Bool (conj Nat Bool z true))
 Nat)

(check-equal?
 ((ntac-prove
   (forall (A : Type) (a : A) A)
   (intros A a)
   (fill by-assumption))
  Nat z)
 z)

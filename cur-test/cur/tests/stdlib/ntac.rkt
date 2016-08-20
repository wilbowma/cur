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
  (try by-assumption)
  nop
  ;; XXX The use of fill is ugly. Perhaps could be infered
  (by-intro A)
  by-intro
  (by-intros c)
  nop
  ;interactive ; try (fill (by-exact A))
  ;; This works too
  (by-exact A)
  ;; And this
  #;(fill by-assumption))

(check-equal?
 (and-proj1 Nat Bool (conj Nat Bool z true))
 Nat)

(check-equal?
 ((ntac
   (forall (A : Type) (a : A) A)
   (try by-assumption)
   (by-intros A a)
   by-assumption)
  Nat z)
 z)

(check-equal?
 ((ntac (forall (A : Type) Type) by-obvious) Nat)
 Nat)

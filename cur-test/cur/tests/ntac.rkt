#lang cur

(require
 rackunit
 cur/stdlib/nat
 cur/stdlib/bool
 cur/stdlib/prop
 cur/stdlib/sugar
 cur/ntac/base
 cur/ntac/standard)

;; Not quite and-proj1; need elim for that.

;; TODO: For some reason, #%app in (And A B) isn't expanded properly. Not getting right binding?
(define-theorem and-proj1
  (forall (A : Type) (B : Type) (c : (And A B)) Type)
  (try by-assumption)
  nop
  (by-intro A-)
  by-intro
  (by-intros c)
  nop
  ;interactive ; try (fill (exact A-))
  ;; This works too
  (by-exact A-)
  ;; And this
  #;by-assumption)

(check-equal?
 (and-proj1 Nat Bool (conj Nat Bool z true))
 Nat)

(check-equal?
 ((ntac
   (forall (A : Type) (a : A) A)
   (try by-assumption)
   (by-intros A a)
   (by-assumption a)
   #;by-assumption)
  Nat z)
 z)

(check-equal?
 (((ntac (forall (A : Type) (a : A) A) by-obvious) Nat) z)
 z)

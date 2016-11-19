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

#;(define-theorem id
  (forall (A : Type) (B : Type) Type)
  (by-intros A B)
  (by-exact A))

(data And : 2 (-> (A : Type) (B : Type) Type)
      (conj : (-> (A : Type) (B : Type) (a : A) (b : B) (And A B))))

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
  #;(by-exact A)
  ;; TODO: Exact is broken when the exact refers to free variables introduced by tactics
  ;; And this
  by-assumption)

(check-equal?
 (and-proj1 Nat Bool (conj Nat Bool z true))
 Nat)

(check-equal?
 ((ntac
   (forall (A : Type) (a : A) A)
   ;; TODO: fails here; binding gets messed up
   (try by-assumption)
   (by-intros A a)
   by-assumption)
  Nat z)
 z)

;(check-equal?
; ((ntac (forall (A : Type) Type) by-obvious) Nat)
; Nat)

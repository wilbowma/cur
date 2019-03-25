#lang cur

(require
 "ntac/rackunit-ntac.rkt"
 rackunit/turnstile
 cur/stdlib/nat
 cur/stdlib/bool
 cur/stdlib/prop
 cur/stdlib/sugar
 cur/ntac/base
 cur/ntac/standard)

(check-ntac-trace
 (Π (A : Type) (B : Type) (c : (And A B)) Type)
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
 #;by-assumption
 ~>
 --------------------------------
 (Π (A : (Type 0)) (B : (Type 0)) (c : (And A B)) (Type 0))

 --------------------------------
 (Π (A : (Type 0)) (B : (Type 0)) (c : (And A B)) (Type 0))

 --------------------------------
 (Π (A : (Type 0)) (B : (Type 0)) (c : (And A B)) (Type 0))

 A- : (Type 0)
 --------------------------------
 (Π (B : (Type 0)) (c : (And A- B)) (Type 0))

 A- : (Type 0)
 B : (Type 0)
 --------------------------------
 (Π (c : (And A- B)) (Type 0))

 A- : (Type 0)
 B : (Type 0)
 c : (And A- B)
 --------------------------------
 (Type 0)

 A- : (Type 0)
 B : (Type 0)
 c : (And A- B)
 --------------------------------
 (Type 0))

;; Not quite and-proj1; need elim for that.

(define-theorem and-proj1
  (Π (A : Type) (B : Type) (c : (And A B)) Type)
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


(check-type (and-proj1 Nat Bool (conj Nat Bool z true)) : Type -> Nat)

(check-type
 ((ntac
   (forall (A : Type) (a : A) A)
   (try by-assumption)
   (by-intros A a)
   (by-assumption a)
   #;by-assumption)
  Nat z)
 : Nat -> z)

(check-type
 (((ntac (forall (A : Type) (a : A) A) by-obvious) Nat) z)
 : Nat -> z)

#lang cur
;; A (non-cohesive) set of examples demonstrating the auto tactic.

(require
  cur/stdlib/ascii
  cur/stdlib/sugar
  cur/stdlib/equality
  cur/stdlib/nat
  cur/stdlib/bool
  cur/ntac/hint
  (except-in cur/ntac/base
             ntac-proc
             define-theorem
             define-theorem/for-export
             ntac
             ntac/debug)
  cur/ntac/standard
  cur/ntac/rewrite)

(define-datatype natprod : Prop
  [pair : (-> Nat Nat natprod)])

(define/rec/match fst : natprod -> Nat
  [(pair x _) => x])

(define/rec/match snd : natprod -> Nat
  [(pair _ y) => y])

(define-theorem silly1
  (∀ [n : Nat] [m : Nat] [o : Nat] [p : Nat]
     (-> (== n m)
         (== (pair n o) (pair n p))
         (== (pair n o) (pair m p))))
  (by-intros n m o p eq1 eq2)
  (by-rewriteL eq1)
  (by-apply eq2))

(define-theorem silly1p
  (∀ [n : Nat] [m : Nat] [o : Nat] [p : Nat]
     (-> (== n m)
         (== (pair n o) (pair n p))
         (== (pair n o) (pair m p))))
  auto)

(define-theorem silly2
  (∀ [n : Nat] [m : Nat] [o : Nat] [p : Nat]
     (-> (== n m)
         (∀ [q : Nat] [r : Nat]
            (-> (== q r)
                (== (pair q o) (pair r p))))
         (== (pair n o) (pair m p))))
  (by-intros n m o p eq1 eq2)
  (by-apply eq2)
  (by-apply eq1))

(define-theorem silly2p
  (∀ [n : Nat] [m : Nat] [o : Nat] [p : Nat]
     (-> (== n m)
         (∀ [q : Nat] [r : Nat]
            (-> (== q r)
                (== (pair q o) (pair r p))))
         (== (pair n o) (pair m p))))
  auto)

(define-theorem pred-example-1
  (∀ [p : Bool]
     (== (and p p) p))
  (by-intros p)
  (by-destruct p)
  reflexivity
  reflexivity)

(define-theorem pred-example-1p
  (∀ [p : Bool]
     (== (and p p) p))
  auto)

(define-theorem pred-example-2
  (∀ [p : Bool] [q : Bool]
     (-> (== p q)
         (== p true)
         (== (and p q) true)))
  (by-intros p q eq1 eq2)
  (by-rewriteL eq1)
  (by-rewrite pred-example-1)
  by-assumption)

(define-theorem pred-example-2p
  (∀ [p : Bool] [q : Bool]
     (-> (== p q)
         (== p true)
         (== (and p q) true)))
  (hints-add! pred-example-1)
  auto)

(define-theorem plus-n-0
  (∀ [n : Nat] (== Nat n (plus n 0)))
  (by-intro n)
  (by-induction n #:as [() (n-1 IH)])
  reflexivity
  (by-rewriteL IH)
  reflexivity)

(define-theorem plus-n-0p
  (∀ [n : Nat] (== Nat n (plus n 0)))
  auto)

(define-theorem plus-n-0pp
  (∀ [n : Nat] (== Nat n (plus n 0)))
  (by-intro n)
  (by-induction n #:as [() (n-1 IH)])
  (set-auto-depth! 2)
  auto ; note that this only keeps the reflexivity step despite taking two steps!
  (by-rewriteL IH)
  reflexivity)
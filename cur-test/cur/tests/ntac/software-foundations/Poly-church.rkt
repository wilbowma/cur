#lang cur
(require cur/stdlib/sugar
         cur/stdlib/equality
         cur/ntac/base
         cur/ntac/standard
         cur/ntac/rewrite
         rackunit/turnstile
         "../rackunit-ntac.rkt")

;; part 3 of 3 of Software Foundations Poly.v chapter

(define nat (∀ [X : Type] (-> (-> X X) X X)))
(define one (λ [X : Type] [s : (-> X X)] [z : X] (s z)))
(define two (λ [X : Type] [s : (-> X X)] [z : X] (s (s z))))

(check-type one : nat)
(check-type two : nat)

(define zero (λ [X : Type] [s : (-> X X)] [z : X] z))

(check-type zero : nat)

(define (do3times [X : Type] [f : (-> X X)] [n : X])
  (f (f (f n))))

(define three do3times)

(check-type three : nat)

(define (succ [n : nat])
  (λ [X : Type] [f : (-> X X)] [x : X] (n X f (f x))))

(check-type succ : (-> nat nat))

;; succ-test1 raw term
(check-type
 (refl (Π (X : Type) (f : (-> X X)) (x : X) X)
       (λ X (λ f (λ x (f x)))))
 : (== (Π (X : Type) (f : (-> X X)) (x : X) X)
       (λ X (λ f (λ x (f x))))
       (λ X (λ s (λ z (s z))))))

(define-theorem succ-test1
  (== (succ zero) one)
  reflexivity)

(check-type succ-test1 : (== (succ zero) one))

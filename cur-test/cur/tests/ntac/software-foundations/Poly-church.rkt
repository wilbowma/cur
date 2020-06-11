#lang cur
(require cur/stdlib/sugar
         cur/stdlib/equality
         cur/ntac/base
         cur/ntac/standard
         cur/ntac/rewrite
         rackunit/turnstile+
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

(define-theorem succ-test2
  (== (succ one) two)
  reflexivity)

(define-theorem succ-test3
  (== (succ two) three)
  reflexivity)

(define (plus [n : nat] [m : nat])
  (λ [X : Type] [f : (-> X X)] [x : X] (n X f (m X f x))))

(check-type plus : (-> nat nat nat))

(define-theorem plus-test1
  (== (plus zero one) one)
  reflexivity)

(define-theorem plus-test2
  (== (plus two three) (plus three two))
  reflexivity)

(define-theorem plus-test3
  (== (plus (plus two two) three) (plus one (plus three three)))
  reflexivity)

(define (mult [n : nat] [m : nat])
  (λ [X : Type] [f : (-> X X)] (m X (n X f))))

(define-theorem mult-test1
  (== (mult one one) one)
  reflexivity)

(define-theorem mult-test2
  (== (mult zero (plus three three)) zero)
  reflexivity)

(define-theorem mult-test3
  (== (mult two three) (plus three three))
  reflexivity)

(define (exp [n : nat] [m : nat])
  (λ [X : Type] (m (-> X X) (n X))))

(define-theorem exp-test1
  (== (exp two two) (plus two two))
  reflexivity)

(define-theorem exp-test2
  (== (exp three two) (plus (mult two (mult two two)) one))
  reflexivity)

(check-type (exp three zero) : nat)

;; TODO: this example doesnt work, here are notes from sf:
;;
;; (** (_Hint_: Polymorphism plays a crucial role here.  However,
;;     choosing the right type to iterate over can be tricky.  If you hit
;;     a "Universe inconsistency" error, try iterating over a different
;;     type: [nat] itself is usually problematic.) *)

#;(define-theorem exp-test3
  (== (exp three zero) one)
  reflexivity)

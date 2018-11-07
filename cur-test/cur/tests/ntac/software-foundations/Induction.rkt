#lang cur

(provide (all-defined-out))

(require
 "../rackunit-ntac.rkt"
 "Basics.rkt"
 cur/stdlib/equality
 cur/stdlib/sugar
 cur/ntac/base
 cur/ntac/standard
 cur/ntac/rewrite)

;; examples from SF Ch 2: Induction.v, using PM equality

;; plus-n-0
(::
 (λ [n : nat]
   (new-elim
    n
    (λ [n : nat] (== nat n (plus n 0)))
    (refl nat 0)
    (λ [n-1 : nat]
      (λ [IH : (== nat n-1 (plus n-1 0))]
        (new-elim
         IH
         (λ [m : nat]
           (λ [H : (== nat n-1 m)]
             (== nat (S n-1) (S m))))
         (refl nat (S n-1)))))))
 (∀ [n : nat] (== nat n (plus n 0))))

(define-theorem plus-n-0
  (∀ [n : nat] (== nat n (plus n 0)))
  (by-intro n)
  simpl ;; this step doesnt do anything except get everything in expanded form
  (by-induction n #:as [() (n-1 IH)])
  ;; subgoal 1
  reflexivity
  ;; subgoal 2
  simpl
  (by-rewriteL IH)
  reflexivity)

(define-theorem minus-diag
  (∀ [n : nat] (== nat (minus n n) 0))
  (by-intro n)
  (by-induction n #:as [() (n-1 IH)])
  ;; subgoal 1
  reflexivity
  ;; subgoal 2
  (by-rewrite IH)
  reflexivity)

(define-theorem mult_0_r
  (∀ [n : nat] (== nat (mult n 0) 0))
  (by-intro n)
  simpl
  (by-induction n #:as [() (n-1 IH)])
  simpl
  reflexivity
  simpl
  (by-rewrite IH)
  reflexivity)

(define-theorem plus-n-Sm
  (∀ [n : nat] [m : nat]
     (== nat (S (plus n m)) (plus n (S m))))
  (by-intro n)
  (by-intro m)
  simpl
  (by-induction n #:as [() (n-1 IH)])
  ;; subgoal 1
  simpl
  reflexivity
  ;; subgoal 1
  simpl
  (by-rewrite IH)
  reflexivity)

(define-theorem plus-comm
  (∀ [n : nat] [m : nat]
     (== nat (plus n m) (plus m n)))
  (by-intro n)
  (by-intro m)
  (by-induction n #:as [() (n-1 IH)])
  ; subgoal 1
  (by-rewriteL plus-n-0 m)
  reflexivity
  ; subgoal 2
  (by-rewriteL plus-n-Sm m n-1)
  (by-rewrite IH)
  reflexivity)

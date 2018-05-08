#lang cur

(require
 rackunit
 "Basics.rkt"
 cur/stdlib/equality
 cur/stdlib/sugar
 cur/ntac/base
 cur/ntac/standard
 cur/ntac/ML-rewrite)

;; examples from SF Ch 2: Induction.v, using ML equality

;; plus-n-0
(::
 (λ [n : nat]
   (new-elim
    n
    (λ [n : nat] (ML-= nat n (plus n 0)))
    (ML-refl nat 0)
    (λ [n-1 : nat]
      (λ [IH : (ML-= nat n-1 (plus n-1 0))]
        (new-elim
         IH
         (λ [n : nat] [m : nat]
            (λ [H : (ML-= nat n m)]
              (ML-= nat (S n) (S m))))
         (λ [n : nat]
           (ML-refl nat (S n))))))))
 (∀ [n : nat] (ML-= nat n (plus n 0))))

(define-theorem plus-n-0
  (∀ [n : nat] (ML-= nat n (plus n 0)))
  (by-intro n)
  simpl ;; this step doesnt do anything except get everything in expanded form
  (by-induction n #:as [() (n-1 IH)])
  ;; subgoal 1
  reflexivity
  ;; subgoal 2
  simpl
  (by-rewriteL IH)
  reflexivity)

(define-theorem mult_0_r
  (∀ [n : nat] (ML-= nat (mult n 0) 0))
  (by-intro n)
  simpl
  (by-induction n #:as [() (n-1 IH)])
  simpl
  reflexivity
  simpl
  (by-rewrite IH)
  reflexivity)

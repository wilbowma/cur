#lang cur

(require
 rackunit
 "Basics.rkt"
 cur/stdlib/prop
 cur/stdlib/sugar
 cur/ntac/base
 cur/ntac/standard
 cur/ntac/prop)


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
         (λ [n : nat] [m : nat]
            (λ [H : (== nat n m)]
              (== nat (S n) (S m))))
         (λ [n : nat]
           (refl nat (S n))))))))
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

;; doesnt work, requires simul recursion
#;(define-theorem minus-diag
  (∀ [n : nat] (== nat (minus n n) 0))
  (by-intro n)
;  simpl
  (by-induction n #:as [() (n-1 IH)])
  display-focus
  ;; subgoal 1
  simpl
  display-focus
  reflexivity
  display-focus
  ;; subgoal 2
  simpl
  display-focus
  (by-rewrite IH)
  display-focus
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

;; plus-comm requires coq=
(require cur/ntac/coqrewrite
         cur/stdlib/coqeq)

(define-theorem plus-n-0/coq
  (∀ [n : nat] (coq= nat n (plus n O)))
  (by-intro n)
  simpl ;; this step doesnt do anything except get everything in expanded form
  (by-induction n #:as [() (n-1 IH)])
  ;; subgoal 1
  coq-reflexivity
  ;; subgoal 2
  simpl
  (by-coq-rewriteL IH)
  coq-reflexivity)

(define-theorem plus-n-Sm/coq
  (∀ [n : nat] [m : nat]
     (coq= nat (S (plus n m)) (plus n (S m))))
  (by-intro n)
  (by-intro m)
  simpl
  (by-induction n #:as [() (n-1 IH)])
  ;; subgoal 1
  simpl
  coq-reflexivity
  ;; subgoal 1
  simpl
  (by-coq-rewrite IH)
  coq-reflexivity)

(define-theorem plus-comm
  (∀ [n : nat] [m : nat]
     (coq= nat (plus n m) (plus m n)))
  (by-intro n)
  (by-intro m)
  simpl
  (by-induction n #:as [() (n-1 IH)])
  ; subgoal 1
  simpl
  (by-coq-rewriteL/thm/expand plus-n-0/coq m)
  coq-reflexivity
  ; subgoal 2
  simpl
  (by-coq-rewriteL/thm/expand plus-n-Sm/coq m n-1)
  (by-coq-rewrite IH)
  coq-reflexivity)


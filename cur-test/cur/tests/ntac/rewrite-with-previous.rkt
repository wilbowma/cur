#lang cur
(require cur/stdlib/equality
         cur/stdlib/sugar
         cur/stdlib/nat
         cur/ntac/base
         cur/ntac/standard
         cur/ntac/rewrite
         "rackunit-ntac.rkt")

;; tests for by-rewrite 

(define-theorem plus-0-n
  (forall [n : Nat] (== Nat (plus 0 n) n))
  by-intro
  simpl
  reflexivity)

;; search goal for instantiation of thm
(define-theorem mult-0-plus/search
  (∀ [n : Nat] [m : Nat]
     (== Nat (mult (plus 0 n) m) (mult n m)))
  by-intro
  by-intro
  (by-rewrite plus-0-n)
  reflexivity)

(define-theorem plus-n-0
  (∀ [n : Nat] (== Nat n (plus n z)))
  (by-intro n)
  (by-induction n #:as [() (n-1 IH)])
  ;; subgoal 1
  reflexivity
  ;; subgoal 2
  (by-rewriteL IH)
  reflexivity)

(define-theorem plus-n-Sm
  (∀ [n : Nat] [m : Nat]
     (== Nat (s (plus n m)) (plus n (s m))))
  (by-intro n)
  (by-intro m)
  (by-induction n #:as [() (n-1 IH)])
  ;; subgoal 1
  reflexivity
  ;; subgoal 2
  (by-rewrite IH)
  reflexivity)

(define-theorem plus_comm
  (∀ [n : Nat] [m : Nat]
     (== Nat (plus n m) (plus m n)))
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

;; automatically instantiate thms
(define-theorem plus_comm/search
  (∀ [n : Nat] [m : Nat]
     (== Nat (plus n m) (plus m n)))
  (by-intro n)
  (by-intro m)
  (by-induction n #:as [() (n-1 IH)])
  ; subgoal 1
  (by-rewriteL plus-n-0)
  reflexivity
  ; subgoal 2
  (by-rewriteL plus-n-Sm) ; 2 params to instantiate
  (by-rewrite IH)
  reflexivity)

;; plus-assoc
(define-theorem plus-assoc
  (∀ [n : Nat] [m : Nat] [p : Nat]
     (== Nat (plus n (plus m p)) (plus (plus n m) p)))
  (by-intros n m p)
  (by-induction n #:as [() (n-1 IH)])
  ; goal 1, n = 0
  reflexivity
  (by-rewrite IH)
  reflexivity)

(define-theorem plus-swap
  (∀ [n : Nat] [m : Nat] [p : Nat]
     (== Nat (plus n (plus m p))
             (plus m (plus n p))))
  (by-intros n m p)
  (by-rewrite plus-assoc n m p)
  (by-assert H (== Nat (plus n m) (plus m n)))
  ; proof of H
  (by-rewrite plus_comm n m)
  reflexivity
  ; proof of rest
  (by-rewrite H)
  (by-rewriteL plus-assoc m n p)
  reflexivity)

(define-theorem plus-swap/search
  (∀ [n : Nat] [m : Nat] [p : Nat]
     (== Nat (plus n (plus m p))
             (plus m (plus n p))))
  (by-intros n m p)
  (by-rewrite plus-assoc) ; 3 params
  (by-assert H (== Nat (plus n m) (plus m n)))
  ; proof of H
  (by-rewrite plus_comm) ; 2 params
  reflexivity
  ; proof of rest
  (by-rewrite H)
  (by-rewriteL plus-assoc) ; left? = #t, 3 params
  reflexivity)

#lang cur

(require
 rackunit
 cur/stdlib/nat
 cur/stdlib/prop
 cur/stdlib/sugar
 cur/ntac/base
 cur/ntac/standard
 cur/ntac/prop)


;; plus-n-0
(::
 (λ [n : Nat]
   (new-elim
    n
    (λ [n : Nat] (== Nat n (plus n 0)))
    (refl Nat z)
    (λ [n-1 : Nat]
      (λ [IH : (== Nat n-1 (plus n-1 0))]
        (new-elim
         IH
         (λ [n : Nat] [m : Nat]
            (λ [H : (== Nat n m)]
              (== Nat (s n) (s m))))
         (λ [n : Nat]
           (refl Nat (s n))))))))
 (∀ [n : Nat] (== Nat n (plus n 0))))

(define-theorem plus-n-0
  (∀ [n : Nat] (== Nat n (plus n 0)))
  (by-intro n)
  simpl ;; this step doesnt do anything except get everything in expanded form
  (by-induction n #:as [() (n-1 IH)])
  ;; subgoal 1
  reflexivity
  ;; subgoal 2
  simpl
  (by-rewriteL IH)
  reflexivity
  )

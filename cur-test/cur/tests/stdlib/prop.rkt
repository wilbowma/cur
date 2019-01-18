#lang cur
(require
 cur/stdlib/prop
 cur/stdlib/sugar
 cur/stdlib/bool
 cur/stdlib/nat
 cur/stdlib/equality
 rackunit/turnstile)

(check-type True : Type -> True)
(check-type pf:anything-implies-true : thm:anything-implies-true)
(check-type pf:and-is-symmetric : thm:and-is-symmetric)
(check-type pf:proj1 : thm:proj1)
(check-type pf:proj2 : thm:proj2)

;; test infer
(check-type (conj (conj T T) T)
            : (And (And True True) True)
            -> (conj (And True True) True (conj True True T T) T))

;; A or A

(define thm:A-or-A
  (Π (A : Type) (o : (Or A A)) A))

(define proof:A-or-A
  (lambda (A : Type) (c : (Or A A))
          (elim Or (lambda (c : (Or A A)) A)
                [(lambda (a : A) a)
                 (lambda (b : A) b)]
                c)
          #;(new-elim c (lambda (c : (Or A A)) A)
                [(lambda (a : A) a)
                 (lambda (b : A) b)])))

(check-type proof:A-or-A : thm:A-or-A)

;; False implies 0=1
(check-type
 (λ [x : False] (elim-False x (λ y (== Nat 0 1))))
 : (-> False (== Nat 0 1)))

;; false implies anything
(define falsey
  (λ [X : Type] [x : False] (elim-False x (λ y X))))
(check-type falsey : (Π [X : Type] (-> False X)))

(check-type
 ((λ [X : Type] [x : False] (elim-False x (λ y X)))
  (== Nat 0 1))
 : (-> False (== Nat 0 1)))


(check-type
 (λ [n : Nat]
   (elim-Nat n (λ m Type) True (λ x y False)))
 : (-> Nat Type))

(define 0neq1
 (λ [h1 : (== Nat 0 1)]
   (elim-==
    h1
    (λ [b : Nat] ; isZero?
      (λ H
        (elim-Nat b (λ n Type) True (λ x y False))))
    I))) ; proof of (isZero 0)
(check-type 0neq1 : (-> (== Nat 0 1) False))

(check-type
 (λ [H : (== Nat 0 1)]
   (falsey (== Nat 2 3) (0neq1 H)))
 : (-> (== Nat 0 1) (== Nat 2 3)))

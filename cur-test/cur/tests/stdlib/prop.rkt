#lang cur
(require
 cur/stdlib/prop
 cur/stdlib/sugar
 cur/stdlib/bool
 cur/stdlib/nat
 turnstile/rackunit-typechecking)

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

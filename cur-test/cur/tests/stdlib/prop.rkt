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

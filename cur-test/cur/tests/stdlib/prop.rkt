#lang cur
(require
 cur/stdlib/prop
 cur/stdlib/sugar
 cur/stdlib/bool
 cur/stdlib/nat
 rackunit)

(check-equal? And And)
(check-equal? True True)
(:: pf:anything-implies-true thm:anything-implies-true)
(:: pf:and-is-symmetric thm:and-is-symmetric)
(:: pf:proj1 thm:proj1)
(:: pf:proj2 thm:proj2)
(check-equal?
 (elim == (λ (x : Bool) (y : Bool) (p : (== Bool x y)) Nat)
       ((λ (x : Bool) z))
       (refl Bool true))
 z)

(check-equal?
 (conj/i (conj/i T T) T)
 (conj (And True True) True (conj True True T T) T))

(define (id (A : Type) (x : A)) x)

(check-equal?
 ((id (== True T T))
  (refl True (run (id True T))))
 (refl True T))

(check-equal?
 ((id (== True T T))
  (refl True (id True T)))
 (refl True T))

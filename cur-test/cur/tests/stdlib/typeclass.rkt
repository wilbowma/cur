#lang cur

(require
 rackunit
 cur/stdlib/sugar
 cur/stdlib/bool
 cur/stdlib/nat
 cur/stdlib/typeclass)

(typeclass (Eqv (A : Type))
           (equal? : (Π (a : A) (b : A) Bool)))
(impl (Eqv Bool)
      (define (equal? (a : Bool) (b : Bool))
        (if a b (not b))))
(impl (Eqv Nat)
      (define equal? nat-equal?))
(check-equal?
 (equal? z z)
 true)
(check-equal?
 (equal? z (s z))
 false)
(check-equal?
 (equal? true false)
 false)
(check-equal?
 (equal? true true)
 true)

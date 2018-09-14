#lang cur
(require
 cur/stdlib/sugar
 cur/stdlib/nat
 cur/stdlib/bool
 turnstile/rackunit-typechecking)

(check-type (add1 (s z)) : Nat -> (s (s z)))
(check-type (sub1 (s z)) : Nat -> z)

(check-type (plus z z) : Nat -> z)
(check-type (plus (s (s z)) (s (s z))) : Nat -> (s (s (s (s z)))))

(check-type (mult 0 0) : Nat -> 0)
(check-type (mult 0 1) : Nat -> 0)

(check-type (mult (s (s z)) z) : Nat -> z)
(check-type (mult (s (s z)) (s z)) : Nat -> (s (s z)))

(check-type (exp z z) : Nat -> (s z))
(check-type (exp (s z) z) : Nat -> z)
(check-type (square (s (s z))) : Nat
            -> (s (s (s (s z)))))
(check-type (square (s (s (s z)))) : Nat
            -> (s (s (s (s (s (s (s (s (s z))))))))))

(check-type (zero? 0) : Bool -> true)
(check-type (zero? 1) : Bool -> false)

;; TODO: fix nat-equal?
(check-type (nat-equal? z z) : Bool -> true)
(check-type (nat-equal? z (s z)) : Bool -> false)
(check-type (nat-equal? (s z) z) : Bool -> false)
(check-type (nat-equal? (s z) (s z)) : Bool -> true)
(check-type (nat-equal? 3 3) : Bool -> true)

(check-type (even? z) : Bool -> true)
(check-type (even? (s z)) : Bool -> false)
(check-type (even? (s (s z))) : Bool -> true)
(check-type (odd? z) : Bool -> false)
(check-type (odd? (s z)) : Bool -> true)
(check-type (odd? (s (s z))) : Bool -> false)
(check-type (odd? (s (s (s z)))) : Bool -> true)

(check-type 0 : Nat -> z)
(check-type 1 : Nat -> (s z))
(check-type 2 : Nat -> (s (s z)))
(check-type 3 : Nat -> (s (s (s z))))
(check-type 4 : Nat -> (s (s (s (s z)))))

(define (fact (n : Nat))
  (match n #:return Nat
    [z 1]
    [(s n-1)
     (mult (s n-1) (fact n-1))]))

(check-type (mult 2 (mult 1 1)) : Nat -> 2)

(check-type (fact 1) : Nat -> 1)
(check-type (fact 2) : Nat -> 2)
(check-type (fact 3) : Nat -> 6)
(check-type (fact 5) : Nat -> 120)

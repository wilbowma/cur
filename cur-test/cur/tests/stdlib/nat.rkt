#lang cur
(require
 cur/stdlib/sugar
 cur/stdlib/nat
 cur/stdlib/bool
 turnstile/rackunit-typechecking)

(check-type (add1 (s z)) : Nat -> (s (s z)))
(check-type add1 : (-> Nat Nat))
(check-type (sub1 (s z)) : Nat -> z)
(check-type sub1 : (-> Nat Nat))

(check-type (plus z z) : Nat -> z)
(check-type (plus (s (s z)) (s (s z))) : Nat -> (s (s (s (s z)))))

;; test for non-full application cases
(check-type plus : (-> Nat Nat Nat))
(check-type (plus 0) : (-> Nat Nat))
(check-type ((plus 0) 0) : Nat -> 0)

(check-type (mult 0 0) : Nat -> 0)
(check-type (mult 0 1) : Nat -> 0)

(check-type (mult (s (s z)) z) : Nat -> z)
(check-type (mult (s (s z)) (s z)) : Nat -> (s (s z)))

;; test for non-full application cases
(check-type mult : (-> Nat Nat Nat))
(check-type (mult 0) : (-> Nat Nat))
(check-type ((mult 0) 0) : Nat -> 0)

(check-type (exp z z) : Nat -> (s z))
(check-type (exp (s z) z) : Nat -> z)
(check-type (exp (s (s z)) z) : Nat -> z)
(check-type (exp (s z) (s z)) : Nat -> (s z))
(check-type (exp (s (s z)) (s z)) : Nat -> (s z))
(check-type (exp (s (s z)) (s (s z))) : Nat -> (s (s (s (s z)))))

(check-type exp : (-> Nat Nat Nat))
(check-type (exp 0) : (-> Nat Nat))
(check-type ((exp 0) 2) : Nat -> 1)

(check-type (square z) : Nat -> z)
(check-type (square (s z)) : Nat -> (s z))
(check-type (square (s (s z))) : Nat
            -> (s (s (s (s z)))))
(check-type (square (s (s (s z)))) : Nat
            -> (s (s (s (s (s (s (s (s (s z))))))))))

(check-type square : (-> Nat Nat))

(check-type zero? : (-> Nat Bool))
(check-type (zero? 0) : Bool -> true)
(check-type (zero? 1) : Bool -> false)

;; TODO: fix nat-equal?
(check-type (nat-equal? z z) : Bool -> true)
(check-type (nat-equal? z (s z)) : Bool -> false)
(check-type (nat-equal? (s z) z) : Bool -> false)
(check-type (nat-equal? (s z) (s z)) : Bool -> true)
(check-type (nat-equal? 3 3) : Bool -> true)

;; non-full application of multi-match, eg nat-equal?
(check-type nat-equal? : (-> Nat Nat Bool))
(check-type (nat-equal? 0) : (-> Nat Bool))
(check-type ((nat-equal? 0) 0) : Bool -> true)
(check-type ((nat-equal? 4) 3) : Bool -> false)
(check-type ((nat-equal? 4) 4) : Bool -> true)

(define my-zero? (nat-equal? 0))

(check-type my-zero? : (-> Nat Bool))
(check-type (my-zero? 0) : Bool -> (zero? 0))
(check-type (my-zero? 1) : Bool -> (zero? 1))
(check-type (my-zero? 3) : Bool -> (zero? 3))

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

#;(define (fact (n : Nat))
  (match n #:return Nat
    [z 1]
    [(s n-1)
     (mult (s n-1) (fact n-1))]))

(define/rec/match fact : Nat -> Nat
  [z => 1]
  [(s n-1) => (mult (s n-1) (fact n-1))])

(check-type (mult 2 (mult 1 1)) : Nat -> 2)

(check-type (fact 1) : Nat -> 1)
(check-type (fact 2) : Nat -> 2)
(check-type (fact 3) : Nat -> 6)
(check-type (fact 5) : Nat -> 120)

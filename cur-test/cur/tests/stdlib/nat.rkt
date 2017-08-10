#lang cur
(require
 cur/stdlib/sugar
 cur/stdlib/nat
 cur/stdlib/bool
 rackunit)

(check-equal? (add1 (s z)) (s (s z)))
(check-equal? (sub1 (s z)) z)

(check-equal? (plus z z) z)
(check-equal? (plus (s (s z)) (s (s z))) (s (s (s (s z)))))

(check-equal? (mult (s (s z)) z) z)
(check-equal? (mult (s (s z)) (s z)) (s (s z)))

(check-equal? (exp z z) (s z))
(check-equal? (exp (s z) z) z)
(check-equal? (square (s (s z))) (s (s (s (s z)))))
(check-equal? (square (s (s (s z)))) (s (s (s (s (s (s (s (s (s z))))))))))

(check-equal? (nat-equal? z z) true)
(check-equal? (nat-equal? z (s z)) false)
(check-equal? (nat-equal? (s z) (s z)) true)

(check-equal? (even? z) true)
(check-equal? (even? (s z)) false)
(check-equal? (even? (s (s z))) true)
(check-equal? (odd? z) false)
(check-equal? (odd? (s z)) true)
(check-equal? (odd? (s (s z))) false)
(check-equal? (odd? (s (s (s z)))) true)

(check-equal? 0 z)
(check-equal? 1 (s z))
(check-equal? 2 (s (s z)))
(check-equal? 3 (s (s (s z))))
(check-equal? 4 (s (s (s (s z)))))

(define (fact (n : Nat))
  (match n
    [z 1]
    [(s n-1)
     (mult (s n-1) (fact n-1))]))
#;(define (fact (n : Nat))
  (elim
   (λ (x : Nat) Nat)
   (1
    (lambda (n : Nat)
      (lambda (n-1 : Nat)
        (mult n (fact n-1)))))))

(check-equal? (mult 2 (mult 1 1)) 2)

(check-equal? (fact 1) 1)
(check-equal? (fact 2) 2)
(check-equal? (fact 3) 6)
(check-equal? (fact 5) 120)

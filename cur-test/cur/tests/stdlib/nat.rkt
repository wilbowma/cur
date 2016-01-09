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

;; TODO Disabled due to performance bugs
#;(check-equal? (exp z z) (s z))
#;(check-equal? (exp (s z) z) z)
#;(check-equal? (square (s (s z))) (s (s (s (s z)))))

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

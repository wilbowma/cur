#lang s-exp "redex-curnel.rkt"
(require "sugar.rkt")
(module+ test
  (require rackunit))

(data nat : Type
  (z : nat)
  (s : (-> nat nat)))

(define (add1 (n : nat)) (s n))
(module+ test
  (check-equal? (add1 (s z)) (s (s z))))

(define (sub1 (n : nat))
  (case n
    [z z]
    [s (lambda (x : nat) x)]))
(module+ test
  (check-equal? (sub1 (s z)) z))

(define plus
  (fix (plus : (forall* (n1 : nat) (n2 : nat) nat))
    (lambda (n1 : nat)
      (lambda (n2 : nat)
        (case n1
          [z n2]
          [s (λ (x : nat) (plus x (s n2)))])))))
(module+ test
  (check-equal? (plus z z) z)
  (check-equal? (plus (s (s z)) (s (s z))) (s (s (s (s z))))))

(add1 (s z))
(sub1 (s z))

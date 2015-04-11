#lang s-exp "../redex-curnel.rkt"
(require "sugar.rkt" "bool.rkt")
;; TODO: override (all-defined-out) to enable exporting all these
;; properly.
(provide nat z s add1 sub1 plus nat-equal?)
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

(define-rec (nat-equal? (n1 : nat) (n2 : nat) : bool)
  (case* n1
    [z (case* n2
         [z btrue]
         [(s (n3 : nat)) bfalse])]
    [(s (n3 : nat))
       (case* n2
         [z btrue]
         [(s (n4 : nat)) (nat-equal? n3 n4)])]))
(module+ test
  (check-equal? (nat-equal? z z) btrue)
  (check-equal? (nat-equal? z (s z)) bfalse)
  (check-equal? (nat-equal? (s z) (s z)) btrue))

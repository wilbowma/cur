#lang s-exp "../redex-curnel.rkt"
(require "sugar.rkt" "bool.rkt")
;; TODO: override (all-defined-out) to enable exporting all these
;; properly.
(provide nat z s add1 sub1 plus )
(module+ test
  (require rackunit))

(data nat : Type
  (z : nat)
  ;; TODO: Can't use -> syntax here due to issues with names
  (s : (forall (x : nat) nat)))

(define (add1 (n : nat)) (s n))
(module+ test
  (check-equal? (add1 (s z)) (s (s z))))

(define (sub1 (n : nat))
  (case* nat n (lambda (x : nat) nat)
    [z z]
    [(s (x : nat)) IH: ((ih-x : nat)) x]))
(module+ test
  (check-equal? (sub1 (s z)) z))

(define (plus (n1 : nat) (n2 : nat))
  (case* nat n1 (lambda (x : nat) nat)
    [z n2]
    [(s (x : nat)) IH: ((ih-x : nat))
     (s ih-x)]))
(module+ test
  (check-equal? (plus z z) z)
  (check-equal? (plus (s (s z)) (s (s z))) (s (s (s (s z))))))

(define (nat-equal? (n1 : nat) (n2 : nat))
  (case* nat n1 (lambda (x : nat) bool)
    [z (case* nat n2 (lambda (x : nat) bool)
         [z btrue]
         [(s (x : nat)) IH: ((ih-x : bool)) bfalse])]
    ;; TODO: Can't finish correct definition due to issues with names
    [(s (x : nat)) IH: ((ih-x : bool))
       (case* nat n2 (lambda (x : nat) bool)
         [z bfalse]
         [(s (x : nat)) IH: ((ih-x : bool))
          ih-x])]))
(module+ test
  (check-equal? (nat-equal? z z) btrue)
  (check-equal? (nat-equal? z (s z)) bfalse)
  (check-equal? (nat-equal? (s z) (s z)) btrue))

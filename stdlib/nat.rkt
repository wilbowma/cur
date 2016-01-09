#lang s-exp "../cur.rkt"
(require "sugar.rkt" "bool.rkt")
;; TODO: override (all-defined-out) to enable exporting all these
;; properly.
(provide Nat z s add1 sub1 plus mult exp square nat-equal? even? odd?)
(module+ test
  (require rackunit))

(data Nat : Type
  (z : Nat)
  (s : (-> Nat Nat)))

(define (add1 (n : Nat)) (s n))
(module+ test
  (check-equal? (add1 (s z)) (s (s z))))

(define (sub1 (n : Nat))
  (match n
    [z z]
    [(s (x : Nat)) x]))
(module+ test
  (check-equal? (sub1 (s z)) z))

(define (plus (n1 : Nat) (n2 : Nat))
  (match n1
    [z n2]
    [(s (x : Nat))
     (s (recur x))]))
(module+ test
  (check-equal? (plus z z) z)
  (check-equal? (plus (s (s z)) (s (s z))) (s (s (s (s z))))))

(define (mult (m : Nat) (n : Nat))
  (match m
    [z z]
    [(s (x : Nat))
     (plus n (recur x))]))
(module+ test
  (check-equal? (mult (s (s z)) z) z)
  (check-equal? (mult (s (s z)) (s z)) (s (s z))))

(define (exp (m : Nat) (e : Nat))
  (match m
    [z (s z)]
    [(s (x : Nat))
     (mult e (recur x))]))
(module+ test
  (check-equal? (exp z z) (s z))
  (check-equal? (exp (s (s z)) z) z))

(define square (run (exp (s (s z)))))
;; TODO: This test takes too long t run
#;(module+ test
  (check-equal? (square (s (s z))) (s (s (s (s z))))))

;; Credit to this function goes to Max
(define nat-equal?
  (elim Nat Type (lambda (x : Nat) (-> Nat Bool))
    (elim Nat Type (lambda (x : Nat) Bool)
          true
          (lambda* (x : Nat) (ih-n2 : Bool) false))
    (lambda* (x : Nat) (ih : (-> Nat Bool))
      (elim Nat Type (lambda (x : Nat) Bool)
            false
            (lambda* (x : Nat) (ih-bla : Bool)
                     (ih x))))))
(module+ test
  (check-equal? (nat-equal? z z) true)
  (check-equal? (nat-equal? z (s z)) false)
  (check-equal? (nat-equal? (s z) (s z)) true))

(define (even? (n : Nat))
  (match n
    [z true]
    [(s (n : Nat))
     (not (recur n))]))

(define (odd? (n : Nat))
  (not (even? n)))

(module+ test
  (check-equal?
    (even? z)
    true)
  (check-equal?
    (even? (s z))
    false)
  (check-equal?
    (even? (s (s z)))
    true)
  (check-equal?
    (odd? z)
    false)
  (check-equal?
    (odd? (s z))
    true)
  (check-equal?
    (odd? (s (s z)))
    false)
  (check-equal?
    (odd? (s (s (s z))))
    true))

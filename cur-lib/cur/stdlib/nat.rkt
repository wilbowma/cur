#lang s-exp "../main.rkt"
(require "sugar.rkt" "bool.rkt")
;; TODO: override (all-defined-out) to enable exporting all these
;; properly.
(provide Nat z s add1 sub1 plus mult exp square nat-equal? even? odd?)

(data Nat : Type
  (z : Nat)
  (s : (-> Nat Nat)))

(define (add1 (n : Nat)) (s n))

(define (sub1 (n : Nat))
  (match n
    [z z]
    [(s (x : Nat)) x]))

(define (plus (n1 : Nat) (n2 : Nat))
  (match n1
    [z n2]
    [(s (x : Nat))
     (s (recur x))]))

(define (mult (m : Nat) (n : Nat))
  (match m
    [z z]
    [(s (x : Nat))
     (plus n (recur x))]))

(define (exp (m : Nat) (e : Nat))
  (match m
    [z (s z)]
    [(s (x : Nat))
     (mult e (recur x))]))

(define square (run (exp (s (s z)))))

(define (zero? (n : Nat))
  (match n
    [z true]
    [(s (n : Nat))
     false]))

(define (nat-equal? (n : Nat))
  (match n
    [z zero?]
    [(s (n-1 : Nat))
     (lambda (m : Nat)
       (match m
         [z false]
         [(s (m-1 : Nat))
          ((recur n-1) m-1)]))]))

(define (even? (n : Nat))
  (match n
    [z true]
    [(s (n : Nat))
     (not (recur n))]))

(define (odd? (n : Nat))
  (not (even? n)))

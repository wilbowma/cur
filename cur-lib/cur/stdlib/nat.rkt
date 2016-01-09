#lang s-exp "../cur.rkt"
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

(define (even? (n : Nat))
  (match n
    [z true]
    [(s (n : Nat))
     (not (recur n))]))

(define (odd? (n : Nat))
  (not (even? n)))

#lang s-exp "../cur.rkt"
(require "sugar.rkt")
(provide Bool true false if not and or)

(data Bool : Type
  (true : Bool)
  (false : Bool))

(define-syntax-rule (if t s f)
  (case t
    [true s]
    [false f]))

(define (not (x : Bool)) (if x false true))

(module+ test
  (require rackunit)
  (check-equal? (not true) false)
  (check-equal? (not false) true))

(define (and (x : Bool) (y : Bool))
  (if x
      y
      (not y)))

(module+ test
  (check-equal? (and true false) false)
  (check-equal? (and false false) true)
  (check-equal? (and false true) false)
  (check-equal? (and true true) true))

(define (or (x : Bool) (y : Bool))
  (if x
      true
      y))

(module+ test
  (check-equal? (or true false) true)
  (check-equal? (or false false) false)
  (check-equal? (or false true) true)
  (check-equal? (or true true) true))

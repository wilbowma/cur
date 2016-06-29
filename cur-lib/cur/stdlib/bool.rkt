#lang s-exp "../main.rkt"
(require "sugar.rkt")
(provide Bool true false if not and or)

(data Bool : 0 Type
  (true : Bool)
  (false : Bool))

(define-syntax-rule (if t s f)
  (match t
    [true s]
    [false f]))

(define (not (x : Bool)) (if x false true))

(define (and (x : Bool) (y : Bool))
  (if x
      y
      (not y)))

(define (or (x : Bool) (y : Bool))
  (if x
      true
      y))

#lang s-exp "../main.rkt"
(require "sugar.rkt")
(provide Bool true false if not and or)

(data Bool : 0 Type
  (true : Bool)
  (false : Bool))

;; NB: Can't use syntax rules due to taint issues
(define-syntax (if syn)
  (syntax-case syn ()
    [(_ t s f)
     (quasisyntax/loc syn
       (match t
         #:in Bool
         [true s]
         [false f]))]))

(define (not (x : Bool)) (if x false true))

(define (and (x : Bool) (y : Bool))
  (if x
      y
      (not y)))

(define (or (x : Bool) (y : Bool))
  (if x
      true
      y))

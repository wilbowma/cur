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
      false))

(define (or (x : Bool) (y : Bool))
  (if x
      true
      y))

(begin-for-syntax
  (provide bool->meta-bool meta-bool->bool)

  ;; TODO: I sense a pattern.
  ;; Follow this pattern hence forth.
  ;; Maybe abstract.
  (define (meta-bool->bool b)
    (if b #'true #'false))

  (define (bool->meta-bool syn)
    (syntax-parse syn
      #:literals (true false)
      [true #t]
      [false #f])))

#lang s-exp "../main.rkt"
(require "sugar.rkt")

(provide Bool true false if not and or)

; Π  λ ≻ ⊢ ≫ → ∧ (bidir ⇒ ⇐) τ⊑ ⇑

(define-datatype Bool : Type
  (true : Bool)
  (false : Bool))

(define-typed-syntax (if tst e1 e2) ≫
  [⊢ e1 ≫ e1- ⇒ τ]
  [⊢ e2 ≫ e2- ⇐ τ]
  ----------
  [≻ (elim-Bool tst (λ [b : Bool] τ) e1- e2-)])

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

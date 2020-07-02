#lang s-exp "../main.rkt"
(require "sugar.rkt")

(provide Bool elim-Bool true false
         (for-syntax true false ~Bool)
         if not and or bool-equal?)

; Π  λ ≻ ⊢ ≫ → ∧ (bidir ⇒ ⇐) τ⊑ ⇑

(define-datatype Bool : Type
  (true : Bool)
  (false : Bool))

;; TODO: generalize to all isomorphic datatypes
(define-typed-syntax (if tst e1 e2) ≫
  [⊢ e1 ≫ e1- ⇒ τ]
  [⊢ e2 ≫ e2- ⇐ τ]
  ----------
  [≻ (elim-Bool tst (λ [b : Bool] τ) e1- e2-)])

(define/rec/match not : Bool -> Bool
  [true => false]
  [false => true])

(define/rec/match and : Bool [b : Bool] -> Bool
  [true => b]
  [false => false])

(define/rec/match or : Bool [b : Bool] -> Bool
  [true => true]
  [false => b])

(define-for-export (bool-equal? [b1 : Bool] [b2 : Bool])
  (or (and b1 b2)
      (not (or b1 b2))))

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

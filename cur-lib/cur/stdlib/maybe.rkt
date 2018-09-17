#lang s-exp "../main.rkt"
(require "sugar.rkt")
(provide Maybe none (rename-out [some/i some]))

(data Maybe : 1 (Π (A : Type) Type)
  (none : (Π (A : Type) (Maybe A)))
  (some : (Π (A : Type) (Π (a : A) (Maybe A)))))

;; inferring version of some
; Π  λ ≻ ⊢ ≫ → ∧ (bidir ⇒ ⇐) τ⊑ ⇑
(define-typed-syntax some/i
  [(_ A a) ≫ --- [≻ (some A a)]]
  [(_ a) ≫ [⊢ a ≫ a- ⇒ A] --- [≻ (some A a-)]])

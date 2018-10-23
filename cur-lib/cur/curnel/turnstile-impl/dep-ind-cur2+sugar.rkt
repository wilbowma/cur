#lang turnstile/lang
(require turnstile/more-utils
         "dep-ind-cur2.rkt")

;; dep-ind-cur2 library, adding some sugar like auto-currying

(provide →
 (rename-out [λ/c λ] [app/c #%app] [app/eval/c app/eval] [define/c define]
             [→ ->] [Π Pi] [Π ∀] [Π forall] [λ/c lambda]))

;; abbrevs for Π/c
;; (→ τ_in τ_out) == (Π (unused : τ_in) τ_out)
(define-simple-macro (→ τ_in ... τ_out)
  #:with (X ...) (generate-temporaries #'(τ_in ...))
  (Π [X : τ_in] ... τ_out))
;; ;; (∀ (X) τ) == (∀ ([X : Type]) τ)
;; (define-simple-macro (∀ X ...  τ)
;;   (Π [X : Type] ... τ))

(define-nested/R λ/c λ)
(define-nested/L app/c #%app)
(define-nested/L app/eval/c app/eval/1)

(define-syntax define/c
  (syntax-parser
    [(_ x:id e) #'(define x e)]
    [(_ (f:id x+τ ...) e)
     #'(define f (λ/c x+τ ... e))]))

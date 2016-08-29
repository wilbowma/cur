define-language stlc
  τ ::= 1  | (τ * τ) | (τ -> τ)
  e ::= () | (cons e e) | (prj i e) |  (λ (x : τ) e) | (e e)


define-language-sugar (let x = e₁ in e₂) ((λ (x : τ) e₂) e₁)
  where τ = infer-type e₁

define-theorem Type-Soundness
  if Γ ⊢ e : τ then e →* v


(begin-for-syntax
  ;; A function in the meta language
  (define (transform-lambda obj)
    (syntax-case obj (:)
      [(_ (x : t) e)
       #'(λ (x : t) e)])))

;; A syntactic hook in the object language
(define-syntax lambda transform-lambda)


(lambda bla bla bla)
;; causes the computation, at compile-time:
(transform-lambda #'(lambda bla bla bla))

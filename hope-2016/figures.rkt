define-language stlc
  τ ::= 1  | (τ * τ) | (τ -> τ)
  e ::= () | (cons e e) | (prj i e) |  (λ (x : τ) e) | (e e)


define-language-sugar (let x = e₁ in e₂) ((λ (x : τ) e₂) e₁)
  where τ = infer-type e₁

define-theorem Type-Soundness
  if Γ ⊢ e : τ then e →* v

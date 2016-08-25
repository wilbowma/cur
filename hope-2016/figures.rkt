#lang cur

require bnf

define-language stlc
  τ ::= 1  | (τ_1 * τ_2) | (τ' -> τ)
  e ::= () | (cons e_1 e_2) | (prj i e)
     |  (λ (x : τ) e) | (e e')

#lang s-exp "dep-ind-cur2.rkt"
(require (only-in turnstile/eval define-typerule/red)
         (only-in turnstile/typedefs define-type)
         "dep-ind-cur2+sugar.rkt")

(provide Nat Z S elim-Nat)

(define-type Nat : Type)

(define-type Z : Nat)
(define-type S : Nat -> Nat)

(define-typerule/red (elim-Nat v P mz ms) ≫
  [⊢ v ≫ v- ⇐ Nat]
  [⊢ P ≫ P- ⇐ (→ Nat Type)] ; prop / motive
  [⊢ mz ≫ mz- ⇐ (P- Z)]
  [⊢ ms ≫ ms- ⇐ (Π [n-1 : Nat] (Π [ih : (P- n-1)] (P- (S n-1))))]
  -----------
  [⊢ (eval-Nat v- P- mz- ms-) ⇒ (P- v-)]
  #:where eval-Nat
  [(elim-Nat- ~Z P mz ms) ~> mz]
  [(elim-Nat- (~S n-1) P mz ms) ~> (app/eval ms n-1 (eval-Nat n-1 P mz ms))])

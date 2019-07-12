#lang s-exp "dep-ind-cur2.rkt"
(require (only-in turnstile/base ⇒ ⇐ ≫ ⊢ ≻)
         (only-in turnstile define-typed-syntax)
         (only-in turnstile/typedefs define-type)
         "dep-ind-cur2+sugar.rkt")

;; another equality lib for dep-ind-cur2.rkt
;; - unlike dep-ind-cur2+eq.rkt, this one uses define-type and define-red,
;;   instead of manually defining the rules and constructors

(provide = eq-refl eq-elim)

;; equality -------------------------------------------------------------------

(define-type = : [A : (Type 0)] [a : A] [b : A] -> (Type 0))

(define-type eq-refl : [A : (Type 0)] [e : A] -> (= A e e))

;; eq-elim: t : T
;;          P : (T -> Type)
;;          pt : (P t)
;;          w : T
;;          peq : (= t w)
;;       -> (P w)
(define-typed-syntax (eq-elim t P pt w peq) ≫
  [⊢ t ≫ t- ⇒ A]
  [⊢ P ≫ P- ⇐ (→ A Type)]
  [⊢ pt ≫ pt- ⇐ (P- t-)]
  [⊢ w ≫ w- ⇐ A]
  [⊢ peq ≫ peq- ⇐ (= A t- w-)]
  --------------
  [⊢ pt- ⇒ (P- w-)])

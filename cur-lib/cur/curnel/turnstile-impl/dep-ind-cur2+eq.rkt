#lang s-exp "dep-ind-cur2.rkt"
(require (only-in turnstile struct #%app- void- define-typed-syntax ⇒ ⇐ ≫ ⊢ ≻)
         "dep-ind-cur2+sugar.rkt")

;; eq lib for dep-ind-cur2.rkt

(provide = eq-refl eq-elim)

;; equality -------------------------------------------------------------------

(struct =- (l r) #:transparent)

(define-typed-syntax (= t1 t2) ≫
  [⊢ t1 ≫ t1- ⇒ ty]
  [⊢ t2 ≫ t2- ⇐ ty]
  ---------------------
  [⊢ (#%app- =- t1- t2-) ⇒ Type])

(define-typed-syntax (eq-refl e) ≫
  [⊢ e ≫ e- ⇒ _ (⇒ ~Type)]
  ----------
  [⊢ (#%app- void-) ⇒ (= e- e-)])

;; eq-elim: t : T
;;          P : (T -> Type)
;;          pt : (P t)
;;          w : T
;;          peq : (= t w)
;;       -> (P w)
(define-typed-syntax (eq-elim t P pt w peq) ≫
  [⊢ t ≫ t- ⇒ ty]
  [⊢ P ≫ P- ⇐ (→ ty Type)]
  [⊢ pt ≫ pt- ⇐ (P- t-)]
  [⊢ w ≫ w- ⇐ ty]
  [⊢ peq ≫ peq- ⇐ (= t- w-)]
  --------------
  [⊢ pt- ⇒ (P- w-)])

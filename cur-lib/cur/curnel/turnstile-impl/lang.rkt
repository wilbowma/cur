#lang racket/base

(provide ;; #%module-begin
         provide require only-in for-syntax all-from-out rename-out except-out
         ;; begin-for-syntax
         ;; define-values begin define #%app λ
         #%plain-app void #%plain-lambda printf displayln quote begin
         define-syntax define-for-syntax
         (for-syntax
          (all-from-out racket/base
                        syntax/parse
                        racket/syntax)))

(require (for-syntax racket/base syntax/parse racket/syntax))

(require "dep-ind-cur2.rkt")
(provide (all-from-out "dep-ind-cur2.rkt")
         (rename-out [λ lambda]))

(require (only-in turnstile/base
                  define-typed-syntax get-orig assign-type
                  subst substs typecheck? typechecks? typeof
                  current-type-eval expand/df)
         turnstile/eval
         (only-in turnstile/typedefs get-type-info)
         (for-syntax macrotypes/stx-utils syntax/stx))
(provide (all-from-out turnstile/base turnstile/eval turnstile/typedefs))

(require "dep-ind-cur2+data2.rkt")
(provide (all-from-out "dep-ind-cur2+data2.rkt"))

; Π  λ ≻ ⊢ ≫ → ∧ (bidir ⇒ ⇐) τ⊑ ⇑

;; shims for old cur forms

(provide data elim new-elim)

(begin-for-syntax
  (define (take-Π t n)
    (syntax-parse t
      [((~and (~literal Π) P) [x:id (~and (~datum :) tag) τ] ... ; sugared stx
                              (~and (~not [_ (~datum :) _])
                                    (~not ((~literal Π) . _))
                                    tout))
       (list (stx-take #'([x τ] ...) n)
             #`(P #,@(stx-drop #'([x tag τ] ...) n) tout))]
      [_                                           ; nested stx
       (let L ([As null] [ty t] [n n])
         (if (zero? n)
             (list (reverse As) ty)
             (syntax-parse ty
               [((~literal Π) [x : τ] rst)
                (L (cons #'[x τ] As) #'rst (sub1 n))])))]))
  (define (split-Π t)
    (syntax-parse t
      [((~literal Π) [x:id (~datum :) τ] ... ; sugared stx
                     (~and (~not [_ (~datum :) _])
                           (~not ((~literal Π) . _))
                           tout))
       (list #'([x τ] ...) #'tout)]
      [_                                    ; nested stx
       (let L ([is null] [ty t])
         (syntax-parse ty
           [((~literal Π) [x : τ] rst)
            (L (cons #'[x τ] is) #'rst)]
           [_ (list (reverse is) ty)]))])))

;; TODO: currently, dont expand TY or tyC, bc of unbound TY
;; - but this means that curried form wont be handled
(define-typed-syntax data
  [(_ TY:id (~datum :) n:exact-nonnegative-integer ty
      [C:id (~datum :) tyC] ...) ≫
   #:when (zero? (stx-e #'n)) ; simple case, no params
  -----------------
  [≻ (define-datatype TY : ty [C : tyC] ...)]]
  [(_ TY:id (~datum :) n:exact-nonnegative-integer ty
      [C:id (~datum :) tyC] ...) ≫
  ;; [⊢ ty ≫ ty- ⇐ Type] ; use unexpanded
  ;; [⊢ tyC ≫ tyC- ⇐ Type] ... ; ow, must use ~unbound as in dep-ind-cur2+data2
  #:with [([A tyA] ...) ty-rst] (take-Π #'ty (stx-e #'n))
  #:with [([i tyi] ...) ty0] (split-Π #'ty-rst)
  #:with ([_ tyC-rst] ...) (stx-map (λ (t) (take-Π t (stx-e #'n))) #'(tyC ...))
  #:with ([([x tyx] ...) tyC0] ...) (stx-map split-Π #'(tyC-rst ...))
  -----------------
  [≻ (define-datatype TY [A : tyA] ... : [i : tyi] ... -> ty0
       [C : [x : tyx] ... -> tyC0] ...)]])

(define-typed-syntax (elim ty:id motive (method ...) target) ≫
  #:with elim-Name (format-id #'ty "elim-~a" #'ty)
  ---
  [≻ (elim-Name target motive method ...)])

(define-typed-syntax (new-elim target motive method ...) ≫
  [⊢ target ≫ target- ⇒ τ]
  #:with (elim-Name . _) (get-type-info #'τ)
  ---
  [≻ (elim-Name target- motive method ...)])



(require
 (for-syntax "reflection.rkt"))
(provide
 (for-syntax
  (all-from-out "reflection.rkt")))

;; (define-syntax define+provide-placeholders
;;   (syntax-parser
;;     [(_ x:id ...)
;;      #'(begin (define x void) ... (provide x ...))]))

;; (define+provide-placeholders Π Type)

#lang racket/base

(provide ;; #%module-begin
 provide require for-syntax
 all-from-out rename-out except-out all-defined-out
 only-in except-in
 begin-for-syntax
 module+
 module*
 module
 submod
 ;; define-values begin define #%app λ
 #%plain-app void #%plain-lambda printf displayln quote begin
 define-syntax define-for-syntax
 (for-syntax
  (all-from-out racket/base
                syntax/parse
                racket/syntax)))

(require (for-syntax racket/base syntax/parse racket/syntax))

(require (only-in turnstile+/base
                  define-typed-syntax syntax-parse/typecheck get-orig assign-type
                  define-typed-variable-syntax current-typecheck-relation
                  current-check-relation
                  subst substs typecheck? typechecks? typeof add-expected-type
                  current-type-eval expand/df typecheck-fail-msg/multi
                  ⇒ ⇐ ≫ ⊢ ≻)
         turnstile+/eval
         turnstile+/typedefs
         (for-syntax macrotypes/stx-utils syntax/stx
                     (for-syntax racket/base syntax/parse)))
(provide (all-from-out turnstile+/base turnstile+/eval turnstile+/typedefs))

(require "cic-saccharata.rkt")
(provide (all-from-out "cic-saccharata.rkt"))

;; shims for old cur forms

(provide data elim new-elim)

(begin-for-syntax
  (define-syntax ~Π/unexpanded
    ;; TODO: make these ~literal
    (let ([out-pat #'(~or (~datum Π) (~datum Pi) (~datum ∀) (~datum forall))])
      (pattern-expander
       (syntax-parser
         [:id out-pat]
         [(_ . rst) #`(#,out-pat . rst)]))))
  (define (take-Π t n)
    (syntax-parse t
      [((~and ~Π/unexpanded P) [x:id (~and (~datum :) tag) τ] ... ; sugared stx
                               (~and (~not [_ (~datum :) _])
                                     (~not (~Π/unexpanded . _))
                                     tout))
       (list (stx-take #'([x τ] ...) n)
             #`(P #,@(stx-drop #'([x tag τ] ...) n) tout))]
      [_                                           ; nested stx
       (let L ([As null] [ty t] [n n])
         (if (zero? n)
             (list (reverse As) ty)
             (syntax-parse ty
               [(~Π/unexpanded [x : τ] rst)
                (L (cons #'[x τ] As) #'rst (sub1 n))])))]))
  (define (split-Π t)
    (syntax-parse t
      [(~Π/unexpanded [x:id (~datum :) τ] ... ; sugared stx
                     (~and (~not [_ (~datum :) _])
                           (~not (~Π/unexpanded . _))
                           tout))
       (list #'([x τ] ...) #'tout)]
      [_                                    ; nested stx
       (let L ([is null] [ty t])
         (syntax-parse ty
           [(~Π/unexpanded [x : τ] rst)
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
  ;; [⊢ tyC ≫ tyC- ⇐ Type] ... ; ow, must use ~unbound as in
  #:with [([A tyA] ...) ty-rst] (take-Π #'ty (stx-e #'n))
;  #:with [([i tyi] ...) ty0] (split-Π #'ty-rst)
  #:with ([([CA _] ...) tyC-rst/CA] ...) (stx-map (λ (t) (take-Π t (stx-e #'n))) #'(tyC ...))
  ;  #:with ([([x tyx] ...) tyC0] ...) (stx-map split-Π #'(tyC-rst ...))
  #:with (tyC-rst ...) (stx-map
                        (λ (CAs tyC)
                          (substs #'(A ...) CAs tyC))
                        #'((CA ...) ...)
                        #'(tyC-rst/CA ...))
  #:with out #'(define-datatype TY [A : tyA] ... : ty-rst [C : tyC-rst] ...)
;  #:do[(pretty-print (stx->datum #'out))]
  -----------------
  [≻ out]])

(define-typed-syntax (elim ty:id motive (method ...) target) ≫
  #:with elim-Name (format-id #'ty "elim-~a" #'ty)
  ---
  [≻ (elim-Name target motive method ...)])

(define-typed-syntax (new-elim target motive method ...) ≫
  [⊢ target ≫ target- ⇒ τ]
  #:with elim-Name (get-datatype-elim #'τ)
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

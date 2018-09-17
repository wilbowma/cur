#lang racket/base

(provide ;; #%module-begin
         provide require only-in for-syntax all-from-out rename-out except-out
         ;; begin-for-syntax
         ;; define-values begin define #%app λ
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
                  define-typed-syntax get-orig assign-type subst substs typecheck? typechecks?)
         (for-syntax macrotypes/stx-utils))
(provide (all-from-out turnstile/base))

(require "dep-ind-cur2+data2.rkt")
(provide (all-from-out "dep-ind-cur2+data2.rkt")
         (rename-out [define-datatype data]))

; Π  λ ≻ ⊢ ≫ → ∧ (bidir ⇒ ⇐) τ⊑ ⇑

;; shims for old cur forms

(provide elim new-elim)

(define-typed-syntax (elim ty:id motive (method ...) target) ≫
  #:with elim-Name (format-id #'ty "elim-~a" #'ty)
  ---
  [≻ (elim-Name target motive method ...)])

(define-typed-syntax (new-elim target motive method ...) ≫
  [⊢ target ≫ target- ⇒ τ]
  #:do[(define exinfo (syntax-property #'τ 'extra))]
  #:fail-unless exinfo (format "could not infer extra info from type ~a" (syntax->datum #'τ))
  #:with (elim-Name _ ...) (or (and (pair? exinfo) (car exinfo)) exinfo)
  ---
  [≻ (elim-Name target- motive method ...)])



(require "reflection.rkt")
(provide (all-from-out "reflection.rkt"))

;; (define-syntax define+provide-placeholders
;;   (syntax-parser
;;     [(_ x:id ...)
;;      #'(begin (define x void) ... (provide x ...))]))

;; (define+provide-placeholders Π Type)

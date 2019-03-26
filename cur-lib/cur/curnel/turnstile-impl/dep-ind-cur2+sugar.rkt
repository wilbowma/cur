#lang turnstile/lang
(require turnstile/more-utils
         (for-syntax turnstile/more-utils)
         "dep-ind-cur2.rkt")

;; dep-ind-cur2 library, adding some sugar like auto-currying

(provide (for-syntax (rename-out [~Π/c ~Π]))
         → ; → = Π = ∀
         (rename-out
          [→ Π] [→ Pi] [→ ∀] [→ forall] [→ ->]
          [λ/c λ] [λ/c lambda] [app/c #%app] [app/eval/c app/eval]
          [define/c define]))

(begin-for-syntax
  (define-syntax-class xs+τ #:attributes ([fst 0] [rst 1])
    (pattern [(~var x0 id) (~var x id) ... (~datum :) τ]
             #:with fst #'[x0 : τ]
             #:with (rst ...) (stx-map (λ (x) #`[#,x : τ]) #'(x ...)))
    (pattern τ ; no label, ie non-dependent →
             #:with fst #`[#,(syntax-property
                              (syntax-property (generate-temporary 'X) 'tmp #t)
                              'display-as
                              #'→) : τ]
             #:with (rst ...) #'())))

;; → = Π = ∀
;; usages:
;; (→ [x y z : τ] ... τout)
;; (→ [x : τ] ... τout)
;; (→ τ ... τout)
(define-syntax →
  (syntax-parser
    [(_ t) #'t]
    [(_ (~var b xs+τ) . rst)
     (quasisyntax/loc this-syntax
       (Π b.fst #,(quasisyntax/loc this-syntax (→ b.rst ... . rst))))]))

(begin-for-syntax
  ;; curried expander
  (define-syntax ~Π/c
    (pattern-expander
     (syntax-parser
       [(_ t) #'t]
       [(_ (~var b x+τ) t_out) #'(~Π b t_out)]
       [(_ (~var b x+τ) (~and (~literal ...) ooo) t_out)
        #'(~and TMP
                (~parse ([b.x (~datum :) b.τ] ooo t_out)
                        (stx-parse/fold #'TMP (~Π b rst))))]))))

;; abbrevs for Π/c
;; (→ τ_in τ_out) == (Π (unused : τ_in) τ_out)
#;(define-simple-macro (→ τ_in ... τ_out)
  #:with (X ...) (stx-map
                  (λ (x)
                    (syntax-property
                     (syntax-property x 'tmp #t)
                     'display-as
                     #'→))
                  (generate-temporaries #'(τ_in ...)))
  #:with out/srcloc (syntax/loc this-syntax (Π/c [X : τ_in] ... τ_out))
  out/srcloc)
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

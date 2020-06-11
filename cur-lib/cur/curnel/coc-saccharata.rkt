#lang turnstile+/quicklang
(require
 turnstile+/more-utils
 (for-syntax turnstile+/more-utils)
 "coc.rkt")

;;;; CoC saccharata (after zea saccharata)
;;;; CoC, but with a little bit of sugar in the curnel, to simplify complex typing rules.
;;;; ------------------------------------------------------------------------

(provide
 (for-syntax
  multi-decl
  xs+τ
  (rename-out [~Π/c ~Π])
  (rename-out [~λ/c ~λ])
  ~#%app)
 →
 ; → = Π = ∀
 (rename-out
  [→ Π] [→ Pi] [→ ∀] [→ forall] [→ ->]
  [λ/c λ] [λ/c lambda]
  [app/c #%app] [app/eval/c app/eval]
  [define/c define])
 ; rexport
 (except-out
  (all-from-out "coc.rkt")
  #%app λ Π define app/eval (for-syntax ~Π ~λ)))

;;; Curried core forms.
;;; -----------------------------------------------------------

;; Curried Π
;; ------------------------------------------------

(begin-for-syntax
  ; Syntax classes for parsing an arbitrary number of variables with the same
  ; type annotation: e.g., [x ... : A]
  (define-syntax-class multi-decl #:attributes ([fst 0] [rst 1] [all 1])
    (pattern [(~var x0 id) (~var x id) ... (~datum :) τ]
             #:with fst #'[x0 : τ]
             #:with (rst ...) (stx-map (λ (x) #`[#,x : τ]) #'(x ...))
             #:with (all ...) (cons #'fst (attribute rst))))

  ; λ declarations can omit the type
  (define-syntax-class multi-λ-decl #:attributes ([fst 0] [rst 1] [all 1])
    (pattern d:multi-decl
             #:with fst (attribute d.fst)
             #:with (rst ...) (attribute d.rst)
             #:with (all ...) (attribute d.all))
    (pattern x:id
             #:with fst #'x
             #:with (rst ...) '()
             #:with (all ...) (list #'fst)))

  ; Π declarations can omit the type
  (define-syntax-class xs+τ #:attributes ([fst 0] [rst 1])
    (pattern d:multi-decl
             #:with fst #'d.fst
             #:with (rst ...) (attribute d.rst))
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
    [(_ b:xs+τ . rst)
     (quasisyntax/loc this-syntax
       (Π b.fst #,(quasisyntax/loc this-syntax (→ b.rst ... . rst))))]))

;; Curried λ
;; ------------------------------------------------

; Currying.
(define-nested/R λ/c- λ)

; Support multi-declaration.
(define-syntax λ/c
  (syntax-parser
    [(_ d:multi-λ-decl ... e)
     (quasisyntax/loc this-syntax
       (λ/c- d.all ... ... e))]))

;; Curried application
;; ------------------------------------------------

(define-nested/L app/c #%app)
(define-nested/L app/eval/c app/eval)

;; Curried define
;; ------------------------------------------------

(define-syntax define/c
  (syntax-parser
    [(_ x:id e) (syntax/loc this-syntax (define x e))]
    [(_ (f:id d:multi-λ-decl ...) e)
     (syntax/loc this-syntax
       (define f (λ/c d ... e)))]))

;;; Pattern expanders for curried core forms.
;;; -----------------------------------------------------------

(begin-for-syntax
  ;; Curried Π
  ;; ------------------------------------------------

  (define-syntax ~Π/c
    (pattern-expander
     (syntax-parser
       [(_ t) #'t]
       [(_ (~var b x+τ) t_out) #'(~Π b t_out)]
       [(_ (~var b x+τ) (~and (~literal ...) ooo) t_out)
        #'(~and TMP
                (~parse ([b.x (~datum :) b.τ] ooo t_out)
                        (stx-parse/fold #'TMP (~Π b rst))))])))

  ;; Curried λ
  ;; ------------------------------------------------

  ; TODO: Copy pasta from Π/c
  (define-syntax ~λ/c
    (pattern-expander
     (syntax-parser
       [(_ t) #'t]
       [(_ (~var b x+τ) t_out) #'(~λ b t_out)]
       [(_ (~var b x+τ) (~and (~literal ...) ooo) t_out)
        #'(~and TMP
                (~parse ([b.x (~datum :) b.τ] ooo t_out)
                        (stx-parse/fold #'TMP (~λ b rst))))])))

  ;; Curried app
  ;; ------------------------------------------------

  (define (fold-plain-app stx)
    (let loop ([stx stx]
               [acc '()])
      (syntax-parse stx
        [((~literal #%plain-app) e1 a1)
         (loop #'e1 (cons #'a1 acc))]
        [last
         #`(last #,acc)])))

  (define-syntax ~#%app
    (pattern-expander
     (syntax-parser
       [(_ e)
        #`e]
       [(_ e a)
        #`(#%plain-app e a)]
       [(_ e a (~and (~literal ...) ooo))
        #'(~and TMP
                (~parse (e (a ooo))
                        (fold-plain-app #'TMP)))]))))

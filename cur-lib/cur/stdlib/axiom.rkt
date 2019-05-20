#lang racket/base
(provide define-axiom print-assumptions im-an-axiom print-extensions define-extension-type-rule
         (for-syntax axiom find-all-axioms))

(require syntax/parse/define
         racket/pretty
         turnstile/base turnstile/typedefs
         (for-syntax racket/base (only-in racket/list append-map)))

;; runtime support for axioms

(define ((im-an-axiom name) . _)
  (error name "encountered axiom during evaluation"))

;; -----------
;; define-axiom
;; -----------

(define-syntax-parser define-axiom
  [(_ name:id τ)
   #'(define-syntax name
       (make-variable-like-transformer
        (assign-type #'(#%plain-app im-an-axiom 'name)
                     #'τ)))])

;; -----------
;; print-assumptions
;; -----------

(begin-for-syntax
  (define-syntax-class axiom
    #:attributes (name)
    [pattern ({~literal #%plain-app}
              {~literal im-an-axiom}
              ({~literal quote} name:id))])

  ;; syntax -> [hash symbol => type]
  (define (find-all-axioms stx)
    (let find ([axioms (hasheq)]
               [stx stx])
      (syntax-parse stx
        [a:axiom
         (hash-update axioms
                      (syntax-e #'a.name)
                      values
                      (λ ()
                        (resugar-type (typeof stx))))]
        [(stuff ...)
         (for/fold ([ax axioms]) ([stx (in-list (attribute stuff))])
           (find ax stx))]
        [_ axioms]))))

(define-syntax-parser print-assumptions
  [(_ expr)
   #:with [(axiom-name . axiom-type) ...]
          (hash->list (find-all-axioms (expand/df #'expr)))
   #'(begin
       (printf "Axioms used by \"~s\":\n" 'expr)
       (printf " - ~s : ~s\n" 'axiom-name 'axiom-type)
       ...)])

(define-syntax define-extension-type-rule
  (syntax-parser
    [(_ (name . args) rule-part ... [(~datum ⊢) e (~datum ⇒) ty])
     #'(define-typed-syntax (name . args)
         rule-part ...
         [⊢ e (⇒ : ty) (⇒ extension #,this-syntax)
                       (⇒ extension-name name)])]))
     
(begin-for-syntax
  (define-syntax-class extension
    #:attributes (e name)
    [pattern e0
             #:when (syntax-property #'e0 'extension)
             #:with e (syntax-property #'e0 'extension)
             #:with name (syntax-property #'e0 'extension-name)])

  ;; syntax -> (listof (list term-stx type-stx name))
  (define (find-all-extensions stx)
    (let find ([extensions null]
               [stx stx])
      (syntax-parse stx
        [a:extension
         (cons (list #'a.e (resugar-type (typeof stx)) #'a.name) extensions)]
        [(stuff ...)
         (for/fold ([ex extensions]) ([stx (in-list (attribute stuff))])
           (find ex stx))]
        [_ extensions]))))

(define-syntax-parser print-extensions
  [(_ expr)
   #:with [(e ty name) ...] (find-all-extensions (expand/df #'expr))
   #`(begin
       (printf "Extensions used by \"~s\":\n" 'expr)
       #,@(stx-map
           (λ (e t name)
             #`(begin
                 (printf "[~a,~a] via rule ~a:\n"
                         #,(syntax-line e)
                         #,(syntax-column e)
                         '#,name)
                 (pretty-print '#,(resugar-type e))
                 (display " : ")
                 (pretty-print '#,t)))
           #'(e ...)
           #'(ty ...)
           #'(name ...)))])

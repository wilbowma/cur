#lang racket/base

(require
 racket/syntax
 syntax/parse
 "stxutils.rkt"
 "runtime-utils.rkt"
 (for-template
  "runtime.rkt"))

(provide
 cur-elab
 cur-elab/ctx)

#|
The Cur elaborator is also the type-checker, sort of.
Unlike Type Systems as Macros, we do not use syntax properties to stores types.
Syntax properties do not work well when storing identifiers, across module, or with compilation,
particularly.
They also use a *lot* of space, since each term and subterm has its type attached by the macros.

Instead, each macro elaborates into a runtime term implementing the term in Racket, which is annotated
enough to recompute its type in a simple function.
This means the type system is not easily extended by adding macros; we would also need to add a case
to the get-type function.
This could be done using an extensible function, simulated with parameters perhaps.
However, we don't really want the type system to be extensible since we desire a small trusted core.
|#

; Evaluation

; Expects a Cur term and produces a cur-runtime-term?, or raises an type error.
(define cur-elab local-expand-expr)

(define (cur-elab/ctx syn ctx)
  (call-with-ctx
   ctx
   (lambda ()
     (define intdef (syntax-local-make-definition-context))
     (syntax-local-bind-syntaxes (map car ctx) #f intdef)
     (local-expand syn 'expression null intdef))))

(module+ test
  (require
   (for-syntax
    chk
    racket/base
    (submod "..")
    "alpha-equiv.rkt"
    "stxutils.rkt")
   "runtime.rkt"
   (submod "runtime.rkt" test))

  (begin-for-syntax
    (define equal-syn? cur-α-equal?)
    (chk
     ; cur-elab tests
     #:eq equal-syn? (cur-elab #'(cur-Type 0)) #'(#%plain-app cur-Type '0)
     #:eq equal-syn? (cur-elab #'(cur-λ (cur-Type 0) (lambda (x) x))) #'(#%plain-app cur-λ (#%plain-app cur-Type '0) (#%plain-lambda (x) x))
     #:eq equal-syn? (cur-elab #'(Nat)) #'(#%plain-app Nat)
     #:eq equal-syn? (cur-elab #'(cur-apply (cur-λ (cur-Type 0) (lambda (x) x)) (z)))
     #'(#%plain-app cur-apply (#%plain-app cur-λ (#%plain-app cur-Type '0) (#%plain-lambda (x) x))
                    (#%plain-app z))

     )))

;; TODO: These will be implemented in a separate module
#;(define-syntax (cur-λ syn)
    (syntax-parse syn
      [(_ (x : type) body)
       #:with type-lab (cur-elab #'type)
       #:with x-type (format-id #'x "~a-type" #'x)
       #:with x-internal (fresh #'x)
       #`(lambda (x-internal)
           (let-syntax ([x-type (lambda (x) type-elab)])
             (let-syntax ([x (make-rename-transformer
                              (syntax-property #'x-internal 'type #'x-type #t))])
               body)))]))

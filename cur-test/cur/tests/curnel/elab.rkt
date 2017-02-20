#lang racket/base

(require
 (for-syntax
  chk
  racket/base
  cur/curnel/racket-impl/elab
  cur/curnel/racket-impl/equiv
  cur/curnel/racket-impl/stxutils)
 cur/curnel/racket-impl/runtime
 "runtime.rkt")

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

   ))

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

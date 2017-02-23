#lang racket/base

(require
 (for-syntax
  chk
  racket/base
  cur/curnel/racket-impl/equiv)
 (only-in cur/curnel/racket-impl/type-check cur-elab)
 cur/curnel/racket-impl/runtime
 "runtime.rkt")
(begin-for-syntax
  (chk
   ; cur-α-equal? tests
   #:t (cur-α-equal? #'(#%plain-app cur-Type '0) #'(#%plain-app cur-Type '0))
   #:t (cur-α-equal? #'(#%plain-app cur-Type '1) #'(#%plain-app cur-Type '1))
   #:! #:t (cur-α-equal? #'(#%plain-app cur-Type '1) #'(#%plain-app cur-Type '0))
   #:! #:t (cur-α-equal? #'(#%plain-app cur-Type '0) #'(#%plain-app cur-Type '1))
   #:t (cur-α-equal? #'Nat #'Nat)
   #:! #:t (cur-α-equal? #'Nat #'z)
   #:t (cur-α-equal? #'z #'z)
   #:t (cur-α-equal? #'(#%plain-app cur-apply s z) #'(#%plain-app cur-apply s z))
   #:t (cur-α-equal? #'(#%plain-app cur-λ Nat (#%plain-lambda (x) x))
                     #'(#%plain-app cur-λ Nat (#%plain-lambda (y) y)))
   #:t (cur-α-equal? #'(#%plain-app cur-Π Nat (#%plain-lambda (x) Nat))
                     #'(#%plain-app cur-Π Nat (#%plain-lambda (y) Nat)))

   ;; β/ι/δ equality
   #:t (cur-equal? (cur-elab #'(cur-Type 0)) (cur-elab #'(cur-Type 0)))
   #:! #:t (cur-equal? (cur-elab #'(cur-Type 0)) (cur-elab #'(cur-Type 1)))
   #:t (cur-equal? (cur-elab #'(cur-apply (cur-λ (cur-Type 1) (lambda (x) x))
                                          (cur-Type 0)))
                   (cur-elab #'(cur-Type 0)))

   ;; subtyping
   #:t (cur-subtype? (cur-elab #'(cur-Type 0)) (cur-elab #'(cur-Type 1)))
   #:! #:t (cur-subtype? (cur-elab #'(cur-Type 1)) (cur-elab #'(cur-Type 0)))))

#lang racket/base

(require
 cur/curnel/racket-impl/runtime
 "runtime.rkt"
 (for-syntax
  racket/base
  chk
  cur/curnel/racket-impl/alpha-equiv
  cur/curnel/racket-impl/runtime-utils))
(begin-for-syntax
  (chk
   #:eq cur-α-equal? (type-of-id #'two) #'(#%plain-app Nat)
   #:eq cur-α-equal? (type-of-constant #'Nat '()) #'(#%plain-app cur-Type '0)
   #:eq cur-α-equal? (type-of-constant #'z '()) #'(#%plain-app Nat)
   #:eq cur-α-equal? (call-with-ctx
                      (list (cons #'x #'(#%plain-app Nat)))
                      (lambda () (type-of-id #'x))) #'(#%plain-app Nat)))

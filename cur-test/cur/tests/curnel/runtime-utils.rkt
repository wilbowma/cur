#lang racket/base

(require
 cur/curnel/racket-impl/runtime
 "runtime.rkt"
 (for-syntax
  racket/base
  chk
  cur/curnel/racket-impl/environment
  cur/curnel/racket-impl/equiv
  cur/curnel/racket-impl/runtime-utils))
(begin-for-syntax
  (chk
   #:eq cur-α-equal? (type-of-id #'two) #'Nat
   #:eq cur-α-equal? (type-of-id #'Nat) #'(#%plain-app cur-Type '0)
   #:eq cur-α-equal? (type-of-id #'z) #'Nat
   #:eq cur-α-equal? (call-with-ctx
                      (list (cons #'x #'Nat))
                      (lambda () (type-of-id #'x))) #'Nat))

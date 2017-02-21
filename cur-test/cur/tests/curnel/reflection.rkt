#lang racket/base

(require
 (for-syntax
  chk
  racket/base
  (except-in cur/curnel/racket-impl/equiv cur-equal?)
  cur/curnel/racket-impl/stxutils
  cur/curnel/racket-impl/reflection)
 cur/curnel/racket-impl/type-check
 cur/curnel/racket-impl/runtime
 "runtime.rkt")

(begin-for-syntax
  (chk
   #:eq cur-equal? (cur-type-infer #'a #:local-env (list (cons #'a #'(cur-Type 0))))
   #'(typed-Type 0)
   #:x (cur-type-infer #'a) "undefined"
   #:x (cur-type-infer #'a #:local-env (list (cons #'a #'(typed-app
                                                          (cur-λ (cur-Type 0) (#%plain-lambda (x) x))
                                                          (cur-Type 0))))) "Expected term of type"))

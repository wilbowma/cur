#lang racket/base

(require
 (for-syntax
  chk
  racket/base
  cur/curnel/racket-impl/equiv
  cur/curnel/racket-impl/stxutils)
 cur/curnel/racket-impl/type-check
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
   ;; TODO syntax class tests

   ;; typed macros
   #:eq equal-syn? (cur-elab #'(typed-Type 0)) (cur-elab #'(cur-Type 0))
   #:x (cur-elab #'(typed-Type -1)) "expected exact-nonnegative-integer"
   #:eq equal-syn? (cur-elab #'(typed-Π (x : (typed-Type 0)) (typed-Type 0)))
   (cur-elab #'(cur-Π (cur-Type 0) (#%plain-lambda (x) (cur-Type 0))))
   #:x (cur-elab #'(typed-Π (x : y) (typed-Type 0))) "unbound identifier"
   #:x (cur-elab #'(typed-Π (x : (cur-λ (cur-Type 0) (#%plain-lambda (x) x))) (typed-Type 0)))
   "Expected a kind"
   #:x (cur-elab #'(typed-Π (x : (typed-Type 0)) (cur-λ (cur-Type 0) (#%plain-lambda (x) x))))
   "Expected a kind"
   #:eq equal-syn? (cur-elab #'(typed-λ (x : (typed-Type 1)) x))
   (cur-elab #'(cur-λ (cur-Type 1) (#%plain-lambda (x) x)))
   #:eq equal-syn? (cur-elab #'(typed-app (cur-λ (cur-Type 1) (#%plain-lambda (x) x)) (cur-Type 0)))
   (cur-elab #'(cur-apply (cur-λ (cur-Type 1) (#%plain-lambda (x) x)) (cur-Type 0)))
   #:t (cur-elab #'(typed-Π (x : (typed-Type 0))
                            (typed-app (cur-λ (cur-Type 1) (#%plain-lambda (x) x))
                                       (cur-Type 0))))
   #:t (local-expand #'(typed-axiom True : (typed-Type 0)) 'top-level '())
   #:x (local-expand #'(typed-axiom True : (typed-λ (x : (typed-Type 0)) x)) 'top-level '()) "Expected an axiom telescope"

   #:t (cur-elab #'(typed-elim (z) (typed-λ (y : (Nat)) (Nat)) (z) (typed-λ (n : (Nat))
                                                                            (typed-λ (ih : (Nat))
                                                                                     ih))))
   #:x (cur-elab #'(typed-elim (typed-Type 0) (typed-λ (y : (Nat)) (Nat)) (z) (typed-λ (n : (Nat))
                                                                          (typed-λ (ih : (Nat))
                                                                                   ih))))
   "Expected target to be a constant"
   #:x (cur-elab #'(typed-elim (z) (cur-Type 0) (z) (typed-λ (n : (Nat))
                                                             (typed-λ (ih : (Nat))
                                                                      ih))))
   #rx"Expected type .* while checking motive"
   #:x (cur-elab #'(typed-elim (z) (typed-λ (x : (cur-Type 0)) x)
                               (z) (typed-λ (n : (Nat))
                                            (typed-λ (ih : (Nat))
                                                     ih))))
   #rx"Expected type .* while checking motive"
   #:x (cur-elab #'(typed-elim (z) (typed-λ (x : (cur-Type 0)) x) (z)))
   "Expected one method for each constructor, but found 2 constructors and 1 branch"
   #:t (local-expand #'(typed-data (True) : 0 (typed-Type 0)
                                   ((I) : (True)))
                     'top-level
                     '())))

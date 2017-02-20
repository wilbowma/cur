#lang racket/base

(require
 (for-syntax
  chk
  racket/base
  cur/curnel/racket-impl/type-reconstruct
  cur/curnel/racket-impl/eval
  cur/curnel/racket-impl/elab
  cur/curnel/racket-impl/stxutils
  cur/curnel/racket-impl/equiv)
 cur/curnel/racket-impl/runtime
 "runtime.rkt")

(define-syntax (infer-type stx)
  (syntax-case stx ()
    [(_ expr)
     (get-type #'expr)]))

(require (for-syntax syntax/parse))
(define-syntax (surface-λ stx)
  (syntax-parse stx
    #:datum-literals (:)
    [(_ (x : t) b)
     #:with type (cur-elab #'t)
     #`(cur-λ type
              (#%plain-lambda (x) #,(cur-elab/ctx #'b (list (cons #'x #'type)))))]))

(begin-for-syntax
  (define get-type/elab (compose get-type local-expand-expr))
  (define (equal-syn/elab? e1 e2)
    (cur-α-equal? (local-expand-expr e1) (local-expand-expr e2)))

  (chk
   ; get-type tests
   #:eq equal-syn/elab? (get-type/elab #'(cur-Type 0)) #'(cur-Type '1)
   #:eq equal-syn/elab? (get-type/elab #'(cur-Type 1)) #'(cur-Type '2)
   #:eq equal-syn/elab? (get-type/elab #'(Nat)) #'(cur-Type 0)
   #:eq equal-syn/elab? (get-type/elab #'(z)) #'(Nat)
   ;; TODO: Predicativity rules have changed.
   #:eq equal-syn/elab? (get-type/elab #'(cur-Π (cur-Type 0) (#%plain-lambda (x) (cur-Type 0)))) #'(cur-Type '1)
   #:eq equal-syn/elab? (get-type/elab #'(cur-λ (cur-Type 0) (#%plain-lambda (x) x)))
   #'(cur-Π (cur-Type '0) (#%plain-lambda (x) (cur-Type '0)))
   #:eq equal-syn/elab?
   (get-type/elab #'(cur-λ (cur-Type 1)
                           (#%plain-lambda (y)
                                           (cur-λ (cur-Type 0) (#%plain-lambda (x) x)))))
   #'(cur-Π (cur-Type '1) (#%plain-lambda (y) (cur-Π (cur-Type '0) (#%plain-lambda (x) (cur-Type '0)))))
   ; Tests that nested contexts work fine.
   #:eq equal-syn/elab?
   (get-type/elab #'(cur-λ (cur-Type 1)
                           (#%plain-lambda (y)
                                           (cur-λ (cur-Type 0) (#%plain-lambda (x) y)))))
   #'(cur-Π (cur-Type '1) (#%plain-lambda (y) (cur-Π (cur-Type '0) (#%plain-lambda (x) (cur-Type '1)))))
   ; Tests that reflection inside the Cur elaborator works fine
   #:eq equal-syn/elab?
   (get-type/elab #'(surface-λ (y : (cur-Type 1))
                               (cur-λ (infer-type y) (#%plain-lambda (x) y))))
   #'(cur-Π (cur-Type '1) (#%plain-lambda (y) (cur-Π (cur-Type '1) (#%plain-lambda (x) (cur-Type '1)))))
   ; Tests application
   #:eq equal-syn/elab? (get-type/elab #'plus) #'(cur-Π (Nat) (#%plain-lambda (n1)
                                                                              (cur-Π (Nat)
                                                                                     (#%plain-lambda
                                                                                      (n2)
                                                                                      (Nat)))))
   #:eq equal-syn/elab?
   (get-type/elab #'(cur-apply plus (z)))
   #'(cur-Π (Nat) (#%plain-lambda (y) (Nat)))
   #:eq equal-syn/elab?
   (get-type/elab #'(cur-apply (cur-apply plus (z)) (s (z))))
   #'(Nat)
   ; Tests elim
   #:eq equal-syn/elab? (cur-eval (get-type/elab #`(cur-apply #,(cur-eval #'plus) (z))))
   #'(cur-Π (Nat) (#%plain-lambda (y) (Nat)))
   ; TODO: Missing dependent application and elim tests
   ))

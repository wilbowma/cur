#lang racket/base

(require
 racket/syntax
 syntax/parse
 "stxutils.rkt"
 "eval.rkt"
 "runtime-utils.rkt"
 (for-template
  "runtime.rkt"))

(provide
 get-type
 get-type/ctx)

;; Takes a cur-runtime-term? and computes it's type, as a cur-runtime-term?.
(define (get-type e)
  (syntax-parse e
    [e:cur-runtime-identifier
     (type-of-id #'e.name)]
    [e:cur-runtime-constant
     (type-of-constant #'e.name (attribute e.rand-ls))]
    [e:cur-runtime-universe
     #`(#%plain-app cur-Type (quote #,(add1 (attribute e.level))))]
    [e:cur-runtime-pi
     ;; TODO: Shouldn't this be the max of the annotation and the result?
     (get-type/ctx #'e.result (list (cons #'e.name #'e.ann)))]
    [e:cur-runtime-lambda
     #`(#%plain-app cur-Π e.ann (#%plain-lambda (e.name) #,(get-type/ctx #'e.body (list (cons #'e.name #'e.ann)))))]
    [e:cur-runtime-app
     #:with t1:cur-runtime-pi (get-type #'e.rator)
     (subst #'e.rand #'t1.name #'t1.result)]
    [e:cur-runtime-elim
     #:with D:cur-runtime-constant (get-type #'e.target)
     (cur-apply* #'e.motive (append (attribute D.rand-ls) (list #'e.target)))]))

(define (get-type/ctx syn ctx)
  (call-with-ctx ctx (lambda () (get-type syn))))

(module+ test
  (require
   (for-syntax
    chk
    racket/base
    (submod "..")
    "eval.rkt"
    "elab.rkt"
    "stxutils.rkt"
    "alpha-equiv.rkt")
   "runtime.rkt"
   (submod "runtime.rkt" test))

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
     )))

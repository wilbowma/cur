#lang racket/base

(require
 racket/syntax
 syntax/parse
 "runtime-utils.rkt"
 "stxutils.rkt"
 (for-template
  "runtime.rkt"))

(provide cur-eval)

; Expects a cur-runtime-term? and returns a cur-runtime-term?
(define (cur-eval syn)
  (let cur-eval ([syn syn])(syntax-parse syn
    [_:cur-runtime-universe syn]
    [e:cur-runtime-constant
     #`(#%plain-app e.name #,@(map cur-eval (attribute e.rand-ls)))]
    [_:cur-runtime-identifier
     ;; NB: Does syn has a phase i+1 binding?
     #:when (identifier-binding syn (add1 (syntax-local-phase-level)))
     #:do [(define maybe-def (syntax-local-eval (identifier-info-delta-def (syntax-local-eval syn))))]
     (or (and maybe-def (cur-eval maybe-def)) syn)]
    [_:cur-runtime-identifier
     #:when (not (identifier-binding syn (add1 (syntax-local-phase-level))))
     syn]
    [e:cur-runtime-pi
     #`(#%plain-app cur-Π #,(cur-eval #'e.ann) (#%plain-lambda (e.name) #,(cur-eval #'e.result)))]
    [e:cur-runtime-app
     #:with a (cur-eval #'e.rand)
     (syntax-parse (cur-eval #'e.rator)
       [f:cur-runtime-lambda
        (cur-eval (subst #'a #'f.name #'f.body))]
       [e1-
        #`(#%plain-app cur-apply e1- a)])]
    [e:cur-runtime-elim
     #:with target:cur-runtime-constant #'e.target
     #:do [(define info (syntax-local-eval #'target.name))]
     #:do [(define recursive-index-ls (constant-info-recursive-index-ls info))]
     ;; TODO PERF: use unsafe version of list operators and such for internal matters
     ;; TODO PERF: list-ref; could we make it a vector?
     (cur-eval
      (cur-apply*
       (list-ref (attribute e.method-ls) (constant-info-constructor-index info))
       (append (attribute target.rand-ls)
                 (for/fold ([m-args '()])
                           ([arg (attribute target.rand-ls)]
                            [i (in-naturals (constant-info-param-count info))]
                            ;; TODO PERF: memq in a loop over numbers...
                            #:when (memq i recursive-index-ls))
                   (cons #`(#%plain-app cur-elim #,arg e.motive #,@(attribute e.method-ls)) m-args)))))]
    [e:cur-runtime-elim
     #`(#%plain-app cur-elim #,(cur-eval #'e.target) #,(cur-eval #'e.motive) #,@(map cur-eval (attribute e.method-ls)))]
    [e:cur-runtime-lambda
     #`(#%plain-app cur-λ e.ann (#%plain-lambda (e.name) #,(cur-eval #'e.body)))]
    [_ (raise-syntax-error 'cur-eval (format "Something has gone horribly wrong: ~a" (syntax->datum syn)) syn)])))


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

    (chk
     ; cur-eval tests
     #:eq cur-α-equal?
     (cur-eval (local-expand-expr #'(cur-Type 0)))
     (local-expand-expr #'(cur-Type '0))
     #:eq cur-α-equal?
     (cur-eval (local-expand-expr #'two))
     (local-expand-expr #'(s (s (z))))
     #:eq cur-α-equal?
     (cur-eval (local-expand-expr #'(cur-apply (cur-λ (cur-Type 0) (lambda (x) x)) (z))))
     #'(#%plain-app z)
     #:eq cur-α-equal?
     (cur-eval (local-expand-expr #'(cur-apply (cur-apply plus (z)) (s (z)))))
     (local-expand-expr #'(s (z))))))

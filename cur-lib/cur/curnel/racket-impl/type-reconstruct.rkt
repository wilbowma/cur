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

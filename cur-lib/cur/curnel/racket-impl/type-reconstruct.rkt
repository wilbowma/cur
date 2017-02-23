#lang racket/base

#|
 | Reconstruct a type from a fully expanded term.
 |#

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

(require racket/trace)
;; Takes a cur-runtime-term? and computes it's type, as a cur-runtime-term?.
(trace-define (get-type syn)
  (syntax-parse syn
    [e:cur-runtime-identifier
     (type-of-id #'e.name)]
    #;[e:cur-runtime-constant
     (type-of-constant #'e.name (attribute e.rand-ls))]
    [e:cur-runtime-universe
     (make-cur-runtime-universe syn (add1 (attribute e.level)))]
    [e:cur-runtime-pi
     ;; TODO: Shouldn't this be the max of the annotation and the result?
     (get-type/ctx #'e.result (list (cons #'e.name #'e.ann)))]
    [e:cur-runtime-lambda
     (make-cur-runtime-pi syn #'e.ann #'e.name (get-type/ctx #'e.body (list (cons #'e.name #'e.ann))))]
    [e:cur-runtime-app
     #:with t1:cur-runtime-pi (get-type #'e.rator)
     (subst #'e.rand #'t1.name #'t1.result)]
    [e:cur-runtime-elim
     #:with D:cur-runtime-constant (get-type #'e.target)
     (cur-apply* syn #'e.motive (append (attribute D.index-rand-ls) (list #'e.target)))]))

(trace-define (get-type/ctx syn ctx)
  (call-with-ctx ctx (lambda () (get-type syn))))

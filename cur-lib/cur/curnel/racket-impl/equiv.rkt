#lang racket/base

(require
 "alpha-equiv.rkt"
 "eval.rkt"
 "stxutils.rkt"
 syntax/parse
 (for-template
  "runtime.rkt"))

(provide
 cur-equal?
 cur-subtype?)

(define (cur-equal? t1 t2 (fail (lambda _ #f)))
  (cur-α-equal? (cur-eval t1) (cur-eval t2) fail))

(define (cur-subtype? t1 t2 (fail (lambda _ #f)))
    (let cur-subtype? ([t1 (cur-eval t1)]
                       [t2 (cur-eval t2)])
      (syntax-parse #`(#,t1 #,t2)
        [(A:cur-runtime-universe B:cur-runtime-universe)
         (or (<= (attribute A.level) (attribute B.level)) (fail t1 t2))]
        [(e1:cur-runtime-pi e2:cur-runtime-pi)
         (and (cur-α-equal? #'e1.ann #'e2.ann fail)
              (cur-subtype? #'e1.result (subst #'e1.name #'e2.name #'e2.result)))]
        [(e1 e2)
         (cur-α-equal? #'e1 #'e2 fail)])))

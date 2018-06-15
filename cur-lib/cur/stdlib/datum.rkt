#lang s-exp "../main.rkt"

(provide #%datum)

(begin-for-syntax
  (provide default-datum current-datum)
  (define (default-datum syn f)
    (raise-syntax-error
     'invalid-datum-error
     "Could not find datum parser"
     syn))
  (define current-datum
    (make-parameter
     default-datum
     (lambda (f)
       (let ([old-f (current-datum)])
         (case-lambda
           [(syn) (f syn old-f)]
           [(syn f)
            (f syn f)]))))))

(define-syntax (#%datum syn)
  (syntax-parse syn
    [(_ . syn)
     ((current-datum) #'syn)]))

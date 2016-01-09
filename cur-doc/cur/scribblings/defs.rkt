#lang racket/base

(require
 scribble/base
 scribble/manual
 racket/sandbox)
(provide (all-defined-out))

(define (todo . ls)
  (apply margin-note* "TODO: " ls))

(define (gtech . x)
  (apply tech x #:doc '(lib "scribblings/guide/guide.scrbl")))

(define (curnel-sandbox init-string)
  (parameterize ([sandbox-output 'string]
                 [sandbox-error-output 'string]
                 ;; TODO: Probs a bad idea
                 [sandbox-eval-limits #f]
                 [sandbox-memory-limit #f])
    (make-module-evaluator
     (format "#lang cur~n~a" init-string))))

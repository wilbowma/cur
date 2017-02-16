#lang racket/base
(require
 (for-syntax
  racket/base
  syntax/parse
  racket/syntax)
 syntax/parse
 syntax/parse/experimental/reflect)

(provide (all-defined-out))

(define (local-expand-expr x) (local-expand x 'expression null))

(define (reified-syntax-class->pred stxclass)
  (lambda (expr)
    (syntax-parse expr
      [(~reflect _ (stxclass)) #t]
      [_ #f])))

(define-syntax-rule (syntax-class->pred id)
  (reified-syntax-class->pred (reify-syntax-class id)))

(define-syntax (define-syntax-class/pred stx)
  (syntax-parse stx
    [(_ name:id expr ...)
     #:with pred? (format-id #'name "~a?" #'name)
     #`(begin
         (define-syntax-class name expr ...)
         (define pred? (syntax-class->pred name)))]))

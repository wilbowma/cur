#lang racket/base
(require
 (for-syntax
  racket/base
  syntax/parse
  racket/syntax)
 (for-template
  racket/base)
 syntax/parse
 racket/syntax
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

(define (subst v x syn)
  (syntax-parse syn
    [y:id
     #:when (free-identifier=? syn x)
     v]
    [(e ...)
     (map (lambda (e) (subst v x e)) (attribute e))]
    [_ syn]))

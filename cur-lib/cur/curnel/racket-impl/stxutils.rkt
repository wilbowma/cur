#lang racket/base
(require
 (for-syntax
  racket/base
  syntax/parse
  racket/syntax)
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

;; Try to make readable fresh names.
(define fresh
  (let ([n 0])
    (lambda ([x #f])
      (set! n (add1 n))
      (or (and x (syntax-property x 'reflected-name))
          (format-id x "~a~a" (or x 'x) n
                     #:source x
                     #:props (and x (syntax-property x 'reflected-name x #t)))))))

(define-syntax (let*-syntax syn)
  (syntax-case syn ()
    [(_ () e)
     #`e]
    [(_ ([x e] r ...) body)
     #`(let-syntax ([x e])
         (let*-syntax (r ...) body))]))

(define-syntax-class in-let-values #:attributes (body)
  #:literals (let-values)
  (pattern (let-values () e:in-let-values)
           #:attr body #'e.body)

  (pattern body))

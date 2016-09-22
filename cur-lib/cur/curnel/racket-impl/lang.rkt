#lang racket/base
(require
 (for-syntax
  racket/base
  syntax/parse))

(provide
 (rename-out
  [cur-type Type]
  [cur-define define]
  [cur-λ λ]
  [cur-Π Π])
 #%datum
 ;(struct-out Type)
 #%module-begin
 (for-syntax
  #%datum))

(begin-for-syntax
  (require racket/trace)
  (define (cur-local-expand e)
    (local-expand e 'expression '()))

  ;; Helpers; based on Types as Macros
  (define (set-type e τ)
    (syntax-property e 'type τ))

  (define (get-type e)
    (syntax-property (cur-local-expand e) 'type))

  (define (erase-type e)
    (cur-local-expand e))

  #;(define (type-equal? τ₁ τ₂)
    #;(or (free-identifier=? τ₁ τ₂) ))

  ;; syntax classes
  #;(define-syntax-class cur-syntax
    )
  (define-syntax-class cur-type-level-annotation
    (pattern i:nat))

  (define-syntax-class cur-expr
    (pattern e:expr #;cur-syntax
             #:fail-unless (get-type (attribute e))
             (raise-syntax-error 'core-type-error "Could not infer any type for term"
                                 (attribute e))))
  )

(define-syntax (cur-define syn)
  (syntax-parse syn
    [(_ name:id body:cur-expr)
     #`(define #,(set-type #'name (get-type #'body)) #,(erase-type #'body))]))

#;(define-syntax cur-module-begin)

#;(define-syntax (cur-data syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(data name:id : params:nat type:cur-expr
           (c:id : c-type:cur-expr)
           ...)
     ]))

(struct Type (level) #:transparent)

(define-syntax (cur-type syn)
  (syntax-parse syn
    [(_ i:cur-type-level-annotation)
     (set-type (quasisyntax/loc syn (Type i))
               (quasisyntax/loc syn (cur-type #,(add1 (eval #'i)))))]))

(define-syntax (cur-var syn)
  (syntax-parse syn
    [(_ x:cur-expr)
     #`(#%variable-reference x)]))

(struct Π ())
(define-syntax (cur-Π syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_ (x:id : t₁:cur-expr) e:expr #;cur-syntax )
     #:attr t₂
     (with-syntax ([x (set-type (attribute x) (attribute t₁))])
       (get-type (attribute e)))
     #:fail-unless (attribute t₂)
     (raise-syntax-error 'core-type-error
                         "Could not infer any type"
                         (attribute e))
     (with-syntax ([x (set-type (attribute x) (attribute t₁))])
       (set-type
        (quasisyntax/loc syn (Π))
        (attribute t₂)))]))

(define-syntax (cur-λ syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_ (x:id : t₁:cur-expr) e:expr #;cur-syntax )
     #:attr t₂
     (get-type
      #`(let-syntax ([x #,(set-type (attribute x) (attribute t₁))])
          e))
     #:fail-unless (attribute t₂)
     (raise-syntax-error 'core-type-error
                         "Could not infer any type"
                         (attribute e))
     (with-syntax ([x (set-type (attribute x) (attribute t₁))])
       (set-type
        (quasisyntax/loc syn (lambda (x) #,(erase-type (attribute e))))
        (quasisyntax/loc syn (cur-Π (x : t₁) t₂))))]))
#;(define-syntax cur-Π)
#;(define-syntax cur-app)
#;(define-syntax cur-elim)

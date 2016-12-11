#lang racket

(begin-for-syntax
  (require
   racket
   racket/syntax
   racket/dict
   syntax/id-table)

  (define def-dict (make-free-id-table)))

(define-for-syntax (typed-identifier x type)
  (format-id x "~a1" x #:props (syntax-property
                                (syntax-property x 'type type #t)
                                'not-free-identifier=? #t #t)))

(define-syntax (define^ syn)
  (syntax-case syn (:)
    [(_ id : type body)
     (with-syntax ([x (typed-identifier #'id #'type)])
       (dict-set! def-dict #'x #'body)
       #`(begin
           (define x body)
           (define-syntax id
             (make-rename-transformer #'x))))]))

(define-for-syntax (type-eval e)
  (dict-ref def-dict e e))

(define-for-syntax (type-equal? e1 e2)
  (let ([x (type-eval e1)]
        [y (type-eval e2)])
    (displayln (identifier-binding x))
    (displayln (identifier-binding y))
    (free-identifier=? x y)))

(define-for-syntax (my-expand syn)
  (local-expand syn 'expression null))

(define-syntax (:: syn)
  (syntax-case syn ()
    [(_ e t)
     (unless (type-equal? (syntax-property (my-expand #'e) 'type) (my-expand #'t))
       (error "Type error"))
     #'(void)]))

(define (Type) (error "Type"))
(define (True) (error "True"))

(define^ T : True (void))

(define^ thm : (Type) True)

(define^ pf : True T)

(:: pf thm)

(provide pf thm ::)

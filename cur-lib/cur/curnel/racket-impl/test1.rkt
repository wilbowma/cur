#lang racket

(begin-for-syntax
  (require
   racket
   racket/syntax
   racket/dict
   syntax/parse
   syntax/id-table)

  (define def-dict (make-free-id-table)))

(define-syntax (define-type syn)
  (syntax-case syn ()
    [(_ e)
     #`(begin
         (struct e ()))]))

(define-for-syntax (typed-identifier x type)
  (format-id x "~a1" x #:props (syntax-property
                                (syntax-property x 'type type #t)
                                'not-free-identifier=? #t #t)))

(define-syntax (define-constr syn)
  (syntax-case syn (:)
    [(_ id : type)
     (with-syntax ([x (typed-identifier #'id #'type)])
       #`(begin
           (struct x ())
           (define-syntax id
             (make-rename-transformer #'x))))]))

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
  (syntax-parse e
    [x:id
     #:attr def (dict-ref def-dict #'x #f)
     #:when (attribute def)
     #'def]
    [_ e]))

(define-for-syntax (type-equal? e1 e2)
  (let ([x (type-eval e1)]
        [y (type-eval e2)])
    (displayln (identifier-binding x))
    (displayln (identifier-binding y))
    (free-identifier=? x y)) )

(define-for-syntax (my-expand syn)
  (local-expand syn 'expression null))

(define-syntax (:: syn)
  (syntax-case syn ()
    [(_ e t)
     (unless (type-equal? (syntax-property (my-expand #'e) 'type) (my-expand #'t))
       (error "Type error"))
     #'(void)]))

(define (Type) (error "Can't use Type at runtime"))

(define-type True)

(define-constr T : True)

(define^ thm : (Type) True)

(define^ pf : True T)

(:: pf thm)

(provide pf thm ::)

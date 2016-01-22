#lang s-exp "../cur.rkt"
(require
  "nat.rkt"
  "bool.rkt"
  "sugar.rkt"
  (for-syntax
    racket/syntax
    racket/dict
    racket/list))
(provide (for-syntax typeclasses) typeclass impl)

;;; NB: This module is extremely unhygienic.
#| TODO:
 | These typeclasses are kind of broken. There are no typeclass constraints so....
 |#
(begin-for-syntax
  #| TODO:
   | A compile-time hash table is stupid. Use something akin to struct
   | type properties to associate method with the identifier for the type,
   | perhaps syntax properties.
   |#
  (define typeclasses (make-hash)))
(define-syntax (typeclass syn)
  (syntax-case syn (: Type)
    [(_ (class (param : Type)) (name : type) ...)
     #`(begin
         #,@(for/list ([name (syntax->list #'(name ...))]
                       [type (syntax->list #'(type ...))])
              (dict-set!
                (dict-ref! typeclasses (syntax->datum #'class) (make-hash))
                (syntax->datum name)
                #`(lambda (param : Type) #,type))
              #| NB:
               | Due to implementation below, methods on typeclass must dispatch on type of first
               | argument. Also prevents currying/point-free style. Maybe type system hooks to get
               | "type of current hole" would help? Related: tactics/base.rkt
               |#
              #`(define-syntax (#,name syn)
                  (syntax-case syn ()
                    [(_ arg args (... ...))
                     #`(#,(format-id syn "~a-~a" '#,name (type-infer/syn #'arg))
                        arg
                        args (... ...))]))))]))

(define-syntax (impl syn)
  #| TODO:
   | Need racket-like define so I can extract name/args/defs.
   |#
  (define (process-def def)
    (syntax-case def (define)
      [(define (name (a : t) ...) body ...)
       (values (syntax->datum #'name) #'(lambda (a : t) ... body ...))]
      [(define name body)
       (values (syntax->datum #'name) #'body)]))
  (syntax-case syn ()
    [(_ (class param) defs ...)
     #`(begin
         #,@(for/list ([def (syntax->list #'(defs ...))])
              (let-values ([(name body) (process-def def)])
                (unless (type-check/syn?
                          body
                          #`(#,(dict-ref
                                 (dict-ref typeclasses (syntax->datum #'class))
                                 name)
                             param))
                  (raise-syntax-error
                    'impl
                    ;"Invalid implementation of typeclass ~a. Must have type ~a."
                    "Invalid implementation of typeclass."
                    #'class
                    #'body))
                #`(define #,(format-id syn "~a-~a" name #'param)
                    #,body))))]))

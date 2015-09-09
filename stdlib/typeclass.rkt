#lang s-exp "../redex-curnel.rkt"
(require
  "nat.rkt"
  "bool.rkt"
  "sugar.rkt"
  (for-syntax
    racket/syntax
    racket/dict
    racket/list))

(begin-for-syntax
  ;; NB: Need this thing to be global w.r.t. the runtime, i.e., exist once
  ;; NB: and for all no matter how many things import typeclass, i.e., not
  ;; NB: local to this module
  (define bla (make-hash)))
(define-syntax (typeclass syn)
  (syntax-case syn (: Type)
    [(_ (class (param : Type))
        (name : type) ...)
     ;; TODO: Doing 2 loops over names, stop being stupid
     (hash-set! bla (syntax->datum #'class)
                (for/list ([p (syntax->list #'((name : type) ...))])
                  (let ([p (syntax->list p)])
                    `(,(syntax->datum (first p)) . ,#`(lambda (param : Type) #,(third p))))))
     #`(begin
         #,@(for/list ([name (syntax->list #'(name ...))])
              ;; NB: Due to implementation below, methods on typeclass
              ;; NB: must dispatch on type of first argument.
              ;; NB: Also prevents currying/point-free style.
              ;; NB: Maybe type system hooks to get "type of current hole"
              ;; NB: would help?
              #`(define-syntax (#,name syn)
                  (syntax-case syn ()
                    [(_ arg args (... ...))
                     #`(#,(format-id syn "~a-~a" '#,name (type-infer/syn #'arg))
                        arg
                        args (... ...))]))))]))

(define-syntax (impl syn)
  (define (process-def def)
    (syntax-case def (define)
      [(define (name (a : t) ...) body ...)
       (values #'name #'(lambda* (a : t) ... body ...))]
      [(define name body)
       (values #'name #'body)]))
  (syntax-case syn ()
    [(_ (class param)
        ;; TODO: Need racket-like define so I can extract
        ;; TODO: name/args/defs, or use local-expand or something
        defs ...)
     #`(begin
       #,@(for/list ([def (syntax->list #'(defs ...))])
            (let-values ([(name body) (process-def def)])
              (unless (type-check/syn? body #`(#,(dict-ref
                                                   (dict-ref bla (syntax->datum #'class))
                                                   (syntax->datum name))
                                               param))
                      (raise-syntax-error 'impl
                        ;"Invalid implementation of typeclass ~a. Must have type ~a."
                        "Invalid implementation of typeclass."
                        #'class
                        #'body))
              #`(define #,(format-id syn "~a-~a" name #'param)
                        #,body))))]))

(module+ test
  (require rackunit)
  (typeclass (Eqv (A : Type))
    (equal? : (forall* (a : A) (b : A) bool)))
  (impl (Eqv bool)
    (define (equal? (a : bool) (b : bool))
      (if a
          (if b btrue bfalse)
          (if b bfalse btrue))))
  (impl (Eqv nat)
    (define equal? nat-equal?))
  (check-equal?
    (equal? z z)
    btrue)
  (check-equal?
    (equal? z (s z))
    bfalse)
  (check-equal?
    (equal? btrue bfalse)
    bfalse)
  (check-equal?
    (equal? btrue btrue)
    btrue))

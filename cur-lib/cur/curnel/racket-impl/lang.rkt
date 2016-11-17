#lang racket/base
#| TODO NB XXX Before merging:
 | 1. Handle all TODOs
 | 2. ensure all error messages are reported with surface expression and source information
 | 3. be consistent about using #' vs attribute. (I seem to think attribute do more than #' even when
 |    referring to pattern variables, but I'm not sure that's true)
 |    (attribute ) should only be used when referring to non-syntax valued attributes.
 | 4. Test
 |    - a. things that should work
 |    - b. things that shouldn't
 | 5. Ensure backwards compatibility
 | ~6. Have Stephen review code/maybe rewrite using his library.~--Library requires term/type/kind
 |     distinction, and has a lot of dependenices. Would complicate core too much.
 | 7. Get rid of boilerplatey stuff; superseded by using library.
 | 8. Abstract errors/make consistent
 |#

(require
 (for-syntax
  ;; imported for export
  racket
  racket/syntax

  racket/base
  syntax/parse)
 (rename-in
  "core.rkt"
  [cur-normalize _cur-normalize]
  [cur-equal? _cur-equal?]))
(provide
 (rename-out
  [cur-type Type]
  [cur-define define]
  [cur-λ λ]
  [cur-Π Π]
  [cur-app #%app]
  [cur-axiom axiom]
  [cur-data data]
  [cur-elim elim])
 ;; TODO: Don't export these by default; export in library or so
;; DYI syntax extension
  define-syntax
  begin-for-syntax
  define-for-syntax
  syntax-case
  syntax-rules
  define-syntax-rule
  (for-syntax
   (all-from-out syntax/parse)
   (all-from-out racket)
   (all-from-out racket/syntax))
 ;; TODO: export all subforms?
 require only-in for-syntax
 provide
 #%top
 ;; TODO: Need to not export datum, but prevents level annotations in type and param annotations in data
 #%datum
 #%module-begin)

(begin-for-syntax
  (define (env->ctx env)
    (let-values ([(names types)
                  (for/fold ([names '()]
                             [types '()])
                            ([p (reverse env)])
                    (syntax-parse (cdr p)
                      ;; TODO: cur-expr/ctx should take a list, not a syntax object
                      [(~var e (cur-expr/ctx (datum->syntax #f (map list names types))))
                       (values
                        (cons (car p) (attribute e.name))
                        (cons #'e.reified (types)))]))
                  ])
      (datum->syntax #f (map list names types))))

  (define (with-env env syn)
    (cur-reify/ctx syn (env->ctx env)))

  (define (cur-normalize syn #:local-env [env '()])
    (cur-reflect
     (cur-normalize (with-env env syn))))

  (define (cur-step syn #:local-env [env '()])
    (printf "Warning: cur-step is not yet supported.~n")
    (cur-normalize syn #:local-env env))

  ;; Are these two terms equivalent in type-systems internal equational reasoning?
  (define (cur-equal? e1 e2 #:local-env [env '()])
    ;; TODO: Performance: env->ctx gets recomputed
    (cur-equal? (with-env env e1) (with-env env e2)))

  (define (cur-type-infer syn #:local-env [env '()])
    (with-handlers ([values (λ _ #f)])
      (let ([t (get-type (with-env env syn))])
        (cur-reflect t))))

  (define (cur-type-check? syn type #:local-env [env '()])
    (cur-subtype? (get-type (with-env env syn)) (with-env env type)))

  ;; Given an identifiers representing an inductive type, return a sequence of the constructor names
  ;; (as identifiers) for the inductive type.
  (define (cur-constructors-for syn)
    (syntax-property (cur-reify syn) 'constructor-ls))

  ;; Given an identifier representing an inductive type, return the number of parameters in that
  ;; inductive, as a natural starting from the first argument to the inductive type.
  (define (cur-data-parameters syn)
    (syntax-property (cur-reify syn) 'param-count))

  ;; Takes a Cur term syn and an arbitrary number of identifiers ls. The cur term is
  ;; expanded until expansion reaches a Curnel form, or one of the
  ;; identifiers in ls.
  (define (cur-expand syn #:local-env [env '()] . ls)
    ;; TODO: env isn't supported yet, since only interface is via cur-reify/ctx, which fully
    ;; elaborates.
    ;; Maybe need a better interface for env, like directly the let-syntax bit in cur-reify/ctx
    (local-expand
       syn
       'expression
       (append (syntax-e #'(cur-type cur-λ cur-app cur-Π cur-data cur-elim))
               ls))))

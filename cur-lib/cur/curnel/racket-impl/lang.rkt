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
  [cur-void void]
  [cur-elim new-elim]
  [depricated-cur-elim elim])
 begin
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
   (all-from-out racket/syntax)
   with-env
   call-with-env
   cur->datum
   cur-expand
   cur-type-infer
   cur-type-check?
   cur-constructors-for
   cur-data-parameters
   cur-normalize
   cur-rename
   cur-step
   cur-equal?)
 ;; TODO: export all subforms?
 require only-in for-syntax
 provide rename-out all-defined-out all-from-out
 #%top
 ;; TODO: Need to not export datum, but prevents level annotations in type and param annotations in data
 #%module-begin)

;; Backward compatible elimination syntax
(define-syntax (depricated-cur-elim syn)
  (syntax-case syn ()
    [(_ _ motive (methods ...) target)
     (quasisyntax/loc syn (cur-elim target motive (methods ...)))]))

(define-syntax-rule (cur-void)
  (#%plain-app void))

(begin-for-syntax
  (require racket/trace)
  (define (env->ctx env)
    (reverse env))

  (define current-env (make-parameter '()))

  (define (call-with-env env t)
    ;; TODO: backwards-compatible, but perhaps very slow/memory intensive
    (parameterize ([current-env (append env (current-env))])
      (t)))

  (define-syntax-rule (with-env env e)
    (call-with-env env (thunk e)))

  (define (cur-reify/env syn)
    (syntax-case (cur-reify/ctx syn (env->ctx (current-env))) ()
      [(_ _ e _ _)
       #'e]))

  (define (cur-get-type/env syn)
    (syntax-case (cur-reify/ctx syn (env->ctx (current-env))) ()
      [(_ _ _ _ t)
       #'t]))

  (define (cur-normalize syn #:local-env [env '()])
    (with-env env
      (cur-reflect
       (_cur-normalize (cur-reify/env syn)))))

  (define (cur-step syn #:local-env [env '()])
    (printf "Warning: cur-step is not yet supported.~n")
    (cur-normalize syn #:local-env env))

  ;; Are these two terms equivalent in type-systems internal equational reasoning?
  (define (cur-equal? e1 e2 #:local-env [env '()])
    ;; TODO: recomputing ctx
    ;; TODO: It's worse than that; because cur-reify with rename the environment differently on each
    ;; go, if e1 and e2 are the same identifier, they will not longer be equal...
    (or
     ;; TODO: A hack to deal with the previous TODO, as a short term solution
     (and
      (identifier? e1)
      (identifier? e2)
      (free-identifier=? e1 e2)
          (cur-type-infer e1 #:local-env env)
          (cur-type-infer e2 #:local-env env))
     (with-env env
      (_cur-equal? (cur-reify/env e1) (cur-reify/env e2)))))

  (define (cur-rename new old term)
    (subst new old term))

  (define (cur-type-infer syn #:local-env [env '()])
    (with-env env
      (with-handlers (#;[values (λ _ #f)])
        (let ([t (cur-get-type/env syn)])
          (cur-reflect t)))))

  (define (cur-type-check? syn type #:local-env [env '()])
    ;; TODO: recomputing ctx
    (with-env env
      (cur-subtype? (cur-get-type/env syn) (cur-reify/env type))))

  ;; Given an identifiers representing an inductive type, return a sequence of the constructor names
  ;; (as identifiers) for the inductive type.
  (define (cur-constructors-for syn)
    (dict-ref constructor-dict (cur-reify/env syn)))

  ;; Given an identifier representing an inductive type, return the number of parameters in that
  ;; inductive, as a natural starting from the first argument to the inductive type.
  (define (cur-data-parameters syn)
    (syntax-property (cur-reify/env syn) 'param-count))

  ;; Takes a Cur term syn and an arbitrary number of identifiers ls. The cur term is
  ;; expanded until expansion reaches a Curnel form, or one of the
  ;; identifiers in ls.
  (define (cur-expand syn #:local-env [env '()] . ls)
    ;; TODO: env isn't supported yet, since only interface is via cur-reify/ctx, which fully
    ;; elaborates.
    ;; Maybe need a better interface for env, like directly the let-syntax bit in cur-reify/ctx
    (define n (local-expand
       syn
       'expression
       (append (syntax-e #'(cur-type cur-λ cur-app cur-Π cur-data depricated-cur-elim))
               ls)))
    ;; TODO: Hack to deal with reflecting identifiers and above TODO
    (if (identifier? n)
        (cur-reflect n)
        n))

  (define (cur->datum syn)
    (syntax->datum (cur-reflect (cur-reify/env syn)))))

#lang racket/base
(require
 racket/syntax
 syntax/parse
 racket/function
 "type-reconstruct.rkt"
 "eval.rkt"
 "runtime-utils.rkt"
 (rename-in "equiv.rkt" [cur-equal? _cur-equal?])
 "stxutils.rkt"
 (for-template "type-check.rkt")
 (for-template "runtime.rkt"))

(provide
 with-env
 call-with-env
 cur->datum
 deprecated-cur-expand
 cur-expand
 cur-type-infer
 cur-type-check?
 cur-constructors-for
 cur-data-parameters
 cur-method-type
 cur-constructor-recursive-index-ls
 cur-constructor-telescope-length
 cur-normalize
 cur-rename
 cur-reflect-id
 cur-step
 cur-equal?)

(define (env->ctx env)
  (for/fold ([ctx '()])
            ([p (reverse env)])
    (define/syntax-parse (~var e (cur-expr/ctx ctx)) (cdr p))
    (cons (cons (car p) (attribute e.reified)) ctx)))

;; TODO: We already have an implementation of an environment, in "environment.rkt"
;; Unfortunately, the interfaces are somewhat different...
(define current-env (make-parameter '()))

(define (call-with-env env t)
  ;; TODO: backwards-compatible, but perhaps very slow/memory intensive
  (parameterize ([current-env (append env (current-env))])
    (t)))

(define-syntax-rule (with-env env e)
  (call-with-env env (thunk e)))

(define (cur-reify/env syn . ls)
  (apply cur-elab/ctx syn (env->ctx (current-env)) ls))

(define (cur-get-type/env syn)
  (get-type/ctx (cur-reify/env syn) (env->ctx (current-env))))

(define (cur-normalize syn #:local-env [env '()])
  (with-env env
    (cur-reflect
     (cur-eval (cur-reify/env syn)))))

(define (cur-step syn #:local-env [env '()])
  (printf "Warning: cur-step is not yet supported.~n")
  (cur-normalize syn #:local-env env))

;; Are these two terms equivalent in type-systems internal equational reasoning?
(define (cur-equal? e1 e2 #:local-env [env '()])
  (with-env env
    (_cur-equal? (cur-reify/env e1) (cur-reify/env e2))))

(define (cur-rename new old term)
  (subst new old term))

(define (cur-reflect-id id)
  id)

(define (cur-type-infer syn #:local-env [env '()])
  (with-env env
    (with-handlers (#;[values (λ _ #f)])
      (let ([t (cur-get-type/env syn)])
        (cur-reflect t)))))

(define (cur-type-check? syn type #:local-env [env '()])
  (with-env env
    (cur-subtype? (cur-get-type/env syn) (cur-reify/env type))))

;; Given an identifiers representing an inductive type, return a sequence of the constructor names
;; (as identifiers) for the inductive type.
(define (cur-constructors-for syn)
  (constant-info-constructor-ls (syntax-local-eval (make-type-name syn))))

;; Given an identifier representing an inductive type, return the number of parameters in that
;; inductive, as a natural starting from the first argument to the inductive type.
;; TODO: Does this work on constructors too? If not, it should.
(define (cur-data-parameters syn)
  (constant-info-param-count (syntax-local-eval (make-type-name syn))))

;; Given an a target (a constructor applied to parameters), and a motive for eliminating
;; it, return the type of the method required for this.
(define (cur-method-type syn motive)
  (syntax-parse syn
    [c:id
     (cur-method-type #'(c) motive)]
    [(c:id ps ...)
     (cur-reflect (branch-type syn #'c (attribute ps) (local-expand motive 'expression null)))]))

;; Given a constructor, return the number of arguments it takes.
(define (cur-constructor-telescope-length syn)
  (let ([info (syntax-local-eval (make-type-name syn))])
    ;; TODO PERF: Maybe store this
    (+ (constant-info-param-count info) (length (constant-info-index-name-ls info)))))

;; Given a constructor, return a 0-indexed list of the positions of its recursive arguments.
;; E.g. for the constructor `s : (Π (x : Nat) Nat)` of the natural numbers, its
;; constructor-telescope-length is 1, and it's recursive-index-ls is '(0)
;; `cons : (Π (A : (Type 0)) (Π (a : A) (Π (a : (List A)) (List A))))` = '(2)
(define (cur-constructor-recursive-index-ls syn)
  (constant-info-recursive-index-ls (syntax-local-eval (make-type-name syn))))

;; Takes a Cur term syn and an arbitrary number of identifiers ls. The cur term is
;; expanded until expansion reaches a Curnel form, or one of the
;; identifiers in ls.
(define (deprecated-cur-expand syn #:local-env [env '()] . ls)
  (local-expand syn 'expression (append (syntax-e #'(typed-Type typed-λ typed-app typed-Π typed-data deprecated-typed-elim typed-elim))
           ls)))

(define (cur-expand syn #:local-env [env '()] . ls)
  (with-env env
    (apply cur-reify/env syn (append (syntax-e #'(typed-Type typed-λ typed-app typed-Π typed-data deprecated-typed-elim typed-elim))
           ls))))

(define (cur->datum syn)
  (syntax->datum (cur-reflect (cur-reify/env syn))))

#lang racket/base

(require
 racket/syntax
 syntax/parse
 "stxutils.rkt"
 (for-template
  racket/base
  "runtime.rkt"))

#|
The Cur elaborator is also the type-checker, sort of.
Unlike Type Systems as Macros, we do not use syntax properties to stores types.
Syntax properties do not work well when storing identifiers, across module, or with compilation,
particularly.
They also use a *lot* of space, since each term and subterm has its type attached by the macros.

Instead, each macro elaborates into a runtime term implementing the term in Racket, which is annotated
enough to recompute its type in a simple function.
This means the type system is not easily extended by adding macros; we would also need to add a case
to the get-type function.
This could be done using an extensible function, simulated with parameters perhaps.
However, we don't really want the type system to be extensible since we desire a small trusted core.
|#

(define (type-of-constant name args)
  ; NB: eval is evil, but this is the least bad way I can figured out to store types.
  (apply (constant-info-type-constr (syntax-local-eval name)) args))

(define (type-of-id syn)
  (identifier-info-type (syntax-local-eval syn)))

(provide (all-defined-out))

;; Takes a runtime term and computes it's type, as a runtime term.
(define (get-type e)
  (syntax-parse e
    [e:cur-runtime-identifier
     (type-of-id #'e.name)]
    [e:cur-runtime-constant
     (type-of-constant #'e.name (attribute e.args))]
    [e:cur-runtime-universe
     #`(cur-Type (quote #,(add1 (attribute e.level))))]
    [e:cur-runtime-pi
     ;; TODO: Shouldn't this be the max of the annotation and the result?
     #:with body (cur-elab/ctx #'e.result (list (cons #'e.name #'e.ann)))
     (get-type #'body)]
    [e:cur-runtime-lambda
     #:with body (cur-elab/ctx #'e.body (list (cons #'e.name #'e.ann)))
     #`(cur-Π e.ann (#%plain-lambda (e.name) #,(get-type #'body)))]
    #;[e:cur-runtime-app
     #:with t1:runtime-pi (get-type #'e.rator)
     (subst #'e.rand #'t1.name #'t1.result)]
    #;[e:cur-runtime-elim
     (cur-eval (cur-app* #'e.motive (append index-ls (list #'target.reified))))]))
;; TODO: Not sure constants have enough information to reconstruct their types... maybe need to store
;; information in the struct type.
;; TODO: implement elim, constants.
;; TODO: Implement subst
;; TODO: Implement cur-eval

(define cur-elab local-expand-expr)

(define (cur-elab/ctx syn ctx)
  (syntax-parse syn
    #:literals (#%plain-lambda let-values begin #%expression begin-for-syntax quote-syntax)
    [_
     #:with (x ...) (map car ctx)
     #:with (t ...) (map cdr ctx)
;     #:with (internal-name ...) (map fresh (attribute x))
;     #:with (x-type ...) (map (lambda (x) (format-type-id x x)) (attribute x))
     ;; NB: consume arbitrary number of let-values.
     #:do [(syntax-local-eval #`(begin (define-values (x ...) (values #'t ...)) (void)))]
     #:with meow (cur-elab #`(lambda (x ...) #,syn))
     #:do [(displayln (syntax->datum #'meow))
           #;(displayln (eval #'meow))]
;     #:with (let-values _ (quote-syntax (#%plain-lambda (_) body))) #'meow
     #:with (#%plain-lambda (_) body) #'meow
     #`body #;((name ...) #'e.body)]))

(module+ test
  (require
   (for-syntax
    chk
    (except-in racket/base λ)
    (submod "..")
    "stxutils.rkt")
   "runtime.rkt"
   (submod "runtime.rkt" test))

  (begin-for-syntax
    ;; TODO: This will just be cur-equal? eventually, I think
    (define (equal-syn? syn1 syn2)
      (cond
        [(and (identifier? syn1) (identifier? syn1))
         (free-identifier=? syn1 syn2)]
        [(and (syntax? syn1) (syntax? syn2))
         (equal?/recur (syntax->datum syn1) (syntax->datum syn2) equal-syn?)]
        [else (equal? syn1 syn2)]))

    (define get-type/elab (compose get-type cur-elab))

    (chk
     #:eq equal-syn? (type-of-id (local-expand-expr #'two)) #'(Nat)
     #:eq equal-syn? (type-of-constant #'Nat '()) #'(cur-Type 0)
     #:eq equal-syn? (type-of-constant #'z '()) #'(Nat)

     #:eq equal-syn? (cur-elab #'(cur-Type 0)) #'(#%app cur-Type (quote 0))
     #:eq equal-syn? (get-type/elab #'(cur-Type 0)) #'(cur-Type '1)
     #:eq equal-syn? (get-type/elab #'(cur-Type 1)) #'(cur-Type '2)
     #:eq equal-syn? (get-type/elab #'(Nat)) #'(cur-Type 0)
     #:eq equal-syn? (get-type/elab #'(z)) #'(Nat)
     ;; TODO: Predicativity rules have changed.
     #:eq equal-syn? (get-type/elab #'(cur-Π (cur-Type 0) (#%plain-lambda (x) (cur-Type 0)))) #'(cur-Type '1)
     #:eq equal-syn? (get-type/elab #'(cur-λ (cur-Type 0) (#%plain-lambda (x) x))) #'(cur-Type '0))
    ))

;; TODO: These will be implemented in a separate module
#;(define-syntax (cur-λ syn)
  (syntax-parse syn
    [(_ (x : type) body)
     #:with type-lab (cur-elab #'type)
     #:with x-type (format-id #'x "~a-type" #'x)
     #:with x-internal (fresh #'x)
     #`(lambda (x-internal)
         (let-syntax ([x-type (lambda (x) type-elab)])
           (let-syntax ([x (make-rename-transformer
                            (syntax-property #'x-internal 'type #'x-type #t))])
             body)))]))

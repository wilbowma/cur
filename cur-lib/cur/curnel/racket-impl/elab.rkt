#lang racket/base

(require
 racket/syntax
 syntax/parse
 racket/struct-info
 (for-template "runtime.rkt"))

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

;; TODO: Implement syntax classes
;(define-syntax-class )

; Get the type of a identifier, such as a define or a struct.
; Types for these are stored with particular names as transformer bindings.
(define (identifier-type syn id)
  (syntax-local-value (format-id syn "type:~a" id)))

(define (type-of-constant syn)
  (syntax-case syn ()
    [(syn args ...)
     ;; NB: More resilient to provide/require renaming, but still annoying use of format-id
     (apply (identifier-type #'syn (car (extract-struct-info (syntax-local-value #'syn))))
            (syntax->list #'(args ...)))]))

(define (type-of-id syn)
  ;; NB: More resilient to provide/require renaming, but still annoying use of format-id
  (identifier-type syn (cadr (identifier-binding syn))))

(provide (all-defined-out))

(module+ test
  (require
   (for-syntax
    chk
    (except-in racket/base λ)
    (submod ".."))
   "runtime.rkt"
   (submod "runtime.rkt" test))

  (begin-for-syntax
    (define (equal-syn? syn1 syn2)
      (equal? (syntax->datum syn1) (syntax->datum syn2)))

    (chk
     #:eq equal-syn? (type-of-id #'two) #'(Nat)
     #:eq equal-syn? (type-of-constant #'(Nat)) #'(Type 0)
     #:eq equal-syn? (type-of-constant #'(z)) #'(Nat)
     #:eq equal-syn? (type-of-constant #'(s z)) #'(Nat))))

#|
;; Takes a runtime term and computes it's type, as a runtime term.
(define (get-type e)
  (syntax-parse e
    [e:runtime-identifier
     (type-of-id #'e)]
    [e:runtime-constant
     (type-of-constant #'e)]
    [e:runtime-universe
     #`(Type (quote #,(add1 (attribute e.level))))]
    [e:runtime-pi
     ;; TODO: Shouldn't this be the max of the annotation and the result?
     (get-type #'e.result)]
    [e:runtime-lambda
     #:with ((x) body) (cur-elab/ctx #'e.body (list #'e.name #'e.ann))
     #`(Π e.ann (#%plain-lambda (x) #,(get-type #'type)))]
    [e:runtime-app
     #:with t1:runtime-pi (get-type #'e.rator)
     (subst #'e.rand #'t1.name #'t1.result)]
    #;[e:runtime-elim
     (cur-eval (cur-app* #'e.motive (append index-ls (list #'target.reified))))]))
;; TODO: Not sure constants have enough information to reconstruct their types... maybe need to store
;; information in the struct type.
;; TODO: implement elim, constants.
;; TODO: Implement subst
;; TODO: Implement cur-eval

(define (cur-elab e)
  (local-expand e 'expression null))

(define-syntax (let*-syntax syn)
  (syntax-case syn ()
    [(_ () e)
     #`e]
    [(_ ([x e] r ...) body)
     #`(let-syntax ([x e])
         (let*-syntax (r ...) body))]))

(define (cur-elab/ctx syn ctx)
  (syntax-parse syn
    #:datum-literals (:)
    #:literals (#%plain-lambda let-values)
    [_
     #:with (x ...) (map car ctx)
     #:with (t ...) (map cdr ctx)
     #:with (internal-name ...) (map fresh (attribute x))
     #:with (x-type ...) (map fresh (attribute x))
     ;; NB: consume arbitrary number of let-values.
     #:with (#%plain-lambda (name ...) e:in-let-values)
     (cur-elab
      #`(lambda (internal-name ...)
          (let*-syntax ([x-type (lambda (stx) #'t)] ...
                        [x (make-rename-transformer
                            (syntax-property #'internal-name 'type-transformer #'x-type))] ...)
                       #,syn)))
     #`((name ...) #'e.body)]))

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

|#

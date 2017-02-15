#lang racket/base

(require
 racket/syntax
 syntax/parse)

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
(define-syntax-class )

;; Takes a runtime term and returns it's type, as a runtime term.
(define (get-type e)
  (syntax-parse e
    [e:runtime-identifier
     (cur-elab (syntax-property #'e.name 'type-transformer))]
    [e:runtime-universe
     (cur-elab #`(Type (quote #,(add1 (attribute e.level)))))]
    [e:runtime-pi
     ;; TODO: Shouldn't this be the max of the annotation and the result?
     (get-type #'e.result)]
    [e:runtime-lambda
     #:with ((x) body) (cur-elab/ctx #'e.body (list #'e.name #'e.ann))
     (cur-elab #`(Π e.ann (#%plain-lambda (x) #,(get-type #'type))))]
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

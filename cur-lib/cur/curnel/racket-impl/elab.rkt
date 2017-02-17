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

; Evaluation
;; TODO: Is there a better way to write this subst?

(define (cur-α-equal? t1 t2 (fail (lambda _ #f)))
  (let cur-α-equal ([t1 t1] [t2 t2])
    (syntax-parse #`(#,t1 #,t2)
      [(x:cur-runtime-identifier y:cur-runtime-identifier)
       (free-identifier=? #'x #'y)]
      [(e1:cur-runtime-constant e2:cur-runtime-constant)
       (and (cur-α-equal? #'e1.name #'e2.name)
            (andmap cur-α-equal? (attribute e1.rand-ls) (attribute e2.rand-ls)))]
      [(A:cur-runtime-universe B:cur-runtime-universe)
       (eq? (attribute A.level) (attribute B.level))]
      [(e1:cur-runtime-pi e2:cur-runtime-pi)
       (and (cur-α-equal? #'e1.ann #'e2.ann)
            (cur-α-equal? #'e1.result (subst #'e1.name #'e2.name #'e2.result)))]
      [(e1:cur-runtime-elim e2:cur-runtime-elim)
       (and (cur-α-equal? #'e1.target #'e2.target)
            (cur-α-equal? #'e1.motive #'e2.motive)
            (andmap cur-α-equal? (attribute e1.method-ls) (attribute e2.method-ls)))]
      [(e1:cur-runtime-app e2:cur-runtime-app)
       (and (cur-α-equal? #'e1.rator #'e2.rator)
            (cur-α-equal? #'e1.rand #'e2.rand))]
      [(e1:cur-runtime-lambda e2:cur-runtime-lambda)
       (and (cur-α-equal? #'e1.ann #'e2.ann)
            (cur-α-equal? #'e1.body (subst #'e1.name #'e2.name #'e2.body)))]
      [_ (fail t1 t2)])))

(define cur-elab local-expand-expr)

(define (cur-apply* rator rands)
  (if (null? rands)
      rator
      (cur-apply* #`(#%plain-app cur-apply #,rator #,(car rands)) (cdr rands))))

(define (cur-eval syn)
  (syntax-parse syn
    [_:cur-runtime-universe syn]
    [e:cur-runtime-constant
     #`(#%plain-app e.name #,@(map cur-eval (attribute e.rand-ls)))]
    [_:cur-runtime-identifier
     ;; TODO: unconditional with-handlers is bad; can we detect whether syn has a phase 1 binding?
     (let ([maybe-def (with-handlers ([(lambda _ #t) (lambda _ #f)])
                        (identifier-info-delta-def (syntax-local-eval syn)))])
       (if maybe-def
           (cur-normalize maybe-def)
           syn))]
    [e:cur-runtime-pi
     #`(#%plain-app cur-Π #,(cur-eval #'e.ann) (#%plain-lambda (e.name) #,(cur-eval #'e.result)))]
    [e:cur-runtime-app
     #:with a (cur-eval #'e.rand)
     (syntax-parse (cur-eval #'e.rator)
       [f:cur-runtime-lambda
        (cur-eval (subst #'a #'f.name #'f.body))]
       [e1-
        #`(#%plain-app cur-apply e1- a)])]
    [e:cur-runtime-elim
     #:with target:cur-runtime-constant #'e.target
     #:do [(define info (syntax-local-eval #'target.name))]
     #:do [(define recursive-index-ls (constant-info-recursive-index-ls info))]
     ;; TODO PERF: use unsafe version of list operators and such for internal matters
     ;; TODO PERF: list-ref; could we make it a vector?
     (cur-eval
      (cur-apply*
       (list-ref (attribute e.method-ls) (constant-info-constructor-index info))
       (append (attribute target.rand-ls)
                 (for/fold ([m-args '()])
                           ([arg (attribute target.rand-ls)]
                            [i (in-naturals (constant-info-param-count info))]
                            ;; TODO PERF: memq in a loop over numbers...
                            #:when (memq i recursive-index-ls))
                   (cons #`(#%plain-app cur-elim arg e.motive #,@(attribute e.method-ls)) m-args)))))]
    [e:cur-runtime-elim
     #`(#%plain-app cur-elim #,(cur-eval #'e.target) #,(cur-eval #'e.motive) #,@(map cur-eval (attribute e.method-ls)))]
    [e:cur-runtime-lambda
     #`(#%plain-app cur-λ e.ann (#%plain-lambda (e.name) #,(cur-eval #'e.body)))]
    [_ (raise-syntax-error 'cur-eval (format "Something has gone horribly wrong: ~a" (syntax->datum syn)) syn)]))

(define cur-normalize (compose cur-eval cur-elab))

(define (type-of-constant name args)
  ; NB: eval is evil, but this is the least bad way I can figured out to store types.
  (apply (constant-info-type-constr (syntax-local-eval name)) args))

(define (type-of-id name)
  (identifier-info-type (syntax-local-eval name)))

(provide (all-defined-out))

;; Takes a runtime term and computes it's type, as a runtime term.
(define (get-type e)
  (syntax-parse e
    [e:cur-runtime-identifier
     (type-of-id #'e.name)]
    [e:cur-runtime-constant
     (type-of-constant #'e.name (attribute e.rand-ls))]
    [e:cur-runtime-universe
     #`(#%plain-app cur-Type (quote #,(add1 (attribute e.level))))]
    [e:cur-runtime-pi
     ;; TODO: Shouldn't this be the max of the annotation and the result?
     #:with body (cur-elab/ctx #'e.result (list (cons #'e.name #'e.ann)))
     (get-type #'body)]
    [e:cur-runtime-lambda
     #:with body (cur-elab/ctx #'e.body (list (cons #'e.name #'e.ann)))
     #`(#%plain-app cur-Π e.ann (#%plain-lambda (e.name) #,(get-type #'body)))]
    [e:cur-runtime-app
     #:with t1:cur-runtime-pi (get-type #'e.rator)
     (cur-eval (subst #'e.rand #'t1.name #'t1.result))]
    [e:cur-runtime-elim
     #:with D:cur-runtime-constant (get-type #'e.target)
     (cur-eval (cur-apply* #'e.motive (append (attribute D.rand-ls) (list #'e.target))))]))

(define (cur-elab/ctx syn ctx)
  (syntax-parse syn
    #:literals (#%plain-lambda)
    [_
     #:with (x ...) (map car ctx)
     #:with (t ...) (map cdr ctx)
     ;; NB: consume arbitrary number of let-values.
     (parameterize ([current-namespace (current-namespace)])
       (for ([name (attribute x)]
             [type (attribute t)])
         (namespace-set-variable-value! (syntax-e name) (identifier-info type #f) #f))
       (define intdef (syntax-local-make-definition-context))
       (syntax-local-bind-syntaxes (attribute x) #f intdef)
       (local-expand syn 'expression null intdef))]))

(module+ test
  (require
   (for-syntax
    chk
    (except-in racket/base λ)
    (submod "..")
    "stxutils.rkt")
   "runtime.rkt"
   (submod "runtime.rkt" test))

  (define-syntax (infer-type stx)
    (syntax-case stx ()
      [(_ expr)
       (get-type #'expr)]))

  (require (for-syntax syntax/parse))
  (define-syntax (surface-λ stx)
    (syntax-parse stx
      #:datum-literals (:)
      [(_ (x : t) b)
       #:with type (cur-elab #'t)
       #`(cur-λ type
                (#%plain-lambda (x) #,(cur-elab/ctx #'b (list (cons #'x #'type)))))]))

  (begin-for-syntax
    (define equal-syn? cur-α-equal?)
    (define (equal-syn/elab? e1 e2)
      (cur-α-equal? (cur-elab e1) (cur-elab e2)))

    (define get-type/elab (compose get-type cur-elab))

    (chk
     ; cur-α-equal? tests
     #:t (cur-α-equal? #'(#%plain-app cur-Type '0) #'(#%plain-app cur-Type '0))
     #:t (cur-α-equal? #'(#%plain-app cur-Type '1) #'(#%plain-app cur-Type '1))
     #:! #:t (cur-α-equal? #'(#%plain-app cur-Type '1) #'(#%plain-app cur-Type '0))
     #:! #:t (cur-α-equal? #'(#%plain-app cur-Type '0) #'(#%plain-app cur-Type '1))
     #:t (cur-α-equal? #'(#%plain-app Nat) #'(#%plain-app Nat))
     #:! #:t (cur-α-equal? #'(#%plain-app Nat) #'(#%plain-app z))
     #:t (cur-α-equal? #'(#%plain-app z) #'(#%plain-app z))
     #:t (cur-α-equal? #'(#%plain-app s (#%plain-app z)) #'(#%plain-app s (#%plain-app z)))
     #:t (cur-α-equal? #'(#%plain-app cur-λ (#%plain-app Nat) (#%plain-lambda (x) x))
                       #'(#%plain-app cur-λ (#%plain-app Nat) (#%plain-lambda (y) y)))
     #:t (cur-α-equal? #'(#%plain-app cur-Π (#%plain-app Nat) (#%plain-lambda (x) (#%plain-app Nat)))
                       #'(#%plain-app cur-Π (#%plain-app Nat) (#%plain-lambda (y) (#%plain-app Nat))))

     ; cur-elab tests
     #:eq equal-syn? (cur-elab #'(cur-Type 0)) #'(#%plain-app cur-Type '0)
     #:eq equal-syn? (cur-elab #'(cur-λ (cur-Type 0) (lambda (x) x))) #'(#%plain-app cur-λ (#%plain-app cur-Type '0) (#%plain-lambda (x) x))
     #:eq equal-syn? (cur-elab #'(Nat)) #'(#%plain-app Nat)
     #:eq equal-syn? (cur-elab #'(cur-apply (cur-λ (cur-Type 0) (lambda (x) x)) (z)))
     #'(#%plain-app cur-apply (#%plain-app cur-λ (#%plain-app cur-Type '0) (#%plain-lambda (x) x))
                    (#%plain-app z))

     ; cur-eval tests
     #:eq equal-syn/elab? (cur-eval (cur-elab #'(cur-Type 0))) #'(cur-Type '0)
     #:eq equal-syn/elab? (cur-eval (cur-elab #'two)) #'(s (s (z)))
     #:eq equal-syn/elab? (cur-eval (cur-elab #'(cur-apply (cur-λ (cur-Type 0) (lambda (x) x)) (z)))) #'(z)
     #:eq equal-syn/elab? (cur-eval (cur-elab #'(cur-apply (cur-apply plus (z)) (s (z))))) #'(s (z))

     ; type-helper tests
     #:eq equal-syn/elab? (type-of-id #'two) #'(Nat)
     #:eq equal-syn/elab? (type-of-constant #'Nat '()) #'(cur-Type 0)
     #:eq equal-syn/elab? (type-of-constant #'z '()) #'(Nat)

     ; get-type tests
     #:eq equal-syn/elab? (get-type/elab #'(cur-Type 0)) #'(cur-Type '1)
     #:eq equal-syn/elab? (get-type/elab #'(cur-Type 1)) #'(cur-Type '2)
     #:eq equal-syn/elab? (get-type/elab #'(Nat)) #'(cur-Type 0)
     #:eq equal-syn/elab? (get-type/elab #'(z)) #'(Nat)
     ;; TODO: Predicativity rules have changed.
     #:eq equal-syn/elab? (get-type/elab #'(cur-Π (cur-Type 0) (#%plain-lambda (x) (cur-Type 0)))) #'(cur-Type '1)
     #:eq equal-syn/elab? (get-type/elab #'(cur-λ (cur-Type 0) (#%plain-lambda (x) x)))
     #'(cur-Π (cur-Type '0) (#%plain-lambda (x) (cur-Type '0)))
     #:eq equal-syn/elab?
     (get-type/elab #'(cur-λ (cur-Type 1)
                                       (#%plain-lambda (y)
                                                       (cur-λ (cur-Type 0) (#%plain-lambda (x) x)))))
     #'(cur-Π (cur-Type '1) (#%plain-lambda (y) (cur-Π (cur-Type '0) (#%plain-lambda (x) (cur-Type '0)))))
     ; Tests that nested contexts work fine.
     #:eq equal-syn/elab?
     (get-type/elab #'(cur-λ (cur-Type 1)
                                       (#%plain-lambda (y)
                                                       (cur-λ (cur-Type 0) (#%plain-lambda (x) y)))))
     #'(cur-Π (cur-Type '1) (#%plain-lambda (y) (cur-Π (cur-Type '0) (#%plain-lambda (x) (cur-Type '1)))))
     ; Tests that reflection inside the Cur elaborator works fine
     #:eq equal-syn/elab?
     (get-type/elab #'(surface-λ (y : (cur-Type 1))
                                           (cur-λ (infer-type y) (#%plain-lambda (x) y))))
     #'(cur-Π (cur-Type '1) (#%plain-lambda (y) (cur-Π (cur-Type '1) (#%plain-lambda (x) (cur-Type '1)))))
     ; Tests application
     #:eq equal-syn/elab? (get-type/elab #'plus) #'(cur-Π (Nat) (#%plain-lambda (n1)
                                                                                (cur-Π (Nat)
                                                                                       (#%plain-lambda
                                                                                        (n2)
                                                                                        (Nat)))))
     #:eq equal-syn/elab?
     (get-type/elab #'(cur-apply plus (z)))
     #'(cur-Π (Nat) (#%plain-lambda (y) (Nat)))
     #:eq equal-syn/elab?
     (get-type/elab #'(cur-apply (cur-apply plus (z)) (s (z))))
     #'(Nat)
     ; Tests elim
     #:eq equal-syn/elab? (get-type/elab #`(cur-apply #,(cur-eval #'plus) (s)))
     #'(cur-Π (Nat) (#%plain-lambda (y) (Nat)))

     ; TODO: Missing dependent application and elim tests
     )))

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

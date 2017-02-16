#lang racket/base

(require
 racket/list
 racket/struct)
(provide (all-defined-out))
#|
Cur is implemented by type-checking macro expansion into Racket run-time terms.

The run-time terms are either:
1. A Racket identifier.
2. A transparent struct inheriting from constant, whose first field is a constant-info, and whose
   other fields are run-time terms.
3. A transparent struct inheriting from inductive, whose first field is a inductive-info, and whose
   other fields are run-time terms.
4. The struct (Type i), where i is a natural number
5. The struct (Π t f), where t is a run-time term and f is a run-time term.
6. The struct (λ t f), where t is a run-time term and f is a run-time term.
7. A plain application (#%plain-app rator rand) of a run-time term to a run-time term.
8. A plain application (#%plain-app elim target motive method-ls), where elim is the function defined
   below, target is a run-time term, motive is a run-time term, and method-ls is a list of run-time
   terms.

A compiled Cur module should be of the form:
(module-begin
   (require ...)
   (provide ...)
   (define-syntax id-type transformer)
   (define id term)
   ...
   term
   ...)

Each provided id must have a syntax-property with the identifier of a transformer that, when expanded,
produces the type of the id.
That transformer must also be provided.

Any module that requires a Racket library, rather than a Cur library, is considered unsafe.
|#

; The run-time representation of univeres. (Type i), where i is a Nat.
(struct Type (i) #:transparent)

; The run-time representation of Π types. (Π t f), where is a type and f is a procedure that computes
; the result type given an argument.
(struct Π (t f))

; The run-time representation of an application is a Racket plain application.
; (#%plain-app e1 e2)

; The run-time representation of a function. (λ t f), where t is a type and f is a procedure that
; computer the result type given an argument of type t.
(struct λ (t f) #:property prop:procedure (struct-field-index f))

; The parameter-count property is natural number representing the number of fields that are parameters.
(define-values (prop:parameter-count parameter-count? parameter-count-ref)
  (make-struct-type-property 'parameter-count))

; The dispatch property is a box containing a curried Racket procedure.
; The procedure accepts a list of length equal to the number of fields the associated constant has,
; then a target, and returns the ith element based on which constructor the target is constructed
; from.
; NB: Currently must be in a box, since the procedure can only be generated after all constant
; structs are defined. Since the constant structs must have the property, the box must exist but be
; initalized later.
(define-values (prop:dispatch dispatch? dispatch-ref)
  (make-struct-type-property 'dispatch))

; The recursive-index-ls property is a list of natural numbers, representing which fields of the
; constant are recursive.
(define-values (prop:recursive-index-ls recursive-index-ls? recursive-index-ls-ref)
  (make-struct-type-property 'recursive-index-ls))

; An inductive type is a transparent struct that inherits constant, and has
; prop:parameter-count.
; For every inductive type (struct i constant ...), a transformer binding of type:i must also be
; defined.
; The binding must be a procedure that takes one argument for every argument to the inductive type,
; and produces a runtime term as a syntax object representing the type of the inductive type.
; TODO: Should probably also provide inductive-info:i, with other type-checking information.

; A constructor is a transparent struct that inherits constant, and has
; prop:parameter-count, prop:dispatch, and prop:recursive-index-ls.
; For every constant (struct c constant ...), a transformer binding of type:c must also be
; defined.
; The binding must be a procedure that takes one argument for every argument to the inductive type,
; and produces a runtime term as a syntax object representing the type of the constant.
; TODO: Should probably also provide constructor-info:i, with other type-checking information.
(struct constant () #:transparent)

;; Target must a constructor, and method-ls must be a list of methods of length equal to the number of
;; constructs for the inductive type of target.
(define (elim target _ method-ls)
  ;; NB: The constant info field plus the parameters
  (define fields-to-drop (parameter-count-ref target))
  (define dispatch ((unbox (dispatch-ref target)) method-ls))
  (let loop ([e target])
    (let* ([method (dispatch e)]
           [args (drop (struct->list e) fields-to-drop)]
           [r-arg-ls (recursive-index-ls-ref e)]
           [r-args
            (for/list ([x args]
                       [i (in-naturals fields-to-drop)]
                       ;; TODO PERF: memq, in a loop, over numbers
                       #:when (memq i r-arg-ls))
              ;; TODO PERF: CBV; eager eval of recursive arguments. Is there a better way?
              (loop x))])
      ;; NB: the method is curried, so ...
      ;; TODO PERF: attempt to uncurry elim methods?
      (for/fold ([app method])
                ([a (append args r-args)])
        (app a)))))

;; NB: Non-essential
;; TODO PERF: Should be able to do a better job since predicates are mutually exclusive.
(define (build-dispatch predicates)
  (lambda (ls)
    (lambda (e)
      (let/ec k
        (for ([p predicates]
              [l ls]
              #:when (p e))
          (k l))
        (error 'run-time "Something very very bad has happened.")))))

(module+ test
  (require chk (for-syntax (submod "..")))
  (struct Nat constant () #:transparent
    #:property prop:parameter-count 0)

  (require (for-syntax (except-in racket/base λ)))

  ;; TODO PERF: When the type takes no arguments, can we avoid making it a function?
  (define-syntax type:struct:Nat (lambda () #`(Type 0)))

  (define Nat-dispatch (box #f))

  (struct z constant () #:transparent
    #:property prop:parameter-count 0
    #:property prop:dispatch Nat-dispatch
    #:property prop:recursive-index-ls null)

  (define-syntax type:struct:z (lambda () #`(Nat)))

  (struct s constant (pred) #:transparent
    #:property prop:parameter-count 0
    #:property prop:dispatch Nat-dispatch
    #:property prop:recursive-index-ls (list 0))

  (define-syntax type:struct:s (lambda (x) #`(Nat)))

  (set-box! Nat-dispatch (build-dispatch (list z? s?)))

  (define two (s (s z)))

  (define-syntax type:def:two #`(Nat))

  ;; TODO PERF: When the constant has no fields, optimize into a singleton structure. this can be
  ;; detected at transformer time using struct-info, by a null field-accessor list
  ;; TODO PERF: When we make singletons, should be possible to optimize equality checks into eq?
  ;; instead of equal?.
  ;; "A structure type can override the default equal? definition through the gen:equal+hash generic interface."
  (require (for-syntax racket/syntax racket/struct-info))
  (define-syntax (type-of-constant syn)
    (syntax-case syn ()
      [(_ (syn args ...))
       ;; NB: More resilient to provide/require renaming, but still annoying use of format-id
       (apply (syntax-local-value (format-id #'syn "type:~a" (car (extract-struct-info (syntax-local-value #'syn))))) (syntax->list #'(args ...)))]))

  (define-syntax (type-of-def syn)
    (syntax-case syn ()
      [(_ syn)
       ;; NB: More resilient to provide/require renaming, but still annoying use of format-id
       (syntax-local-value (format-id #'syn "type:def:~a" (cadr (identifier-binding #'syn))))]))

  (chk
   #:t (Type 0)
   #:t (Type 1)
   #:t (λ (Type 1) (#%plain-lambda (x) x))
   #:t (Π (Type 1) (#%plain-lambda (x) (Type 1)))
   #:= (#%plain-app (λ (Type 1) (#%plain-lambda (x) x)) (Type 0)) (Type 0)
   #:? z? (z)
   #:? s? (s z)
   #:= (elim (z) void (list (z) (lambda (p) (lambda (ih) p)))) (z)
   #:! #:= (elim (s (s (z))) void (list (z) (lambda (p) (lambda (ih) p)))) (z)
   #:= (elim (s (s (z))) void (list (z) (lambda (p) (lambda (ih) p)))) (s (z))
   #:= (Type 0) (type-of-constant (Nat))
   #:= (Nat) (type-of-constant (z))
   #:= (Nat) (type-of-constant (s z))
   #:= (Nat) (type-of-def two)
   )
  )

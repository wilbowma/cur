#lang racket/base

(require
 racket/list
 racket/struct)

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

; The constant-type property is a Racket procedure that computes the type of a constant.
; It accepts the fields of a constant, as runtime terms, and returna a runtime term.
(define-values (prop:constant-type constant-type? constant-type-ref)
  (make-struct-type-property 'type))

; The parameter-count property is natural number representing the number of fields that are parameters.
(define-values (prop:parameter-count parameter-count? parameter-count-ref)
  (make-struct-type-property 'parameter-count))

; The dispatch property is a box containing a curried Racket procedure.
; The procedure accepts a list of length equal to the number of fields the associated constant has,
; then a target, and returns the ith element based on which constructor the target is constructed
; from.
; TODO: Currently must be in a box, since the procedure can only be generated after all constant
; structs are defined. Since the constant structs must have the property, the box must exist but be
; initalized later.
(define-values (prop:dispatch dispatch? dispatch-ref)
  (make-struct-type-property 'dispatch))

; The recursive-index-ls property is a list of natural numbers, representing which fields of the
; constant are recursive.
(define-values (prop:recursive-index-ls recursive-index-ls? recursive-index-ls-ref)
  (make-struct-type-property 'recursive-index-ls))

; The inductive property is set to #t for constants that are inductively defined types
(define-values (prop:inductive inductive? inductive-ref)
  (make-struct-type-property 'inductive))

; The constructor property is set to #t for constants that are constructors for an inductively defined type.
(define-values (prop:constructor constructor? constructor-ref)
  (make-struct-type-property 'constructor))

; An inductive type is a transparent struct that inherits constant, and has prop:inductive,
; prop:constant-type, prop:parameter-count.

; A constructor is a transparent struct that inherits constant, and has prop:constructor,
; prop:constant-type, prop:parameter-count, prop:dispatch, and prop:recursive-index-ls.
(struct constant () #:transparent)

;; Target must a constant, and method-ls must be a list of methods of length equal to the number of
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

(define constant-equal? equal?)

(module+ test
  (require chk)
  (struct Nat constant () #:transparent
    #:property prop:inductive #t
    #:property prop:constant-type (Type 0)
    #:property prop:parameter-count 0)

  (define Nat-dispatch (box #f))

  (struct z constant () #:transparent
    #:property prop:constructor #t
    #:property prop:constant-type (Nat)
    #:property prop:parameter-count 0
    #:property prop:dispatch Nat-dispatch
    #:property prop:recursive-index-ls null)

  (struct s constant (pred) #:transparent
    #:property prop:constructor #t
    #:property prop:constant-type (Nat)
    #:property prop:parameter-count 0
    #:property prop:dispatch Nat-dispatch
    #:property prop:recursive-index-ls (list 0))

  (set-box! Nat-dispatch (build-dispatch (list z? s?)))

  ;; TODO PERF: When the constant has no fields, optimize into a singleton structure.
  ;; TODO PERF: When we make singletons, should be possible to optimize equality checks into eq?
  ;; instead of equal?. Might require defining a genric for constants, instantiating, etc.

  (chk
   #:t (Type 0)
   #:t (Type 1)
   #:t (λ (Type 1) (#%plain-lambda (x) x))
   #:t (Π (Type 1) (#%plain-lambda (x) (Type 1)))
   #:= (#%plain-app (λ (Type 1) (#%plain-lambda (x) x)) (Type 0)) (Type 0)
   #:? z? (z)
   #:? s? (s z)
   #:eq constant-equal? (elim (z) void (list (z) (lambda (p) (lambda (ih) p)))) (z)
   #:! #:eq constant-equal? (elim (s (s (z))) void (list (z) (lambda (p) (lambda (ih) p)))) (z)
   #:eq constant-equal? (elim (s (s (z))) void (list (z) (lambda (p) (lambda (ih) p)))) (s (z))))

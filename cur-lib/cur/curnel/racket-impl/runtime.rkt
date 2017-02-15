#lang racket/base

(require
 racket/list
 racket/struct)

#|
Cur is implemented by type-checking macro expansion into Racket run-time terms.

The run-time terms are either:
1. A Racket identifier.
2. The struct (Type i), where i is a natural number
3. The struct (Π t f), where t is a run-time term and f is a run-time term.
4. The struct (λ t f), where t is a run-time term and f is a run-time term.
5. A plain application (#%plain-app rator rand) of a run-time term to a run-time term.
6. A plain application (#%plain-app id target motive method-ls) of an identifier with the syntax
   property 'elim set to #t, to a target (a run-time term) a motive (a run-time term) and a list of
   run-time terms.

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

; Each inductive type has some required metadata:
; 1. a type (a universe)
; 2. some number of parameters
; 3. a number of constructors given by constructor-count
; 4. a curried dispatch function:
;    Dispatch accepts a list of length constructor-count in constructor order and a target, and returns
;    the ith element based on which constructor the target is constructed from.
(struct inductive-info (type parameter-count constructor-count dispatch))

; An inductive type is a transparent struct that inherits inductive.
; Each inductive has a field containing metadata about the inductive type, followed by arguments to
; the inductive type.
(struct inductive (iinfo) #:transparent)

; Each constant has some required metadata:
; 1. A type that is an inductive
; 2. number of fields
; 3. A list of indecies indicating which fields are recurisve arguemnts.
(struct constant-info (type field-count recursive-index-ls))

; A constant is a transparent struct that inherits constant.
; Each constant has a field containing metadata about the constant, followed by additional arguments
; to the constant.
(struct constant (cinfo) #:transparent)

;; Target must a constant, and method-ls must be a list of methods of length equal to the number of
;; constructs for the inductive type of target.
(define (elim target _ method-ls)
  (define cinfo (constant-cinfo target))
  (define type (constant-info-type cinfo))
  (define iinfo (inductive-iinfo type))
  (define dispatch ((inductive-info-dispatch iinfo) method-ls))
  ;; NB: The constant info field plus the parameters
  (define fields-to-drop (+ 1 (inductive-info-parameter-count iinfo)))
  (let loop ([e target])
    (let* ([method (dispatch e)]
           [args (drop (struct->list e) fields-to-drop)]
           [r-args
            (for/list ([x args]
                       [i (in-naturals fields-to-drop)]
                       ;; TODO PERF: memq, in a loop, over numbers
                       #:when (memq i (constant-info-recursive-index-ls (constant-cinfo e))))
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

(define (constant-equal? i1 i2)
  (if (null? i1)
      (equal? i1 i2)
      (equal?/recur (drop (struct->list i1) 1) (drop (struct->list i2) 1) constant-equal?)))

(module+ test
  (require chk)
  (struct Nat inductive () #:transparent)
  (struct z constant () #:transparent)
  (struct s constant (pred) #:transparent)

  ;; TODO PERF: When the make-x functions take no argument, optimize into a singleton structure.
  ;; TODO PERF: When the info does not depend on arguments, optimize info into a singleton structure
  ;; and reference it.
  (define (make-Nat)
    (Nat (inductive-info (Type 0) 0 2 (build-dispatch (list z? s?)))))
  (define (make-z)
    (z (constant-info (make-Nat) 0 null)))
  (define (make-s x)
    (s (constant-info (make-Nat) 1 (list 0)) x))
  ;; TODO PERF: When we make singletons, should be possible to optimize equality checks into eq?
  ;; instead of equal?. Might require defining a genric for constants, instantiating, etc.

  (chk
   #:t (Type 0)
   #:t (Type 1)
   #:t (λ (Type 1) (#%plain-lambda (x) x))
   #:t (Π (Type 1) (#%plain-lambda (x) (Type 1)))
   #:= (#%plain-app (λ (Type 1) (#%plain-lambda (x) x)) (Type 0)) (Type 0)
   #:? z? (make-z)
   #:? s? (make-s make-z)
   #:eq constant-equal? (elim (make-z) void (list (make-z) (lambda (p) p))) (make-z)
   #:! #:eq constant-equal? (elim (make-s (make-s (make-z))) void (list (make-z) (lambda (p) p))) (make-z)
   #:eq constant-equal? (elim (make-s (make-s (make-z))) void (list (make-z) (lambda (p) p))) (make-s (make-z))))

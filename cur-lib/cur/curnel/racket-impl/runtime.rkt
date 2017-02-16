#lang racket/base

(require
 racket/list
 racket/struct
 (for-syntax
  racket/base
  racket/list
  racket/struct-info
  syntax/parse
  racket/syntax))
(provide (all-defined-out))
#|
Cur is implemented by type-checking macro expansion into Racket run-time terms.

The run-time terms are either:
1. A Racket identifier x, as long as the transformer binding type:x also exist. If the transformer
   binding delta:x also exists, the identifer is eligible for delta reduction.
2. A transparent struct inheriting from constant, as described below.
3. The struct (Type i), where i is a natural number
4. The struct (Π t f), where t is a run-time term and f is a run-time term.
5. The struct (λ t f), where t is a run-time term and f is a run-time term.
6. A plain application (#%plain-app rator rand) of a run-time term to a run-time term.
7. A plain application (#%plain-app elim target motive method-ls), where elim is the function defined
   below, target is a run-time term, motive is a run-time term, and method-ls is a list of run-time
   terms.

Any module that requires a Racket library, rather than a Cur library, is considered unsafe.
Cur does not guarantee that requiring such modules with succeed, and if it succeeds Cur does not
guarantee that it will run, and if it runs Cur does not guarnatee safety.
|#


; The run-time representation of univeres. (Type i), where i is a Nat.
; NB: Separate extra-constructor-name makes identifying constructor with free-identifier=? easier.
(struct cur-Type (i) #:transparent #:extra-constructor-name Type #:reflection-name 'Type)

; The run-time representation of Π types. (Π t f), where is a type and f is a procedure that computes
; the result type given an argument.
(struct cur-Π (t f) #:extra-constructor-name Π #:reflection-name 'Π)

; The run-time representation of an application is a Racket plain application.
; (#%plain-app e1 e2)

; The run-time representation of a function. (λ t f), where t is a type and f is a procedure that
; computer the result type given an argument of type t.
(struct cur-λ (t f) #:property prop:procedure (struct-field-index f) #:extra-constructor-name λ #:reflection-name 'λ)

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
; For every inductive type (struct i constant ...), where i is of the format "constant:~a", and a
; transformer binding of type:i must also be defined.
; The binding must be a procedure that takes one argument for every argument to the inductive type,
; and produces a runtime term as a syntax object representing the type of the inductive type.
; TODO: Should probably also provide inductive-info:i, with other type-checking information.

; A constructor is a transparent struct that inherits constant, and has
; prop:parameter-count, prop:dispatch, and prop:recursive-index-ls.
; For every constant (struct c constant ...), , where c is of the format "constant:~a", and a
; transformer binding of type:c must also be defined.
; The binding must be a procedure that takes one argument for every argument to the inductive type,
; and produces a runtime term as a syntax object representing the type of the constant.
; TODO: Should probably also provide constructor-info:i, with other type-checking information.
(struct constant () #:transparent)

;; Target must a constructor, and method-ls must be a list of methods of length equal to the number of
;; constructs for the inductive type of target.
(define (elim target _ . method-ls)
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

; Syntax classes for matching cur run-time terms.
; These classes only do shallow pattern matching, since we assume all run-time terms were
; type-checked.
(begin-for-syntax
  (require "stxutils.rkt")
  (provide
   cur-runtime-identifier
   cur-runtime-constant
   cur-runtime-universe
   cur-runtime-pi
   cur-runtime-lambda
   cur-runtime-app
   cur-runtime-elim
   cur-runtime-term

   cur-runtime-identifier?
   cur-runtime-constant?
   cur-runtime-universe?
   cur-runtime-pi?
   cur-runtime-lambda?
   cur-runtime-app?
   cur-runtime-elim?
   cur-runtime-term?)

  (define-syntax-class/pred cur-runtime-identifier
    (pattern name:id))

  (define-syntax-class/pred cur-runtime-constant
    #:literals (#%plain-app)
    (pattern (#%plain-app name:id args ...)
             #:when
             ; TODO: format-id is annoying; more identifier based conventions. Need something
             ; better. E.g. how do we overload an identifier to do one thing at runtime, and another
             ; with syntax-local-value, the way struct works?
             (let ([v (syntax-local-value (format-id #'name "constant:~a" #'name) (lambda () #f))])
                 (and v (free-identifier=? #'constant (sixth (extract-struct-info v)))))))

  (define universe-constructor (second (extract-struct-info (syntax-local-value #'cur-Type))))

  (define-syntax-class/pred cur-runtime-universe #:attributes (level-syn level)
    #:literals (#%plain-app quote)
    (pattern (#%plain-app constr:id (quote level-syn))
             #:when (free-identifier=? #'constr universe-constructor)
             #:attr level (syntax->datum #'level-syn)))

  (define pi-constructor (second (extract-struct-info (syntax-local-value #'cur-Π))))

  (define-syntax-class/pred cur-runtime-pi #:attributes (name ann result)
    #:literals (#%plain-app #%plain-lambda)
    (pattern (#%plain-app constr:id ann (#%plain-lambda (name) result))
             #:when (free-identifier=? #'constr pi-constructor)))

  (define lambda-constructor (second (extract-struct-info (syntax-local-value #'cur-λ))))

  (define-syntax-class/pred cur-runtime-lambda #:attributes (name ann body)
    #:literals (#%plain-app #%plain-lambda)
    (pattern (#%plain-app constr:id ann (#%plain-lambda (name) body))
             #:when (free-identifier=? #'constr lambda-constructor)))

  (define-syntax-class/pred cur-runtime-app #:attributes (rator rand)
    #:literals (#%plain-app)
    ; NB: Additional matching to ensure mutually exclusive syntax classes.
    ; TODO: Is this worth the cost? Perhaps Cur could use #%plain-app apply rator rand as the
    ; application form, or so. But that may shift the cost to run-time instead of expansion time.
    (pattern (~and (#%plain-app rator rand)
                   (~not e:cur-runtime-universe)
                   (~not e:cur-runtime-lambda)
                   (~not e:cur-runtime-pi)
                   (~not e:cur-runtime-elim)
                   (~not e:cur-runtime-constant))))

  (define-syntax-class/pred cur-runtime-elim #:attributes (target motive (method-ls 1))
    #:literals (#%plain-app elim)
    (pattern (#%plain-app elim target motive method-ls ...)))

  (define-syntax-class/pred cur-runtime-term
    (pattern e:cur-runtime-identifier)
    (pattern e:cur-runtime-constant)
    (pattern e:cur-runtime-universe)
    (pattern e:cur-runtime-pi)
    (pattern e:cur-runtime-lambda)
    (pattern e:cur-runtime-app)
    (pattern e:cur-runtime-elim)))

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
        ;; NB: This error should be impossible when used with well-typed code.
        (error 'build-dispatch "Something very very bad has happened.")))))

(module+ test
  (require
   chk
   syntax/parse
   (for-syntax
    (submod "..")
    (except-in racket/base λ)
    syntax/transformer))
  (provide (all-defined-out))

  (struct constant:Nat constant () #:transparent
    #:extra-constructor-name Nat
    #:reflection-name 'Nat
    #:property prop:parameter-count 0)

  ;; TODO PERF: When the type takes no arguments, can we avoid making it a function?
  (define-syntax type:struct:constant:Nat (lambda () #`(Type 0)))

  (define Nat-dispatch (box #f))

  (struct constant:z constant () #:transparent
    #:extra-constructor-name z
    #:reflection-name 'z
    #:property prop:parameter-count 0
    #:property prop:dispatch Nat-dispatch
    #:property prop:recursive-index-ls null)

  (define-syntax type:struct:constant:z (lambda () #`(Nat)))

  (struct constant:s constant (pred) #:transparent
    #:extra-constructor-name s
    #:reflection-name 's
    #:property prop:parameter-count 0
    #:property prop:dispatch Nat-dispatch
    #:property prop:recursive-index-ls (list 0))

  (define-syntax type:struct:constant:s (lambda (x) #`(Nat)))

  (set-box! Nat-dispatch (build-dispatch (list constant:z? constant:s?)))

  (define-syntax type:two #`(Nat))
  (define-syntax delta:two (make-variable-like-transformer #'(s (s (z)))))
  (define two delta:two)

  ;; TODO PERF: Could we remove λ procedure indirect for certain defines? The type is given
  ;; separately, so we may not need the annotations we use the λ indirect for.
  ;; However, the delta: definition has to remain, so it would only be the run-time definition that is
  ;; optimized, resulting in code duplication. Perhaps should be opt-in
  (define-syntax type:plus #`(Π (Nat) (#%plain-lambda (x) (Nat))))
  (define-syntax delta:plus
    (make-variable-like-transformer
     #`(λ (Nat)
         (#%plain-lambda (n1)
           (λ (Nat)
             (#%plain-lambda (n2)
               (elim n1 void n2 (lambda (n1-1) (lambda (ih) (s ih))))))))))

  (define plus delta:plus)

  ;; TODO PERF: When the constant has no fields, optimize into a singleton structure. this can be
  ;; detected at transformer time using struct-info, by a null field-accessor list
  ;; TODO PERF: When we make singletons, should be possible to optimize equality checks into eq?
  ;; instead of equal?.
  ;; "A structure type can override the default equal? definition through the gen:equal+hash generic interface."

  (chk
   #:t (Type 0)
   #:t (Type 1)
   #:t (λ (Type 1) (#%plain-lambda (x) x))
   #:t (Π (Type 1) (#%plain-lambda (x) (Type 1)))
   #:= (#%plain-app (λ (Type 1) (#%plain-lambda (x) x)) (Type 0)) (Type 0)
   #:? constant:z? (z)
   #:? constant:s? (s z)
   #:= (elim (z) void (z) (lambda (p) (lambda (ih) p))) (z)
   #:! #:= (elim (s (s (z))) void (z) (lambda (p) (lambda (ih) p))) (z)
   #:= (elim (s (s (z))) void (z) (lambda (p) (lambda (ih) p))) (s (z))
   #:= (s (s (s (s (z))))) ((plus (s (s (z)))) (s (s (z)))))

  (begin-for-syntax
    (require chk)

    (chk
     #:? cur-runtime-universe? #'(Type 0)
     #:? cur-runtime-term? #'(Type 0)
     #:! #:? cur-runtime-identifier? #'(Type 0)
     #:! #:? cur-runtime-constant? #'(Type 0)
     #:! #:? cur-runtime-lambda? #'(Type 0)
     #:! #:? cur-runtime-pi? #'(Type 0)
     #:! #:? cur-runtime-app? #'(Type 0)
     #:! #:? cur-runtime-elim? #'(Type 0)
     #:? cur-runtime-identifier? #'two
     #:? cur-runtime-term? #'two
     #:! #:? cur-runtime-constant? #'two
     #:! #:? cur-runtime-universe? #'two
     #:! #:? cur-runtime-pi? #'two
     #:! #:? cur-runtime-lambda? #'two
     #:! #:? cur-runtime-app? #'two
     #:! #:? cur-runtime-elim? #'two
     #:? cur-runtime-pi? #'(Π (Type 0) (lambda (x) x))
     #:? cur-runtime-term? #'(Π (Type 0) (lambda (x) x))
     #:! #:? cur-runtime-lambda? #'(Π (Type 0) (lambda (x) x))
     #:! #:? cur-runtime-app? #'(Π (Type 0) (lambda (x) x))
     #:! #:? cur-runtime-elim? #'(Π (Type 0) (lambda (x) x))
     #:! #:? cur-runtime-universe? #'(Π (Type 0) (lambda (x) x))
     #:! #:? cur-runtime-identifier? #'(Π (Type 0) (lambda (x) x))
     #:! #:? cur-runtime-constant? #'(Π (Type 0) (lambda (x) x))
     #:? cur-runtime-constant? #'(z)
     #:! #:? cur-runtime-identifier? #'(z)
     #:! #:? cur-runtime-app? #'(z)
     #:! #:? cur-runtime-universe? #'(z)
     #:? cur-runtime-constant? #'(s (z))
     #:! #:? cur-runtime-app? #'(s (z))
     #:? cur-runtime-lambda? #'(λ (Type 0) (lambda (x) x))
     #:! #:? cur-runtime-pi? #'(λ (Type 0) (lambda (x) x))
     #:! #:? cur-runtime-app? #'(λ (Type 0) (lambda (x) x))
     #:? cur-runtime-app? #'(plus (z))
     #:? cur-runtime-term? #'(plus (z))
     #:! #:? cur-runtime-constant? #'(plus (z))
     #:! #:? cur-runtime-elim? #'(plus (z))
     #:! #:? cur-runtime-identifier? #'(plus (z))
     #:! #:? cur-runtime-universe? #'(plus (z))
     #:! #:? cur-runtime-lambda? #'(plus (z))
     #:! #:? cur-runtime-pi? #'(plus (z))
     #:? cur-runtime-app? #'((plus (z)) (z))
     #:? cur-runtime-term? #'((plus (z)) (z))
     #:? cur-runtime-elim? #'(elim (z) void (z) (s (z)))
     #:? cur-runtime-term? #'(elim (z) void (z) (s (z)))
     #:! #:? cur-runtime-app? #'(elim (z) void (z) (s (z)))
     #:! #:? cur-runtime-constant? #'(elim (z) void (z) (s (z)))
     #:! #:? cur-runtime-lambda? #'(elim (z) void (z) (s (z)))
     #:! #:? cur-runtime-pi? #'(elim (z) void (z) (s (z))))))

#lang racket/base

(require
 (only-in racket/list drop)
 (only-in racket/struct struct->list)
 (for-syntax
  racket/base
  syntax/parse))
(provide
 #%plain-app
 #%plain-lambda
 quote

 cur-Type
 cur-Π
 cur-apply
 cur-λ
 cur-elim

 (struct-out constant)

 prop:parameter-count
 parameter-count-ref

 prop:dispatch
 dispatch-ref

 prop:recursive-index-ls
 recursive-index-ls-ref)

#|
Cur is implemented by type-checking macro expansion into Racket run-time terms.

TODO: Shouldn't these be curnel-terms, not run-time terms? Maybe not, if we're calling the Surface
language core "Curnel"

The run-time terms are either:
1. A Racket identifier x, as long as the binding x at one phase higher is bound to an identifier-info.
2. A transparent struct inheriting from constant, as described below.
3. The struct (cur-Type i), where i is a natural number
4. The struct (cur-Π t f), where t is a run-time term and f is a run-time term.
5. The struct (cur-λ t f), where t is a run-time term and f is a run-time term.
6. A plain application (#%plain-app cur-apply rator rand) of a run-time term to a run-time term.
7. A plain application (#%plain-app cur-elim target motive method-ls), where elim is the function defined
   below, target is a run-time term, motive is a run-time term, and method-ls is a list of run-time
   terms.

Any module that requires a Racket library, rather than a Cur library, is considered unsafe.
Cur does not guarantee that requiring such modules with succeed, and if it succeeds Cur does not
guarantee that it will run, and if it runs Cur does not guarnatee safety.
|#

; The run-time representation of univeres. (cur-Type i), where i is a Nat.
; NB: Separate extra-constructor-name makes identifying constructor with free-identifier=? easier.
(struct Type (i) #:transparent #:extra-constructor-name cur-Type)

; The run-time representation of Π types. (cur-Π t f), where is a type and f is a procedure that computes
; the result type given an argument.
(struct Π (t f) #:extra-constructor-name cur-Π)

; The run-time representation of an application is a Racket plain application.
; (#%plain-app cur-apply e1 e2)
(define (cur-apply rator rand) (rator rand))

; The run-time representation of a function. (cur-λ t f), where t is a type and f is a procedure that
; computer the result type given an argument of type t.
(struct λ (t f) #:property prop:procedure 1 #:extra-constructor-name cur-λ)

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

(begin-for-syntax
  (provide
   (struct-out constant-info)
   (struct-out identifier-info))

  ;; TODO PERF: Could use vectors instead of lists; since we store the count anyway... or maybe we won't
  ;; need to by storing param and index decls separately.
  (struct constant-info (type-constr param-count param-name-ls param-ann-ls index-name-ls index-ann-ls
                                     constructor-count constructor-ls constructor-index
                                     recursive-index-ls))

  (struct identifier-info (type delta-def)))

; A Cur identifier is any identifier that is bound at phase j to a runtime term and bound at phase j+1
; to an identifier-info.

; An inductive type is a transparent struct that inherits constant, and has
; prop:parameter-count.
; The sturct should have a constructor D that is not bound in the transformer environment, but is bound
; as a constructor at phase j and is bound to a constant-info as phase j+1.
; The constant-info-type-constr must be a procedure that takes one argument for every argument to the
; inductive type, and produces a runtime term as a syntax object representing the type of the
; inductive type.

; A constructor is a transparent struct that inherits constant, and has
; prop:parameter-count, prop:dispatch, and prop:recursive-index-ls.
; The struct should have a constructor c that is not bound in the transformer environment, but is bound
; as a constructor at phase j and is bound to a constant-info as phase j+1.
; The constant-info-type-constr must be a procedure that takes one argument for every argument to the
; constant, and produces a runtime term as a syntax object representing the type of the
; constant.
; The type of the constant must be an inductive type, possibly applied to dependent indices.
(struct constant () #:transparent)

;; Target must a constructor, and method-ls must be a list of methods of length equal to the number of
;; constructs for the inductive type of target.
(define (cur-elim target _ . method-ls)
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

   make-cur-runtime-constant
   make-cur-runtime-universe
   make-cur-runtime-pi
   make-cur-runtime-lambda
   make-cur-runtime-app
   make-cur-runtime-elim

   cur-runtime-identifier?
   cur-runtime-constant?
   cur-runtime-universe?
   cur-runtime-pi?
   cur-runtime-lambda?
   cur-runtime-app?
   cur-runtime-elim?
   cur-runtime-term?

   cur-runtime-literals)

  (define-syntax-class/pred cur-runtime-identifier
    (pattern name:id))

  (define-literal-set cur-runtime-literals (cur-Type cur-Π cur-λ cur-apply cur-elim))
  (define cur-runtime-literal? (literal-set->predicate cur-runtime-literals))

  (define-syntax-class/pred cur-runtime-constant #:attributes (name (rand-ls 1))
    #:literals (#%plain-app)
    (pattern (#%plain-app name:id rand-ls ...)
             #:when (not (cur-runtime-literal? #'name))
             ;; NB: We could double check, but since we're assuming all runtime terms are well-typed,
             ;; we need not bother. Also lets us avoid this annoying format-id hack.
             #;(let ([v (syntax-local-value (format-id #'name "constant:~a" #'name) (lambda () #f))])
                 (and v (free-identifier=? #'constant (sixth (extract-struct-info v)))))))

  (define (make-cur-runtime-constant name rand-ls (syn #f))
    (quasisyntax/loc syn
      (#%plain-app name #,@rand-ls)))

  (define-syntax-class/pred cur-runtime-universe #:attributes (level-syn level)
    #:literals (#%plain-app quote cur-Type)
    (pattern (#%plain-app cur-Type ~! (quote level-syn))
             #:attr level (syntax->datum #'level-syn)))

  ;; Takes a syntax object matching a natrual number, returns a cur-runtime-universe?
  (define (make-cur-runtime-universe i (syn #f))
    (quasisyntax/loc syn (#%plain-app cur-Type '#,i)))

  (define-syntax-class/pred cur-runtime-pi #:attributes (name ann result)
    #:literals (#%plain-app #%plain-lambda cur-Π)
    (pattern (#%plain-app cur-Π ~! ann (#%plain-lambda (name) result))))

  ;; Takes a cur-runtime-term as ann and result, an identifer as name.
  (define (make-cur-runtime-pi ann name result (syn #f))
    (quasisyntax/loc syn
      (#%plain-app cur-Π #,ann (#%plain-lambda (#,name) #,result))))

  (define-syntax-class/pred cur-runtime-lambda #:attributes (name ann body)
    #:literals (#%plain-app #%plain-lambda cur-λ)
    (pattern (#%plain-app cur-λ ~! ann (#%plain-lambda (name) body))))

  (define (make-cur-runtime-lambda ann name body (syn #f))
    (quasisyntax/loc syn
      (#%plain-app cur-λ #,ann (#%plain-lambda (#,name) #,body))))

  (define-syntax-class/pred cur-runtime-app #:attributes (rator rand)
    #:literals (#%plain-app cur-apply)
    (pattern (#%plain-app cur-apply ~! rator rand)))

  (define (make-cur-runtime-app rator rand (syn #f))
    (quasisyntax/loc syn (#%plain-app cur-apply #,rator #,rand)))

  (define-syntax-class/pred cur-runtime-elim #:attributes (target motive (method-ls 1))
    #:literals (#%plain-app cur-elim)
    (pattern (#%plain-app cur-elim ~! target motive method-ls ...)))

  (define (make-cur-runtime-elim target motive method-ls (syn #f))
    (quasisyntax/loc syn
      (#%plain-app cur-elim #,target #,motive #,@method-ls)))

  (define-syntax-class/pred cur-runtime-term
    (pattern e:cur-runtime-identifier)
    (pattern e:cur-runtime-constant)
    (pattern e:cur-runtime-universe)
    (pattern e:cur-runtime-pi)
    (pattern e:cur-runtime-lambda)
    (pattern e:cur-runtime-app)
    (pattern e:cur-runtime-elim)))

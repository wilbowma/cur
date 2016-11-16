#lang racket/base
#| TODO NB XXX Before merging:
 | 1. Handle all TODOs
 | 2. ensure all error messages are reported with surface expression and source information
 | 3. be consistent about using #' vs attribute. (I seem to think attribute do more than #' even when
 |    referring to pattern variables, but I'm not sure that's true)
 |    (attribute ) should only be used when referring to non-syntax valued attributes.
 | 4. Test
 |    - a. things that should work
 |    - b. things that shouldn't
 | 5. Ensure backwards compatibility
 | ~6. Have Stephen review code/maybe rewrite using his library.~--Library requires term/type/kind
 |     distinction, and has a lot of dependenices. Would complicate core too much.
 | 7. Get rid of boilerplatey stuff; superseded by using library.
 | 8. Abstract errors/make consistent
 |#
;; NB: have to use erased terms in types because the erased terms may have renamed
;; variables, e.g., from the expansion that happens in get-type.

;; TODO: Naming conventions. Lots of awkwardly/adhocly named things in here:
;; number-of-bla should be: bla-count
;; bla index or position should be: bla-index
;; _ should always be used for unreferenced identifier
;; a list of blas is: bla-ls
;; a type annotation is: ann
;; the variable name is: name
;; the operator in an application is: rator
;; the argument in an application is: rand
;; functions have bodies, Π types have results
;; if bla is boolean valued: bla?

(require
 (only-in racket/struct struct->list)
 ;; TODO: maybe don't use curry; results in bad source location for procedures? OTOH, shouldn't really
 ;; be observing the value of a procedure
 (only-in racket/function curry)
 (only-in racket/list drop)
 (for-syntax
  racket/base
  (only-in racket/function curry)
  (only-in racket/syntax format-id)
  syntax/parse))
(provide
 (rename-out
  [cur-type Type]
  [cur-define define]
  [cur-λ λ]
  [cur-Π Π]
  [cur-app #%app]
  [cur-axiom axiom]
  [cur-data data]
  [cur-elim elim]
  #;[cur-var #%variable-reference])
 ;; TODO: export all subforms?
 require only-in for-syntax
 provide
 ;; TODO: Who needs top?
; #%top
 ;; TODO: Need to not export datum
 #%datum
 ;(struct-out Type)
 #%module-begin)


;;; Testing
;;; ------------------------------------------------------------------------
(begin-for-syntax
  (module+ test
    (require chk)))

;;; Debugging
;;; ------------------------------------------------------------------------
(require
 racket/trace
 (for-syntax
  racket/trace))
(begin-for-syntax
  (define (maybe-syntax->datum x)
    (if (syntax? x)
        (syntax->datum x)
        x))

  (current-trace-print-args
   (let ([ctpa (current-trace-print-args)])
     (lambda (s l kw l2 n)
       (ctpa s (map maybe-syntax->datum l) kw l2 n))))
  (current-trace-print-results
   (let ([ctpr (current-trace-print-results)])
     (lambda (s l n)
       (ctpr s (map maybe-syntax->datum l) n))))

  (require racket/list)
  (define (and-print . e)
    (map (compose displayln maybe-syntax->datum) e)
    (last e)))

;;; Reflected (compile-time) and reified (run-time) representations of Curnel terms
;;; ------------------------------------------------------------------------

;; Reified
;; ----------------------------------------------------------------

;; All reified expressions have the syntax-property 'type.
(begin-for-syntax
  (define (reified-get-type e)
    (syntax-property e 'type))

  (define (reified-set-type e t)
    (syntax-property e 'type t))

  (define (reified-copy-type e syn)
    (reified-set-type e (reified-get-type syn))))

; The run-time representation of univeres. (Type i), where i is a Nat.
(struct Type (l) #:transparent)

; The run-time representation of Π types. (Π t f), where is a type and f is a procedure that computes
; the result type given an argument.
(struct Π (t f))
;; TODO: Should unierses and Π types have a run-time representation?

; The run-time representation of an application is a Racket plain application.
; (#%plain-app e1 e2)

; The run-time representation of a function is a Racket plain procedure.
; (#%plain-lambda (f) e)
(begin-for-syntax
  ;; Reified syntax classes match or fail, but do not report errors. That is left to higher levels of
  ;; abstraction.

  ; A syntax class for detecting the constructor of a struct
  ;; TODO: Maybe want #:no-delimit-cut for some of these
  ;; Hm, prevents use in ~not
  (define-syntax-class (constructor constr-syn) #:attributes (constr)
    (pattern x:id
             #:attr constr (syntax-property #'x 'constructor-for)
             #:when (and (attribute constr) (free-identifier=? constr-syn #'constr))))

  (define-syntax-class reified-universe #:attributes (level-syn level)
    #:literals (#%plain-app quote Type)
    (pattern (#%plain-app (~var _ (constructor #'Type)) ~! (quote level-syn:nat))
             #:attr level (syntax->datum #'level-syn)))

  (define (reify-universe syn i)
    (reified-copy-type (cur-reify (quasisyntax/loc syn (Type (quote i)))) syn))

  (define-syntax-class reified-pi #:attributes (name ann result)
    #:literals (#%plain-app #%plain-lambda Π)
    (pattern (#%plain-app (~var _ (constructor #'Π)) ~! ann (#%plain-lambda (name) result))))

  (define (reify-pi syn x t e)
    (reified-copy-type (cur-reify (quasisyntax/loc syn (Π #,t (#%plain-lambda (#,x) #,e)))) syn))

  (define-syntax-class reified-lambda #:attributes (name ann body)
    #:literals (#%plain-lambda)
    (pattern (#%plain-lambda (name) body)
             ; NB: Require type anotations on variables in reified syntax.
             #:attr ann (reified-get-type #'name)))

  (define (reify-lambda syn x e)
    (reified-copy-type (quasisyntax/loc syn (#%plain-lambda (#,x) #,e)) syn))

  (define-syntax-class reified-app #:attributes (rator rand)
    #:literals (#%plain-app)
    (pattern (#%plain-app rator rand)))

  (define (reify-app syn e . rest)
    (reified-copy-type
     (for/fold ([app (quasisyntax/loc syn #,e)])
               ([arg rest])
       (quasisyntax/loc syn (#%plain-app #,app #,arg)))
     syn))

  ;; TODO x is a bad name
  ;; TODO: methods should be method-ls
  (define-syntax-class reified-elim #:attributes (x target motive (methods 1))
    #:literals (#%plain-app)
    (pattern (#%plain-app x:id target motive methods ...)
             #:when (syntax-property #'x 'elim)))

  (define (reify-elim syn x d m methods)
    (reified-copy-type (quasisyntax/loc syn (#%plain-app #,x #,d #,m #,@methods)) syn))

  ;; Reification: turn a compile-time term into a run-time term.
  ;; This is done implicitly via macro expansion; each of the surface macros define the
  ;; transformation.
  ;; We define one helper for when we need to control reification.
  (define (cur-reify e)
    (local-expand e 'expression null))

  ;; For restricting top-level identifiers, such as define.
  (define-syntax-class top-level-id #:attributes ()
    (pattern x:id
             #:fail-unless (case (syntax-local-context)
                             [(module top-level module-begin) #t]
                             [else #f])
             (raise-syntax-error
              (syntax->datum #'x)
              (format "Can only use ~a at the top-level."
                      (syntax->datum #'x))
              this-syntax)))

  ;;; Reified composite forms

  ;; Constants are nested applications with a constructor or inductive type in head position:
  ;; refieid-constant ::= Θ[c]
  ;; Θ ::= hole (Θ e)
  (define-syntax-class reified-constant #:attributes (constr rand-ls constructor-index)
    (pattern app:reified-app
             #:with e:reified-constant #'app.rator
             ;; NB: Append
             ;; TODO: This one should be eliminated; this is used a lot and could become a bottleneck.
             ;; Maybe need a pre-reified-constant and then reverse the list once
             #:attr rand-ls (append (attribute e.rand-ls) (list #'app.rand))
             #:attr constr #'e.constr
             #:attr constructor-index (attribute e.constructor-index))

    (pattern constr:id
             #:attr rand-ls '()
             #:attr constructor-index (syntax-property #'constr 'constructor-index)
             #:when (syntax-property #'constr 'constant?)))

  ;; Telescopes are nested Π types.
  (define-syntax-class reified-telescope #:attributes (length ann-ls result)
    (pattern e:reified-pi
             #:with tmp:reified-telescope #'e.result
             #:attr result #'tmp.result
             #:attr length (add1 (attribute tmp.length))
             #:attr ann-ls (cons #'e.ann (attribute tmp.ann-ls)))

    (pattern (~and result (~not _:reified-pi))
             #:attr length 0
             #:attr ann-ls '()))

  ;; Axiom telescopes are nested Π types with a universe or constant as the final result
  (define-syntax-class reified-axiom-telescope #:attributes (length ann-ls result)
    (pattern e:reified-telescope
             #:with (~and result (~or _:reified-universe _:reified-constant)) #'e.result
             #:attr length (attribute e.length)
             #:attr ann-ls (attribute e.ann-ls)))

  ;; Inductive telescopes are nested Π types with a universe as the final result.
  (define-syntax-class reified-inductive-telescope #:attributes (length ann-ls result)
    (pattern e:reified-telescope
             #:with result:reified-universe #'e.result
             #:attr length (attribute e.length)
             #:attr ann-ls (attribute e.ann-ls)))

  ;; Constructor telescopes are nested Π types that return a constant with the inductive type type in
  ;; head position.
  (define-syntax-class (reified-constructor-telescope inductive)
    #:attributes (length ann-ls recursive-index-ls result)
    (pattern e:reified-telescope
             #:with result:reified-constant #'e.result
             #:when (cur-equal? #'result.constr inductive)
             #:attr length (attribute e.length)
             #:attr ann-ls (attribute e.ann-ls)
             #:attr recursive-index-ls
             (for/list ([t (attribute ann-ls)]
                        [i (attribute length)]
                        #:when (syntax-parse t
                                 ;; TODO: Can e be a telescope whose result is a reified-constant? Model
                                 ;; suggests yes; see method-type recursive case
                                 [e:reified-constant
                                  (cur-equal? #'e.constr inductive)]
                                 [_ #f]))
               ;; NB: Would like to return x, but can't rely on names due to alpha-conversion
               i))))

;; TODO: Should this be specified last? Probably should work on reified form in curnel, and let users
;; use reflected forms. But see later TODO about problems with types of types, which Types as Macros
;; current approach doesn't support well...

;; Reflected
;; ----------------------------------------------------------------
(begin-for-syntax
  ;; TODO: These reflected versions aren't used anywhere... probably shouldn't be. Should rely on
  ;; above macros, I think.
  (define-syntax-class reflected-universe
    #:literals (cur-type)
    (pattern (cur-type i:nat)))

  (define-syntax-class reflected-pi
    #:literals (cur-Π)
    (pattern (cur-Π (name : ann) result)))

  (define-syntax-class reflected-lambda
    #:literals (cur-λ)
    (pattern (cur-λ (name : ann) body)))

  (define-syntax-class reflected-app
    #:literals (cur-app)
    (pattern (cur-app rator rand)))

  ;; Reflection: turn a run-time term back into a compile-time term.
  ;; This is done explicitly when we need to pattern match.
  (define (cur-reflect e)
    (syntax-parse e
      [x:id e]
      [e:reified-universe
       #`(cur-type e.level-syn)]
      [e:reified-pi
       #`(cur-Π (e.name : #,(cur-reflect #'e.ann)) #,(cur-reflect #'e.result))]
      [e:reified-app
       #`(cur-app #,(cur-reflect #'e.rator) #,(cur-reflect #'e.rand))]
      [e:reified-lambda
       #`(cur-λ (e.name : #,(cur-reflect #'e.ann)) #,(cur-reflect #'e.body))]
      [e:reified-elim
       #`(cur-elim #,(cur-reflect #'e.target) #,(cur-reflect #'e.motive)
                   #,(map cur-reflect (attribute e.methods)))])))

;;; Intensional equality
;;; ------------------------------------------------------------------------
(begin-for-syntax
  (define (subst v x e)
    (syntax-parse e
      [y:id
       #:when (bound-identifier=? e x)
       v]
      [(e ...)
       #`(#,@(map (lambda (e) (subst v x e)) (attribute e)))]
      [_ e]))
  (module+ test
    (define syn-eq? (lambda (x y) (equal? (syntax->datum x) (syntax->datum y))))
    (chk
     #:eq bound-identifier=? (subst #'z #'x #'x) #'z
     #:eq bound-identifier=? (subst #'z #'x #'y) #'y
     ; TODO Not sure how to capture this test; x isn't getting the "right" binding...
     ; but syntax-local-introduce only works in the macro expander ...
     ; maybe should do subst by applying?
     ;; #:eq syn-eq? (subst #'z #'x (expand-syntax-once #'(#%plain-lambda (y) x))) #'(#%plain-lambda (y) z)
     #:eq syn-eq? (subst #'z #'x (expand-syntax-once #'(#%plain-lambda (x) x))) #'(#%plain-lambda (x) x)))

  ;; TODO: Should this be parameterizable, to allow for different eval strategies if user wants?
  ;; TODO: Performance: Should the interpreter operate directly on syntax? Might be better to first
  ;; parse into structs, turn back into syntax later?
  (define (cur-eval syn)
    (syntax-parse syn
      [_:reified-universe syn]
      [_:id syn]
      [e:reified-pi
       (reify-pi syn #'e.name (cur-eval #'e.ann) (cur-eval #'e.result))]
      [e:reified-app
       #:with a (cur-eval #'e.rand)
       (syntax-parse (cur-eval #'e.rator)
         [f:reified-lambda
          (cur-eval (subst #'a #'f.name #'f.body))]
         [e1-
          (reify-app syn #'e1- #'a)])]
      [e:reified-elim
       #:with target:reified-constant #'e.target
       ;; TODO: Maybe recursive args should be a syntax property on the constructor
       #:do [(define recursive-index-ls
               (syntax-property (attribute target.constr) 'recursive-index-ls))]
       ;; TODO: Performance hack: use unsafe version of list operators and such for internal matters
       (cur-eval
        (apply reify-app syn (list-ref (attribute e.methods) (attribute target.constructor-index))
               (for/fold ([m-args (attribute target.rand-ls)])
                         ([arg (attribute target.rand-ls)]
                          [i (in-naturals)]
                          [j recursive-index-ls]
                          ;; TODO: Change all these =s to eq?s
                          #:when (= i j))
                 ;; TODO: Badness 10000; append in a loop
                 (append m-args (list (reify-elim syn #'e.x arg #'e.motive (attribute e.methods)))))))]
      [e:reified-lambda
       (reify-lambda syn #'e.name (cur-eval #'e.body))]
      [_ (error 'cur-eval "Something has gone horribly wrong: ~a" syn)]))

  (define (cur-normalize e)
    ;; TODO:
    ;; Beta reduce until no more betas
    ;; Eta expand while non-lambda term that is of function type.
    ;; alternative: do equality up-to eta expansion. might be
    ;; Reify the runtime syntax into the surface syntax.
    (cur-eval (cur-reify e))
    #;(reify (eta-expand (beta-reduce (cur-reify e)))))

  ;; When are two Cur terms intensionally equal? When they normalize the α-equivalent reified syntax.
  (define (cur-equal? t1 t2)
    (syntax-parse #`(#,(cur-normalize t1) #,(cur-normalize t2))
      [(x:id y:id)
       (free-identifier=? #'x #'y)]
      [(A:reified-universe B:reified-universe)
       (= (attribute A.level) (attribute B.level))]
      ;; TODO: Can we compile surface patterns into the expanded representation? Do we need to? Maybe
      ;; reify does that work
      #;[((cur-Π (x:id : A₁) B₁)
          (cur-Π (y:id : A₂) B₂))]
      [(e1:reified-pi e2:reified-pi)
       (and (cur-equal? #'e1.ann #'e2.ann)
            (cur-equal? #'e1.result (subst #'e1.name #'e2.name #'e2.result)))]
      [(e1:reified-elim e2:reified-elim)
       (and (cur-equal? #'e1.target #'e2.target)
            (cur-equal? #'e1.motive #'e2.motive)
            (map cur-equal? (attribute e1.methods) (attribute e2.methods)))]
      [(e1:reified-app e2:reified-app)
       (and (cur-equal? #'e1.rator #'e2.rator)
            (cur-equal? #'e1.rand #'e2.rand))]
      [(e1:reified-lambda e2:reified-lambda)
       (and (cur-equal? #'e1.ann #'e2.ann)
            (cur-equal? #'e1.body (subst #'e1.name #'e2.name #'e2.body)))]
      [_ #f])))

;;; TODO: subtyping

;;; Nothing before here should be able to error. Things after here might, since they are dealing with
;;; terms before they are type-checked.

;;; Errors
;;; ------------------------------------------------------------------------
(begin-for-syntax
  ;; TODO: Should be catchable; maybe should have hierarchy. See current Curnel

  ;; syn: the source syntax of the error
  ;; expected: a format string describing the expected type or term.
  ;; term: a datum or format string describing the term that did not match the expected property. If a
  ;;       format string, remaining args must be given as rest.
  ;; type: a datum or format string describing the type that did not match the expected property. If a
  ;;       format string, remaining args must be given as rest.
  ;; rest: more datums
  (define (cur-type-error syn expected term type . rest)
    (raise-syntax-error
     'core-type-error
     (apply
      format
      (format "Expected ~a, but found ~a of type ~a."
              expected
              term
              type)
      rest)
     syn)))

;;; Types as Macros; type system helpers.
;;; ------------------------------------------------------------------------
(begin-for-syntax
  (define (fresh [x #f])
    (datum->syntax x (gensym (if x (syntax->datum x) 'x))))

  (define (set-type e t)
    (syntax-property e 'type (syntax-local-introduce t)))

  (define (merge-type-props syn t)
    (if (pair? t)
        ;; TODO: Is there no better way to loop over a cons list?
        ;; TODO: Performance: Should merge-type-props be used when elaborating, to prevent the 'type
        ;; list from growing large?
        (let ([t1 (car t)])
          (let loop ([t (cdr t)])
            (let ([t2 (and (pair? t) (cadr t))])
              (when t2
                (unless (cur-equal? t1 t2)
                  (raise-syntax-error
                   'core-type-error
                   (format "Found multiple incompatible types for ~a: ~a and ~a"
                           syn
                           (syntax->datum t1)
                           (syntax->datum t2))
                   syn))
                (loop (cdr t)))))
          t1)
        t))

  (define (get-type e)
    (define type (syntax-property e 'type))
    ;; NB: This error is a last result; macros in e should have reported error before now.
    (unless type
      (raise-syntax-error
       'internal-error
       "Something terrible has occured. Expected a cur term, but found something else."
       e))
    (cur-normalize (cur-reify (syntax-local-introduce (merge-type-props e type)))))

  ;; When reifying a term in an extended context, the names may be alpha-converted.
  ;; cur-reify/ctx returns both the reified term and the alpha-converted names.
  ;; #`((zv ...) e)
  ;; where zv ... are the alpha-renamed bindings from ctx in e and t
  ;;       e is the well-typed compiled Cur term
  ;; NB: ctx must only contained well-typed types.
  (define (cur-reify/ctx syn ctx)
    (syntax-parse ctx
      #:datum-literals (:)
      #:literals (#%plain-lambda let-values)
      [([x:id t] ...)
       #:with (internal-name ...) (map fresh (attribute x))
       #:with (#%plain-lambda (name ...) (let-values () (let-values () e)))
       (cur-reify
        #`(lambda (#,@(map set-type (attribute internal-name) (attribute t)))
            (let-syntax ([x (make-rename-transformer (set-type #'internal-name #'t))] ...)
              #,syn)))
       #`((name ...) e)]))

  ;; Type checking via syntax classes

  ;; Expect *some* well-typed expression.
  ;; NB: Cannot check that type is well-formed eagerly, otherwise infinite loop.
  (define-syntax-class cur-expr #:attributes (reified type)
    (pattern e:expr
             #:attr reified (cur-reify #'e)
             #:attr type (get-type #'reified)))

  ;; Expect *some* well-typed expression, in an extended context.
  (define-syntax-class (cur-expr/ctx ctx) #:attributes ((name 1) reified type)
    (pattern e:expr
             #:with ((name ...) reified) (cur-reify/ctx #'e ctx)
             #:attr type (get-type #'reified)))

  ;; Expected a well-typed expression of a particular type.
  (define-syntax-class (cur-expr-of-type type) #:attributes (reified)
    (pattern e:cur-expr
             ;; TODO: Subtyping?
             #:fail-unless (cur-equal? #'e.type type)
             (cur-type-error
              this-syntax
              "term of type ~a"
              (syntax->datum #'e)
              (syntax->datum #'e.type)
              (syntax->datum type))
             #:attr reified #'e.reified))

  ;; Expect a well-typed function.
  (define-syntax-class cur-procedure #:attributes (reified type ann name result)
    (pattern e:cur-expr
             #:with (~or type:reified-pi) #'e.type
             #:fail-unless (attribute type)
             (raise-syntax-error
              'core-type-error
              (format "Expected function, but found ~a of type ~a"
                      ;; TODO Should probably be using 'origin  in more error messages. Maybe need principled
                      ;; way to do that.
                      (syntax->datum #'e)
                      ;; TODO: Not always clear how to resugar; probably need some function for this:
                      ;; 1. Sometimes, origin is the best resugaring.
                      ;; 2. Sometimes, just syntax->datum is.
                      ;; 3. Sometimes, it seems none are, because the type was generated in the macro
                      ;; (e.g. the types of univeres) and origin gives a very very bad
                      ;; resugaring.. Maybe a Racket bug? Bug seems likely, happens only with Type and
                      ;; Pi, which go through struct. Other types seem fine.
                      ;(syntax->datum (last (syntax-property (attribute e) 'origin)))
                      ;(syntax->datum #'e.type)
                      #;(third (syntax-property #'f-type 'origin))
                      (syntax->datum (last (syntax-property #'e.type 'origin))))
              #'e)
             #:attr ann #'type.ann
             #:attr name #'type.name
             #:attr result #'type.result
             #:attr reified #'e.reified))

  ;; Expect a well-typed expression whose type is a universe (kind)
  (define-syntax-class cur-kind #:attributes (reified type)
    (pattern e:cur-expr
             ;; TODO: A pattern
             #:with (~or type:reified-universe) #'e.type
             #:fail-unless (attribute type)
             (cur-type-error
              #'e
              "a kind (a type whose type is a universe)"
              (syntax->datum #'e)
              (syntax->datum (last (syntax-property #'e.type 'origin))))
             #:attr reified #'e.reified))

  (define-syntax-class cur-axiom-telescope #:attributes (reified length ann-ls)
    (pattern e:cur-expr
             #:with (~or reified:reified-axiom-telescope) #'e.reified
             #:fail-unless (attribute reified)
             (cur-type-error
              #'e
              "an axiom telescope (a nested Π type whose final result is a universe or a constant)"
              (syntax->datum #'e)
              (syntax->datum (last (syntax-property #'e.type 'origin))))
             #:attr length (attribute reified.length)
             #:attr ann-ls (attribute reified.ann-ls)))

  (define-syntax-class cur-inductive-telescope #:attributes (reified length ann-ls)
    (pattern e:cur-expr
             #:with (~or reified:reified-inductive-telescope) #'e.reified
             #:fail-unless (attribute reified)
             (cur-type-error
              #'e
              "an inductive telescope (a nested Π type whose final result is a universe)"
              (syntax->datum #'e)
              (syntax->datum (last (syntax-property #'e.type 'origin))))
             #:attr length (attribute reified.length)
             #:attr ann-ls (attribute reified.ann-ls)))

  ;; The inductive type must be first in the ctx, which makes sense anyway
  (define-syntax-class (cur-constructor-telescope inductive)
    #:attributes (reified length ann-ls recursive-index-ls)
    (pattern e:cur-expr
             #:with (~or (~var reified (reified-constructor-telescope inductive))) #'e.reified
             #:fail-unless (attribute reified)
             (cur-type-error
              #'e
              "a constructor telescope (a nested Π type whose final result is ~a applied to any indices)"
              (syntax->datum #'e.reified)
              (syntax->datum (last (syntax-property #'e.type 'origin)))
              (syntax->datum inductive))
             #:attr length (attribute reified.length)
             #:attr recursive-index-ls (attribute reified.recursive-index-ls)
             #:attr ann-ls (attribute reified.ann-ls))))

;;; Typing
;;;------------------------------------------------------------------------

(begin-for-syntax
  (require (for-syntax racket/base))

  ;; Can only be used under a syntax-parse
  (define-syntax (⊢ syn)
    (syntax-case syn (:)
      [(_ e : t)
       (quasisyntax/loc syn
         (set-type
          (quasisyntax/loc this-syntax e)
          (quasisyntax/loc this-syntax t)))])))

(define-syntax (cur-type syn)
  (syntax-parse syn
    [(_ i:nat)
     (⊢ (Type i) : (cur-type #,(add1 (syntax->datum #'i))))]))

(define-syntax (cur-Π syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_ (x:id : t1:cur-kind) (~var e (cur-expr/ctx #`([x t1.reified]))))
     #:declare e.type cur-kind
     (⊢ (Π t1.reified (#%plain-lambda (#,(car (attribute e.name))) e.reified)) : e.type)]))

(define-syntax (cur-λ syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_ (x:id : t1:cur-kind) (~var e (cur-expr/ctx #`([x t1.reified]))))
     #:declare e.type cur-kind
     (⊢ (#%plain-lambda (#,(car (attribute e.name))) e.reified) :
        (cur-Π (#,(car (attribute e.name)) : t1.reified) e.type))]))

(begin-for-syntax
  ;; TODO: Maybe mulit-artiy functions would be a good thing. Always currying probably incurs a
  ;; performance hit.
  (define (cur-app* e args)
    (for/fold ([e e])
              ([arg args])
      #`(cur-app #,e #,(car args)))))

(define-syntax (cur-app syn)
  (syntax-parse syn
    [(_ e1:cur-procedure (~var e2 (cur-expr-of-type #'e1.ann)))
     (⊢ (#%plain-app e1.reified e2.reified) :
        #,(cur-reflect (subst #'e2.reified #'e1.name #'e1.result)))]))

(begin-for-syntax
  (define (define-typed-identifier name type reified-term (y (fresh name)))
    #`(begin
        (define-syntax #,name
          (make-rename-transformer
           (set-type (quasisyntax/loc #'#,name #,y)
                     (quasisyntax/loc #'#,name #,type))))
        (define #,y #,reified-term))))

(define-syntax (cur-define syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_:top-level-id name:id body:cur-expr)
     (define-typed-identifier #'name #'body.type #'body.reified)]))

(define-syntax (cur-axiom syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_:top-level-id n:id : type:cur-axiom-telescope)
     ;; TODO: Hmmm no longer can use 'constant to mean constructor or inductive type, but maybe to
     ;; mean axioms too is okay.
     #:do [(define name (syntax-property #'n 'constant? #t))]
     #:with axiom (fresh name)
     #:with make-axiom (format-id name "make-~a" #'axiom #:props name)
     #`(begin
         (struct axiom #,(for/list ([_ (in-range (attribute type.length))]) (fresh)) #:transparent #:reflection-name '#,name)
         #,(define-typed-identifier name #'type.reified #'((curry axiom)) #'make-axiom)
         ;; NB: Need a predicate with a known name to generate eliminators, but need a fresh
         ;; name for struct to handle typing.
         (define #,(format-id name "~a?" name) #,(format-id name "~a?" #'axiom)))]))

(define-for-syntax (syntax-properties e als)
  (for/fold ([e e])
            ([pair als])
    (syntax-property e (car pair) (cdr pair))))

;; TODO: Strict positivity checking
;; NB: To simplify checking, and maximize reuse, we cur-data generates into a series of cur-axioms,
;; a macro that performs positivity checking (TODO), and a macro that generates elimination definition.
;; The advantage of this over doing everying in cur-data (via e.g. helper functions) is that we reuse
;; macro expansion to handle issues of alpha-equivalence.
(define-syntax (_cur-constructor syn)
  (syntax-parse syn
   #:datum-literals (:)
   ;; TODO: Maybe that local expand should be elsewhere, e.g., cur-constructor
   [(_ name (D) : (~var type (cur-constructor-telescope (cur-reify #'D))))
    #`(cur-axiom #,(syntax-properties
                    #'name
                    `((recursive-index-ls . ,(attribute type.recursive-index-ls)))) : type)]))

(define-syntax (_cur-elim syn)
  (syntax-parse syn
   [(_ elim-name D c:cur-expr ...)
    ;; TODO cur-reify
    #:do [(define D- (cur-reify #'D))
          (define constructor-count (syntax-property D- 'constructor-count))
          ;; TODO: Could pass constructor-predicate as a syntax-property...
          ;; TODO: Passing identifiers as syntax properties seems to lose some binding information?
          ;; couldn't do it with elim-name
          (define constructor-predicates (map (curry format-id #'D "~a?") (attribute c)))
          (define method-names (map fresh (attribute c)))]
    #:with ((~var t (cur-constructor-telescope D-)) ...) #'(c.type ...)
    #:with p (syntax-property D- 'param-count)
    #`(define elim-name
        ;; NB: _ is the motive; necessary in the application of elim for compile-time evaluation,
        ;; which may need to recover the type.
        (lambda (e _ #,@method-names)
          (let loop ([e e])
            (cond
              #,@(for/list ([pred? constructor-predicates]
                            [m method-names]
                            [_ (attribute t.length)]
                            [rargs (attribute t.recursive-index-ls)])
                   ;; TODO: Wouldn't it be better to statically generate the dereferencing of each field
                   ;; from the struct? This would also make it easy to place the recursive elimination.
                   ;; Can't do that easily, due to alpha-conversion; won't know the name of the
                   ;; field reference function
                   #`[(#,pred? e)
                      ;; TODO: Efficiency hack: use vector instead of list?
                      (let* ([args (drop (struct->list e) 'p)]
                             ;; TODO: Stub for recursive args
                             ;; apply loop to each recursive arg
                             ;; TODO: should these be lazy? tail recursive?
                             [recursive-index-ls
                              (for/list ([x args]
                                         [i (in-naturals)]
                                         [j '#,rargs]
                                         #:when (eq? i j))
                                (loop x))])
                        ;; NB: the method is curried, so ...
                        ;; TODO: Efficiency hack: attempt to uncurry elim methods?
                        ;; TODO: Abstract this as "curried-apply?"
                        (for/fold ([app #,m])
                                  ([a (append args recursive-index-ls)])
                            (app a)))])))))]))

(define-syntax (cur-data syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_:top-level-id name:id : p:nat type:cur-inductive-telescope (c-name:id : c-type) ...)
     #:do [(define constructor-count (length (attribute c-name)))
           (define elim-name (syntax-property (format-id syn "~a-elim" #'name) 'elim #t))
           (define param-count (syntax->datum #'p))
           (define index-ls (build-list constructor-count values))]
     #:with (a-name ...) (map (λ (n i)
                                (syntax-properties n
                                 `((constant? . #t)
                                   (constructors-inductive . ,#'name)
                                   (param-count . ,param-count)
                                   (constructor-index . ,i))))
                              (attribute c-name)
                              index-ls)
     #`(begin
         (cur-axiom #,(syntax-properties #'name
                       `((inductive? . #t)
                         (constant? . #t)
                         (constructor-ls . ,(attribute a-name))
                         (constructor-count . ,constructor-count)
                         (param-count . ,param-count)
                         (elim-name . ,elim-name))) : type)
         (_cur-constructor a-name (name) : c-type) ...
         (_cur-elim #,elim-name name c-name ...))]))

(begin-for-syntax
  ;; corresponds to check-motive judgment in model
  (define (check-motive syn D params t_D t_motive)
    ;; Apply D and t_D to params
    (define-values (Dp t_Dp)
      (for/fold ([Dp D]
                 [t_Dp t_D])
                ([p params])
        (values
         #`(#%plain-app #,Dp #,p)
         (syntax-parse t_Dp
           [e:reified-pi
            (subst p #'e.name #'e.result)]))))
    (let loop ([Dp Dp]
               [t_Dp t_Dp]
               [t_motive t_motive])
      (syntax-parse #`(#,Dp #,t_Dp #,t_motive)
        [(e e1:reified-universe ~! e2:reified-pi)
         ;; TODO: Not sure why this version doesn't work. Maybe something to do with backtracking
;         #:with (~or result:reified-universe) #'e2.result
;         #:fail-unless (attribute result)
         #:with result:cur-expr #'e2.result
         #:fail-unless (syntax-parse #'result [_:reified-universe #t] [_ #f])
         (raise-syntax-error
          'core-type-error
          (format "Expected result of motive to be a kind, but found something of type ~a."
                  ;; TODO: ad-hoc resugaring
                  (syntax->datum (cur-reflect #'e2.result)))
          syn)
         (unless (cur-equal? #'e #'e2.ann)
           (raise-syntax-error
            'core-type-error
            (format "Expected final argument of motive to be the same type as the target, i.e. ~a, but found ~a."
                    #'e
                    #'e2.ann))
           syn)]
        [(e e1:reified-pi ~! e2:reified-pi)
         (loop #`(#%plain-app e e2.name) (subst #'e2.name #'e1.name #'e1.result) #'e2.result)]
        [_ (error 'check-motive (format "Something terrible has happened: ~a" this-syntax))])))

  ;; TODO: Check recursive arguments; not sure if they can be Ξ[(D e ...)]; see brady2005
  (define (check-method syn name n params motive method constr)
    (define/syntax-parse m:cur-expr method)
    (define/syntax-parse c:cur-expr (cur-app* constr params))
    (define/syntax-parse (~var c-tele (reified-constructor-telescope name)) #'c.type)
    (define rargs (attribute c-tele.recursive-index-ls))
    (let loop ([c-type #'c.type]
               [m-type #'m.type]
               [i 0]
               [target #'c.reified]
               [recursive '()])
      (syntax-parse #`(#,c-type #,m-type)
        [(e1:reified-constant ~! e:reified-telescope)
         #:do [(define expected-return-type (cur-normalize (cur-app* motive `(,@(drop (attribute e1.rand-ls) n) ,target))))]
         #:do [(define return-type
                 (for/fold ([r #'e])
                           ([t (attribute e.ann-ls)]
                            [rarg recursive])
                   ;; TODO: Recomputing some of the recurisve argument things...
                   (syntax-parse (cdr rarg)
                     [e:reified-constant
                      ;; TODO: append
                      #:with r-:reified-pi r
                      #:do [(define ih (cur-normalize (cur-app* motive (append (drop (attribute e.rand-ls) n)
                                                                               (list (car rarg))))))]
                      #:fail-unless (cur-equal? t ih)
                      (raise-syntax-error
                       'core-type-error
                       (format "Expected an inductive hypothesis equal to ~a, but found ~a."
                               ih
                               t)
                       syn
                       t)
                      #'r-.result])))]
         #:fail-unless (cur-equal? return-type expected-return-type)
         (raise-syntax-error
          'core-type-error
          ;; TODO: Resugar
          (format "Expected method to return type ~a, but found return type of ~a"
                  (syntax->datum expected-return-type)
                  (syntax->datum return-type))
          syn)
         (void)]
        [(e1:reified-pi ~! e2:reified-pi)
         ;; TODO: Subtypes? No, I think equal types, since argument.
         #:fail-unless (cur-equal? #'e1.ann #'e2.ann)
         (raise-syntax-error
          'core-type-error
          (format "Expected ~ath method argument to have type ~a, but found type ~a"
                  i
                  #'e1.ann
                  #'e2.ann)
          syn)
         (loop #'e1.result (subst #'e1.name #'e2.name #'e2.result) (add1 i) #`(cur-app #,target e1.name)
               (if (memq i rargs)
                   (cons (cons #'e1.name #'e1.ann) recursive)
                   recursive))]))))

;; TODO: Rewrite and abstract this code omg
(define-syntax (cur-elim syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_ target:cur-expr motive:cur-procedure (method:cur-expr ...))
     #:with (~or type:reified-constant) #'target.type
     #:fail-unless (attribute type)
     (cur-type-error
      syn
      "target to be a fully applied inductive type"
      "found target ~a"
      "~a, which accepts more arguments"
      (syntax->datum #'target)
      (syntax->datum #'target.type))
     #:fail-unless (syntax-property #'type.constr 'inductive?)
     (cur-type-error
      syn
      ;; TODO: Maybe check if axiom and report that? Might be easy to confuse axiom and inductive.
      "target to inhabit an inductive type"
      (syntax->datum #'target)
      (syntax->datum (car (syntax-property (attribute target.type) 'origin))))
     #:do [(define inductive-name #'type.constr)
           (define param-count (syntax-property inductive-name 'param-count))
           (define rand-ls (attribute type.rand-ls))
           (define indices (drop rand-ls param-count))
           (define param-ls (take rand-ls param-count))
           (define method-count (length (attribute method)))]
     #:with elim-name (syntax-property inductive-name 'elim-name)
     #:with n:cur-expr inductive-name
     #:do [(check-motive #'motive inductive-name param-ls #'n.type #'motive.type)]
     #:do [(for ([m (attribute method.reified)]
                 [c (syntax-property inductive-name 'constructor-ls)])
             (check-method syn inductive-name param-count param-ls #'motive.reified m c))]
     #:attr constructor-count (syntax-property inductive-name 'constructor-count)
     #:fail-unless (= (attribute constructor-count) method-count)
     (raise-syntax-error 'core-type-error
                         (format "Expected one method for each constructor, but found ~a constructors and ~a branches."
                                 (attribute constructor-count)
                                 method-count)
                         syn)
     (⊢ (elim-name target.reified motive.reified method.reified ...) :
        ;; TODO: Need cur-reflect anytime there is computation in a type..?
        ;; TODO: append
        #,(cur-reflect (cur-normalize (cur-app* #'motive.reified (append indices (list #'target.reified))))))]))

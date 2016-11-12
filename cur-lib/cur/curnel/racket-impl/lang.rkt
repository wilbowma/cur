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
(require
 (only-in racket/struct struct->list)
 (only-in racket/function curryr)
 (for-syntax
  racket/base
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
 require only-in
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
; The run-time representation of univeres. (Type i), where i is a Nat.
(struct Type (level) #:transparent)

; The run-time representation of Π types. (Π t f), where is a type and f is a procedure that computes
; the body type given an argument.
(struct Π (t f))
;; TODO: Should unierses and Π types have a run-time representation?

; The run-time representation of an application is a Racket plain application.
; (#%plain-app e1 e2)

; The run-time representation of a function is a Racket plain procedure.
; (#%plain-lambda (f) e)
(begin-for-syntax
  ;; A syntax class for detecting the constructor of a struct
  (define-syntax-class (constructor constr-syn)
    (pattern x:id
             #:attr constr (syntax-property #'x 'constructor-for)
             #:when (and (attribute constr) (free-identifier=? constr-syn #'constr))))

  (define-syntax-class reified-universe
    #:literals (#%plain-app quote Type)
    (pattern (#%plain-app (~var constr (constructor #'Type)) ~! (quote level-syn:nat))
             #:attr level (syntax->datum #'level-syn)))

  (define-syntax-class reified-pi
    #:literals (#%plain-app #%plain-lambda Π)
    (pattern (#%plain-app (~var constr (constructor #'Π)) ~! type-ann (#%plain-lambda (name) body))))

  (define-syntax-class reified-lambda
    #:literals (#%plain-lambda)
    (pattern (#%plain-lambda (name) body)
             #:with (_ _ (_ : t)) (get-type this-syntax)
             #:declare t reified-pi
             #:attr type-ann #'t.type-ann))

  (define-syntax-class reified-app
    #:literals (#%plain-app)
    (pattern (#%plain-app operator operand)))

  (define-syntax-class reified-elim
    #:literals (#%plain-app)
    (pattern (#%plain-app x:id discriminant motive methods ...)
             #:when (syntax-property #'x 'elim)))

  (define-syntax-class reified-constant
    #:literals (#%plain-app)
    (pattern (#%plain-app e:reified-constant es ...)
             #:attr args (append (attribute e.args) (attribute es))
             #:attr constr #'e.constr)

    (pattern constr:id
             #:attr args '()
             ;; TODO: Probably inducitves should also have 'constant
             #:when (or (syntax-property #'constr 'constant)
                        (syntax-property #'constr 'inductive))))

  ;; Reification: turn a compile-time term into a run-time term.
  ;; This is done implicitly via macro expansion; each of the surface macros define the
  ;; transformation.
  ;; We define one helper for when we need to control reification.
  (define (cur-local-expand e)
    (local-expand e 'expression null)))

;; TODO: Should this be specified last? Probably should work on reified form in curnel, and let users
;; use reflected forms. But see later TODO about problems with types of types, which Types as Macros
;; current approach doesn't support well...

;; Reflected
;; ----------------------------------------------------------------
(begin-for-syntax
  (define-syntax-class reflected-universe
    #:literals (cur-type)
    (pattern (cur-type i:nat)))

  (define-syntax-class reflected-pi
    #:literals (cur-Π)
    (pattern (cur-Π (name : type-ann) body)))

  (define-syntax-class reflected-lambda
    #:literals (cur-λ)
    (pattern (cur-λ (name : type-ann) body)))

  (define-syntax-class reflected-app
    #:literals (cur-app)
    (pattern (cur-app operator operand)))

  ;; TODO: Part of reflected syntax, but needed in type system.
  ;; Should it be reflected-telescope? cur-telescope?
  (define-syntax-class telescope
    (pattern (cur-Π (x : t1) t2:telescope)
             #:attr hole #'t2.hole
             #:attr xs (cons #'x (attribute t2.xs)))

    (pattern hole:expr
             #:attr xs '()))

  ;; Reflection: turn a run-time term back into a compile-time term.
  ;; This is done explicitly when we need to pattern match.
  (define (cur-reflect e)
    (syntax-parse e
      #:literals (#%plain-app #%plain-lambda)
      [x:id e]
      [e:reified-universe
       #`(cur-type e.level-syn)]
      [e:reified-pi
       #`(cur-Π (e.name : #,(cur-reflect #'e.type-ann)) #,(cur-reflect #'e.body))]
      [e:reified-app
       #`(cur-app #,(cur-reflect #'e.operator) #,(cur-reflect #'e.operand))]
      [e:reified-lambda
       #`(cur-λ (e.name : #,(cur-reflect #'e.type-ann)) #,(cur-reflect #'e.body))])))

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
  (define (cur-eval e)
    (syntax-parse e
      #:literals (#%plain-app #%plain-lambda)
      [_:reified-universe e]
      [_:id e]
      [e:reified-pi
       (cur-local-expand
        #`(cur-Π (e.name : #,(cur-eval #'e.type-ann)) #,(cur-eval #'e.body)))]
      [e:reified-app
       #:with a (cur-eval #'e.operand)
       (syntax-parse (cur-eval #'e.operator)
         [f:reified-lambda
          (cur-eval (subst #'a #'f.name #'f.body))]
         [e1-
          (cur-local-expand
           #`(cur-app e1- a))])]
      [e:reified-elim
       (error "Sorry, can't handle this yet." (syntax->datum #'e))
       #;(cur-eval
        #`(#%plain-app #,(list-ref (attribute e.methods) (attribute e.discriminant.constructor))
                       e.discriminant))
       ]
      [e:reified-lambda
       (cur-local-expand
        #`(cur-λ (e.name : #,(cur-eval #'e.type-ann)) #,(cur-eval #'e.body)))]
      [_ (error 'cur-beta-iota-short "Something has gone horribly wrong: ~a" e)]))

  (define (cur-normalize e)
    ;; TODO:
    ;; Beta reduce until no more betas
    ;; Eta expand while non-lambda term that is of function type.
    ;; alternative: do equality up-to eta expansion. might be
    ;; Reify the runtime syntax into the surface syntax.
    (cur-eval (cur-local-expand e))
    #;(reify (eta-expand (beta-reduce (cur-local-expand e)))))

  ;; When are two Cur terms intensionally equal? When they normalize the α-equivalent reified syntax.
  (define (cur-equal? t1 t2)
    (syntax-parse #`(#,(cur-normalize t1) #,(cur-normalize t2))
      [(x:id y:id)
       (free-identifier=? t1 t2)]
      [(A:reified-universe B:reified-universe)
       (= (attribute A.level) (attribute B.level))]
      ;; TODO: Can we compile surface patterns into the expanded representation? Do we need to? Maybe
      ;; reify does that work
      #;[((cur-Π (x:id : A₁) B₁)
          (cur-Π (y:id : A₂) B₂))]
      [(e1:reified-pi e2:reified-pi)
       (and (cur-equal? #'e1.type-ann #'e2.type-ann)
            (cur-equal? #'e1.body (subst #'e1.name #'e2.name #'e2.body)))]
      [(e1:reified-app e2:reified-app)
       (and (cur-equal? #'e1.operator #'e2.operator)
            (cur-equal? #'e1.operand #'e2.operand))]
      [(e1:reified-lambda e2:reified-lambda)
       (and (cur-equal? #'e1.type-ann #'e2.type-ann)
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

  ;; Helpers; based on Types as Macros
  (define (set-type e t)
    (syntax-property e 'type (syntax-local-introduce t)))

  (define (erase-type e)
    (cur-local-expand e))

  (define (merge-type-props syn t)
    ;; TODO: Check that list is consistent and report error if not
    (if (pair? t) (car t) t))

  (define (get-type e #:ctx [ctx #'()])
    (syntax-parse ctx
      #:datum-literals (:)
      #:literals (#%plain-lambda let-values)
      [([x:id t] ...)
       #:with (yv ...) (map fresh (attribute x))
       #:with (#%plain-lambda (zv ...) (let-values () (let-values () e2)))
       (cur-local-expand
        #`(lambda (yv ...)
            (let-syntax ([x (make-rename-transformer (set-type #'yv #'t))] ...)
              #,e)))
       ;; TODO: Not sure if this is sensible; testing seemed to indicate "no"
       ;#:with (yt ...) (map fresh (attribute x))
       ;#:with (#%plain-lambda (zt ...) (let-values () (let-values () t2)))
       #;(cur-local-expand
          #`(lambda (yt ...)
              (let-syntax ([x (make-rename-transformer (set-type #'yt #'t))] ...)
                #,(merge-type-props e (syntax-property (attribute e2) 'type)))))
       ;; TODO: if t2 is ever #f, an error should be raised. However, this error should be a last resort;
       ;; typed macros should be able to provide their own error message.
       ;; 1. could use exceptions
       ;;    + always get a type error
       ;;    + simplified interface
       ;;    - exceptions feel weird to me
       ;;    - have to remember to handle them in macros
       ;; 2. could pass in an error message
       ;;    + statically enforced that you give a more specific error message
       ;;    + always get a type error
       ;;    - adds some burden to use
       ;;    - may not cover all use cases
       ;; 3. could put in error monad
       ;;    + flexible
       ;;    - may get random, unrelated error if you forget to handle
       ;; look into how types as macros does this
       #:attr maybe-t2 (syntax-property (attribute e2) 'type)
       #:fail-unless (attribute maybe-t2)
       (raise-syntax-error
        'core-type-error
        "Expected a well-typed Curnel term, but found something else"
        (attribute e2))
       #:with t2 (cur-local-expand (syntax-local-introduce (merge-type-props e (attribute maybe-t2))))
       #`((zv ...) (zv ...) (e2 : t2))]))


  ;; TODO: Am I misusing syntax classes to do error checking and not just (or really, any) parsing?

  ;; Make typing easier
  ;; TODO: Should check that type is well-typed? shouldn't be necessary, I think, since get-type
  ;; always expands it's type. Should maybe check that it's not #f
  ;; OTOH, eagarly expanding type might be bad... could send typing universes into an infinite loop.

  ;; Expect *some* well-typed expression.
  (define-syntax-class cur-typed-expr
    (pattern e:expr
             #:with (_ _ (erased : type)) (get-type #'e))

    ;; Shouldn't be necessary, since the term e should have it's own error message if it's not well-typed
    #;(pattern _ #:do [(raise-syntax-error 'core-type-error
                                           "Expected well-typed expression"
                                           #'this-syntax)]))

  ;; Expect *some* well-typed expression, in an extended context.
  (define-syntax-class (cur-typed-expr/ctx ctx)
    (pattern e:expr
             #:with ((value-name) (type-name) (erased : type)) (get-type #'e #:ctx ctx)))

  ;; Expected a well-typed expression of a particular type.
  (define-syntax-class (cur-expr-of-type type)
    (pattern e:cur-typed-expr
             ;; TODO: Subtyping?
             #:fail-unless (cur-equal? #'e.type type)
             (cur-type-error
              this-syntax
              "term of type ~a"
              (syntax->datum #'e)
              (syntax->datum #'e.type)
              (syntax->datum type))
             #:attr erased #'e.erased))

  ;; Expect a well-typed function.
  (define-syntax-class cur-procedure
    (pattern e:cur-typed-expr
             #:attr erased #'e.erased
             #:attr type #'e.type
             #:fail-unless (syntax-parse #'e.type [_:reified-pi #t] [ _ #f])
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
             #:with tmp #'e.type
             #:declare tmp reified-pi
             #:attr arg-type #'tmp.type-ann
             ;; TODO: Bad varible naming; why "type-name"? is it clear that that is the name used in
             ;; the result type to refer to the argument? I think not.
             #:attr type-name #'tmp.name
             #:attr result-type #'tmp.body))

  ;; Expect a well-typed expression whose type is a universe (kind)
  (define-syntax-class cur-kind
    (pattern e:cur-typed-expr
             ;; TODO There's got to be a better way
             #:fail-unless (syntax-parse #'e.type [_:reified-universe #t] [_ #f])
             (raise-syntax-error
              'core-type-error
              (format "Expected a kind (a type whose type is a universe), but found ~a of type ~a"
                      (syntax->datum #'e)
                      (syntax->datum (last (syntax-property #'e.type 'origin))))
              #'e)
             #:attr erased #'e.erased
             #:attr type #'e.type)))

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
    [(_ (x:id : t1:cur-kind) (~var e (cur-typed-expr/ctx #`([x t1.erased]))))
     #:declare e.type cur-kind
     (⊢ (Π t1.erased (lambda (e.value-name) e.erased)) : e.type)]))

(define-syntax (cur-λ syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_ (x:id : t1:cur-kind) (~var e (cur-typed-expr/ctx #`([x t1.erased]))))
     #:declare e.type cur-kind
     ;; TODO: Wish to use t1 instead of t1.erased, to keep types in reflected syntax. But only the
     ;; erased syntax has the right bindings due to how get-type handles bindings/renamings
     (⊢ (#%plain-lambda (e.value-name) e.erased) : (cur-Π (e.type-name : t1.erased) e.type))]))

(define-syntax (cur-app syn)
  (syntax-parse syn
    [(_ e1:cur-procedure (~var e2 (cur-expr-of-type #'e1.arg-type)))
     ;; TODO: This computation seems to be over erased terms, hence t2^ has no type.
     ;; Need to reify t2^ back into the core macros, so it's type will be computed if necessary.
     ;; This may be part of a large problem/solution: need to reify terms after evaluation, so we can
     ;; pattern match on the core syntax and not the runtime representation.
     ;; HMM.. this is not always true.. sometimes it's un-erased?
     ;; NB: Okay, always using reflected syntax as type works so far, but always need to expand syntax in
     ;; get-type... why? .. because all macros exected reified syntax... why not just redesign them to
     ;; expect reflected syntax?
     (⊢ (#%app e1.erased e2.erased) : #,(cur-reflect (subst #'e2.erased #'e1.type-name #'e1.result-type)))]))

(begin-for-syntax
  (define (define-typed-identifier name type erased-term (y (fresh name)))
    #`(begin
        (define-syntax #,name
          (make-rename-transformer
           (set-type (quasisyntax/loc #'#,name #,y)
                     (quasisyntax/loc #'#,name #,type))))
        (define #,y #,erased-term))))

(define-syntax (cur-define syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(e name:id body:cur-typed-expr)
     #:fail-unless (case (syntax-local-context)
                     [(module top-level module-begin) #t]
                     [else #f])
     (raise-syntax-error
      (syntax->datum #'e)
      (format "Can only use ~a at the top-level."
              (syntax->datum #'e))
      syn)
     (define-typed-identifier #'name #'body.type #'body.erased)]))

;; Returns the definitions for the axiom, the constructor (as an identifier) and the predicate (as an identifier).
(define-for-syntax (make-axiom n t)
  (syntax-parse (list n t)
    [(name:id type:telescope)
     #:with axiom (fresh n)
     #:with make-axiom (format-id n "make-~a" (syntax->datum #'axiom) #:props n)
     (values
      #`(begin
          (struct axiom (#,@(attribute type.xs)) #:transparent #:reflection-name 'name)
          #,(define-typed-identifier #'name #'type #'((curryr axiom)) #'make-axiom))
      #'make-axiom
      (format-id n "~a?" (syntax->datum #'axiom)))]
    [_ (error 'make-axiom "Something terrible has happened")]))

(define-syntax (cur-axiom syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(e name:id : type:cur-kind)
     #:fail-unless (case (syntax-local-context)
                     [(module top-level module-begin) #t]
                     [else #f])
     (raise-syntax-error
      (syntax->datum #'e)
      (format "Can only use ~a at the top-level."
              (syntax->datum #'e))
      syn)
     (let-values ([(defs _1 _2) (make-axiom #'name #'type)])
       defs)]))

;; TODO: Strict positivity checking
;; TODO: Recursion
;; TODO: Rewrite and abstract this code omg
(define-syntax (cur-data syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(data name:id : params:nat type
           (c:id : c-type)
           ...)
     #:attr numbers (build-list (length (syntax->list #'(c ...))) values)
     #:with (cs ...) (map (λ (x n)
                            (syntax-property (syntax-property (syntax-property x 'constant #t) 'params
                                                              (syntax->datum #'params)) 'constructor n))
                          (syntax->list #'(c ...))
                          (attribute numbers))
     #:with (m ...) (map fresh (syntax->list #'(c ...)))
     #:attr ls (for/list ([c (syntax->list #'(cs ...))]
                          [t (syntax->list #'(c-type ...))])
                 (let-values ([(defs _ pred?) (make-axiom c t)])
                   (cons defs (λ (e m)
                                #`[(#,pred? #,e)
                                   (if (null? (struct->list #,e))
                                       #,m
                                       (apply #,m (struct->list #,e)))]))))
     #:attr c-defs (map car (attribute ls))
     #:attr branch-templates (map cdr (attribute ls))
     #:attr elim-name (syntax-property (format-id syn "~a-elim" (syntax->datum #'name)) 'elim #t)
     #`(begin
         (cur-axiom #,(syntax-property (syntax-property (syntax-property (syntax-property #'name 'inductive #t)
                                                        'constructors (length (syntax->list #'(c
                                                                                               ...))))
                                                        'params (syntax->datum #'params)) 'elim-name (attribute
                                                                                             elim-name)) : type)
         #,@(attribute c-defs)
         (define #,(attribute elim-name)
           ;; NB: _ is the motive; necessary in the application of elim for compile-time evaluation,
           ;; which may need to recover the type.
           (lambda (e _ m ...)
             (cond
               #,@(map (λ (f m) (f #'e m)) (attribute branch-templates) (syntax->list #'(m ...)))))))]))

(begin-for-syntax
  (define (check-motive mt D)
    (syntax-parse (get-type D)
      [(_ _ (_ : t))
       #'t]
      [_ (error "meow")])))

;; TODO: Type check motive, methods.
(define-syntax (cur-elim syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_ e:cur-typed-expr motive:cur-procedure methods)
     #:with e-type #'e.type
     #:declare e-type cur-typed-expr
     #:fail-unless (syntax-parse #'e-type.type
                     [_:reified-universe #t]
                     [_ #f])
     (cur-type-error
      syn
      "discriminant to be a fully applied inductive type"
      "but found discriminant ~a"
      "~a, which accepts more arguments"
      (syntax->datum #'e)
      (syntax->datum #'e.type))
     ;; TODO: Need reified constant.. but reflected constant .. is the same?
     #:fail-unless (syntax-parse #'e-type.erased
                     [e:reified-constant
                      (syntax-property #'e.constr 'inductive)]
                     [_ #f])
     (cur-type-error
      syn
      ;; TODO: Maybe check if axiom and report that? Might be easy to confuse axiom and inductive.
      "discriminant to inhabit an inductive type"
      (syntax->datum #'e)
      (syntax->datum (car (syntax-property (attribute e.type) 'origin))))
     #:with name
     (syntax-parse #'e-type.erased
       [e:reified-constant
        #'e.constr])
     #:with elim-name
     (syntax-property #'name 'elim-name)
;     #:do [(check-motive #'motive.type #'name)]
     #:attr constructors (syntax-property #'name 'constructors)
     #:fail-unless (= (attribute constructors) (length (syntax->list #'methods)))
     (raise-syntax-error 'core-type-error
                         (format "Expected one method for each constructor, but found ~a constructors and ~a branches."
                                 (attribute constructors)
                                 (length (syntax->list #'methods)))
                         syn)
     #:with ((_ _ (methods^ : _)) ...) (map get-type (syntax->list #'methods))
     ;; TODO: Need indices too
     (⊢ (elim-name e.erased motive.erased methods^ ...) : #,(cur-normalize #`(cur-app motive e)))]))

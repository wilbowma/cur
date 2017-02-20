#lang racket/base

(require
 (for-syntax
  "equiv.rkt"
  "type-reconstruct.rkt"
  "stxutils.rkt"
  "runtime-utils.rkt"
  racket/base
  racket/syntax
  (only-in racket/list last)
  syntax/parse)
 "runtime.rkt")

(provide
 cur-elab
 cur-elab/ctx

 cur-reflect

 typed-Type
 typed-Π
 typed-λ
 typed-app
 typed-elim
 typed-data
 typed-axiom
 typed-define)

#|
The Cur elaborator is also the type-checker, because Type Systems are Macros.

Unlike Type Systems as Macros, we do not use syntax properties to stores types.
Syntax properties do not work well when storing identifiers, across module, or with compilation,
particularly.
They also use a *lot* of space, since each term and subterm has its type attached by the macros.

Instead, each macro elaborates into a runtime term implementing the term in Racket, which is annotated
enough to recompute its type in a simple function.
This means the type system is not easily extended merely by adding macros; we would also need to add a
case to the get-type function.
This could be done using an extensible function, simulated with parameters perhaps.
However, we don't really want the type system to be extensible since we desire a small trusted core.
|#

(begin-for-syntax

  ; Expects a Cur term and produces a cur-runtime-term?, returns a cur-runtime-term? or raises a type error.
  (define cur-elab local-expand-expr)

  (define (cur-elab/ctx syn ctx)
    (call-with-ctx
     ctx
     (lambda ()
       (define intdef (syntax-local-make-definition-context))
       (syntax-local-bind-syntaxes (map car ctx) #f intdef)
       (local-expand syn 'expression null intdef))))

  (define (cur-reflect syn)
    (syntax-parse syn
      [x:cur-runtime-identifier
       syn]
      [e:cur-runtime-universe
       (quasisyntax/loc syn (typed-Type e.level-syn))]
      [e:cur-runtime-pi
       (quasisyntax/loc syn
         (typed-Π (#,(cur-reflect #'e.name) : #,(cur-reflect #'e.ann))
                  #,(cur-reflect #'e.result)))]
      [e:cur-runtime-app
       (quasisyntax/loc syn
         (typed-app #,(cur-reflect #'e.rator) #,(cur-reflect #'e.rand)))]
      [e:cur-runtime-lambda
       (quasisyntax/loc syn
         (typed-λ (#,(cur-reflect #'e.name) : #,(cur-reflect #'e.ann)) #,(cur-reflect #'e.body)))]
      [e:cur-runtime-elim
       (quasisyntax/loc syn
         (typed-elim #,(cur-reflect #'e.target) #,(cur-reflect #'e.motive)
                     #,@(map cur-reflect (attribute e.method-ls))))]))

  ;; TODO: Should be catchable; maybe should have hierarchy. See current Curnel
  ;; TODO: Should be in separate module

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
     syn))

  (define-syntax-class cur-expr #:attributes (reified type)
    (pattern e:expr
             #:attr reified (cur-elab #'e)
             #:attr type (get-type #'reified)))

  (define-syntax-class (cur-expr/ctx ctx) #:attributes (reified type)
    (pattern e:expr
             #:with reified (cur-elab/ctx #'e ctx)
             #:with type (get-type #'reified)))

  (define-syntax-class (cur-expr-of-type type) #:attributes (reified)
    (pattern e:cur-expr
             #:fail-unless (cur-subtype? #'e.type type)
             (cur-type-error
              this-syntax
              "term of type ~a"
              (syntax->datum #'e)
              (syntax->datum (cur-reflect #'e.type))
              (syntax->datum (cur-reflect type)))
             #:attr reified #'e.reified))

  (define-syntax-class cur-kind #:attributes (reified type)
    (pattern e:cur-expr
             ;; TODO: A pattern
             #:with (~or type:cur-runtime-universe) #'e.type
             #:fail-unless (attribute type)
             (cur-type-error
              #'e
              "a kind (a type whose type is a universe)"
              (syntax->datum #'e)
              (syntax->datum (last (syntax-property #'e.type 'origin))))
             #:attr reified #'e.reified))

  (define-syntax-class cur-procedure #:attributes (reified type ann name result)
    (pattern e:cur-expr
             #:with (~or type:cur-runtime-pi) #'e.type
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

  ;; Telescopes are nested Π types.
  (define-syntax-class cur-runtime-telescope #:attributes (length ann-ls result name-ls)
    (pattern e:cur-runtime-pi
             #:with tmp:cur-runtime-telescope #'e.result
             #:attr result #'tmp.result
             #:attr length (add1 (attribute tmp.length))
             #:attr ann-ls (cons #'e.ann (attribute tmp.ann-ls))
             #:attr name-ls (cons #'e.name (attribute tmp.name-ls))
             )

    (pattern (~and result (~not _:cur-runtime-pi))
             #:attr length 0
             #:attr ann-ls '()
             #:attr name-ls '()))

  ;; Axiom telescopes are nested Π types with a universe or constant as the final result
  (define-syntax-class cur-runtime-axiom-telescope #:attributes (length ann-ls result name-ls)
    (pattern e:cur-runtime-telescope
             #:with (~and result (~or _:cur-runtime-universe _:cur-runtime-constant)) #'e.result
             #:attr length (attribute e.length)
             #:attr ann-ls (attribute e.ann-ls)
             #:attr name-ls (attribute e.name-ls)))

  (define-syntax-class cur-axiom-telescope #:attributes (reified length ann-ls name-ls)
    (pattern e:cur-expr
             #:with (~or reified:cur-runtime-axiom-telescope) #'e.reified
             #:fail-unless (attribute reified)
             (cur-type-error
              #'e
              "an axiom telescope (a nested Π type whose final result is a universe or a constant)"
              (syntax->datum #'e)
              (syntax->datum (last (syntax-property #'e.type 'origin))))
             #:attr length (attribute reified.length)
             #:attr ann-ls (attribute reified.ann-ls)
             #:attr name-ls (attribute reified.name-ls))))

(define-syntax (typed-Type syn)
  (syntax-parse syn
    [(_ i:nat)
     (make-cur-runtime-universe #'i syn)]))

(define-syntax (typed-Π syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_ (x:id : t1:cur-kind) (~var e (cur-expr/ctx (list (cons #'x #'t1.reified)))))
     #:declare e.type cur-kind
     (make-cur-runtime-pi #'te.reified #'x #'e.reified syn)]))

(define-syntax (typed-λ syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_ (x:id : t1:cur-kind) (~var e (cur-expr/ctx (list (cons #'x #'t1.reified)))))
     (make-cur-runtime-lambda #'t1.reified #'x #'e.reified syn)]))

(define-syntax (typed-app syn)
  (syntax-parse syn
    [(_ e1:cur-procedure (~var e2 (cur-expr-of-type #'e1.ann)))
     (make-cur-runtime-app #'e1.reified #'e2.reified syn)]))

(define-syntax (typed-define syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_:top-level-id name:id body:cur-expr)
     #:with delta (format-id #'name "delta:~a" #'name)
     #`(begin
         (define-syntax delta (make-variable-like-transformer body.reified))
         (define name delta)
         (define-for-syntax name (identifier-info #'body.type #'delta)))]))

(define-syntax (typed-axiom syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_:top-level-id name:id : type:cur-axiom-telescope)
     #:with c (format-id #'name "constant:~a" #'name)
     #`(begin
         (struct c constant (#,@(attribute type.name-ls)) #:transparent
           #:extra-constructor-name name
           #:reflection name 'name)
         (define-for-syntax name
           (constant-info (lambda (#,@(attribute type.name-ls)) #'type.reified))))]))

;; Inductive types

;; New syntax:
;; (data (Nat) : 0 (Type 0)
;;   ((z) : (Nat))
;;   ((s (x : (Nat))) : (Nat)))
;; No more pretending these things are functions.

;; TODO: positivity is broken, and hence disabled. here are stubs. see github issue
;; NB: arg-flag is #f at the "top-level", i.e., when we're analyzing the top-level type of a
;; constructor, and #t when analyzing an argument to the constructor.
(define-for-syntax (positive D type arg-flag (fail (lambda _ #f)))
  (let loop ([type type])
    (syntax-parse type
      [e:reified-constant
       ;; TODO: I mean this makes sense to me now but
       (not
        (and
         (cur-equal? D #'e.constr)
         arg-flag
         (fail this-syntax)))]
      [e:reified-pi
       (and
        (syntax-parse #'e.ann
          [arg:reified-constant
           #:when (cur-equal? D #'arg.constr)
           #t]
          [_
           (nonpositive D this-syntax fail)])
        (loop #'e.result))]
      [_ #t])))

(define-for-syntax (nonpositive D type (fail (lambda _ #f)))
  (let loop ([type type])
    (syntax-parse type
      [e:reified-pi
       (and (syntax-parse #'e.ann
              [arg:reified-constant
               #:when (cur-equal? D #'arg.constr)
               (fail this-syntax)]
              [_
               (positive D this-syntax #t fail)])
            (loop #'e.result))]
      [_ #t])))

(define-syntax (typed-data syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_:top-level-id (name:id (i:id : itype:cur-expr) ...) : p:nat type:cur-kind
                     ((c-name:id (a:id : (~var atype (cur-expr/ctx (list (cons #'name #'type.reified)))))
                                 ...)
                      :
                      ((~and cD (~fail #:unless (free-identifier=? #'cD #'name)
                                       (format "Expected constructor ~a to return ~a (possibly applied to arguments), but found ~a."
                                               #'c-name
                                               #'name
                                               #'cD)))
                       (~var r (cur-expr/ctx (list (map cons (attribute a) (attribute atype.reified))))) ...))
                     ...)
     #:do [(define constructor-count (length (attribute c-name)))]
     #:with dispatch (format-id #'name "~a-dispatch" #'name)
     #:with structD (format-id #'name "constant:~a" #'name)
     #:with (structC ...) (map (lambda (x) (format-id x "constant:~a" x)))
     #:with (c-index ...) (build-list constructor-count values)
     #:with (c-recursive-index-ls ...)
     (for/list ([type-ls (attribute atype.reified)])
       (for/list ([type type-ls]
                  [i (in-naturals)]
                  #:when (syntax-parse type
                           [e:cur-runtime-constant
                            (free-identifier=? #'e.name #'name)]))
         i))
     #`(begin
         (define dispatch (box #f))
         (struct structD constant (i ...) #:transparent
           #:extra-constructor-name name
           #:reflection-name 'name
           #:property prop:parameter-count 'p)

         (define-for-syntax name
           (constant-info
            (lambda (i ...)
              #'type.reified)
            'p
            #f
            #f))

         (struct structC constant (a ...) #:transparent
           #:extra-constructor-name c-name
           #:reflection-name 'c-name
           #:property prop:parameter-count 'p
           #:property prop:dispatch dispatch
           #:property prop:recursive-index-ls c-recursive-index-ls)
         ...

         (define-for-syntax c-name
           (constant-info
            (lambda (a ...)
              #'(#%plain-app name r.reified ...))
            'p
            c-index
            c-recursive-index-ls)) ...)]))

;; Elim
(begin-for-syntax
  ;; Construct the expected motive type; expects well-typed cur-runtime-term? inputs and must produce
  ;; well-typed cur-runtime-term? outputs
  (define (motive-type syn D params)
    (let loop ([inductive-type (get-type (cur-apply* D params))]
               [indices '()])
      (syntax-parse inductive-type
        [e:cur-runtime-pi
         (make-cur-runtime-pi #'e.ann #'e.name (loop #'e.result (cons #'e.name indices)) syn)]
        [e:reified-universe
         ;; TODO PERF: append, reverse
         ;; NB: (Type 0) is an arbitrary choice here... really, any universe type is valid. Must
         ;; check this is a subtype of motive's type
         (make-cur-runtime-pi (cur-apply* D (append params (reverse indices))) #'_
                              (make-cur-runtime-universe #'0) syn)])))

  ;; Check the given motive against the expected motive type.
  ;; Expected D, params, and motive-t to be cur-runtime-terms that are well-typed in isolation, but
  ;; may not be well-typed when combined.
  ;; TODO: Need to check that D applied to params is well typed before calling motive-type.
  (define (check-motive syn D params motive-t)
    (define/syntax-parse e:cur-expr (typed-app* D params))
    (define expected (motive-type syn D params))
    (cur-subtype? expected motive-t
                (lambda (t1 t2)
                  (raise-syntax-error
                   'core-type-error
                   ;; TODO: Resugar
                   (format "Expected type ~a, but found type of ~a while checking motive."
                           (syntax->datum t1)
                           (syntax->datum t2))
                   syn))))

  (define (branch-type syn constr motive)
    (define/syntax-parse e:cur-expr constr)
    (define/syntax-parse c:cur-runtime-constant (attribute e.reified))
    (define recursive-index-ls (syntax-property (attribute c.constr) 'recursive-index-ls))
    ;; TODO: syntax-property get merged; could be a cons pair not a natural. Applies to others
    (define maybe-param-count (syntax-property (attribute c.constr) 'param-count))
    ;; TODO: Should check consistency
    (define param-count (if (pair? maybe-param-count) (car maybe-param-count) maybe-param-count))
    (let branch-type ([target (attribute c)]
                      [type (attribute e.type)]
                      [i param-count]
                      [r-ann-ls '()])
      (syntax-parse type
        [e:cur-runtime-pi
         ;; NB: Should this be type-checked? I don't think so, since it is generated in the core.
         (make-cur-runtime-pi
          #'e.ann
          #'e.name
          (branch-type (make-cur-runtime-app target #'e.name) #'e.result (add1 i)
                       ;; TODO PERF: memq in a loop. over numbers, should be
                       ;; performant way to do this.
                       (if (memq i recursive-index-ls)
                           (cons (cons #'e.name #'e.ann) r-ann-ls)
                           r-ann-ls))
          syn)]
        [e:cur-runtime-constant
         #:do [(define index-ls (drop (attribute e.rand-ls) param-count))
               (define final-result (cur-apply* motive (append index-ls (list target))))]
         (for/fold ([r final-result])
                   ([p (reverse r-ann-ls)])
           (define/syntax-parse r-ann:cur-runtime-constant (cdr p))
           (define r-index-ls (drop (attribute r-ann.rand-ls) param-count))
           (define r-arg (car p))
           (quasisyntax/loc syn
             (cur-Π (#,(fresh r-arg) : #,(cur-app* motive (append r-index-ls (list r-arg))))
                    #,r)))])))

  (define (check-method syn c motive br-type method)
    (define expected (branch-type syn c motive))
    (cur-subtype? expected br-type
                (lambda (t1 t2)
                  (raise-syntax-error
                   'core-type-error
                   ;; TODO: Resugar
                   (format "Expected type ~a, but found type of ~a while checking method for ~a"
                           (syntax->datum t1)
                           (syntax->datum t2)
                           (syntax->datum c))
                   syn
                   method)))))

(define-syntax (cur-elim syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_ target:cur-expr motive:cur-procedure method:cur-expr ...)
     #:with (~or type:cur-runtime-constant) #'target.type
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
           (define index-ls (drop rand-ls param-count))
           (define param-ls (take rand-ls param-count))
           (define method-count (length (attribute method)))]
     #:with elim-name (dict-ref elim-dict inductive-name)
     #:attr constructor-count (syntax-property inductive-name 'constructor-count)
     #:fail-unless (= (attribute constructor-count) method-count)
     (raise-syntax-error 'core-type-error
                         (format "Expected one method for each constructor, but found ~a constructors and ~a branches."
                                 (attribute constructor-count)
                                 method-count)
                         syn)
     #:do [(check-motive #'motive inductive-name param-ls #'motive.type)]
     #:do [(for ([m (attribute method.type)]
                 [method (attribute method)]
                 [c (dict-ref constructor-dict inductive-name) #;(syntax-property inductive-name 'constructor-ls)])
             (check-method syn (cur-app* c param-ls) #'motive.reified m method))]
     (⊢ (elim-name target.reified motive.reified method.reified ...) :
        ;; TODO: append
        #,(cur-app* #'motive.reified (append index-ls (list #'target.reified))))]))

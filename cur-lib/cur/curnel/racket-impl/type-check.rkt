#lang racket/base

(require
 (for-syntax
  "eval.rkt"
  "equiv.rkt"
  "type-reconstruct.rkt"
  "stxutils.rkt"
  "runtime-utils.rkt"
  racket/base
  racket/syntax
  racket/list
  racket/function
  syntax/parse)
 "runtime.rkt"
 (only-in "runtime-utils.rkt" build-dispatch)
 (only-in racket/function curry))

(provide
 (for-syntax
  cur-elab
  cur-elab/ctx

  cur-reflect)

 typed-Type
 typed-Π
 typed-λ
 typed-app
 typed-elim
 typed-data
 typed-axiom
 typed-define
 deprecated-typed-elim
 cur-void

 (for-syntax
  make-cur-runtime-pi*
  ;; for testing
  cur-expr
  cur-expr/ctx
  cur-expr-of-type
  cur-kind
  cur-procedure

  branch-type
  motive-type
  check-motive
  check-method)
 )
(require racket/trace (for-syntax racket/trace))
(begin-for-syntax
  (define (maybe-syntax->datum syn)
    (if (syntax? syn)
        (syntax->datum syn)
        syn))
  (current-trace-print-args
   (let ([ctpa (current-trace-print-args)])
     (lambda (s l kw l2 n)
       (ctpa s (map maybe-syntax->datum l) kw l2 n))))
  (current-trace-print-results
   (let ([ctpr (current-trace-print-results)])
     (lambda (s l n)
       (ctpr s (map maybe-syntax->datum l) n)))))
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
  (define (cur-elab syn)
    (define/syntax-parse e:in-let-values (local-expand-expr syn))
    (attribute e.body))

  (require racket/trace)
  (define (cur-elab/ctx syn ctx . ls)
    (call-with-ctx
     ctx
     (lambda ()
       (define intdef (syntax-local-make-definition-context))
       (syntax-local-bind-syntaxes (map car ctx) #f intdef)
       (define/syntax-parse e:in-let-values
         (internal-definition-context-introduce intdef (local-expand syn 'expression ls intdef)
                                                'remove))
       (attribute e.body))))

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
             #:with type (get-type/ctx #'reified ctx)))

  (define (cur-type-check syn e t1 t2)
    (unless (cur-subtype? t1 t2)
      (cur-type-error
       syn
       "term of type ~a"
       (syntax->datum e)
       (syntax->datum (cur-reflect t1))
       (syntax->datum (cur-reflect t2)))))

  (define-syntax-class (cur-expr-of-type type) #:attributes (reified)
    (pattern e:cur-expr
             #:do [(cur-type-check this-syntax #'e #'e.type type)]
             #:attr reified #'e.reified))

  (define-syntax-class cur-kind #:attributes (reified type)
    (pattern e:cur-expr
             #:fail-unless (cur-runtime-universe? #'e.type)
             (cur-type-error
              #'e
              "a kind (a type whose type is a universe)"
              (syntax->datum #'e)
              (syntax->datum (cur-reflect #'e.type)))
             #:attr reified #'e.reified
             #:attr type #'e.type))

  ;; TODO: Copy/pasta from cur-kind
  (define-syntax-class (cur-kind/ctx ctx) #:attributes (reified type)
    (pattern (~var e (cur-expr/ctx ctx))
             #:fail-unless (cur-runtime-universe? #'e.type)
             (cur-type-error
              #'e
              "a kind (a type whose type is a universe)"
              (syntax->datum #'e)
              (syntax->datum (cur-reflect #'e.type)))
             #:attr reified #'e.reified
             #:attr type #'e.type))

  (define-syntax-class cur-procedure #:attributes (reified type ann name result)
    (pattern e:cur-expr
             #:fail-unless (cur-runtime-pi? #'e.type)
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
                      (syntax->datum (cur-reflect #'e.type)))
              #'e)
             #:with type:cur-runtime-pi #'e.type
             #:attr ann #'type.ann
             #:attr name #'type.name
             #:attr result #'type.result
             #:attr reified #'e.reified))

  (define-syntax-class cur-axiom-telescope #:attributes (reified type name-ls ann-ls result)
    (pattern e:cur-expr
             #:fail-unless (cur-runtime-axiom-telescope? #'e.reified)
             (cur-type-error
              #'e
              "an axiom telescope (a nested Π type whose final result is a universe or a constant)"
              (syntax->datum #'e)
              (syntax->datum (cur-reflect #'e.type)))
             #:with reified:cur-runtime-axiom-telescope #'e.reified
             #:attr type #'e.type
             #:attr name-ls (attribute reified.name-ls)
             #:attr ann-ls (attribute reified.ann-ls)
             #:attr result #'reified.result))

  (define-syntax-class cur-inductive-telescope #:attributes (reified length name-ls ann-ls result)
    (pattern e:cur-expr
             #:with (~or reified:cur-runtime-inductive-telescope) #'e.reified
             #:fail-unless (attribute reified)
             (cur-type-error
              #'e
              "an inductive telescope (a nested Π type whose final result is a universe)"
              (syntax->datum #'e)
              (syntax->datum (cur-reflect #'e.type)))
             #:attr name-ls (attribute reified.name-ls)
             #:attr result (attribute reified.result)
             #:attr length (attribute reified.length)
             #:attr ann-ls (attribute reified.ann-ls)))

  )

(define-syntax (typed-Type syn)
  (syntax-parse syn
    [(_ i:nat)
     (make-cur-runtime-universe syn #'i)]))

(define-syntax (typed-Π syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_ (x:id : t1:cur-kind) (~var e (cur-expr/ctx (list (cons #'x #'t1.reified)))))
     #:with (~var _ (cur-kind/ctx (list (cons #'x #'t1.reified)))) #'e.reified
     (make-cur-runtime-pi syn #'t1.reified #'x #'e.reified)]))

(define-syntax (typed-λ syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_ (x:id : t1:cur-kind) (~var e (cur-expr/ctx (list (cons #'x #'t1.reified)))))
     (make-cur-runtime-lambda syn #'t1.reified #'x #'e.reified)]))

(define-syntax (typed-app syn)
  (syntax-parse syn
    [(_ e1:cur-procedure (~var e2 (cur-expr-of-type #'e1.ann)))
     (make-cur-runtime-app syn #'e1.reified #'e2.reified)]))

(define-syntax (typed-define syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_:top-level-id name:id body:cur-expr)
     #:with delta (format-id #'name "delta:~a" #'name #:source #'name)
     ;; TODO: Can we avoid duplicating the syntax of the body?
     #`(begin
         (define-for-syntax delta #'body.reified)
         (define name body.reified)
         ;; TODO: Need a provide transformer to provide only when necessary
         (provide (for-syntax name delta))
         (define-for-syntax name (identifier-info #'body.type delta)))]))

(define-syntax (typed-axiom syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_:definition-id name:id : type:cur-axiom-telescope)
     #:with c (format-id this-syntax "constant:~a" #'name #:source #'name)
     #`(begin
         (struct c constant (#,@(attribute type.name-ls)) #:transparent
;           #:extra-constructor-name name1
           #:reflection-name 'name)
         (define name ((curry c)))
         (provide (for-syntax name))
         (define-for-syntax name
           (constant-info #'type.reified #f #f #f #f #f #f #f #f #f)))]))

;; Inductive types

;; TODO: Eventually,New syntax:
;; (data (Nat) : 0 (Type 0)
;;   ((z) : (Nat))
;;   ((s (x : (Nat))) : (Nat)))
;; No more pretending these things are functions.

;; NB: This macro both type checks the data, and caches a lot of the information about the constant.
;; This caching makes typing elim must easier, and faster. We assume eliminating an inductive type is
;; at least as usual as introducing one, justifying this decision.
;; TODO PERF: It might be good to expose two different kinds of data/elim forms, and let users (macros)
;; decide which to generate.

;; TODO: For future
;; NB: Alternative to this method of checking constants: constant could be checked only when used. A
;; constant can only be used:
;; 1. as an annotation
;; 2. as an argument to a function
;; 3. as the target of an elimination.
;; This would break some fundamental assumptions, and I don't see a huge performance different. It
;; would generate some what less code, and would make generating constants slightly easier. But, not
;; worth it.
(define-for-syntax (make-typed-constant-transformer name)
  (let ([info (syntax-local-eval name)])
    (lambda (stx)
      (syntax-parse stx
        [(_ rand-ls:cur-expr ...)
         (let* ([param-name-ls (constant-info-param-name-ls info)]
                [param-ann-ls (constant-info-param-ann-ls info)]
                [index-name-ls (constant-info-index-name-ls info)]
                [index-ann-ls (constant-info-index-ann-ls info)])
           ;; TODO PERF: append in a loop; can we traverse this backwards, checking the last argument
           ;; first? That would be much more efficient, might result in weird type errors though.
           (for/fold ([names '()]
                      [vals '()])
                     ([name (append param-name-ls index-name-ls)]
                      [ann (append param-ann-ls index-ann-ls)]
                      [type (attribute rand-ls.type)]
                      [rand (attribute rand-ls)]
                      [reified (attribute rand-ls.reified)])
             (cur-type-check this-syntax rand type (subst* vals names ann))
             (values (append names (list name)) (append vals (list reified))))
           #`(#%plain-app #,name rand-ls.reified ...))]))))

;; TODO: Should have guarnatee that if a constructor is well-typed, then the type we
;; generate here is well typed. Need more checks above, e.g., to check parameter
;; declarations are consistent, check that constructor type annotation is valid (since
;; that type annotation exists before the type-checking macro exists.)
;; Could solve that by first generating name and it's constant info, then generating separate macro to
;; deal with constructors.

(define-syntax (typed-data syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_:definition-id name:id : p:nat type:cur-inductive-telescope
                      (c-name:id : _c-type)
                     #;((c-name:id (a:id : (~var atype (cur-expr/ctx (list (cons #'name #'type.reified)))))
                                 ...)
                      :
                      ((~and cD (~fail #:unless (free-identifier=? #'cD #'name)
                                       (format "Expected constructor ~a to return ~a (possibly applied to arguments), but found ~a."
                                               #'c-name
                                               #'name
                                               #'cD)))
                       (~var r (cur-expr/ctx (list (map cons (attribute a) (attribute atype.reified))))) ...))
                     ...)
;     #:with ((~var c-type (cur-runtime-constructor-telescope #'name)) ...) #'(_c-type ...)
     #:with runtime-name (fresh #'name)
     #:with (runtime-c-name ...) (map fresh (attribute c-name))
     ;; TODO: Abstract and pull all this out for separate testing.
     #:do [(define param-count (syntax->datum #'p))
           (define constructor-count (length (attribute c-name)))
           (define-values (d-param-name-ls d-index-name-ls)
             (split-at (attribute type.name-ls) param-count))
           (define-values (d-param-ann-ls d-index-ann-ls)
             (split-at (attribute type.ann-ls) param-count))]
     #:with dispatch (format-id this-syntax "~a-dispatch" #'name #:source #'name)
     #:with structD (format-id #'name "constant:~a" #'name #:source #'name)
     #:with (d-param-name ...) d-param-name-ls
     #:with (d-param-ann ...) d-param-ann-ls
     #:with (d-index-name ...) d-index-name-ls
     #:with (d-index-ann ...) d-index-ann-ls
     #`(begin
         (define dispatch (box #f))
         (struct structD constant (#,@(attribute type.name-ls)) #:transparent
;           #:extra-constructor-name runtime-name
           #:reflection-name 'name
           #:property prop:parameter-count 'p)

         (define name ((curry structD)))

         (provide (for-syntax name))
         (define-for-syntax name
           ;; TODO: Really need inductive-info and constructor-info, inheriting constant-info
           (constant-info
            #'type.reified
            #f
            'p
            (list #'d-param-name ...)
            (list #'d-param-ann ...)
            (list #'d-index-name ...)
            (list #'d-index-ann ...)
            '#,constructor-count
            (list #'c-name ...)
            #f
            #f))
;         (define-syntax name (make-typed-constant-transformer #'runtime-name))

         (typed-constructors
          name
          dispatch
          (c-name : _c-type) ...))]))

(define-syntax (typed-constructors stx)
  (syntax-parse stx
    [(_ name dispatch (c-name : _c-type:cur-expr) ...)
     #:with ((~var c-type (cur-runtime-constructor-telescope #'name)) ...) #'(_c-type.reified ...)
     #:do [(define constructor-count (length (attribute c-name)))
           (define param-count (constant-info-param-count (syntax-local-eval #'name)))
           (define-values (ls-ls-name-param-c ls-ls-name-index-c)
             (for/fold ([ls-param '()]
                        [ls-index '()])
                       ([name-ls (attribute c-type.name-ls)])
               (let-values ([(param index) (split-at name-ls param-count)])
                 (values
                  (cons param ls-param)
                  (cons index ls-index)))))
           (define-values (c-param-name-ls-ls c-index-name-ls-ls)
             (values
              (reverse ls-ls-name-param-c)
              (reverse ls-ls-name-index-c)))
           (define-values (ls-ls-ann-param-c ls-ls-ann-index-c)
             (for/fold ([ls-param '()]
                        [ls-index '()])
                       ([ann-ls (attribute c-type.ann-ls)])
               (let-values ([(param index) (split-at ann-ls param-count)])
                 (values
                  (cons param ls-param)
                  (cons index ls-index)))))
           (define-values (c-param-ann-ls-ls c-index-ann-ls-ls)
             (values
              (reverse ls-ls-ann-param-c)
              (reverse ls-ls-ann-index-c)))]
     #:with p param-count
     #:with (structC ...) (map (lambda (x) (format-id x "constant:~a" x #:source x)) (attribute c-name))
     #:with (c-name-pred ...) (map (lambda (x) (format-id x "constant:~a?" x #:source x)) (attribute c-name))
     #:with (c-index ...) (build-list constructor-count values)
     #:with ((c-recursive-index ...) ...) (attribute c-type.recursive-index-ls)
     #:with ((c-param-name ...) ...) c-param-name-ls-ls
     #:with ((c-index-name ...) ...) c-index-name-ls-ls
     #:with ((c-param-ann ...) ...) c-param-ann-ls-ls
     #:with ((c-index-ann ...) ...) c-index-ann-ls-ls
     #:with ((i ...) ...) (attribute c-type.name-ls)
     #`(begin
         (struct structC constant (i ...) #:transparent
;           #:extra-constructor-name runtime-c-name
           #:reflection-name 'c-name
           #:property prop:parameter-count 'p
           #:property prop:dispatch dispatch
           #:property prop:recursive-index-ls (list 'c-recursive-index ...))
         ...

         (define c-name ((curry structC))) ...

         (set-box! dispatch (build-dispatch (list c-name-pred ...)))

         (provide (for-syntax c-name ...))
         (define-for-syntax c-name
           (constant-info
            #'c-type
            #f
            'p
            (list #'c-param-name ...)
            (list #'c-param-ann ...)
            (list #'c-index-name ...)
            (list #'c-index-ann ...)
            '#,constructor-count
            (list #'c-name ...)
            'c-index
            (list 'c-recursive-index ...)))
         ...)]))

;; Elim
(begin-for-syntax
  ;; TODO: Where do I belong? runtime.rkt? cur-apply* is in eval.rkt. Hm. Maybe runtime-utils.
  ;; TODO: cur-apply* should be renamed make-cur-runtime-apply*
  (define (make-cur-runtime-pi* syn name-ls ann-ls result)
    (for/fold ([result result])
              ;; TODO PERF: By using vectors, could efficiently iterate in reverse. That applies to other
              ;; uses of -ls
              ([name (reverse name-ls)]
               [ann (reverse ann-ls)])
      (make-cur-runtime-pi syn ann name result)))

  ;; Construct the expected motive type; expects well-typed cur-runtime-term? inputs and must produce
  ;; well-typed cur-runtime-term? outputs
  (define (motive-type syn D param-ls)
    (let* ([info (syntax-local-eval D)]
           [name-ls (constant-info-index-name-ls info)]
           [param-name-ls (constant-info-param-name-ls info)]
           [ann-ls (map (curry subst* param-ls param-name-ls) (constant-info-index-ann-ls info))])
      ;; TODO PERF: Appends... but not in a loop
      (make-cur-runtime-pi*
       syn
       (append name-ls (list #'_))
       (append ann-ls (list (make-cur-runtime-constant syn D (append param-ls name-ls))))
       ;; NB: (Type 0) is an arbitrary choice here... really, any universe type is valid. Must
       ;; check this is a subtype of motive's type
       (make-cur-runtime-universe syn #'0))))

  ;; Check the given motive against the expected motive type.
  ;; Expects D, params, and motive-t to be cur-runtime-terms that are well-typed.
  ;; TODO: Need to check that params as valid parameters for D before calling this function.
  (define (check-motive syn D param-ls motive-t)
    (define expected (motive-type syn D param-ls))
    (cur-subtype? expected motive-t
                (lambda (t1 t2)
                  (raise-syntax-error
                   'core-type-error
                   ;; TODO: Resugar
                   (format "Expected type ~a, but found type of ~a while checking motive."
                           (syntax->datum t1)
                           (syntax->datum t2))
                   syn))))

  ;; Construct the expected branch type for constr; expects well-typed cur-runtime-term? inputs and
  ;; must produce well-typed cur-runtime-term? outputs
  (define (branch-type syn constr-name param-ls target motive)
    ;; TODO: Maybe need get-type/eval, or always return type in normal form?
    ;; TODO: We already computed the type of target; just pass it in
    (define/syntax-parse e:cur-runtime-constant (cur-eval (get-type target)))
    (let* ([info (syntax-local-eval constr-name)]
           [recursive-index-ls (constant-info-recursive-index-ls info)]
           [param-count (constant-info-param-count info)]
           [name-ls (constant-info-index-name-ls info)]
           ;; TODO: copy/pasta from motive-type
           [param-name-ls (constant-info-param-name-ls info)]
           [ann-ls (map (curry subst* param-ls param-name-ls) (constant-info-index-ann-ls info))])
      ;; TODO PERF: Many append
      (let-values ([(inductive-name-ls inductive-ann-ls)
                    (for/fold ([ih-name-ls '()]
                               [ih-ann-ls '()])
                              ([name name-ls]
                               [ann ann-ls]
                               ;; NB: Start counting *after* the parameters
                               [i (in-naturals param-count)]
                               ;; TODO PERF: memq over a list of numbers; must be more efficient way
                               #:when (memq i recursive-index-ls))
                      (define/syntax-parse e:cur-runtime-constant (cur-eval ann))
                      (values (cons #'_ ih-name-ls)
                              (cons (cur-apply* syn motive
                                                (append (attribute e.index-rand-ls)
                                                        (list name)))
                                    ih-ann-ls)))])
        (make-cur-runtime-pi*
         syn
         ;; TODO Don't I need to reverse inductive-*-ls
         (append name-ls inductive-name-ls)
         (append ann-ls inductive-ann-ls)
         (cur-apply* syn motive
                     ;; NB: Get the indices of the target
                     ;; TODO PERF: Didn't I already compute those in typed-elim?
                     (append (attribute e.index-rand-ls)
                             (list target)))))))

  ;; Check the branch type for the given constructor.
  ;; Expects constr-name, param-ls, motive, br-type to be cur-runtime-terms that are well-typed.
  ;; Expects method to be be surface term, for error messages only
  (define (check-method syn constr-name param-ls target motive br-type method)
    (define expected (branch-type syn constr-name param-ls target motive))
    (cur-subtype? expected br-type
                (lambda (t1 t2)
                  (raise-syntax-error
                   'core-type-error
                   ;; TODO: Resugar
                   (format "Expected type ~a, but found type of ~a while checking method for ~a"
                           (syntax->datum t1)
                           (syntax->datum t2)
                           (syntax->datum constr-name))
                   syn
                   method)))))

(define-syntax (typed-elim syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_ target:cur-expr motive:cur-expr method:cur-expr ...)
     #:attr ttype (cur-eval #'target.type)
     #:fail-unless (cur-runtime-constant? #'ttype)
     (cur-type-error
      syn
      "target to be a constant"
      "target ~a"
      "~a"
      (syntax->datum #'target)
      (syntax->datum #'ttype))
     ;; TODO: That should now be checked by above, but need to test error messages
     ;#:fail-unless (syntax-property #'type.constr 'inductive?)
     #;(cur-type-error
      syn
      ;; TODO: Maybe check if axiom and report that? Might be easy to confuse axiom and inductive.
      "target to inhabit an inductive type"
      (syntax->datum #'target)
      (syntax->datum (car (syntax-property (attribute target.type) 'origin))))
     #:with type:cur-runtime-constant #'ttype
     #:do [(define inductive-name #'type.name)
           (define info (syntax-local-eval inductive-name))
           (define param-count (constant-info-param-count info))
           (define rand-ls (attribute type.rand-ls))
           (define-values (param-ls index-ls)
             (split-at rand-ls param-count))
           (define method-count (length (attribute method)))
           (define constructor-count (constant-info-constructor-count info))
           (define constructor-ls (constant-info-constructor-ls info))]
     #:fail-unless (= constructor-count method-count)
     (raise-syntax-error 'core-type-error
                         (format "Expected one method for each constructor, but found ~a constructors and ~a branches."
                                 constructor-count
                                 method-count)
                         syn)
     #:with (param:cur-expr ...) param-ls
     #:do [(check-motive #'motive inductive-name (attribute param.reified) #'motive.type)]
     #:do [(for ([mtype (attribute method.type)]
                 [method (attribute method.reified)]
                 [constr-name constructor-ls])
             (check-method method constr-name (attribute param.reified) #'target.reified #'motive.reified mtype method))]
     (make-cur-runtime-elim this-syntax #'target.reified #'motive.reified (attribute method.reified))]))

;; Backward compatible elimination syntax
(define-syntax (deprecated-typed-elim syn)
  (syntax-case syn ()
    [(_ _ motive (methods ...) target)
     (quasisyntax/loc syn (typed-elim target motive methods ...))]))

(define-syntax-rule (cur-void)
  (#%plain-app void))

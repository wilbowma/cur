#lang racket/base

(require
 (only-in racket/struct struct->list)
 (only-in racket/function curry)
 (only-in racket/list drop)
 (for-syntax
  racket/base
  syntax/stx
  (only-in racket/function curry curryr)
  (only-in racket/syntax format-id)
  syntax/parse))
(provide
  cur-type
  cur-define
  cur-λ
  cur-Π
  cur-app
  cur-axiom
  cur-data
  cur-elim

  (for-syntax
   fresh
   cur-eval
   cur-normalize
   subst
   cur-equal?
   cur-subtype?
   cur-reflect
   cur-reify
   cur-reify/ctx
   get-type
   set-type

   cur-expr
   cur-expr/ctx

   ))

;; NB: Naming conventions
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

;; NB: have to use erased terms in types because the erased terms may have renamed
;; variables, e.g., from the expansion that happens in get-type.

;;; Some gross mutual stores that seem necessary due to limitations in syntax-properties
(begin-for-syntax
  (provide constructor-dict elim-dict)
  (require racket/dict syntax/id-table)
  (define constructor-dict (make-free-id-table))
  (define elim-dict (make-free-id-table))
  (define def-dict (make-free-id-table))
  ;; TODO: Can we always reflect things back into surface syntax?
  (define id-reflect-dict (make-free-id-table)))

;;; Debugging
;;; ------------------------------------------------------------------------
(require
 racket/trace
 (for-syntax
  racket/trace))
(begin-for-syntax
#;  (define syntax-local-introduce values)
#;  (define syntax-local-identifier-as-binding values)
  (define (maybe-syntax->datum x)
    (if (syntax? x)
        (syntax->datum x)
        x))

  #;(current-trace-print-args
   (let ([ctpa (current-trace-print-args)])
     (lambda (s l kw l2 n)
       (ctpa s (map maybe-syntax->datum l) kw l2 n))))
  #;(current-trace-print-results
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
(struct Type (i) #:transparent)

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
  ;; TODO: Performance: Maybe want #:no-delimit-cut for some of these, but prevents use in ~not
  (define-syntax-class (constructor constr-syn) #:attributes (constr)
    (pattern x:id
             ;; TODO: Something about this causes failure when compiled.
             ;; 'constructor-for is not preserved, so can't use that.
             #:attr constr (local-expand constr-syn 'expression null)
             #:when (and (attribute constr) (free-identifier=? #'x #'constr))))

  (define-syntax-class reified-universe #:attributes (level-syn level)
    #:literals (#%plain-app quote Type)
    (pattern (#%plain-app (~var _ (constructor #'Type)) ~! (quote level-syn:nat))
             #:attr level (syntax->datum #'level-syn)))

  (define (reify-universe syn i)
    (quasisyntax/loc syn (#%plain-app #,(local-expand #'Type 'expression null) (quote #,i))))

  ;; All reified expressions have the syntax-property 'type, except universes
  (define (reified-get-type e)
    (syntax-parse e
      [e:reified-universe
       (reify-universe this-syntax (add1 (attribute e.level)))]
      [_
       (define x (syntax-property e 'type))
       ;; TODO: Should we do something about this? Some reified terms don't have types.. and that's okay...?
       (if x
           (syntax-local-introduce (if (pair? x) (car x) x))
           (begin
             #;(printf "Warning: reified term ~a does not have a type.~n" e)
             x))]))

  (define (reified-set-type e t)
    (if t
        (syntax-property e 'type t #t)
        (begin
          #;(printf "Warning: reified term ~a given #f as a type.~n" e)
          e)))

  (define (reified-copy-type e syn)
    (reified-set-type e (reified-get-type syn)))

  (define-syntax-class reified-pi #:attributes (name ann result)
    #:literals (#%plain-app #%plain-lambda Π)
    (pattern (#%plain-app (~var _ (constructor #'Π)) ~! ann (#%plain-lambda (name) result))))

  (define (reify-pi syn x t e)
    (reified-copy-type (cur-reify (quasisyntax/loc syn (Π #,t (#%plain-lambda (#,x) #,e)))) syn))

  ;; TODO: Look at pattern expanders instead of syntax-classes
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

  (define-syntax-class reified-elim #:attributes (elim target motive (method-ls 1))
    #:literals (#%plain-app)
    (pattern (#%plain-app elim:id target motive method-ls ...)
             #:when (syntax-property #'elim 'elim)))

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

  ;; NB: Used to prevent append in a loop
  (define-syntax-class _reified-constant #:attributes (constr reversed-rand-ls constructor-index)
    (pattern app:reified-app
             #:with e:_reified-constant #'app.rator
             #:attr reversed-rand-ls (cons #'app.rand (attribute e.reversed-rand-ls))
             #:attr constr #'e.constr
             #:attr constructor-index (attribute e.constructor-index))

    (pattern constr:id
             #:attr reversed-rand-ls '()
             #:attr constructor-index (syntax-property #'constr 'constructor-index)
             #:when (syntax-property #'constr 'constant?)))

  (define-syntax-class reified-constant #:attributes (constr rand-ls constructor-index)
    (pattern e:_reified-constant
             #:attr rand-ls (reverse (attribute e.reversed-rand-ls))
             #:attr constr #'e.constr
             #:attr constructor-index (attribute e.constructor-index)))

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
                                 [e:reified-constant
                                  (cur-equal? #'e.constr inductive)]
                                 [_ #f]))
               ;; NB: Would like to return x, but can't rely on names due to alpha-conversion
               i))))

;; Reflected
;; ----------------------------------------------------------------

;; NB: Due to compile-time computation in types, and because types of types are computed via macro
;; expansion, a reflection procedure is necessary when building a new type-level computation that does
;; not yet have a type.
;; TODO: Can I get rid of that requirement by building such types and doing set-type?
(begin-for-syntax
  ;; Reflection: turn a run-time term back into a compile-time term.
  ;; This is done explicitly when we need to pattern match.
  (define (cur-reflect syn)
    (syntax-parse syn
      [x:id
       (dict-ref id-reflect-dict syn syn)]
      [e:reified-universe
       (quasisyntax/loc syn (cur-type e.level-syn))]
      [e:reified-pi
       (quasisyntax/loc syn (cur-Π (#,(cur-reflect #'e.name) : #,(cur-reflect #'e.ann))
                                   #,(subst (cur-reflect #'e.name) #'e.name (cur-reflect #'e.result))))]
      [e:reified-app
       (quasisyntax/loc syn (cur-app #,(cur-reflect #'e.rator) #,(cur-reflect #'e.rand)))]
      [e:reified-lambda
       (quasisyntax/loc syn (cur-λ (#,(cur-reflect #'e.name) : #,(cur-reflect #'e.ann))
                                   #,(subst (cur-reflect #'e.name) #'e.name (cur-reflect #'e.body))))]
      [e:reified-elim
       (quasisyntax/loc syn (cur-elim #,(cur-reflect #'e.target) #,(cur-reflect #'e.motive)
                   #,(map cur-reflect (attribute e.method-ls))))])))

;;; Intensional equality
;;; ------------------------------------------------------------------------
(begin-for-syntax
#| TODO:
  Observed substitution bug in cur-normalize. Changed bound-identifier=? to free-identifier=?, which
  seems to have solve it ...
  > (cur-normalize
   '(#%plain-app
     (#%plain-lambda
      (A13413101341475)
      (#%app
       Π2
       A13413101341475
       (#%plain-lambda
        (anon-parameter134130713413141341479)
        (#%app
         Π2
         (#%plain-app make-List1341258 A13413101341475)
         (#%plain-lambda
          (anon-parameter134130813413211341486)
          (#%plain-app make-List1341258 A13413101341475))))))
     A1341360))
  < '(#%app
    Π2
    A1341360
    (#%plain-lambda
     (anon-parameter134130713413141341479)
     (#%app
      Π2
      (#%plain-app make-List1341258 A13413101341475)
      (#%plain-lambda
       (anon-parameter134130813413211341486)
       (#%plain-app make-List1341258 A13413101341475)))))
  |#
  (define (subst v x syn)
    (syntax-parse syn
      [y:id
       ;; TODO: BAD BAD BAD BAD BAD; need to be bound-identifier, but...
       ;; or maybe not
       #:when (free-identifier=? syn x)
       (quasisyntax/loc syn #,v)]
      [(e ...)
       (datum->syntax syn (map (lambda (e) (subst v x e)) (attribute e)))]
      [_ syn]))
  #;(module+ test
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
      [_:id
       #:attr def (dict-ref def-dict syn #f)
       #:when (attribute def)
       (cur-normalize (quasisyntax/loc syn def))]
      [_:id
       #:when (not (dict-ref def-dict syn #f))
       syn]
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
       #:do [(define recursive-index-ls
               (syntax-property (attribute target.constr) 'recursive-index-ls))]
       ;; TODO: Performance: use unsafe version of list operators and such for internal matters
       ;; TODO: Performance: list-ref; could we make it a vector?
       (cur-eval
        (apply reify-app syn (list-ref (attribute e.method-ls) (attribute target.constructor-index))
               (append (attribute target.rand-ls)
                       (for/fold ([m-args '()])
                                 ([arg (attribute target.rand-ls)]
                                  [i (in-naturals (syntax-property (attribute target.constr) 'param-count))]
                                  ;; TODO: Performance: memq in a loop
                                  #:when (memq i recursive-index-ls))
                         (cons (reify-elim syn #'e.elim arg #'e.motive (attribute e.method-ls)) m-args)))))]
      [e:reified-elim
       (reify-elim syn #'e.elim (cur-eval #'e.target) (cur-eval #'e.motive) (map cur-eval (attribute e.method-ls)))]
      [e:reified-lambda
       (reify-lambda syn #'e.name (cur-eval #'e.body))]
      [_ (raise-syntax-error 'cur-eval (format "Something has gone horribly wrong: ~a" (syntax->datum syn)) syn)]))

  (define (cur-normalize e)
    ;; TODO: eta-expand! or, build into equality
    (cur-eval (cur-reify e)))

  ;; TODO: Need as option to cur-normalize
  ;; TODO: Need generic fold over reified term

  ;; When are two Cur terms intensionally equal? When they normalize the α-equivalent reified syntax.
  (define (cur-equal? t1 t2)
                ;; TODO: Performance: Okay this is stupidly inefficient
    (syntax-parse #`(#,(cur-normalize t1) #,(cur-normalize t2))
      [(x:id y:id)
;       (printf "~a binding: ~a~n" #'x (identifier-binding #'x))
;       (printf "~a binding: ~a~n" #'y (identifier-binding #'y))
       (free-identifier=? #'x #'y)]
      [(A:reified-universe B:reified-universe)
       (= (attribute A.level) (attribute B.level))]
      [(e1:reified-pi e2:reified-pi)
       (and (cur-equal? #'e1.ann #'e2.ann)
            (cur-equal? #'e1.result (subst #'e1.name #'e2.name #'e2.result)))]
      [(e1:reified-elim e2:reified-elim)
       (and (cur-equal? #'e1.target #'e2.target)
            (cur-equal? #'e1.motive #'e2.motive)
            (map cur-equal? (attribute e1.method-ls) (attribute e2.method-ls)))]
      [(e1:reified-app e2:reified-app)
       (and (cur-equal? #'e1.rator #'e2.rator)
            (cur-equal? #'e1.rand #'e2.rand))]
      [(e1:reified-lambda e2:reified-lambda)
       (and (cur-equal? #'e1.ann #'e2.ann)
            (cur-equal? #'e1.body (subst #'e1.name #'e2.name #'e2.body)))]
      [_ #f]))

  (define (cur-subtype? t1 t2)
    ;; TODO: Performance
    (syntax-parse #`(#,(cur-normalize t1) #,(cur-normalize t2))
      [(A:reified-universe B:reified-universe)
       (<= (attribute A.level) (attribute B.level))]
      [(e1:reified-pi e2:reified-pi)
       (and (cur-equal? #'e1.ann #'e2.ann)
            (cur-subtype? #'e1.result (subst #'e1.name #'e2.name #'e2.result)))]
      [(e1 e2)
       ;; TODO: results in extra calls to cur-normalize
       (cur-equal? #'e1 #'e2)])))

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
    (datum->syntax x (gensym (if x (syntax->datum x) 'x)) x x))

  (define (n-fresh n [x #f])
    (for/list ([_ (in-range n)]) (fresh x)))

  (define (set-type e t)
    (syntax-property e 'type (syntax-local-introduce (cur-normalize t)) #t))

  (define (merge-type-props syn t)
    (if (pair? t)
        ;; TODO: Is there no better way to loop over a cons list?
        ;; TODO: Performance: Should merge-type-props be used when elaborating, to prevent the 'type
        ;; list from growing large?
        (let ([t1 (car t)])
          (let loop ([t (cdr t)])
            (let ([t2 (and (pair? t) (car t))])
              (when t2
                ;; TODO: Subtypes?
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

  ;; TODO: What if e is in a context, and we should be using cur-reify/ctx? and cur-normalzie needs to
  ;; run under that? I see now why these were the same function.
  (define (get-type e)
    (define type (reified-get-type e))
    ;; NB: This error is a last result; macros in e should have reported error before now.
    (unless type
      (raise-syntax-error
       'internal-error
       "Something terrible has occured. Expected a cur term, but found something else."
       e))
    type
    #;(syntax-local-introduce (merge-type-props e type)))

  (define-syntax-class in-let-values #:attributes (body)
    #:literals (let-values)
    (pattern (let-values () e:in-let-values)
             #:attr body #'e.body)

    (pattern body))

  ;; When reifying a term in an extended context, the names may be alpha-converted.
  ;; cur-reify/ctx returns both the reified term and the alpha-converted names.
  ;; #`((zv ...) e)
  ;; where zv ... are the alpha-renamed bindings from ctx in e and t
  ;;       e is the well-typed compiled Cur term
  ;; NB: ctx must only contained well-typed types.
  (define (cur-reify/ctx syn ctx)
    (syntax-parse syn
      #:datum-literals (:)
      #:literals (#%plain-lambda let-values)
      [_
       #:with (x ...) (map car ctx)
       #:with (t ...) (map cdr ctx)
       ;; TODO: This is teh cause of many problems. Cannot store t as a type since it may contain
       ;; unbound identifiers, but need to store t as a type or things break.
       #:with (internal-name ...) (map set-type (map fresh (attribute x)) (attribute t))
       #:do [;; TODO: See earlier todo
             (for ([in (attribute internal-name)]
                   [n (attribute x)]
                   [t (attribute t)])
               #;(printf "~a reflects to ~a~n" in (dict-ref id-reflect-dict (syntax-local-introduce n) n))
               ;; TODO: Use syntax-properties; testing show they work fine.
               (dict-set! id-reflect-dict in (dict-ref id-reflect-dict n (set-type n t))))]
       ;; TODO: syntax-parameter support added this hack
       ;; NB: consume arbitrary number of let-values.
       #:with (#%plain-lambda (name ...) e:in-let-values)
       (cur-reify
        #`(lambda (#,@(attribute internal-name))
            ;; TODO: Need let*-syntax
            (let-syntax ([x (make-rename-transformer #'internal-name)] ...)
              #,syn)))
       #:with (#%plain-lambda (tname ...) type)
       (cur-reify
        #`(lambda (#,@(map syntax-local-identifier-as-binding (attribute name)))
            #,(get-type #'e.body)))
       #`((name ...) (tname ...) e.body : #,(syntax-local-introduce #'type))]))

  ;; Type checking via syntax classes

  ;; Expect *some* well-typed expression.
  ;; NB: Cannot check that type is well-formed eagerly, otherwise infinite loop.
  (define-syntax-class cur-expr #:attributes (reified type)
    (pattern e:expr
             #:attr reified (cur-reify #'e)
             #:attr type (get-type #'reified)))

  ;; Expect *some* well-typed expression, in an extended context.
  ;; TODO: name should be name-ls
  (define-syntax-class (cur-expr/ctx ctx) #:attributes ((name 1) (tname 1) reified type)
    (pattern e:expr
             #:with ((name ...) (tname ...) reified : type) (cur-reify/ctx #'e ctx)))

  ;; Expected a well-typed expression of a particular type.
  (define-syntax-class (cur-expr-of-type type) #:attributes (reified)
    (pattern e:cur-expr
             #:fail-unless (cur-subtype? #'e.type type)
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
     ;; NB: Need to store types reified. Using reflected syntax for Type in type of Type causes
     ;; infinite derivations. Instead, we use the reified syntax. If we ever need the type of a
     ;; reified universe, get-type handles that, breaking what would otherwise be an infinite
     ;; expansion.
     #`(Type 'i)]))

(define-syntax (cur-Π syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_ (x:id : t1:cur-kind) (~var e (cur-expr/ctx (list (cons #'x #'t1.reified)))))
     #:declare e.type cur-kind
     (⊢ (Π t1.reified (#%plain-lambda (#,(car (attribute e.name))) e.reified)) : e.type)]))

(define-syntax (cur-λ syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_ (x:id : t1:cur-kind) (~var e (cur-expr/ctx (list (cons #'x #'t1.reified)))))
     #:with result:cur-kind #'e.type
     (⊢ (#%plain-lambda (#,(car (attribute e.name))) e.reified) :
        #;(cur-Π (#,(car (attribute e.name)) : t1.reified) e.type)
        #,(reify-pi #'result (car (attribute e.tname)) #'t1.reified #'e.type))]))

(begin-for-syntax
  ;; TODO: Performance: Maybe mulit-artiy functions.
  (define (cur-app* e args)
    (for/fold ([e e])
              ([arg args])
      #`(cur-app #,e #,arg))))

(define-syntax (cur-app syn)
  (syntax-parse syn
    [(_ e1:cur-procedure (~var e2 (cur-expr-of-type #'e1.ann)))
     (⊢ (#%plain-app e1.reified e2.reified) :
        #,(cur-reflect (subst #'e2.reified #'e1.name #'e1.result)))]))

(begin-for-syntax
  (define (define-typed-identifier name type reified-term (y (format-id name "~a" (fresh name) #:props name)))
    #`(begin
        (define #,y #,reified-term)
        (define-syntax #,name
          (make-rename-transformer
           ;; TODO: Clean this up. Need to be *very* careful when preserving properties
           (format-id #'#,name
                      "~a"
                      #'#,y
                      #:props
                      (set-type
                       (syntax-property #'#,name 'not-free-identifier=? #t #t)
                       #'#,type))))
        ;; TODO: Do I need to provide this? Shouldn't need to; racket can handle moving non-exported
        ;; names across module boundaries
        #;(provide #,y))))

(define-syntax (cur-define syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_:top-level-id name:id body:cur-expr)
     ;; NB: Store definition to get δ reduction
     #:do [(define y (format-id #'name "~a" (fresh #'name) #:props #'name))]
     (dict-set! def-dict y #'body.reified)
     (define-typed-identifier #'name #'body.type #'body.reified y)]))

(define-syntax (cur-axiom syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_:top-level-id n:id : type:cur-axiom-telescope)
     #:with axiom (fresh #'n)
     #:do [(define name (syntax-properties
                         #'n
                         `((constant? . #t)
                           (pred . ,(format-id #'n "~a?" #'axiom)))))]
     #:with make-axiom (format-id name "make-~a" #'axiom #:props name)
     #`(begin
         (struct #,(syntax-local-identifier-as-binding #'axiom) #,(n-fresh (attribute type.length)) #:transparent #:reflection-name '#,name)
         ;; TODO: Cannot store reified types as syntax-properties; else namespace errors ensue
         #,(define-typed-identifier name #'type #'((curry axiom)) #'make-axiom))]))

(define-for-syntax (syntax-properties e als)
  (for/fold ([e e])
            ([pair als])
    (syntax-property e (car pair) (cdr pair) #t)))

;; TODO: Strict positivity checking
(define-syntax (_cur-constructor syn)
  (syntax-parse syn
   #:datum-literals (:)
   [(_ name (D) : (~var type (cur-constructor-telescope #'D)))
    #`(cur-axiom #,(syntax-properties
                    #'name
                    ;; TODO: Maybe adjust for parameters; all uses seem to do this now.
                    `((recursive-index-ls . ,(attribute type.recursive-index-ls)))) : type)]))

(require (for-template (only-in racket/trace trace-define trace-let trace)))
(define-syntax (_cur-elim syn)
  (syntax-parse syn
   [(_ elim-name D c:cur-expr ...)
    #:do [(define constructor-count (syntax-property #'D 'constructor-count))
          (define constructor-predicates (map (curryr syntax-property 'pred) (attribute c.reified)))
          (define method-names (map fresh (attribute c)))]
    #:with ((~var t (cur-constructor-telescope #'D)) ...) #'(c.type ...)
    #:with p (syntax-property #'D 'param-count)
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
                   ;; TODO: Performance: Generate the dereferencing of each field instead of struct->list?
                   ;; Can't do that easily, due to alpha-conversion; won't know the name of the
                   ;; field reference function. Might solve this by storing accessor abstraction in
                   ;; syntax-property of constructor
                   #`[(#,pred? e)
                      ;; TODO: Performance/code size: this procedure should be a (phase 0) function.
                      (let* ([args (drop (struct->list e) 'p)]
                             [recursive-args
                              ;; TODO: Do we not have constructor argument count?
                              (for/list ([x args]
                                         [i (in-naturals 'p)]
                                         ;; TODO: Performance: memq, in a loop
                                         ;; TODO: Performance/code size: Duplicating rargs in code
                                         #:when (memq i '#,rargs))
                                (loop x))])
                        ;; NB: the method is curried, so ...
                        ;; TODO: Performance: attempt to uncurry elim methods?
                        (for/fold ([app #,m])
                                  ([a (append args recursive-args)])
                            (app a)))])))))]))

;; NB: By generating a sequence of macros, we reuse the elaborators environment management to thread
;; alpha-renamed identifiers implicitly, rather than dealing with it ourselves via cur-reify/ctx

(define-syntax (cur-data syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_:top-level-id name:id : p:nat type:cur-inductive-telescope (c-name:id : c-type) ...)
     #:do [(define constructor-count (length (attribute c-name)))
           (define elim-name (syntax-property (format-id syn "~a-elim" #'name) 'elim #t #t))
           (define param-count (syntax->datum #'p))
           (define index-ls (build-list constructor-count values))]
     #:with (a-name ...) (map (λ (n i)
                                (syntax-properties n
                                 `((constant? . #t)
                                   (param-count . ,param-count)
                                   (constructor-index . ,i))))
                              (attribute c-name)
                              index-ls)
     #:with inductive-name (syntax-properties #'name
                             `((inductive? . #t)
                               (constant? . #t)
                               ;; TODO: can't do this since a-name isn't bound yet, doesn't  get bound
                               ;; in the syntax parameter.
                               ;; resorting to global state...
                               ;(constructor-ls . ,(attribute a-name))
                               (constructor-count . ,constructor-count)
                               (param-count . ,param-count)
                               #;(elim-name . ,elim-name)))
     #`(begin
         (cur-axiom inductive-name : type)
         (_cur-constructor a-name (inductive-name) : c-type) ...
         (begin-for-syntax
           (dict-set! constructor-dict (cur-reify #'inductive-name) (list #'a-name ...)))
         (_cur-elim #,elim-name inductive-name c-name ...)
         (begin-for-syntax
           (dict-set! elim-dict (cur-reify #'inductive-name) #'#,elim-name)))]))

;; TODO: Rewrite and abstract this code omg
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
      (syntax-parse #`(#,t_Dp #,t_motive)
        [(e1:reified-universe ~! e2:reified-pi)
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
         (unless (cur-equal? Dp #'e2.ann)
           (raise-syntax-error
            'core-type-error
            (format "Expected final argument of motive to be the same type as the target, i.e. ~a, but found ~a."
                    Dp
                    #'e2.ann))
           syn)]
        [(e1:reified-pi ~! e2:reified-pi)
         (loop #`(#%plain-app #,Dp e2.name) (subst #'e2.name #'e1.name #'e1.result) #'e2.result)]
        [_ (error 'check-motive (format "Something terrible has happened: ~a" this-syntax))])))

  (define (check-method syn name param-count params motive method constr)
    (define/syntax-parse m:cur-expr method)
    (define/syntax-parse c:cur-expr (cur-app* constr params))
    (define/syntax-parse (~var c-tele (reified-constructor-telescope name)) #'c.type)
    (define rargs (attribute c-tele.recursive-index-ls))
;    (printf "Constr type      ~a~n" (syntax->datum (get-type (cur-reify constr))))
;    (printf "Constr           ~a~n" (syntax->datum constr))
;    (printf "Parameters       ~a~n" (map syntax->datum params))
;    (printf "Constrw/ param   ~a~n" (syntax->datum (cur-app* constr params)))
;    (printf "Constructor type ~a~n" (syntax->datum #'c.type))
;    (printf "Method type      ~a~n" (syntax->datum #'m.type))
;    (printf "Recursive indices ~a~n" rargs)
    (let loop ([c-type #'c.type]
               [m-type #'m.type]
               ;; NB: Since c.type and m.type are param adjusted already, index is not.
               [i 0]
               [target #'c.reified]
               [recursive '()])
      (syntax-parse #`(#,c-type #,m-type)
        [(e1:reified-constant ~! e:reified-telescope)
         ;; TODO: No recurisve in expected return type?
         #:do [(define expected-return-type (cur-normalize (cur-app* motive `(,@(drop (attribute e1.rand-ls) param-count) ,target))))]
         #:do [(define return-type
                 (for/fold ([r #'e])
                           ([t (attribute e.ann-ls)]
                            [rarg recursive])
                   ;; TODO: Recomputing some of the recurisve argument things...
                   (syntax-parse (cdr rarg)
                     [e:reified-constant
                      ;; TODO: append in a loop
                      #:with r-:reified-pi r
                      #:do [(define ih (cur-normalize (cur-app* motive (append (drop (attribute e.rand-ls) param-count)
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
         #:fail-unless (cur-subtype? expected-return-type return-type)
         (raise-syntax-error
          'core-type-error
          ;; TODO: Resugar
          (format "Expected method to return type ~a, but found return type of ~a"
                  (syntax->datum expected-return-type)
                  (syntax->datum return-type))
          syn)
         (void)]
        [(e1:reified-pi ~! e2:reified-pi)
         #:fail-unless (cur-equal? #'e1.ann #'e2.ann)
         (raise-syntax-error
          'core-type-error
          (format "Expected argument ~a (0 indexed) to have type ~a, but found type ~a."
                  i
                  (syntax->datum (last (syntax-property #'e1.ann 'origin)))
                  (syntax->datum (last (syntax-property #'e2.ann 'origin))))
          method
          #'e1.name
          (list syn)
          )
         (loop #'e1.result (subst #'e1.name #'e2.name #'e2.result) (add1 i) #`(cur-app #,target e1.name)
               (if (memq i rargs)
                   (cons (cons #'e1.name #'e1.ann) recursive)
                   recursive))]))))

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
           (define index-ls (drop rand-ls param-count))
           (define param-ls (take rand-ls param-count))
           (define method-count (length (attribute method)))]
     #:with elim-name (dict-ref elim-dict inductive-name)
     #:with n:cur-expr inductive-name
     #:do [(check-motive #'motive inductive-name param-ls #'n.type #'motive.type)]
     #:do [(for ([m (attribute method.reified)]
                 [c (dict-ref constructor-dict inductive-name) #;(syntax-property inductive-name 'constructor-ls)])
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
        #,(cur-reflect (cur-normalize (cur-app* #'motive.reified (append index-ls (list #'target.reified))))))]))

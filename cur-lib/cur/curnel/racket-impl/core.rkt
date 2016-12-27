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
   reified-constant
   reified-telescope
   branch-type))

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

;; TODO PERF: Would global dictionaries be less memory intensive than syntax-properties?
(begin-for-syntax
  (provide constructor-dict elim-dict)
  (require racket/dict syntax/id-table)
  (define constructor-dict (make-free-id-table))
  (define elim-dict (make-free-id-table)))

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
;; TODO: Should all reified terms have type in run-time representation, instead of just syntax-property?
;; ----------------------------------------------------------------

; The run-time representation of univeres. (Type i), where i is a Nat.
(struct Type (i) #:transparent)

; The run-time representation of Π types. (Π t f), where is a type and f is a procedure that computes
; the result type given an argument.
(struct Π (t f))

; The run-time representation of an application is a Racket plain application.
; (#%plain-app e1 e2)

; The run-time representation of a function is a Racket plain procedure.
; (#%plain-lambda (f) e)
(begin-for-syntax
  ;; Reified syntax classes match or fail, but do not report errors. That is left to higher levels of
  ;; abstraction.

  ; A syntax class for detecting the constructor of a struct
  ;; TODO PERF: Maybe want #:no-delimit-cut for some of these, but prevents use in ~not
  (define-syntax-class (constructor constr-syn) #:attributes (constr)
    (pattern x:id
             ;; TODO: Something about this causes failure when compiled.
             ;; 'constructor-for is not preserved, so can't use that.
             ;; TODO PERF: Unnnecessary repeated local-expand of constr name. Could require
             ;; fully-expanded name, and define-for-syntax once
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
       (if x
           (syntax-local-introduce (if (pair? x) (car x) x))
           (begin
             #;(printf "Warning: reified term ~a does not have a type.~n" e)
             x))]))

  (define (reified-set-type e t)
    (if t
        ;; TODO: Theory: this syntax property needs to be attached "in the expander", i.e., under a #`. See
        ;; fixes for δreduction discussed below, introduced in commit a6c3d7dbf88cafbcdf65508c8a6649863f9127b5
        ;; Otherwise, compilation will not work.
        ;; After much tinkering, couldn't get rid of the compilation problem. Not sure this theory holds.
        (syntax-property e 'type t #t)
        (begin
          #;(printf "Warning: reified term ~a given #f as a type.~n" e)
          e)))

  (define (reified-copy-type e syn)
    (reified-set-type e (reified-get-type syn)))

  (define-syntax-class reified-pi #:attributes (name ann result)
    #:literals (#%plain-app #%plain-lambda Π)
    (pattern (#%plain-app (~var _ (constructor #'Π)) ~! ann (#%plain-lambda (n) r))
             ;; TODO: Hack; n should already have the right type if substitution is done correctly
             #:attr name (reified-set-type #'n #'ann)
             #:attr result (subst (attribute name) #'n #'r)))

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

(begin-for-syntax
  ;; Reflection: turn a run-time term back into a compile-time term.
  ;; This is done explicitly when we need to pattern match.
  (define (cur-reflect syn)
    (syntax-parse syn
      [x:id
       syn
       ;; TODO: I'd love to reflect the names, but I don't think we can.
       #;(or (syntax-property syn 'reflected-name) syn)]
      [e:reified-universe
       (quasisyntax/loc syn (cur-type e.level-syn))]
      [e:reified-pi
       (quasisyntax/loc syn (cur-Π (#,(cur-reflect #'e.name) : #,(cur-reflect #'e.ann))
                                   ;; TODO: subst should always be called on reified syntax?
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
  ;; TODO PERF: Might be better for if this was syntax directed; avoids trying to substitute
  ;; into non-syntax like quote or 0
  (define (subst v x syn)
    (syntax-parse syn
      [y:id
       #:when (free-identifier=? syn x)
       v]
      [(e ...)
       #:attr ls (map (lambda (e) (subst v x e)) (attribute e))
       ;; NB: Will induce warnings since blindly copies syntax
       (reified-copy-type (quasisyntax/loc syn #,(datum->syntax syn (attribute ls))) syn)]
      [_
       ;; TODO: A pattern
       ;; NB: When substituting into a term, need to take into account that dependent types will change.
       ;; previously, cur-reflect did this. But we want to avoid using cur-reflect.
       ;; TODO: This doesn't seem to work well enough
       (define type (reified-get-type syn))
       (if type
           (reified-set-type syn (subst v x type))
           syn)]))

  ;; TODO: Should this be parameterizable, to allow for different eval strategies if user wants?
  ;; TODO PERF: Should the interpreter operate directly on syntax? Might be better to first
  ;; parse into structs, turn back into syntax later? Alternatively, represent procedures as custom
  ;; struct (with attached syntax), use eval, then turn back into syntax?
  ;; TODO PERF: Might be worth manually reifying/copying types instead of using the type-assigning
  ;; macros (which we were doing); however, this complicates things a bit, due to issues with
  ;; syntax-properties containing identifiers
  (define (cur-eval syn)
    (syntax-parse syn
      [_:reified-universe syn]
      [_:id
       #:attr def (syntax-property syn 'definition)
       #:when (attribute def)
       (cur-eval (cur-reify (attribute def)))]
      [_:id
       #:when (not (syntax-property syn 'definition))
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
       ;; TODO PERF: use unsafe version of list operators and such for internal matters
       ;; TODO PERF: list-ref; could we make it a vector?
       (cur-eval
        (apply reify-app syn (list-ref (attribute e.method-ls) (attribute target.constructor-index))
               (append (attribute target.rand-ls)
                       (for/fold ([m-args '()])
                                 ([arg (attribute target.rand-ls)]
                                  [i (in-naturals (syntax-property (attribute target.constr) 'param-count))]
                                  ;; TODO PERF: memq in a loop over numbers...
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

  ;; TODO: Need generic fold over reified term

  ;; When are two Cur terms intensionally equal? When they normalize to α-equivalent reified syntax.
  (define (cur-equal? t1 t2 (fail (lambda _ #f)))
    (let cur-equal? ([t1 (cur-normalize t1)]
                     [t2 (cur-normalize t2)])
      (syntax-parse #`(#,t1 #,t2)
        [(x:id y:id)
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
        [_ (fail t1 t2)])))

  (define (cur-subtype? t1 t2 (fail (lambda _ #f)))
    (let cur-subtype? ([t1 (cur-normalize t1)]
                       [t2 (cur-normalize t2)])
      (syntax-parse #`(#,t1 #,t2)
        [(A:reified-universe B:reified-universe)
         (or (<= (attribute A.level) (attribute B.level)) (fail t1 t2))]
        [(e1:reified-pi e2:reified-pi)
         (and (cur-equal? #'e1.ann #'e2.ann fail)
              (cur-subtype? #'e1.result (subst #'e1.name #'e2.name #'e2.result)))]
        [(e1 e2)
         ;; TODO PERF: results in (2) extra calls to cur-normalize
         (cur-equal? #'e1 #'e2 fail)]))))

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
  ;; Try to make readable fresh names.
  (define fresh
    (let ([n 0])
      (lambda ([x #f])
        (set! n (add1 n))
        (or (and x (syntax-property x 'reflected-name))
            (format-id x "~a~a" (or x 'x) n #:props (and x (syntax-property x 'reflected-name x #t)))))))

  (define (n-fresh n [x #f])
    (for/list ([_ (in-range n)]) (fresh x)))

  (define (set-type e t)
    (syntax-property e 'type (syntax-local-introduce (cur-normalize t)) #t))

  (define (merge-type-props syn t)
    (if (pair? t)
        ;; TODO: Is there no better way to loop over a cons list?
        ;; TODO PERF: Should merge-type-props be used when elaborating, to prevent the 'type
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

  (define (get-type e)
    (define type (reified-get-type e))
    ;; NB: This error is a last result; macros in e should have reported error before now.
    (unless type
      (raise-syntax-error
       'internal-error
       "Something terrible has occured. Expected a cur term, but found something else."
       e))
    type)

  (define-syntax-class in-let-values #:attributes (body)
    #:literals (let-values)
    (pattern (let-values () e:in-let-values)
             #:attr body #'e.body)

    (pattern body)))

(define-syntax (let*-syntax syn)
  (syntax-case syn ()
    [(_ () e)
     #`e]
    [(_ ([x e] r ...) body)
     #`(let-syntax ([x e])
         (let*-syntax (r ...) body))]))

(begin-for-syntax
  ;; When reifying a term in an extended context, the names may be alpha-converted.
  ;; cur-reify/ctx returns both the reified term and the alpha-converted names.
  (define (cur-reify/ctx syn ctx)
    (syntax-parse syn
      #:datum-literals (:)
      #:literals (#%plain-lambda let-values)
      [_
       #:with (x ...) (map car ctx)
       #:with (t ...) (map cdr ctx)
       #:with (internal-name ...) (map fresh (attribute x))
       ;; NB: consume arbitrary number of let-values.
       #:with (#%plain-lambda (name ...) e:in-let-values)
       (cur-reify
        #`(lambda (internal-name ...)
            (let*-syntax ([x (make-rename-transformer (set-type #'internal-name #'t))] ...)
              #,syn)))
       ;; TODO: duplicate names since types no longer expanded in separate context.
       ;; NB: This syntax-local-introduce should be reduntant, but apparently isn't (introduces bug
       ;; with cur-call)
       #`((name ...) (name ...) e.body : #,(syntax-local-introduce (get-type #'e.body)))]))

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
     (quasisyntax/loc syn (Type 'i))]))

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
     (⊢ (#%plain-lambda (#,(set-type (car (attribute e.name)) #'t1.reified)) e.reified) :
        (cur-Π (#,(car (attribute e.tname)) : t1.reified) e.type))]))

(begin-for-syntax
  ;; TODO PERF: Maybe mulit-artiy functions.
  ;; TODO: cur-app generates bad error messages; loses type info
  (define (cur-app* rator args)
    (for/fold ([e rator])
              ([arg args])
      (quasisyntax/loc rator (cur-app #,e #,arg)))))

(define-syntax (cur-app syn)
  (syntax-parse syn
    [(_ e1:cur-procedure (~var e2 (cur-expr-of-type #'e1.ann)))
     (⊢ (#%plain-app e1.reified e2.reified) :
        #,(subst #'e2.reified #'e1.name #'e1.result))]))

(begin-for-syntax
  (define (define-typed-identifier name type reified-term (y (format-id name "~a" (fresh name) #:props name)))
    #`(begin
        (define #,y #,reified-term)
        (define-syntax #,name
          (make-rename-transformer
           ;; TODO: Clean this up. Need to be *very* careful when preserving properties
           ;; TODO: Should be able to simplify this some; seems to have been affected by some bug in Racket
           ;; fixed as of ce370c2f6475c108ecf0b172417944b5ed10950d
           ;; Partially a bug in this code, since that bug is only triggered when identifier is
           ;; missing source location information
           (format-id #'#,name
                      "~a"
                      #'#,y
                      #:props
                      (set-type
                       (syntax-property #'#,name 'not-free-identifier=? #t #t)
                       #'#,type)))))))

(define-syntax (cur-define syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_:top-level-id name:id body:cur-expr)
     ;; NB: Store definition to get δ reduction
     #:do [(define y (format-id #'name "~a" (fresh #'name) #:props #'name))
           (define info (format-id #'name "~a-info" y))]
     #`(begin
         (define-syntax #,info (λ (_) #'body.reified))
         (define #,y body.reified)
         ;; TODO: Bit of code duplication here
         ;; TODO NB can't reused define-typed-indentifier because need to
         ;; delay the syntax-property attachment until inside the macro expander. This is probably
         ;; true of *all* syntax-properties I use; hard to explain why, but see also:
         ;; https://groups.google.com/forum/#!topic/racket-users/TGax2h8dVxs
         ;; https://github.com/racket/racket/issues/1495
         ;; https://github.com/lexi-lambda/rascal/commit/d7c92bffcc5347125b37f6e4ba8a080a548cdf78
         (define-syntax name
           (make-rename-transformer
            (syntax-property
             (syntax-property
              (set-type #'#,y #'body.type)
              'not-free-identifier=? #t #t)
             'definition #'(#,info)
             #t)))
         #;(define-typed-identifier name (syntax-property name 'definition #`(#,info) #t) body.type body.reified y))]))

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
         (struct axiom #,(n-fresh (attribute type.length)) #:transparent #:reflection-name '#,name)
         #,(define-typed-identifier name #'type.reified #'((curry axiom)) #'make-axiom))]))

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
                   ;; TODO PERF: Generate the dereferencing of each field instead of struct->list?
                   ;; Can't do that easily, due to alpha-conversion; won't know the name of the
                   ;; field reference function. Might solve this by storing accessor abstraction in
                   ;; syntax-property of constructor
                   #`[(#,pred? e)
                      ;; TODO PERF: /code size: this procedure should be a (phase 0) function.
                      (let* ([args (drop (struct->list e) 'p)]
                             [recursive-args
                              ;; TODO: Do we not have constructor argument count?
                              (for/list ([x args]
                                         [i (in-naturals 'p)]
                                         ;; TODO PERF: memq, in a loop, over numbers
                                         ;; TODO PERF: /code size: Duplicating rargs in code
                                         #:when (memq i '#,rargs))
                                (loop x))])
                        ;; NB: the method is curried, so ...
                        ;; TODO PERF: attempt to uncurry elim methods?
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

(begin-for-syntax
  (define (motive-type syn D params)
    (define/syntax-parse e:cur-expr (cur-app* D params))
    (let loop ([inductive-type (attribute e.type)]
               [indices '()])
      (syntax-parse inductive-type
        [e:reified-pi
         ;; TODO PERF: maybe use reified-Π here instead of cur-Π
         (quasisyntax/loc syn (cur-Π (e.name : e.ann) #,(loop #'e.result (cons #'e.name indices))))]
        [e:reified-universe
         ;; TODO PERF: append, reverse
         ;; NB: (cur-type 0) is an arbitrary choice here... really, any universe type is valid. Must
         ;; check this is a subtype of motive's type
         (quasisyntax/loc syn (cur-Π (_ : #,(cur-app* D (append params (reverse indices)))) (cur-type 0)))])))

  (define (check-motive syn D params motive-t)
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
    (define/syntax-parse c:reified-constant (attribute e.reified))
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
        [e:reified-pi
         ;; TODO PERF: maybe use reified-Π here instead of cur-Π
         (quasisyntax/loc syn
           (cur-Π (e.name : e.ann)
                  #,(branch-type (quasisyntax/loc syn (cur-app #,target e.name)) #'e.result (add1 i)
                                 ;; TODO PERF: memq in a loop. over numbers, should be
                                 ;; performant way to do this.
                                 (if (memq i recursive-index-ls)
                                     (cons (cons #'e.name #'e.ann) r-ann-ls)
                                     r-ann-ls))))]
        [e:reified-constant
         #:do [(define index-ls (drop (attribute e.rand-ls) param-count))
               (define final-result (cur-app* motive (append index-ls (list target))))]
         (for/fold ([r final-result])
                   ([p (reverse r-ann-ls)])
           (define/syntax-parse r-ann:reified-constant (cdr p))
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

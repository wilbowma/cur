#lang turnstile+/quicklang
(require
 #;(except-in "coc-saccharata.rkt" define)
 "coc-saccharata.rkt"
 turnstile+/eval turnstile+/typedefs turnstile+/more-utils)

;;;; The Calculus of Constructions + strictly positive inductive type schemas,
;;;; plus necessary sugar.
;;;; More or less the Calculus of Inductive Constructions.
;;;; ------------------------------------------------------------------------

(provide
 (all-from-out "coc-saccharata.rkt")
 define-datatype
 (for-syntax
  mk-cons+pat-transformer
  (rename-out [pattern->ctxt pat->ctxt])
  (rename-out [get-is get-idxs/unexp])
  ;; get-datatype-info fns
  get-datatype-info
  get-datatype-match-info
  get-datatype-elim
  ;; datatype-info fns
  (rename-out [datatype-info-constructor-names datatype-info-constructors]
              [datatype-info-param-names datatype-info-params]
              [datatype-info-is-inductive?/checked datatype-info-is-inductive?])
  datatype-info-constructor-patterns
  datatype-info-constructor-arg-types))
  

;;; Define abbreviation for a typerule that is also usable in pattern position
;;; -----------------------------------------------------------

(begin-for-syntax
 (define-tycons-instance mk-cons+pat-transformer pat->ctxt)

  ;; pat->ctxt :
  ;; Transform a pattern `pat` of 'type' `ty` into a a ctxt, representing the
  ;; arguments (and their types) that will be bound in the clause of matcher
  ;; using this pattern.
  (define-generic-type-method (pat->ctxt pat ty) #:unexpanded)

  ;; wrapper for pat->ctxt, includes some general cases, eg _ and lone variables.
  (define (pattern->ctxt pat ty)
    (syntax-parse pat
      [(~or C:id (C:id . _))
       #:when (has-method? #'C #'pat->ctxt)
       (pat->ctxt pat ty)]
      ; datum
      [(~datum _) null]
      ; pattern variable case
      [:id (list (list pat ty))]))

  ;; ty is unexpanded, series of curried mono-applications of type constructor
  (define (get-curried-operator ty)
    (if (id? ty) ty (get-curried-operator (stx-car ty))))

  ;; Type checked the 'type' `t1` of a pattern against an expected 'type' t2.
  ;; Patterns are "well-typed" when they match shallowly, up to the outer most constructor.
  ;; Types t1 must be unexpanded, and t2 must be curried: series of curried
  ;; mono-applications of type constructor
  (define (pattern-typecheck? t1 t2)
    (if (identifier? t1)
        (typecheck? ((current-type-eval) t1) ((current-type-eval) t2))
        (free-id=? (stx-car t1) (get-curried-operator t2)))))

;; TODO: Bah syntactic sugar in the core?!:
;; Define a Coq-like inductive constructor: automatic currying and can be used
;; in a pattern matcher.
;; differences with define-type*:
;; - expander name same as constructor name
;; - constructor name is a type-pattern-transformer, for pattern positions
(define-syntax define-data-constructor
  (syntax-parser
    ; A data constructor `name` with parameters `A ...`, indexes `i+x ...` and
    ; type `τ-out`; plus keyword arguments support by `define-type` in `rst.
    ; NB: τ and τ-out have "unexpanded" shape, i.e., curried with single-applications.
    ; TODO: should they be unexpanded before or after passing to define-data-constructor?
    [(_ name [A:id (~datum :) τA] ... (~datum :) [i+x (~datum :) τ] ... (~datum ->) τ-out . rst)
     #:with name/internal (fresh #'name)
     #:with name/internal-expander (mk-~ #'name/internal)
     #:with name-expander #'name
     #:with (p ...) (generate-temporaries #'(A ... i+x ...))
     (syntax/loc this-syntax
       (begin-
         (define-type name/internal : [A : τA] ... [i+x : τ] ... -> τ-out . rst)

         (define-syntax name
           (mk-cons+pat-transformer

            ; If the constructor `name` is used as a function, support automagic currying.
            ; NOTE: η-expand the transformer to preserve source location information.
            (λ (stx)
              ((make-variable-like-transformer
                (quasisyntax/loc stx
                  (λ [A : τA] ... [i+x : τ] ...
                     #,(syntax/loc stx (name/internal A ... i+x ...)))))
               stx))
            ; Setup the pattern transformer for `name`.
            ; pat should have type t (unexpanded type)
            (λ (pat t)
              (syntax-parse pat
                [(~or C:id (C:id p ...))
                 #:fail-unless (pattern-typecheck? t #'τ-out)
                 (format "expected pattern for type ~a, given pattern for ~a: ~a\n"
                         ((current-resugar) t) ((current-resugar) #'τ-out) (syntax->datum pat))
                 (let loop ([res null]
                            ; drop param pats, which aren't bound by the pattern
                            [ps (stx-drop #'(p ...) (stx-length #'(A ...)))]
                            [xs (stx->list #'(i+x ...))]
                            [τs (stx->list
                                 (if (stx-null? #'(A ...))
                                     #'(τ ...)
                                     (substs (if (id? t) #'() (stx-take (stx-cdr t) (stx-length #'(A ...))))
                                             #'(A ...)
                                             #'(τ ...))))])
                   (if (stx-null? ps)
                       res
                       (let ([x+tys (pattern->ctxt (car ps) (transfer-props t (car τs)))])
                         (loop (append res x+tys)
                               (cdr ps)
                               (cdr xs)
                               (if (and (not (null? x+tys))
                                        (id? (car ps))
                                        (free-id=? (car ps) (caar x+tys)))
                                   (map (λ (t) (subst (car ps) (car xs) t)) (cdr τs))
                                   (cdr τs))))))]))))

         (begin-for-syntax
           (define-syntax name-expander
             (make-rename-transformer #'name/internal-expander)))))]))

;;; Define types with automagic currying
;;; -----------------------------------------------------------

; define-type* wraps define-type to enable currying of constructor
; and record additional information about constructors for static checking.
(define-syntax define-type*
  (syntax-parser
    [(_ name (~datum :) [A+i:id (~datum :) τ] ... (~datum ->) τ-out
        . rst)
     #:with name/internal (fresh #'name)
     #:with name/internal-expander (mk-~ #'name/internal)
     #:with name-expander (mk-~ #'name)
     #'(begin-
         (define-type name/internal : [A+i : τ] ... -> τ-out . rst)
         (define-syntax name
           (lambda (stx)
             ((make-variable-like-transformer
               (quasisyntax/loc stx
                 (λ [A+i : τ] ...
                    #,(syntax/loc stx (name/internal A+i ...)))))
              stx)))
         (begin-for-syntax
           (define-syntax name-expander
             (make-rename-transformer #'name/internal-expander))))]))

;;; Define inductive type schemas
;;; -----------------------------------------------------------

;; Finding the recursive arguments of ctxts.

(begin-for-syntax
  ;; x+τss = (([x τ] ...) ...)
  ;; Returns the subset of each (x ...) that is recursive, i.e., where x : τ = (TY . args),
  ;; along with the indices needed by each recursive x.
  ;; - ASSUME: the recursive argument has type (TY . args) where TY is unexpanded, i.e.,
  ;;   a series of curried mono-apps, where indices are the last num-is args to TY.
  (define (find-recur/is TY num-is x+τss)
    (stx-map
     (λ (x+τs)
       (define xs (stx-map stx-car x+τs))
       (stx-filtermap
        (syntax-parser
          [(x t:id) (and (free-id=? #'t TY) (list #'x))] ; num-is should be = 0
          [(x t) #:when (free-id=? (get-curried-operator #'t) TY)
                 (cons #'x (get-is #'t num-is))]
          [_ #f])
        x+τs))
     x+τss))

  ;; ty is unexpanded, series of curried mono-applications of type constructor
  (define (get-is ty num-is)
    (if (zero? num-is) null (append (get-is (stx-car ty) (sub1 num-is)) (stx-cdr ty)))))

;; define-datatype : minics the syntax of Coq's Inductive.

;; TODO: Rename some of these pattern vars to be a little more textbook.
(define-typed-syntax define-datatype
  ; Define the declaration syntax:
  ; First, the name of the inductive type.
  [(_ TY:id
      ; "Applied" to the parameters: each τA_ may reference preceding A
      [A_:id (~datum :) τA_] ...
      ; Then a literal :
      (~datum :)
      ; Followed by a type describing the indices and type of TY.
      τTY_
      ; Then the constructors, in either record of function-symbol syntax.
      ; I.e., (C x ...) : (Π (y : A) ... (TY ...))
      ; full type of each C is (Π [A_ : τA_] ... x+τx ... τC)
      [C:id (~and (~not (~datum :)) x+τx) ...
            (~optional (~seq (~datum :) τC
                             ; NOTE: Detect whether we're in record-only syntax,
                             ; for better errors.
                             (~parse τout-given? #'#t))
                       #:defaults ([τC #'(TY A_ ...)]))] ...) ≫


   ;; Validate inputs
   ; Validate the type of TY
   [[A_ ≫ A- : τA_] ... ⊢ [τTY_ ≫ (~Π [i : τi-] ... τ-) ⇒ (~Type _)]]

   #:do [(define num-params (stx-length (attribute A-)))
         (define num-idxs (stx-length (attribute i)))]

   ; A better error when you have failed to give the necessary indices
   #:fail-when (and (not (attribute τout-given?)) (not (zero? num-idxs)))
   "must explicitly declare output of constructors for types with indices > 0"

   ; Validate the types of the constructors
   ; TODO: Lot of re-expansion going on. See turnstile-merging for work on a fix.
   [[A_ ≫ A : τA_] ...
    ; Need TY in env
    ; Must reexpand τTY_ in scope of A ..., to get scopes right.
    [TY ≫ TY- : (Π [A_ : τA_] ... τTY_)]
    ⊢
    ; NOTE: While it appears that there could be a reference to TY in its own
    ; type, this isn't possible since we already validated τTY_.
    [τTY_ ≫ (~Π [i- : τi_] ... τ_) ⇒ (~Type _)]
    ; TODO: This is should be checking that i+x is first the indices, then other arguments.
    ; TODO: Check that t_out is (TY args ...)
    [(Π x+τx ... τC) ≫ (~and A_c (~Π [i+x : τin_] ... τout_)) ⇒ (~Type _)] ...]

   ;; Reconstruct surface types with proper binders and references.

   ; Replace the unexpanded `A_ ...` with the expanded and fresh `A ...` in each
   ; of the unexpanded `τA_ ...`, since only `A ...` will be bound.
   #:with (τA ...) (substs #'(A ...) #'(A_ ...) #'(τA_ ...))

   ; Unexpand the type of `TY`.
   ; This is necessary due to problems with syntax properties being lost
   ; across module boundaries.
   ; By unexpanding, the properties get reinstalled when τi ... τ get
   ; re-expanded on the other side of the boundary.
   #:with (τi ... τ) (stx-map unexpand #'(τi_ ... τ_))

   ; Replace recursive references to `TY-` by the surface `TY` in the types of
   ; constructors, and unexpand them in the context of `TY`.
   #:with ((τin^ ... τout) ...) (stx-map
                                 (λ (ts) (stx-map (unexpand/ctx #'TY) ts))
                                 (subst #'TY #'TY- #'((τin_ ... τout_) ...)))

   ; Decorate each recursive argument's type with a 'recur property.
   #:with ((τin ...) ...) (for/list ([types (attribute τin^)])
                            (for/list ([A types])
                              (if (free-identifier=? (get-curried-operator A) #'TY)
                                (syntax-property A 'recur #t #t)
                                A)))

   ; Figure out the recursive arguments.
   ; Each `xrec ...` is the subset of `x ...` that are recur arguments, i.e.,
   ; they are not fresh ids.
   ; Each `xrec` is accompanied with `irec ...`, which are the indices in `i+x ...`
   ; needed by `xrec`.
   #:with (((xrec irec ...) ...) ...)
   (find-recur/is #'TY num-idxs #'(([i+x τin] ...) ...))

   ; TODO: Using ~#%app should make this cleaner.
   ; ASSUMING: τout is unexpanded curried single-apps
   ; - this is the same "patvar trick" as re-using A below
   ; - it makes sure that the method output types properly reference the right i
   #:with ((τouti ...) ...) (stx-map (λ (t) (get-is t num-idxs)) #'(τout ...))

   ; Each constructor `C ...` must satisfy the positivity condition for the type `TY`.
   #:do [(define pos?
           ; If this continuation gets back a string, it's an error message and
           ; positivity checking has failed.
           (let/ec k
             (for/and ([A (attribute A_c)])
               (positivity? A #'TY- k))))]
   #:fail-when (string? pos?) pos?

   ;; Now generate the type rules for `TY`, `C ...`, the eliminator for `TY`, and its type rule.

   ;; Pre-generate pattern variables, to make nested macros below easier to read.

   ; i* = inferred (concrete) i in elim
   #:with (i* ...) (generate-temporaries #'(i ...))

   ; Duplicate the parameters `A ...` for each constructor `C`, for ellipses
   ; matching.
   #:with ((AxC ...) ...) (stx-map (lambda _ #'(A ...)) #'(C ...))
   #:with ((τAxC ...) ...) (stx-map (λ _ #'(τA ...)) #'(C ...))

   ; Methods
   #:with (m ...) (generate-temporaries #'(C ...))
   ; Expanded methods
   #:with (m- ...) (generate-temporaries #'(C ...))
   ; Pattern expander name
   #:with TY-patexpand (mk-~ #'TY)
   ; Eliminator name
   #:with elim-TY (format-id #'TY "elim-~a" #'TY)
   ; Reduction rule
   #:with eval-TY (format-id #'TY "match-~a" #'TY)
   ; Types of methods
   #:with (τm ...) (generate-temporaries #'(m ...))

   #:with param-info #'([A τA] ...)
   #:with indices-info #'([i τi] ...)
   #:with constructor-info #'((C ([i+x τin] ... τout) ((xrec irec ...) ...)) ...)
   ;; This is the info about the datatype that must be passed to `match` and similar forms
   #:with info #'(datatype-info #t #'elim-TY #'param-info #'indices-info #'constructor-info)
   ; Constructor pattern for each reduction rule for this eliminator.
   #:with (C-pat ...) (compute-constructor-patterns #'param-info #'constructor-info)
   --------
   [≻ (begin-
      ;; Define the inductive type `TY`.
      (define-type* TY : [A : τA] ... [i : τi] ... -> τ
        #:implements get-datatype-info info)

      ;; Define the constructors.
      (define-data-constructor C [AxC : τAxC] ... : [i+x : τin] ... -> τout) ...

      ;; Define eliminator `elim-TY`.
      ;; v = target
      ;; - infer A ... from v
      ;; P = motive
      ;; - is a (curried) fn that consumes:
      ;;   - indices i ... with type τi
      ;;   - and TY A ... i ...
      ;;     - where A ... args is A ... inferred from v
      ;;     - and τi also instantiated with A ...
      ;; - output is a type
      ;; m = branches
      ;; - each is a fn that consumes:
      ;;   - maybe indices i ... (if they are needed by args)
      ;;   - constructor args
      ;;     - inst with A ... inferred from v
      ;;   - maybe IH for recursive args

      (define-typerule/red (elim-TY v P m ...) ≫
        ; Check the type of the target, and bind the parameters and indices.

        ; NOTE: This should just be the following line
        ;   [⊢ v ≫ v- ⇒ (TY-patexpand A ... i* ...)]
        ; But, we can get better inference if we specialize when we can (i.e.,
        ; when there are no parameters or indices to bind).
        #,(if (zero? (+ num-params num-idxs))
              #'[⊢ v ≫ v- ⇐ TY]
              #'[⊢ v ≫ v- ⇒ (TY-patexpand A ... i* ...)])

        ; Every pattern variable in the define-datatype input pattern that
        ; references the *names* `A ...` is now instantiated with the particular
        ; parameters from the type of `v-`, since we use the names `A ...` as
        ; the pattern variables in its type.
        ;
        ; For reasons I can't explain yet, this means we need to unexpand any
        ; references to these concrete parameters and indices.

        ; Check the type of the motive, which expects the indices `i ...` of
        ; types `τi ...`.

        ; NOTE HACK: Using (Type 9001) here to get better inference on motives.
        ; The correct version should be something like
        ;  [⊢ P ≫ P- ⇒ (~Π [i** : τi] ...
        ;                  (~Π [t* : (TY-patexpand A ... i** ...)] (~Type motive_level:nat)))]
        ; But, that's in infer mode and we have to provide more annotations.
        ; The *right* approach is to add some kind of unification.

        ; NOTE: Escape the current quasi, re-enter syntax-quote so that the
        ; unquasisyntax splicing is delayed; it doesn't happen until define-typerule/red
        ; runs, when `A ...` are concrete.
        #,#'[⊢ P ≫ P- ⇐ (Π [i : τi] ...
                          (→ (TY #,@(stx-map unexpand #'(A ...)) i ...) (Type 9001)))]

        ; Each method, m, is a curried function consuming 3 (possibly empty)
        ; sets of args:
        ; 1,2) i+x  - The indices of the target, and args the constructor `C`.
        ;             The indices may not be included, when not needed by the xs.
        ;              TODO: Huh? Indices must always be included...
        ; 3) IHs - for each xrec ... (which are a subset of i+x ...)
        #:with (τm ...)
        ; NOTE: Can't be inlined due to ellipses matching issues...
        #`((Π [i+x : τin] ... ; constructor args ; ASSUME: i+x includes indices
              (→ (P- irec ... xrec) ... ; IHs
                 (P- #,@(stx-map unexpand #'(τouti ...))
                     (C #,@(stx-map unexpand #'(AxC ...)) i+x ...)))) ...)
        [⊢ m ≫ m- ⇐ τm] ...
        -----------
        ; NOTE: Again, escape current quasi to delay unexpand until `i* ...` are concrete.
        [⊢ (eval-TY v- P- m- ...) ⇒ #,#'(P- #,@(stx-map unexpand #'(i* ...)) v-)]

        #:where eval-TY #:display-as elim-TY
        [(#%plain-app C-pat P m ...)
         ~> (app/eval m i+x ... (eval-TY xrec P m ...) ...)] ...))]])

; Strict positivity
; https://coq.inria.fr/doc/language/cic.html#positivity-condition
(begin-for-syntax
  ; Identifier X is not free in type Y
  (define (not-free-in? X Y)
    (not (stx-contains-id? Y X)))

  ;; Define datatype info and it's generic getter method.
  ;; A datatype info is a datatype-info struct with fields:
  ;; - is-inductive? : true means a type defined with define-datatype
  ;; - elim : stx id of eliminator term of the type
  ;; - params : stx ([A τA] ...) representing parameters
  ;; - indices : stx ([i τi] ...)
  ;; - constructors : stx
  ;;     (C ([i+x τin] ... τout)        : constructor and field names, with input and output types
  ;;        ((xrec irec ...) ...)) ...) : recursive field names and the indices they reference
  ;;   - (xrec ...) \subseteq (i+x ...)
  ;;   - each (irec ...) \subseteq (i+x ...)

  (define-generic-type-method get-datatype-info #:default #f)

  (struct datatype-info (is-inductive? elim params indices constructors))

  ;; return just the stx obj parts of datatype-info
  (define (get-datatype-match-info ty)
    (define info (get-datatype-info ty))
    (if info
        (list* (datatype-info-params info)
               (datatype-info-indices info)
               (datatype-info-constructors info))
        (error
          (format "Type has no match info ~a" (resugar-type ty)))))
  
  ; Differs from turnstile+ get-match-info: accepts type's internal id instead of entire type
  ; - returns the match-info, or #f
  (define (get-match-info I)
    (define d (eval-syntax I))
    (and (dict? d) (dict-ref d #'get-datatype-info #f)))

  (define (get-datatype-elim ty)
    (datatype-info-elim (get-datatype-info ty)))
  
  ;; TODO There's better ways to do this... a syntax property, e.g.,
  (define (datatype-info-is-inductive?/checked maybe-info)
    (and maybe-info (datatype-info-is-inductive? maybe-info)))

  ; Get the number of parameters for inductive I.
  (define (datatype-info-param-count info)
    (stx-length (datatype-info-params info)))

  ; Get the patterns expected in a reduction rule/pattern match
  ; This is the constructor applied to its parameters and other arguments.
  (define (datatype-info-constructor-patterns info ty)
    (if (datatype-info? info)
        (compute-constructor-patterns (datatype-info-params info)
                                      (datatype-info-constructors info))
        (error
         (format "Expected valid match info for inductive type, but got ~a for type ~a" info ty))))

  (define (compute-constructor-patterns As Cs)
    (syntax-parse (list As Cs)
      ; params x constructors
      [(([A _] ...) ((C ([i+x _] ... _) _) ...))
       #:with (C-pat ...) (stx-map
                           (λ (C xs)
                             (if (and (stx-null? #'(A ...)) (stx-null? xs))
                                 ; NOTE: must not be (C) pattern; unlike #%app,
                                 ; (C) \neq C due to id macro behavior
                                 C
                                 #`(#,C A ... . #,xs)))
                           #'(C ...)
                           #'((i+x ...) ...))
       (attribute C-pat)]))

  (define (datatype-info-constructor-names info ty)
    (syntax-parse (datatype-info-constructors info)
      [((C . _) ...) (attribute C)]
      [_ (error
         (format "Expected valid match info for inductive type, but got ~a for type ~a" info ty))]))

  (define (datatype-info-constructor-arg-types info ty)
    (syntax-parse (datatype-info-constructors info)
      [((C (decls ... τout) _) ...) (attribute decls)]
      [_ (error
          (format "Expected valid match info for inductive type, but got ~a for type ~a" info ty))]))

  (define (datatype-info-param-names info ty)
    (syntax-parse (datatype-info-params info)
      [([A _] ...) (attribute A)]
      [_ (error
          (format "Expected valid match info for inductive type, but got ~a for type ~a" info ty))]))

  ; The type `T` satisfies the positivity condition for constant `X`.
  (define (positivity? T X [fail (lambda _ #f)])
    (let loop ([T T])
      (or
       (syntax-parse T
         [(~Π [x : A] B)
          (and (strict-positivity? #'A X fail) (loop #'B))]
         [(~#%app Y:id t₁ ...)
          (and (free-identifier=? #'Y X)
               (andmap (curry not-free-in? X) (attribute t₁)))])
       (fail
        (format "~a does not satisfy positivity with respect to ~a"
                T #;(type->str T) (reflect X))))))

  ; The constant `X` occurs strictly positivity in type `T`.

  ; type-hash remembers which types we've already started checking, to avoid an
  ; infinite loop.
  ; I think it's okay to say that if we've started checking it once, it's safe
  ; assume its strict until something else says no.
  ;
  ; Strict and nested can get stuck in a loop due to parameters; consider rose trees.
  ; We end up checking that (List (Rose A)) satisfies strict positivity, which
  ; requires that we instantiate the constructors of List with (Rose A) to check
  ; nested, which requires that we check (List (Rose A)) satisfies strict.
  ;
  ; The Coq spec has nothing to say on this.
  (define (strict-positivity? T X [fail (lambda _ #f)] [type-hash (make-immutable-hash)])
    ; Core checking algorithm
    (define (check loop T type-hash)
      (syntax-parse T
        [(~Π [x : A] B)
         (and (not-free-in? X #'A) (loop #'B type-hash))]
        [(~#%app Y:id τ₁ ...)
         #:when (free-identifier=? #'Y X)
         (andmap (curry not-free-in? X) (attribute τ₁))]
        [(~#%app I:id t ...)
         #:do[(define info (get-match-info #'I))]
         ; 1. I is inductive
         #:when (datatype-info-is-inductive? info)
         ; 2. I has m params
         #:do [(define m (datatype-info-param-count info))]
         #:with (C ...) (datatype-info-constructor-names info #'I)
         #:with ((p ...) ...) (map (lambda _ (take (attribute t) m)) (attribute C))
         #:with (A_c ...) (stx-map (compose typeof expand/df) #'((C p ...) ...))
         ; 3. each of I's constructors, instantiated with params from t ...,
         ;    satisfy nested positivity for ind.
         (and
          (andmap (curry not-free-in? X) (drop (attribute t) m))
          (andmap (lambda (type) (nested-positivity? type #'I m X type-hash fail)) (attribute A_c)))]))
    (let loop ([T T]
               [type-hash type-hash])
      (or
       ; NOTE: Is syntax->datum an okay thing to hash or should I do a
       ; free-identifier=? on all ids?
       (hash-ref type-hash (syntax->datum T) #f)
       (not-free-in? X T)
       (let ([type-hash (hash-set type-hash (syntax->datum T) #t)])
         (check loop T type-hash))
       (fail
        (format "~a does not satisfy strict positivity with respect to ~a"
                (type->str T) (reflect X))))))

  ; The type `T` of the constructor for inductive `I` satisfies the
  ; nested positivity condition for constant `X`.
  (define (nested-positivity? T I m X type-hash [fail (lambda _ #f)])
    (let loop ([T T])
      (or
       (syntax-parse T
         [(~Π (x : A) B)
          (and (strict-positivity? #'A X fail type-hash) (loop #'B))]
         [(~#%app I-:id t ...)
          #:when (free-identifier=? #'I- I)
          (andmap (curry not-free-in? X) (drop (attribute t) m))])
       (fail
        (format "~a does not satisfy nested positivity with respect to ~a"
                (type->str T) (reflect X)))))))

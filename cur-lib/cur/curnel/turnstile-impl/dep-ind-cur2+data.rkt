#lang turnstile/lang
(require (except-in "dep-ind-cur2.rkt" λ #%app Π ~Π)
         (except-in "dep-ind-cur2+sugar.rkt" define)
         turnstile/eval turnstile/typedefs turnstile/more-utils)

;; library for dep-ind-cur2 enabling definition of datatypes
;; ie, define-datatype

; Π  λ ≻ ⊢ ≫ → ∧ (bidir ⇒ ⇐) τ⊑ ⇑

(provide define-datatype (for-syntax datacons pat->ctxt))

(begin-for-syntax
  (struct datacons (proc pat->ctxt)
    #:property prop:procedure (struct-field-index proc))
  ;; pattern pat has type ty
  (define (pat->ctxt pat ty)
    ;; (printf "converting pat: ~a\n" (stx->datum pat))
    ;; (printf "with type: ~a\n" (stx->datum ty))
    ;; (when (id? pat)
    ;;   (displayln (syntax-local-value pat (λ () #f))))
    (syntax-parse pat
      [(~datum _) null]
      [C:id
       #:when (datacons? (syntax-local-value #'C (λ () #f))) ; nullary constructor
       ((datacons-pat->ctxt (syntax-local-value #'C)) pat ty)]
      [:id (list (list pat ty))]
      [(C . _)
       ((datacons-pat->ctxt (syntax-local-value #'C)) pat ty)])))
    

;; define-cur-constructor is mostly sugar for define-type, and:
;; - allows writing whole type in declaration, eg (define-cur-constructor name : TY)
;; - constructor is curried (eg, can partially apply)
(define-syntax define-cur-constructor
  (syntax-parser
    [(_ name (~datum :) ty)
     (syntax/loc this-syntax
       (define-cur-constructor name : ty #:extra))]
    [(_ name (~datum :) ty #:extra . extra-info)
     #:with (~Π [A+i : τ] ... τ-out) ((current-type-eval) #'ty)
     #:with name/internal (fresh #'name)
     #:with name/internal-expander (mk-~ #'name/internal)
     #:with name-expander #'name
     #:with (p ...) (generate-temporaries #'(A+i ...))
     (syntax/loc this-syntax
       (begin-
         (define-type name/internal : [A+i : τ] ... -> τ-out #:extra . extra-info)
         (define-syntax name
           (datacons
            (make-variable-like-transformer
             ;; TODO: This is losing source location information
             #'(λ [A+i : τ] ... (name/internal A+i ...)))
            (λ (pat t)
              (syntax-parse pat
                [:id ; nullary constructor, no extra binders
                 #:fail-unless (typecheck? ((current-type-eval) t) #'τ-out)
                 (format "expected pattern for type ~a, given pattern for ~a: ~a\n"
                         (type->str t) (type->str #'τ-out) (syntax->datum pat))
                 null]
                [(_ p ...)
                 #:fail-unless (typecheck? ((current-type-eval) t) #'τ-out)
                 (format "expected pattern for type ~a, given pattern for ~a: ~a\n"
                         (type->str t) (type->str #'τ-out) (syntax->datum pat))
                 (stx-appendmap
                  pat->ctxt
                  #'(p ...)
                  #'(τ ...))]))))
         (begin-for-syntax
           (define-syntax name-expander
             (make-rename-transformer #'name/internal-expander)))))]))

;; TmpTy is a placeholder for undefined names
(struct TmpTy- ())
(define-syntax TmpTy
  (syntax-parser
    [:id (assign-type #'TmpTy- #'Type)]
    ;; TODO: orig will get stuck with eg, (TmpTy A)
    [(_ . args) (assign-type #'(app/eval TmpTy- . args) #'Type)]))
(define-for-syntax TmpTy+ (expand/df #'TmpTy))

;; helper syntax fns
(begin-for-syntax
  ;; drops first n bindings in Π type
  (define (prune t n)
    (if (zero? n)
        t
        (syntax-parse t
          [(~Π [_ : _] t1)
           (prune #'t1 (sub1 n))])))
  ;; x+τss = (([x τ] ...) ...)
  ;; returns subset of each (x ...) that is recursive, ie τ = TY
  (define (find-recur TY x+τss)
    (stx-map
     (λ (x+τs)
       (stx-filtermap
        (syntax-parser [(x τ) (and (identifier? #'τ) (free-id=? #'τ TY) #'x)])
        x+τs))
     x+τss))
  ;; x+τss = (([x τ] ...) ...)
  ;; returns subset of each (x ...) that is recursive, ie τ = (TY . args)
  ;; along with the indices needed by each recursive x
  ;; - ASSUME: the needed indices are first `num-is` arguments in x+τss
  ;; - ASSUME: the recursive arg has type (TY . args) where TY is unexpanded
  (define (find-recur/i TY num-is x+τss)
    (stx-map
     (λ (x+τs)
       (define xs (stx-map stx-car x+τs))
       (stx-filtermap
        (syntax-parser
          ;; TODO: generalize these patterns with ~plain-app/c
          [(x (_ t:id . _)) (and (free-id=? #'t TY) (cons #'x (stx-take xs num-is)))]
          [(x (_ (_ t:id . _) . _)) (and (free-id=? #'t TY) (cons #'x (stx-take xs num-is)))]
          [_ #f])
        x+τs))
     x+τss))
  )

;; use this macro to expand e, which contains references to unbound X
(define-syntax (with-unbound stx)
  (syntax-parse stx
    [(_ X:id e)
     ;swap in a tmp (bound) id `TmpTy` for unbound X
     #:with e/tmp (subst #'TmpTy #'X #'e)
     ;; expand with the tmp id
      (expand/df #'e/tmp)]))
(define-syntax (drop-params stx)
  (syntax-parse stx
    [(_ (A ...) τ)
     (prune #'τ (stx-length #'(A ...)))]))
;; must be used with with-unbound
(begin-for-syntax
  (define-syntax ~unbound
    (pattern-expander
     (syntax-parser
       [(_ X:id pat)
        ;; un-subst tmp id in expanded stx with type X
        #'(~and TMP
                (~parse pat (reflect (subst #'X TmpTy+ #'TMP free-id=?))))])))
  )

(begin-for-syntax
  (require turnstile/more-utils)
  (define-nested/L ~app/eval/c (~literal app/eval/1) #:as pattern-expander))

(define-typed-syntax define-datatype
  ;; simple datatypes, eg Nat -------------------------------------------------
  ;; - ie, `TY` is an id with no params or indices
  [(_ TY:id (~datum :) τ [C:id (~datum :) τC] ...) ≫
   ;; need with-unbound and ~unbound bc `TY` name still undefined here
   ;; TODO: is with-unbound needed?
   ;; - is it possible to defer check to define-constructor below, after TY is defined?
   [⊢ (with-unbound TY τC) ≫ (~unbound TY (~Π [x : τin] ... _)) ⇐ Type] ...
   ;; ---------- pre-define some pattern variables for cleaner output:
   ;; recursive args of each C; where (xrec ...) ⊆ (x ...)
   #:with ((xrec ...) ...) (find-recur #'TY #'(([x τin] ...) ...))
   ;; elim methods and method types
   #:with (m ...) (generate-temporaries #'(C ...))
   #:with (m- ...) (generate-temporaries #'(m ...))
   #:with (τm ...) (generate-temporaries #'(m ...))
   #:with elim-TY (format-id #'TY "elim-~a" #'TY)
   #:with eval-TY (format-id #'TY "eval-~a" #'TY)
   #:with TY/internal (fresh #'TY)
   #:with (C-expander ...) #'(C ...)
   #:with (C-pat ...) (stx-map
                       (λ (C xs) (if (stx-null? xs) C #`(#,C . #,xs)))
                       #'(C-expander ...)
                       #'((x ...) ...))
;   #:with TY-expander (mk-~ #'TY)
   --------
   [≻ (begin-
        ;; define the type, eg "Nat"
        #,(syntax/loc #'TY
            (define-type TY : τ #:extra elim-TY (C ([x τin] ...) ((xrec) ...)) ...))

        ;; define the data constructors, eg Z and S
        #,@(for/list ([C (attribute C)]
                      [τC (attribute τC)])
             (quasisyntax/loc C
               (define-cur-constructor #,C : #,τC)))

        ;; elimination form
        (define-typerule/red (elim-TY v P m ...) ≫
          [⊢ v ≫ v- ⇐ TY]
;          [⊢ v ≫ v- ⇒ TY-expander]
          [⊢ P ≫ P- ⇐ (→ TY Type)] ; prop / motive
          ;; each `m` can consume 2 sets of args:
          ;; 1) args of the constructor `x` ... 
          ;; 2) IHs for each `x` that has type `TY`
          #:with (τm ...) #'((Π [x : τin] ...
                                (→ (P- xrec) ... (P- (C x ...)))) ...)
          [⊢ m ≫ m- ⇐ τm] ...
          -----------
          [⊢ (eval-TY v- P- m- ...) ⇒ (P- v-)]
          #:where eval-TY #:display-as elim-TY ; elim reduction rule
          [(#%plain-app C-pat P m ...) ; elim redex
           ~> (app/eval m x ... (eval-TY xrec P m ...) ...)] ...)
        )]]
  ;; --------------------------------------------------------------------------
  ;; defines inductive type family `TY`, with:
  ;; - params A ...
  ;; - indices i ...
  ;; - ie, TY is a type constructor with type (Π [A : τA] ... [i τi] ... τ)
  ;; --------------------------------------------------------------------------
  #;[(_ TY:id [A:id (~datum :) τA] ... (~datum :) ; params
            [i:id (~datum :) τi] ... ; indices
            (~datum ->) τ
   [C:id (~datum :) τC] ...) ≫
   ; need to expand `τC` but `TY` is still unbound so use tmp id
   [⊢ (with-unbound TY τC) ≫ (~unbound TY (~Π [A+i+x : τA+i+x] ... τout)) ⇐ Type] ...
   ;; split τC args into params and others
   ;; TODO: check that τA matches τCA (but cant do it in isolation bc they may refer to other params?)
   #:with ((([CA τCA] ...)
            ([i+x τin] ...)) ...)
          (stx-map
           (λ (x+τs) (stx-split-at x+τs (stx-length #'(A ...))))
           #'(([A+i+x τA+i+x] ...) ...))

   ;; - each (xrec ...) is subset of (x ...) that are recur args,
   ;; ie, they are not fresh ids
   ;; - each xrec is accompanied with irec ...,
   ;;   which are the indices in i+x ... needed by xrec
   ;; ASSUME: the indices are the first (stx-length (i ...)) args in i+x ...
   ;; ASSUME: indices cannot have type (TY ...), they are not recursive
   ;;         (otherwise, cannot include indices in args to find-recur/i)
   #:with (((xrec irec ...) ...) ...)
          (find-recur/i #'TY (stx-length #'(i ...)) #'(([i+x τin] ...) ...))
   ;; ---------- pre-generate other patvars; makes nested macros below easier to read
   #:with (A- ...) (generate-temporaries #'(A ...))
   #:with (i- ...) (generate-temporaries #'(i ...))
   ;; inst'ed τin and τout (with A ...)
   #:with ((τin/A ...) ...) (stx-map generate-temporaries #'((τin ...) ...))
   #:with (τout/A ...) (generate-temporaries #'(C ...))
   ; τoutA matches the A and τouti matches the i in τout/A,
   ; - ie τout/A = (TY τoutA ... τouti ...)
   ; - also, τoutA refs (ie bound-id=) CA and τouti refs i in i+x ...
   #:with ((τoutA ...) ...) (stx-map (lambda _ (generate-temporaries #'(A ...))) #'(C ...))
   #:with ((τouti ...) ...) (stx-map (lambda _ (generate-temporaries #'(i ...))) #'(C ...))
   ;; differently named `i`, to match type of P
   #:with (j ...) (generate-temporaries #'(i ...))
   ; dup (A ...) C times, again for ellipses matching
   #:with ((A*C ...) ...) (stx-map (lambda _ #'(A ...)) #'(C ...))
   #:with (m ...) (generate-temporaries #'(C ...))
   #:with (τ1 ...) (generate-temporaries #'(C ...))
   #:with (m- ...) (generate-temporaries #'(C ...))
   #:with TY- (mk-- #'TY)
   #:with TY-patexpand (mk-~ #'TY)
   #:with elim-TY (format-id #'TY "elim-~a" #'TY)
   #:with eval-TY (format-id #'TY "match-~a" #'TY)
   #:with (τm ...) (generate-temporaries #'(m ...))
   #:with (C-expander ...) (stx-map mk-~ #'(C ...))
   ;; these are all the generated definitions that implement the define-datatype
   #:with OUTPUT-DEFS
    #'(begin-
        ;; define the type
        (define-cur-constructor TY : (Π [A : τA] ... [i : τi] ... τ))

        ;; define the data constructors
        (define-cur-constructor C : τC) ...

        ;; define eliminator-form elim-TY
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
          ;; target, infers A ...
          [⊢ v ≫ v- ⇒ (TY-patexpand A ... i ...)]
          
          ;; inst τin and τout with inferred A ...
          ;; - unlike in the TY def, must explicitly instantiate here
          ;; bc these types reference a different binder, ie CA instead of A
          ;; - specifically, replace CA ... with the inferred A ... params
          ;; - don't need to instantiate τi ... bc they already reference A,
          ;;   which we reused as the pattern variable above
          #:with ((τin/A ... τout/A) ...)
                 (stx-map
                  (λ (As τs) (substs #'(A ...) As τs))
                  #'((CA ...) ...)
                  #'((τin ... τout) ...))

          ;; τi here is τi above, instantiated with A ... from v-
          [⊢ P ≫ P- ⇐ (Π [j : τi] ... (→ (TY A ... j ...) Type))]

          ;; get the params and indices in τout/A
          ;; - dont actually need τoutA, except to find τouti
          ;; - τouti dictates what what "index" args P should be applied to
          ;;   in each method output type
          ;;     ie, it is the (app P- τouti ...) below
          ;;   It is the index, "unified" with its use in τout/A
          ;;   Eg, for empty indexed list, for index n, τouti = 0
          ;;       for non-empt indx list, for index n, τouti = (Succ 0)
          ;; ASSUMING: τoutA has shape (TY . args) (ie, unexpanded)
          #:with ((~app/eval/c (~literal TY) τoutA ... τouti ...) ...) #'(τout/A ...)

          ;; each m is curried fn consuming 3 (possibly empty) sets of args:
          ;; 1,2) i+x  - indices of the tycon, and args of each constructor `C`
          ;;             the indices may not be included, when not needed by the xs
          ;; 3) IHs - for each xrec ... (which are a subset of i+x ...)
          #:with (τm ...)
                 #'((Π [i+x : τin/A] ... ; constructor args ; ASSUME: i+x includes indices
                       (→ (P- irec ... xrec) ... ; IHs
                          (P- τouti ... (C A*C ... i+x ...)))) ...)
          [⊢ m ≫ m- ⇐ τm] ...
          -----------
          [⊢ (eval-TY v- P- m- ...) ⇒ (P- i ... v-)]
          #:where eval-TY #:display-as elim-TY ; elim reduction rule
          [(#%plain-app (C-expander CA ... i+x ...) P m ...) ; elim redex
           ~> (app/eval m i+x ... (eval-TY xrec P m ...) ...)] ...)
        )
   --------
   [≻ OUTPUT-DEFS]])


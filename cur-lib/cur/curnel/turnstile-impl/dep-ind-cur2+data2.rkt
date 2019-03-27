#lang turnstile/lang
(require (except-in "dep-ind-cur2.rkt" λ #%app Π ~Π)
         (except-in "dep-ind-cur2+sugar.rkt" define)
         (only-in "dep-ind-cur2+data.rkt" [define-datatype define-datatype1] pat->ctxt datacons)
         turnstile/eval turnstile/typedefs turnstile/more-utils)

;; a 2nd dep-ind-cur2 library implementing define-datatype
;; - uses define-type directly instead of define-cur-constructor
;; - so does not curry
;; - but is cleaner to explain

; Π  λ ≻ ⊢ ≫ → ∧ (bidir ⇒ ⇐) τ⊑ ⇑

(provide define-datatype (for-syntax pat->ctxt))

;; define-data-constructor wraps define-type to enable currying of constructor,
;; differences with define-type*:
;; - expander name same as constructor name
(define-syntax define-data-constructor
  (syntax-parser
    [(_ name (~datum :) [A+i:id Atag:id τ] ... (~datum ->) τ-out . rst)
     #:with name/internal (fresh #'name)
     #:with name/internal-expander (mk-~ #'name/internal)
     #:with name-expander #'name
     #:with (p ...) (generate-temporaries #'(A+i ...))
      #'(begin-
         (define-type name/internal : [A+i Atag τ] ... -> τ-out . rst)
         (define-syntax name
           (datacons
            (λ (stx)
              ((make-variable-like-transformer
                (quasisyntax/loc stx
                  (λ [A+i : τ] ...
                     #,(syntax/loc stx (name/internal A+i ...)))))
               stx))
            #;(make-variable-like-transformer
               #'(λ [A+i : τ] ... (name/internal A+i ...)))
            (λ (pat t) ; pat should have type t (unexpanded type)
              (syntax-parse pat
                [:id ; nullary constructor, no extra binders
                 #:fail-unless (free-id=? (stx-car t) (stx-car #'τ-out))
                 (format "expected pattern for type ~a, given pattern for ~a: ~a\n"
                         (type->str t) (type->str #'τ-out) (syntax->datum pat))
                 null]
                [(_ p ...)
                 #:fail-unless (free-id=? (stx-car t) (stx-car #'τ-out))
                 (format "expected pattern for type ~a, given pattern for ~a: ~a\n"
                         (type->str t) (type->str #'τ-out) (syntax->datum pat))
                 #:with (_ . params) t ; unexpanded type
                 (stx-appendmap
                  pat->ctxt
                  #'(p ...)
                  ;; if pat for a param is omitted, infer from t
                  ;; TODO: is this right?
                  (let-values ([(missingAs missingparams)
                                (for/lists (l1 l2)
                                           ([param (in-stx-list #'params)]
                                            [A (stx-take #'(A+i ...) (stx-length #'params))]
                                            [pp (stx-take #'(p ...) (stx-length #'params))]
                                            #:when (equal? (stx->datum pp) '_))
                                  (values A param))])
                    (substs missingparams missingAs #'(τ ...))))]))))
         (begin-for-syntax
           (define-syntax name-expander
             (make-rename-transformer #'name/internal-expander))))]))

;; define-type* wraps define-type to enable currying of constructor
(define-syntax define-type*
  (syntax-parser
    [(_ name (~datum :) [A+i:id Atag:id τ] ... (~datum ->) τ-out . rst)
     #:with name/internal (fresh #'name)
     #:with name/internal-expander (mk-~ #'name/internal)
     #:with name-expander (mk-~ #'name)
      #'(begin-
         (define-type name/internal : [A+i Atag τ] ... -> τ-out . rst)
         (define-syntax name
           #;(make-variable-like-transformer
            #'(λ [A+i : τ] ... (name/internal A+i ...)))
           (λ (stx)
             ((make-variable-like-transformer
               (quasisyntax/loc stx
                 (λ [A+i : τ] ...
                    #,(syntax/loc stx (name/internal A+i ...)))))
              stx)))
         (begin-for-syntax
           (define-syntax name-expander
             (make-rename-transformer #'name/internal-expander))))]))

(begin-for-syntax
  ;; x+τss = (([x τ] ...) ...)
  ;; returns subset of each (x ...) that is recursive, ie τ = (TY . args)
  ;; along with the indices needed by each recursive x
  ;; - ASSUME: the needed indices are first `num-is` arguments in x+τss
  ;; - ASSUME: the recursive arg has type (TY . args) where TY is unexpanded
  (define (find-recur/is TY num-is x+τss)
    (stx-map
     (λ (x+τs)
       (define xs (stx-map stx-car x+τs))
       (stx-filtermap
        (syntax-parser
          [(x t:id) (and (free-id=? #'t TY) (list #'x))] ; num-is should be = 0
          [(x (t:id . _)) (and (free-id=? #'t TY) (cons #'x (stx-take xs num-is)))]
          [_ #f])
        x+τs))
     x+τss))
  )

;; TmpTy is a placeholder for undefined names
(struct TmpTy- ())
(define-syntax TmpTy
  (syntax-parser
    [:id (assign-type #'TmpTy- #'Type)]
    ;; TODO: orig will get stuck with eg, (TmpTy A)
    [(_ . args) (assign-type (syntax/loc this-syntax (app/eval TmpTy- . args)) #'Type)]))

;; use this macro to expand e, which contains references to unbound X
(define-syntax (with-unbound stx)
  (syntax-parse stx
    [(_ X:id e)
     ;swap in a tmp (bound) id `TmpTy` for unbound X
     #:with e/tmp (subst #'TmpTy #'X #'e)
     ;; expand with the tmp id
      (expand/df #'e/tmp)]))

;; TODO: problem: use unexpanded A ... and τA ..., or expanded A2 and τA2 ?
;; - must expand:
;;   - ow var capture possible (eg binder types) due to patvar trick in output macros
;;     - manual subst will capture as well
;;     - (cant use function application to inst bc of mixing expanded (P-) and unexpanded terms)
;;   - eg (define-datatype TY [A : Type] [B : (Π [A : Type] A)] -> Type)
;;     - the 2nd A binding will get replaced with whatever the first A arg is
;;       - eg (TY (Π [X : Type] X) _) -> "non-id err" due to  (Π [(Π [X : Type] X) : Type] _)
;;   - see also dep-ind-cur2+data2-tests
;; - must not expand:
;;   - passing already-expanded types to define-type (and other forms)
;;     may result in loss of types of types when crossing module boundry
;;     - bc stx props not preserved deeply
;;   - eg, run stdlib/sigma tests when giving expanded types to define-type
;; - workaround:
;;   - dont expand, until expander is fixed
;;   - but manually check for captured binders (TODO)
(define-typed-syntax define-datatype
  ;; simple datatypes, eg Nat -------------------------------------------------
  ;; - ie, `TY` is an id with no params or indices
  [(_ TY:id (~datum :) τ [C:id (~datum :) τC] ...) ≫
   ----------
   [≻ (define-datatype1 TY : τ [C : τC] ...)]]
  [(_ TY:id (~and (~not (~datum :)) A) ...  (~datum ->) . rst) ≫ ; no indices
   ----------
   [≻ (define-datatype TY A ... : -> . rst)]]
  ;; --------------------------------------------------------------------------
  ;; defines inductive type family `TY`, with:
  ;; - params A ...
  ;; - indices i ...
  ;; - ie, TY is a type constructor with type (Π [A : τA] ... [i τi] ... τ)
  ;; --------------------------------------------------------------------------
  [(_ TY:id [A:id Atag:id τA] ... (~datum :) ; params: τA may reference preceding A
            [i:id itag:id τi] ... ; indices: τis may reference As and preceding i
            (~datum ->) τ
            ;; constructors: τin ... τout may reference A ... and preceding i+x ...
            (~or* (~and [C:id (~datum :) τout] ;; nullary constructor
                        (~parse ([i+x i+xtag τin]...) #'()))
                  (~and [C:id (~datum :)
                              [i+x1:id (~datum :) #;i+xtag1:id τin1] ... ; named args
                              (~and τin2 (~not [_:id (~datum :) _])) ... ; unnamed args
                              (~datum ->) τout]
                        (~parse ([i+x i+xtag τin] ...)
                                (append
                                 (syntax->list #'([i+x1 : #;i+xtag1 τin1] ...))
                                 (stx-map
                                  (λ (t)
                                    (list
                                     (syntax-property (generate-temporary) 'tmp #t)
                                     ':
                                     t))
                                  #'(τin2 ...))))))
            ...) ≫

   ;; validate types: use nested telescopes
   [[A ≫ _ Atag τA ≫ _] ... ⊢
    [[i ≫ _ itag τi ≫ _] ... ⊢ τ ≫ _ ⇒ (~Type ilvl)]
    [[i+x ≫ _ i+xtag (with-unbound TY τin) ≫ _] ... ⊢ (with-unbound TY τout) ≫ _ ⇒ (~Type jlvl)] ...]
   ;; TODO: Need to check the relation between i and j. Would be automatic if we just checked these as function types.

   ;; - each (xrec ...) is subset of (x ...) that are recur args,
   ;; ie, they are not fresh ids
   ;; - each xrec is accompanied with irec ...,
   ;;   which are the indices in i+x ... needed by xrec
   ;; ASSUME: the indices are the first (stx-length (i ...)) args in i+x ...
   ;; ASSUME: indices cannot have type (TY ...), they are not recursive
   ;;         (otherwise, cannot include indices in args to find-recur/i)
   #:with (((xrec irec ...) ...) ...)
          (find-recur/is #'TY (stx-length #'(i ...)) #'(([i+x τin] ...) ...))

   ;; ---------- pre-generate other patvars; makes nested macros below easier to read
   ;; i* = inferred (concrete) i in elim
   #:with (i* ...) (generate-temporaries #'(i ...))
   ; dup (A ...) C times, for ellipses matching
   #:with ((AxC ...) ...) (stx-map (lambda _ #'(A ...)) #'(C ...))
   #:with ((AtagxC ...) ...) (stx-map (lambda _ #'(Atag ...)) #'(C ...))
   #:with ((τAxC ...) ...) (stx-map (λ _ #'(τA ...)) #'(C ...))
   #:with (m ...) (generate-temporaries #'(C ...))
   #:with (m- ...) (generate-temporaries #'(C ...))
   #:with TY-patexpand (mk-~ #'TY)
   #:with elim-TY (format-id #'TY "elim-~a" #'TY)
   #:with eval-TY (format-id #'TY "match-~a" #'TY)
   #:with (τm ...) (generate-temporaries #'(m ...))
   #:with (C-expander ...) (stx-map mk-~ #'(C ...))

   ;; ASSUMING: τoutA has shape (TY A ... τouti ...), or id
   ;; - this is the same "patvar trick" as re-using A below
   ;; - it makes sure that the method output types properly reference the right i
   #:with ((τouti ...) ...) (stx-map
                             (λ (ts)
                               (or (and (stx-pair? ts) (stx-drop ts (add1 (stx-length #'(A ...)))))
                                   #'()))
                             #'(τout ...))

   ;; these are all the generated definitions that implement the define-datatype
   #:with OUTPUT-DEFS
    #'(begin-
        ;; define the type
        (define-type* TY : [A Atag τA] ... [i itag τi] ... -> τ
          #:extra elim-TY
                  ([A τA] ...)
                  ([i τi] ...)
                  (C ([i+x τin] ... τout) ((xrec irec ...) ...)) ...)

        ;; define the data constructors
        (define-data-constructor C : [AxC AtagxC τAxC] ... [i+x i+xtag τin] ... -> τout) ...

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
          ;; this means every patvar in define-datatype input pattern that references A
          ;; is now instantiated with inferred A
          ;; (see also comments below)
          [⊢ v ≫ v- ⇒ (TY-patexpand A ... i* ...)]

          ;; τi instantiated with A ... from v-
          [⊢ P ≫ P- ⇐ (Π [i itag τi] ...
                         (→ (TY #,@(stx-map unexpand #'(A ... i ...))) TypeTop))]

          ;; each m is curried fn consuming 3 (possibly empty) sets of args:
          ;; 1,2) i+x  - indices of the tycon, and args of each constructor `C`
          ;;             the indices may not be included, when not needed by the xs
          ;; 3) IHs - for each xrec ... (which are a subset of i+x ...)
          #:with (τm ...)
                 #`( (Π [i+x i+xtag τin] ... ; constructor args ; ASSUME: i+x includes indices
                        (→ (P- irec ... xrec) ... ; IHs
                           (P- #,@(stx-map unexpand #'(τouti ...))
                               (C #,@(stx-map unexpand #'(AxC ... i+x ...))))))
                     ...)
          [⊢ m ≫ m- ⇐ τm] ...
          -----------
          [⊢ (eval-TY v- P- m- ...) ⇒ (P- #,@(stx-map unexpand #'(i* ...)) v-)]

          #:where eval-TY #:display-as elim-TY ; elim reduction rule
          [(#%plain-app (C AxC ... i+x ...) P m ...) ; elim redex
           ~> (app/eval m i+x ... (eval-TY xrec P m ...) ...)] ...)
        )
;    #:do[(pretty-print (stx->datum #'OUTPUT-DEFS))]
   --------
   [≻ OUTPUT-DEFS]])

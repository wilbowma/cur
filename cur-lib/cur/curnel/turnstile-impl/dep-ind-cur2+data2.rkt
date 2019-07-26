#lang turnstile/lang
(require (except-in "dep-ind-cur2.rkt" λ #%app Π ~Π)
         (except-in "dep-ind-cur2+sugar.rkt" define)
         turnstile/eval turnstile/typedefs turnstile/more-utils)

;; a 2nd dep-ind-cur2 library implementing define-datatype
;; - tries to match coq Inductive syntax

; Π  λ ≻ ⊢ ≫ → ∧ (bidir ⇒ ⇐) τ⊑ ⇑

(provide define-datatype
         (for-syntax datacons datacons-pat->ctxt pat->ctxt (rename-out [get-is get-idxs/unexp])))

(begin-for-syntax
  (struct datacons (proc pat->ctxt)
    #:property prop:procedure (struct-field-index proc))
  ;; pattern `pat` has (unexpanded) type `ty`
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
      ;; TODO: only set 'recur for rec args?
      [:id (list (list pat (syntax-property ty 'recur #t)))] ; patvar
      [(C . _)
       ((datacons-pat->ctxt (syntax-local-value #'C)) pat ty)])))

;; define-data-constructor wraps define-type to enable currying of constructor,
;; differences with define-type*:
;; - expander name same as constructor name
;; - constructor name is a datacons transformer, for pattern positions
(define-syntax define-data-constructor
  (syntax-parser
    [;; τ and τ-out have "unexpanded" shape, ie curried with single-applications
     ;; TODO: should they be unexpanded before or after passing to define-data-constructor?
     (_ name [A:id Atag:id τA] ... (~datum :) [i+x (~datum :) τ] ... (~datum ->) τ-out . rst)
     #:with name/internal (fresh #'name)
     #:with name/internal-expander (mk-~ #'name/internal)
     #:with name-expander #'name
     #:with (p ...) (generate-temporaries #'(A ... i+x ...))
      #'(begin-
         (define-type name/internal : [A Atag τA] ... [i+x : τ] ... -> τ-out . rst)
         (define-syntax name
           (datacons
            (λ (stx)
              ((make-variable-like-transformer
                (quasisyntax/loc stx
                  (λ [A Atag τA] ... [i+x : τ] ...
                     #,(syntax/loc stx (name/internal A ... i+x ...)))))
               stx))
            #;(make-variable-like-transformer
               #'(λ [A+i : τ] ... (name/internal A+i ...)))
            (λ (pat t) ; pat should have type t (unexpanded type)
              (syntax-parse pat
                #;[debug
                   #:do[(printf "pat->ctxt: ~a : ~a (expected ~a)\n"
                                (stx->datum #'debug) (stx->datum t) (stx->datum #'τ-out))]
                   #:when #f #'debug]
                [:id ; nullary constructor, no extra binders
                 #:fail-unless (if (id? t)
                                   (typecheck? ((current-type-eval) t)
                                               ((current-type-eval) #'τ-out))
                                   (free-id=? (stx-car t) (get-ty-name #'τ-out)))
                 (format "expected pattern for type ~a, given pattern for ~a: ~a\n"
                         ((current-resugar) t) ((current-resugar) #'τ-out) (syntax->datum pat))
                 null]
                [(_ p ...)
                 #:fail-unless (if (id? t)
                                   (typecheck? ((current-type-eval) t)
                                               ((current-type-eval) #'τ-out))
                                   (free-id=? (stx-car t) (get-ty-name #'τ-out)))
                 (format "expected pattern for type ~a, given pattern for ~a: ~a\n"
                         ((current-resugar) t) ((current-resugar) #'τ-out) (syntax->datum pat))
                 (let L ([res null]
                         ;; drop param pats, for now
                         ;; to include them, need to make them equiv to params in t?
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
                       (let ([x+tys (pat->ctxt (car ps) (transfer-props t (car τs)))])
                         (L (append res x+tys)
                            (cdr ps)
                            (cdr xs)
                            (if (and (not (null? x+tys))
                                     (id? (car ps))
                                     (free-id=? (car ps) (caar x+tys)))
                                (map (λ (t) (subst (car ps) (car xs) t)) (cdr τs))
                                (cdr τs))))))]))))
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
  ;; - ASSUME: the recursive arg has type (TY . args) where TY is unexpanded
  ;;   series of curried mono-apps, where indices are last num-is args to TY
  (define (find-recur/is TY num-is x+τss)
    (stx-map
     (λ (x+τs)
       (define xs (stx-map stx-car x+τs))
       (stx-filtermap
        (syntax-parser
          [(x t:id) (and (free-id=? #'t TY) (list #'x))] ; num-is should be = 0
          [(x t) #:when (free-id=? (get-ty-name #'t) TY)
                 (cons #'x (get-is #'t num-is))]
          [_ #f])
        x+τs))
     x+τss))
  ;; ty is unexpanded, series of curried mono-applications of type constructor
  (define (get-ty-name ty)
    (if (id? ty) ty (get-ty-name (stx-car ty))))
  ;; ty is unexpanded, series of curried mono-applications of type constructor
  (define (get-is ty num-is)
    (if (zero? num-is) null (append (get-is (stx-car ty) (sub1 num-is)) (stx-cdr ty))))
  )

;; define-datatype : matches coq Inductive defs
(define-typed-syntax define-datatype
  [(_ TY:id [A_:id (~datum :) τA_] ... ; params: τA_ may reference preceding A
            (~datum :) τTY_ ; possibly declares indices, may reference params
            ;; constructors, full type of each C is (Π [A_ : τA_] ... x+τx ... τC)
            [C:id (~and (~not (~datum :)) x+τx) ...
                  (~optional (~seq (~datum :) τC) ; TODO: improve err with no τout and indices
;                                   (~parse τout-omitted? #'#t))
                             #:defaults ([τC #'(TY A_ ...)]))] ...) ≫
   ;; validate inputs
   [[A_ ≫ A : τA_] ...
    [TY ≫ TY- : (Π [A_ : τA_] ... τTY_)] ; need TY in env for inductive args
                   ;; TODO: Am I missing any predicativity checks?
                   ⊢ [τTY_ ≫ (~Π [i : τi_] ... τ_) ⇒ (~Type _)]
                     [(Π x+τx ... τC) ≫ (~Π [i+x : τin_] ... τout_) ⇒ (~Type _)] ...]

   ;; TODO: this err msg comes too late, ie the above already fails
   ;; problem is we dont know number of indices until after expanding
   ;; #:fail-when (and (attribute τout-omitted?) (not (zero? (stx-length #'(i ...)))))
   ;;             "must explicitly declare output types when indices > 0"

   ;; reconstruct surface tys, with proper binder and references
   ;; - must work with unexpanded stx bc TY still undefined
   ;; eg, if TY is base type, references in τin_ or τout_ will appear unexpanded
   #:with (τA ...) (substs #'(A ...) #'(A_ ...) #'(τA_ ...))
   #:with (τi ... τ) (stx-map (unexpand/ctx #'TY) #'(τi_ ... τ_))
   #:with ((τin ... τout) ...) (stx-map
                                (λ (ts) (stx-map (unexpand/ctx #'TY) ts))
                                (subst #'TY #'TY- #'((τin_ ... τout_) ...)))

   ;; - each (xrec ...) is subset of (x ...) that are recur args,
   ;; ie, they are not fresh ids
   ;; - each xrec is accompanied with irec ...,
   ;;   which are the indices in i+x ... needed by xrec
   #:do[(define num-params (stx-length #'(A ...)))
        (define num-idxs (stx-length #'(i ...)))]
   #:with (((xrec irec ...) ...) ...)
          (find-recur/is #'TY num-idxs #'(([i+x τin] ...) ...))

   ;; below here is same as define-datatype ------------------------------
          
   ;; ---------- pre-generate other patvars; makes nested macros below easier to read
   ;; i* = inferred (concrete) i in elim
   #:with (i* ...) (generate-temporaries #'(i ...))
   ; dup (A ...) C times, for ellipses matching
   #:with ((AxC ...) ...) (stx-map (lambda _ #'(A ...)) #'(C ...))
   #:with ((τAxC ...) ...) (stx-map (λ _ #'(τA ...)) #'(C ...))
   #:with (m ...) (generate-temporaries #'(C ...))
   #:with (m- ...) (generate-temporaries #'(C ...))
   #:with TY-patexpand (mk-~ #'TY)
   #:with elim-TY (format-id #'TY "elim-~a" #'TY)
   #:with eval-TY (format-id #'TY "match-~a" #'TY)
   #:with (τm ...) (generate-temporaries #'(m ...))
   #:with (C-pat ...) (stx-map
                       (λ (C xs)
                         (if (and (zero? num-params) (stx-null? xs))
                             C ; must not be (C) pattern; unlike #%app, (C) \neq C due to id macro behavior
                             #`(#,C A ... . #,xs)))
                       #'(C ...)
                       #'((i+x ...) ...))

   ;; ASSUMING: τout is unexpanded curried single-apps
   ;; - this is the same "patvar trick" as re-using A below
   ;; - it makes sure that the method output types properly reference the right i
   #:with ((τouti ...) ...) (stx-map (λ (t) (get-is t num-idxs)) #'(τout ...))

   ;; these are all the generated definitions that implement the define-datatype
   #:with OUTPUT-DEFS
    #`(begin-
        ;; define the type
        (define-type* TY : [A : τA] ... [i : τi] ... -> τ
          #:extra elim-TY
                  ([A τA] ...)
                  ([i τi] ...)
                  (C ([i+x τin] ... τout) ((xrec irec ...) ...)) ...)

        ;; define the data constructors
        (define-data-constructor C [AxC : τAxC] ... : [i+x : τin] ... -> τout) ...

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
          ;; - must unexpand all types that reference A ...
          ;; (see also comments below)
          #,(if (zero? (+ num-params num-idxs))
                #'[⊢ v ≫ v- ⇐ TY]
                #'[⊢ v ≫ v- ⇒ (TY-patexpand A ... i* ...)])

          ;; τi instantiated with A ... from v-
          ;; nb: without this conditional, sf/Poly.rkt fails with mysterious tyerr
          #,@(if (zero? (+ num-params num-idxs))
                 ;; NB: Hack to get better inference on motives.
                 ;; I *expect* the user will never use a type as large as 9001,
                 ;; and so this is a reasonable type to check against.
                 ;; The right approach is to add some kind of universe
                 ;; polymorphism, or unification, but I'm not going to do that yet.
                 ;; TODO: Generate multiple clauses, one that tries this, and
                 ;; one that falls back to inference.
                 (list
                  #'[⊢ P ≫ P- ⇐ (→ TY (Type 9001))])
                (list
                 ;; TODO: This much more intuitive thing doesn't work because ~Π
                 ;; patterns can't be nested this way... think they could, if ~Π
                 ;; was implemented using stx-parse/fold-right?
                 ;#'[⊢ P ≫ P- ⇒ (~Π [i** : τi] ...
                 ;                  (~Π [t* : (TY-patexpand A ... i** ...)] (~Type motive_level:nat)))]
                 ; The infer version:
                 ;#'[⊢ P ≫ P- ⇒ (~Π [i** : τi**] (... ...) ; TODO: unexpand τi? (may reference A ...?)
                 ;                  (~Type motive_level:nat))]
                 ;#'#:when
                 ;#'(typecheck?
                 ;   (expand/df #'(Π [i** : τi**] (... ...) (Type motive_level)))
                 ;   (expand/df #`(Π [i : τi] ... ; TODO: unexpand τi? (may reference A ...?)
                 ;        (→ (TY #,@(stx-map unexpand #'(A ...)) i ...) (Type motive_level)))))
                 #'[⊢ P ≫ P- ⇐ (Π [i : τi] ... ; TODO: unexpand τi? (may reference A ...?)
                                  (→ (TY #,@(stx-map unexpand #'(A ...)) i ...) (Type 9001)))]

                 ))

          ;; each m is curried fn consuming 3 (possibly empty) sets of args:
          ;; 1,2) i+x  - indices of the tycon, and args of each constructor `C`
          ;;             the indices may not be included, when not needed by the xs
          ;; 3) IHs - for each xrec ... (which are a subset of i+x ...)
          #:with (τm ...)
          ;; #,(if (zero? (+ num-idxs num-params))
          ;;       #'#'((Π [i+x : τin] ...
          ;;             (→ (P- xrec) ... (P- (C i+x ...)))) ...)
          ;;       #'#`( (Π [i+x : τin] ... ; constructor args ; ASSUME: i+x includes indices
          ;;                (→ (P- irec ... xrec) ... ; IHs
          ;;                   ;; need to unexpand τouti again bc it may reference (new) A ...
          ;;                  (P- #,@(stx-map unexpand #'(τouti ...))
          ;;                      (C #,@(stx-map unexpand #'(AxC ...)) i+x ...))))
          ;;             ...))
          ;; TODO: unexpand τin ...? (may reference A ...?)
          #`( (Π [i+x : τin] ... ; constructor args ; ASSUME: i+x includes indices
                 (→ (P- irec ... xrec) ... ; IHs
                    ;; need to unexpand τouti again bc it may reference (new) A ...
                    (P- #,@(stx-map unexpand #'(τouti ...))
                        (C #,@(stx-map unexpand #'(AxC ...)) i+x ...))))
              ...)
          
          [⊢ m ≫ m- ⇐ τm] ...

          ;; #:with out-ty #,(if (zero? (+ num-params num-idxs))
          ;;                     #'#'(P- v-)
          ;;                     #'#`(P- #,@(stx-map unexpand #'(i* ...)) v-))
          #:with out-ty #`(P- #,@(stx-map unexpand #'(i* ...)) v-)
          -----------
          [⊢ (eval-TY v- P- m- ...) ⇒ out-ty]

          #:where eval-TY #:display-as elim-TY ; elim reduction rule
          [(#%plain-app C-pat P m ...) ; elim redex
           ~> (app/eval m i+x ... (eval-TY xrec P m ...) ...)] ...)
        )
;    #:do[(pretty-print (stx->datum #'OUTPUT-DEFS))]
   --------
   [≻ OUTPUT-DEFS]])


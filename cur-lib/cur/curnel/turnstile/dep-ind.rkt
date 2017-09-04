#lang turnstile/lang
;commit SHA: 8eb637a 
; a basic dependently-typed calculus
; - with inductive datatypes

; Π  λ ≻ ⊢ ≫ → ∧ (bidir ⇒ ⇐) τ⊑

(provide Type (rename-out [Type *])
         Π → ∀
         = eq-refl eq-elim
         λ (rename-out [app #%app]) ann
         define-datatype define define-type-alias
)

;; TODO:
;; - map #%datum to S and Z
;; - rename define-type-alias to define
;; - add "assistant" part
;; - provide match and match/lambda so nat-ind can be fn
;;   - eg see https://gist.github.com/AndrasKovacs/6769513
;; - add dependent existential
;; - remove debugging code?

;; set (Type n) : (Type n+1)
;; Type = (Type 0)
(define-internal-type-constructor Type)
(define-typed-syntax Type
  [:id ≫ --- [≻ (Type 0)]]
  [(_ n:exact-nonnegative-integer) ≫
   #:with n+1 (+ (syntax-e #'n) 1)
  -------------
  [≻ #,(syntax-property
        (syntax-property 
         #'(Type- 'n) ':
         (syntax-property
          #'(Type- 'n+1)
          'orig
          (list #'(Type n+1))))
        'orig
        (list #'(Type n)))]])

(begin-for-syntax
  (define debug? #f)
  (define type-eq-debug? #f)
  (define debug-match? #f)

  ;; TODO: fix `type` stx class
  ;; current-type and type stx class not working
  ;; for case where var has type that is previous var
  ;; that is not yet in tyenv
  ;; eg in (Π ([A : *][a : A]) ...)
  ;; expansion of 2nd type A will fail with unbound id err
  ;;
  ;; attempt 2
  ;; (define old-type? (current-type?))
  ;; (current-type?
  ;;  (lambda (t)
  ;;    (printf "t = ~a\n" (stx->datum t))
  ;;    (printf "ty = ~a\n" (stx->datum (typeof t)))
  ;;    (or (Type? (typeof t))
  ;;        (syntax-parse (typeof t)
  ;;          [((~literal Type-) n:exact-nonnegative-integer) #t]
  ;;          [_ #f]))))
  ;; attempt 1
  ;; (define old-type? (current-type?))
  ;; (current-type?
  ;;  (lambda (t) (or (#%type? t) (old-type? t))))


  (define old-relation (current-typecheck-relation))
  (current-typecheck-relation
   (lambda (t1 t2)
     (define res
       ;; expand (Type n) if unexpanded
       (or (syntax-parse t1
             [((~literal Type-) n)
              (typecheck? ((current-type-eval) t1) t2)]
             [_ #f])
           (old-relation t1 t2)))
     (when type-eq-debug?
       (pretty-print (stx->datum t1))
       (pretty-print (stx->datum t2))
       (printf "res: ~a\n" res))
     res))
  ;; used to attach type after app/eval
  ;; but not all apps will have types, eg
  ;; - internal type representation
  ;; - intermediate elim terms
  (define (maybe-assign-type e t)
    (if (syntax-e t) (assign-type e t) e)))

(define-internal-type-constructor →) ; equiv to Π with no uses on rhs
(define-internal-binding-type ∀)     ; equiv to Π with Type for all params

;; Π expands into combination of internal →- and ∀-
;; uses "let*" syntax where X_i is in scope for τ_i+1 ...
;; TODO: add tests to check this
(define-typed-syntax (Π ([X:id : τ_in] ...) τ_out) ≫
  [[X ≫ X- : τ_in] ... ⊢ [τ_out ≫ τ_out- ⇒ tyoutty]
                         [τ_in  ≫ τ_in-  ⇒ tyinty] ...]
  ;; check that types have type (Type _)
  ;; must re-expand since (Type n) will have type unexpanded (Type n+1)
  #:with ((~Type _) ...) (stx-map (current-type-eval) #'(tyoutty tyinty ...))
  -------
  [⊢ (∀- (X- ...) (→- τ_in- ... τ_out-)) ⇒ Type]
  #;[⊢ #,#`(∀- (X- ...)
             #,(assign-type
                #'(→- τ_in- ... τ_out-)
                #'#%type)) ⇒ #%type])

;; abbrevs for Π
;; (→ τ_in τ_out) == (Π (unused : τ_in) τ_out)
(define-simple-macro (→ τ_in ... τ_out)
  #:with (X ...) (generate-temporaries #'(τ_in ...))
  (Π ([X : τ_in] ...) τ_out))
;; (∀ (X) τ) == (∀ ([X : Type]) τ)
(define-simple-macro (∀ (X ...)  τ)
  (Π ([X : Type] ...) τ))

;; pattern expanders
(begin-for-syntax
  (define-syntax ~Π
    (pattern-expander
     (syntax-parser
       [(_ ([x:id : τ_in] ... (~and (~literal ...) ooo)) τ_out)
        #'(~∀ (x ... ooo) (~→ τ_in ... ooo τ_out))]
       [(_ ([x:id : τ_in] ...)  τ_out)
        #'(~∀ (x ...) (~→ τ_in ... τ_out))]))))

;; equality -------------------------------------------------------------------
(define-internal-type-constructor =)
(define-typed-syntax (= t1 t2) ≫
  [⊢ t1 ≫ t1- ⇒ ty]
  [⊢ t2 ≫ t2- ⇐ ty]
  ;; #:do [(printf "t1: ~a\n" (stx->datum #'t1-))
  ;;       (printf "t2: ~a\n" (stx->datum #'t2-))]
;  [t1- τ= t2-]
  ---------------------
  [⊢ (=- t1- t2-) ⇒ Type])

;; Q: what is the operational meaning of eq-refl?
(define-typed-syntax (eq-refl e) ≫
  [⊢ e ≫ e- ⇒ _]
  ----------
  [⊢ (#%app- void-) ⇒ (= e- e-)])

;; eq-elim: t : T
;;          P : (T -> Type)
;;          pt : (P t)
;;          w : T
;;          peq : (= t w)
;;       -> (P w)
(define-typed-syntax (eq-elim t P pt w peq) ≫
  [⊢ t ≫ t- ⇒ ty]
  [⊢ P ≫ P- ⇐ (→ ty Type)]
  [⊢ pt ≫ pt- ⇐ (app P- t-)]
  [⊢ w ≫ w- ⇐ ty]
  [⊢ peq ≫ peq- ⇐ (= t- w-)]
  --------------
  [⊢ pt- ⇒ (app P- w-)])

;; lambda and #%app -----------------------------------------------------------

;; TODO: fix `type` stx class
(define-typed-syntax λ
  ;; expected ty only
  [(_ (y:id ...) e) ⇐ (~Π ([x:id : τ_in] ... ) τ_out) ≫
   [[x ≫ x- : τ_in] ... ⊢ #,(substs #'(x ...) #'(y ...) #'e) ≫ e- ⇐ τ_out]
   ---------
   [⊢ (λ- (x- ...) e-)]]
  ;; both expected ty and annotations
  [(_ ([y:id : τ_in*] ...) e) ⇐ (~Π ([x:id : τ_in] ...) τ_out) ≫
;  [(_ ([y:id : τy_in:type] ...) e) ⇐ (~Π ([x:id : τ_in] ...) τ_out) ≫
   #:fail-unless (stx-length=? #'(y ...) #'(x ...))
                 "function's arity does not match expected type"
   [⊢ τ_in* ≫ τ_in** ⇐ Type] ...
;   #:when (typechecks? (stx-map (current-type-eval) #'(τ_in* ...))
   #:when (typechecks? #'(τ_in** ...) #'(τ_in ...))
;   #:when (typechecks? #'(τy_in.norm ...) #'(τ_in ...))
;   [τy_in τ= τ_in] ...
   [[x ≫ x- : τ_in] ... ⊢ #,(substs #'(x ...) #'(y ...) #'e) ≫ e- ⇐ τ_out]
   -------
   [⊢ (λ- (x- ...) e-)]]
  ;; annotations only
  [(_ ([x:id : τ_in] ...) e) ≫
   [[x ≫ x- : τ_in] ... ⊢ [e ≫ e- ⇒ τ_out] [τ_in ≫ τ_in- ⇒ _] ...]
   -------
   [⊢ (λ- (x- ...) e-) ⇒ (Π ([x- : τ_in-] ...) τ_out)]])

;; helps debug which terms (app/evals) do not have types, eg
;; - → in internal type representation
;; - intermediate elim terms
(define-for-syntax false-tys 0)

;; TODO: fix orig after subst, for err msgs
;; app/eval should not try to ty check anymore
(define-syntax app/eval
  (syntax-parser
    #;[(_ f . args) #:do[(printf "app/evaling ")
                       (printf "f: ~a\n" (stx->datum #'f))
                       (printf "args: ~a\n" (stx->datum #'args))]
     #:when #f #'void]
    [(_ f:id (_ matcher) (_ _ . args))
     #:do[(when debug-match?
            (printf "potential delayed match ~a ~a\n"
                  (stx->datum #'matcher)
                  (stx->datum #'args)))]
     #:with ty (typeof this-syntax)
     ;; TODO: use pat expander instead
     #:with (_ m/d . _) (local-expand #'(#%app match/delayed 'dont 'care) 'expression null)
     #:when (free-identifier=? #'m/d #'f)
     #:do[(when debug-match? (printf "matching\n"))]
     ;; TODO: need to attach type?
     #;[
          (unless (syntax-e #'ty)
            (displayln 3)
            (displayln #'ty)
            (set! false-tys (add1 false-tys))
            (displayln false-tys))]
     (maybe-assign-type #'(matcher . args) (typeof this-syntax))]
    ;; TODO: apply to only lambda args or all args?
    [(_ (~and f ((~literal #%plain-lambda) (x ...) e)) e_arg ...)
     #:do[(when debug?
            (printf "apping: ~a\n" (stx->datum #'f))
            (printf "args\n")
            (pretty-print (stx->datum #'(e_arg ...))))]
;     #:with (~Π ([X : _] ...) τ_out) (typeof #'f) ; must re-subst in type
     ;; TODO: need to replace all #%app- in this result with app/eval again
     ;; and then re-expand
;     #:with ((~literal #%plain-app) newf . newargs) #'e
 ;    #:do[(displayln #'newf)(displayln #'newargs)(displayln (stx-car #'e+))]
     #:with r-app (datum->syntax (if (identifier? #'e) #'e (stx-car #'e)) '#%app)
     ;; TODO: is this assign-type needed only for tests?
     ;; eg, see id tests in dep2-peano.rkt
     #:with ty (typeof this-syntax)
     #:do[(when debug?
            (define ttt (typeof this-syntax))
            (define ttt2 (and ttt
                              (substs #'(app/eval e_arg ...) #'(r-app x ...) ttt free-identifier=?)))
            (define ttt3 (and ttt2
                              (local-expand ttt2 'expression null)))
            (printf "expected type\n")
            (pretty-print (stx->datum ttt))
            (pretty-print (stx->datum ttt2))
            (pretty-print (stx->datum ttt3)))]
     #:with e-inst (substs #'(app/eval e_arg ...) #'(r-app x ...) #'e free-identifier=?)
     ;; some apps may not have type (eg in internal reps)
     #:with e+ (if (syntax-e #'ty)
                   (assign-type
                    #'e-inst
                    (local-expand
;                     (substs #'(app/eval e_arg ...) #'(r-app x ...) #'ty free-identifier=?)
                     ;; TODO: this is needed, which means there are some uneval'ed matches
                     ;; but is this the right place?
                     ;; eg, it wasnt waiting on any arg
                     ;; so that mean it could have been evaled but wasnt at some point
                     (substs #'(app/eval) #'(r-app) #'ty free-identifier=?)
                     'expression null))
                   #'e-inst)
     #:do[(when debug?
            (displayln "res:--------------------")
            (pretty-print (stx->datum #'e+))
            ;; (displayln "actual type:")
            ;; (pretty-print (stx->datum (typeof #'e+)))
            (displayln "new type:")
            (pretty-print (stx->datum (typeof #'e+)))
            ;; (displayln "res expanded:------------------------")
            ;; (pretty-print
            ;;  (stx->datum (local-expand (substs #'(e_arg ...) #'(x ...) #'e) 'expression null)))
            (displayln "res app/eval re-expanding-----------------------"))]
     #:with ((~literal let-values) () ((~literal let-values) () e++))
            (local-expand
             #'(let-syntax (#;[app (make-rename-transformer #'app/eval)]
                            #;[x (make-variable-like-transformer #'e_arg)]) e+)
                 'expression null)
     #:do[(when debug?
            (pretty-print (stx->datum #'e++))
;            (pretty-print (stx->datum (typeof #'e++)))
            #;(local-expand
             #'(let-syntax ([app (make-rename-transformer #'app/eval)]
                            #;[x (make-variable-like-transformer #'e_arg)]) e+)
             'expression null))]
     #;[(when (not (syntax-e #'ty))
            (displayln 1)
            (displayln (stx->datum this-syntax))
            (displayln #'ty)
            (set! false-tys (add1 false-tys))
            (displayln false-tys))]
     #'e++ #;(substs #'(e_arg ...) #'(x ...) #'e)]
    [(_ f . args)
    #:do[(when debug?
           (printf "not apping\n")
           (pretty-print (stx->datum #'f))
           (displayln "args")
           (pretty-print (stx->datum #'args)))]
     #:with f+ (expand/df #'f)
     #:with args+ (stx-map expand/df #'args)
     ;; TODO: need to attach type?
     #:with ty (typeof this-syntax)
     #;[(unless (syntax-e #'ty)
            (displayln 2)
            (displayln (stx->datum this-syntax))
            (displayln #'ty)
            (displayln (syntax-property this-syntax '::))
            (set! false-tys (add1 false-tys))
            (displayln false-tys))]
     (syntax-parse #'f+
       [((~literal #%plain-lambda) . _)
        (maybe-assign-type #'(app/eval f+ . args+) #'ty)]
       [_
        ;(maybe-assign-type
         #'(#%app- f+ . args+)
         ;#'ty)
        ])]))
     
;; TODO: fix orig after subst
(define-typed-syntax app
  [(_ e_fn e_arg ...) ≫
   #:do[(when debug?
          (displayln "TYPECHECKING")
          (pretty-print (stx->datum this-syntax)))]
;   #:do[(printf "applying (1) ~a\n" (stx->datum #'e_fn))]
;   [⊢ e_fn ≫ (~and e_fn- (_ (x:id ...) e ~!)) ⇒ (~Π ([X : τ_inX] ...) τ_outX)]
   [⊢ e_fn ≫ e_fn- ⇒ (~Π ([X : τ_in] ...) τ_out)]
   #:fail-unless (stx-length=? #'[τ_in ...] #'[e_arg ...])
                 (num-args-fail-msg #'e_fn #'[τ_in ...] #'[e_arg ...])
   ;; #:do[(displayln "expecting")
   ;;      (pretty-print (stx->datum #'(τ_in ...)))]
   ;; [⊢ e_arg ≫ _ ⇒ ty2] ... ; typechecking args
   ;; #:do[(displayln "got")
   ;;      (pretty-print (stx->datum (stx-map typeof #'(ty2 ...))))]
   [⊢ e_arg ≫ e_arg- ⇐ τ_in] ... ; typechecking args
   -----------------------------
   [⊢ (app/eval e_fn- e_arg- ...) ⇒ #,(substs #'(e_arg- ...) #'(X ...) #'τ_out)]])
   
(define-typed-syntax (ann e (~datum :) τ) ≫
  [⊢ e ≫ e- ⇐ τ]
  --------
  [⊢ e- ⇒ τ])

;; top-level ------------------------------------------------------------------
;; TODO: shouldnt need define-type-alias, should be same as define
(define-syntax define-type-alias
  (syntax-parser
    [(_ alias:id τ);τ:any-type)
     #'(define-syntax- alias
         (make-variable-like-transformer #'τ))]
    #;[(_ (f:id x:id ...) ty)
     #'(define-syntax- (f stx)
         (syntax-parse stx
           [(_ x ...)
            #:with τ:any-type #'ty
            #'τ.norm]))]))

;; TODO: delete this?
(define-typed-syntax define
  [(_ x:id (~datum :) τ e:expr) ≫
   [⊢ e ≫ e- ⇐ τ]
   #:with y (generate-temporary #'x)
   #:with y+props (transfer-props #'e- #'y #:except '(origin))
   --------
   [≻ (begin-
        (define-syntax x (make-rename-transformer #'y+props))
        (define- y e-))]]
  [(_ x:id e) ≫
   ;This won't work with mutually recursive definitions
   [⊢ e ≫ e- ⇒ _]
   #:with y (generate-temporary #'x)
   #:with y+props (transfer-props #'e- #'y #:except '(origin))
   --------
   [≻ (begin-
        (define-syntax x (make-rename-transformer #'y+props))
        (define- y e-))]]
  #;[(_ (f [x (~datum :) ty] ... (~or (~datum →) (~datum ->)) ty_out) e ...+) ≫
   #:with f- (add-orig (generate-temporary #'f) #'f)
   --------
   [≻ (begin-
        (define-syntax- f
          (make-rename-transformer (⊢ f- : (→ ty ... ty_out))))
        (define- f-
          (stlc+lit:λ ([x : ty] ...)
            (stlc+lit:ann (begin e ...) : ty_out))))]])


(define-typed-syntax (unsafe-assign-type e (~datum :) τ) ≫ --- [⊢ e ⇒ τ])

(struct TmpTy- ())
(define-syntax TmpTy
  (syntax-parser
    [:id (assign-type #'TmpTy- #'Type)]
    [(_ . args) (assign-type #'(#%app TmpTy- . args) #'Type)]))

(struct match/delayed (name args) #:transparent)

(define-typed-syntax define-datatype
  ;; datatype type `TY` is an id ---------------------------------------------------
  ;; - ie, no params or indices
  [(_ Name (~datum :) TY:id
      [C:id (~datum :) CTY] ...) ≫
   ; need to expand `CTY` to find recur args,
   ; but `Name` is still unbound so swap in a tmp id `TmpTy`
   #:with (CTY/tmp ...) (subst #'TmpTy #'Name #'(CTY ...))
   [⊢ CTY/tmp ≫ CTY/tmp- ⇐ Type] ...
   #:with TmpTy+ (local-expand #'TmpTy 'expression null)
   ;; un-subst TmpTy for Name in expanded CTY
   ;; TODO: replace TmpTy in origs of CTY_in ... CTY_out
   ;; TODO: check CTY_out == `Name`?
   #:with ((~Π ([x : CTY_in] ...) CTY_out) ...)
          (subst #'Name #'TmpTy+ #'(CTY/tmp- ...) free-id=?)
   #:with (C/internal ...) (generate-temporaries #'(C ...))
   #:with (Ccase ...) (generate-temporaries #'(C ...))
   #:with (Ccase- ...) (generate-temporaries #'(C ...))
   #:with ((recur-x ...) ...) (stx-map
                               (lambda (xs ts)
                                 (filter
                                  (lambda (x) x) ; filter out #f
                                  (stx-map
                                   (lambda (x t) ; returns x or #f
                                     (and (free-id=? t #'Name) x))
                                   xs ts)))
                               #'((x ...) ...) #'((CTY_in ...) ...))
   #:with elim-Name (format-id #'Name "elim-~a" #'Name)
   #:with match-Name (format-id #'Name "match-~a" #'Name)
   #:with Name/internal (generate-temporary #'Name)
   --------
   [≻ (begin-
        ;; define `Name`, eg "Nat", as a valid type
;        (define-base-type Name) ; dont use bc uses '::, and runtime errs
        (struct Name/internal ())
        (define-typed-syntax Name [_:id ≫ --- [⊢ (Name/internal) ⇒ TY]])
        ;; define structs for `C` constructors
        (struct C/internal (x ...) #:transparent) ...
        (define C (unsafe-assign-type C/internal : CTY)) ...
        ;; elimination form
        (define-typed-syntax (elim-Name v P Ccase ...) ≫
          [⊢ v ≫ v- ⇐ Name]
          [⊢ P ≫ P- ⇐ (→ Name Type)] ; prop / motive
          ;; each `Ccase` require 2 sets of args (even if set is empty):
          ;; 1) args of the constructor `x` ... 
          ;; 2) IHs for each `x` that has type `Name`
          [⊢ Ccase ≫ Ccase- ⇐ (Π ([x : CTY_in] ...)
                                 (→ (app P- recur-x) ...
                                    (app P- (app C x ...))))] ...
          -----------
          [⊢ (match-Name v- P- Ccase- ...) ⇒ (app P- v-)])
        ;; eval the elim redexes
        (define-syntax match-Name
          (syntax-parser
            #;[(_ . args)
             #:do[(printf "trying to match:\n~a\n" (stx->datum #'args))]
             #:when #f #'(void)]
            [(_ v P Ccase ...)
             #:with ty (typeof this-syntax)
             ; local expand since v might be unexpanded due to reflection
             (syntax-parse (local-expand #'v 'expression null)
               ; do eval if v is an actual `C` instance
               [((~literal #%plain-app) C-:id x ...)
                #:with (_ C+ . _) (local-expand #'(C 'x ...) 'expression null)
                #:when (free-identifier=? #'C- #'C+)
                (maybe-assign-type
                 #`(app/eval (app Ccase x ...)
;                             (match-Name x P Ccase ...) ...)
                             #,@(stx-map (lambda (y)
                                           (maybe-assign-type
                                            #`(match-Name #,y P Ccase ...)
                                           #'ty))
                                         #'(x ...)))
                 #'ty)]
               ...
               ; else generate a delayed term
               ;; must be #%app-, not #%plain-app, ow match will not dispatch properly
               [_ ;(maybe-assign-type
                   #'(#%app- match/delayed 'match-Name (void v P Ccase ...))
                   ;#'ty)
                  ])]))
        )]]
  ;; --------------------------------------------------------------------------
  ;; datatype type `TY` is a fn:
  ;; - params A ... and indices i ... must be in separate fn types
  ;; - but actual type formation constructor flattens to A ... i ...
  ;; - and constructors also flatten to A ... i ...
  ;; - all cases in elim-Name must consume i ... (but A ... is inferred)
  ;; --------------------------------------------------------------------------
  [(_ Name (~datum :) TY
      [C:id (~datum :) CTY] ...) ≫

   ;; params and indices specified with separate fn types, to distinguish them,
   ;; but are combined in other places,
   ;; eg (Name A ... i ...) or (CTY A ... i ...)
   [⊢ TY ≫ (~Π ([A : TYA] ...) ; params
               (~Π ([i : TYi] ...) ; indices
                   TY_out)) ⇐ Type]

   ; need to expand `CTY` but `Name` is still unbound so use tmp id
   ; - extract arity of each `C` ...
   ; - find recur args   
   #:with (CTY/tmp ...) (subst #'TmpTy #'Name #'(CTY ...))
   [⊢ CTY/tmp ≫ CTY/tmp- ⇐ Type] ...
   #:with (_ TmpTy+) (local-expand #'(TmpTy) 'expression null)
   ;; ;; TODO: replace TmpTy in origs of τ_in ... τ_out
   ;; TODO: how to un-subst TmpTy (which is now a constructor)?
   ;; - for now, dont use these τ_in/τ_out; just use for arity
   ;; - instead, re-expand in generated `elim` macro below
   ;;
   ;; - 1st Π is tycon params and indices, dont care for now
   ;; - 2nd Π is constructor args
   #:with ((~Π ([_ : _] ...) (~Π ([x : CTY_in/tmp] ...) CTY_out/tmp)) ...)
          #'(CTY/tmp- ...)
   ;; each (recur-x ...) is subset of (x ...) that are recur args,
   ;; ie, they are not fresh ids
   #:with ((recur-x ...) ...) (stx-map
                               (lambda (xs ts)
                                 (filter
                                  (lambda (y) y) ; filter out #f
                                  (stx-map
                                   (lambda (x t)
                                     (and
                                      (syntax-parse t
                                        [((~literal #%plain-app) tmp . _)
                                         (free-id=? #'tmp #'TmpTy+)]
                                        [_ #f])
                                      x)) ; returns x or #f
                                   xs ts)))
                               #'((x ...) ...)
                               #'((CTY_in/tmp ...) ...))

   ;; pre-generate other patvars; makes nested macros below easier to read
   #:with (A- ...) (generate-temporaries #'(A ...))
   #:with (i- ...) (generate-temporaries #'(i ...))
   ;; need to multiply A and i patvars, to match types of `C` ... constructors
   ;; must be fresh vars to avoid dup patvar errors
   #:with ((CA ...) ...) (stx-map (lambda _ (generate-temporaries #'(A ...))) #'(C ...))
   #:with ((CTYA ...) ...) (stx-map (lambda _ (generate-temporaries #'(A ...))) #'(C ...))
   #:with ((Ci ...) ...) (stx-map (lambda _ (generate-temporaries #'(i ...))) #'(C ...))
   #:with ((CTYi ...) ...) (stx-map (lambda _ (generate-temporaries #'(TYi ...))) #'(C ...))
   ; Ci*recur dups Ci for each recur, to get the ellipses to work out below
   #:with (((Ci*recur ...) ...) ...) (stx-map
                                      (lambda (cis recurs)
                                        (stx-map (lambda (r) cis) recurs))
                                      #'((Ci ...) ...)
                                      #'((recur-x ...) ...))
   ;; not inst'ed CTY_in
   #:with ((CTY_in/CA ...) ...) (stx-map generate-temporaries #'((CTY_in/tmp ...) ...))
   ;; inst'ed CTY_in (with A ...)
   #:with ((CTY_in ...) ...) (stx-map generate-temporaries #'((CTY_in/tmp ...) ...))
   #:with (CTY_out/CA ...) (generate-temporaries #'(C ...))
   #:with (CTY_out ...) (generate-temporaries #'(C ...))
   ; CTY_out_A matches the A and CTY_out_i matches the i in CTY_out,
   ; - ie CTY_out = (Name CTY_out_A ... CTY_out_i ...)
   ; - also, CTY_out_A refs (ie bound-id=) CA and CTY_out_i refs Ci
   #:with ((CTY_out_A ...) ...) (stx-map (lambda _ (generate-temporaries #'(A ...))) #'(C ...))
   #:with ((CTY_out_i ...) ...) (stx-map (lambda _ (generate-temporaries #'(i ...))) #'(C ...))
   ;; differently named `i`, to match type of P
   #:with (j ...) (generate-temporaries #'(i ...))
   ; dup (A ...) C times, again for ellipses matching
   #:with ((A*C ...) ...) (stx-map (lambda _ #'(A ...)) #'(C ...))
   #:with (C/internal ...) (generate-temporaries #'(C ...))
   #:with (Ccase ...) (generate-temporaries #'(C ...))
   #:with (Ccase- ...) (generate-temporaries #'(C ...))
   #:with Name- (mk-- #'Name)
   #:with Name-patexpand (mk-~ #'Name)
   #:with elim-Name (format-id #'Name "elim-~a" #'Name)
   #:with match-Name (format-id #'Name "match-~a" #'Name)
   --------
   [≻ (begin-
        ;; define the type
        (define-internal-type-constructor Name)
        (define-typed-syntax (Name A ... i ...) ≫
          [⊢ A ≫ A- ⇐ TYA] ...
          [⊢ i ≫ i- ⇐ TYi] ...
          ----------
          [⊢ (Name- A- ... i- ...) ⇒ TY_out])

        ;; define structs for constructors
        (struct C/internal (x ...) #:transparent) ...
        ;; TODO: this define should be a macro instead?
        (define C (unsafe-assign-type (lambda (A ... i ...) C/internal) : CTY)) ...

        ;; define eliminator-form
        (define-typed-syntax (elim-Name v P Ccase ...) ≫
          ;; re-extract CTY_in and CTY_out, since we didnt un-subst above
          #:with ((~Π ([CA : CTYA] ... ; ignore params, instead infer `A` ... from `v`
                       [Ci : CTYi] ...)
                      (~Π ([_ : CTY_in/CA] ...)
                          CTY_out/CA))
                  ...)
                 (stx-map (current-type-eval) #'(CTY ...))

          ;; target, infers A ...
          [⊢ v ≫ v- ⇒ (Name-patexpand A ... i ...)]

          ;; inst CTY_in/CA and CTY_out/CA with inferred A ...
          #:with ((CTY_in ... CTY_out) ...) (stx-map (lambda (ts cas) (substs #'(A ...) cas ts))
                                                     #'((CTY_in/CA ... CTY_out/CA) ...)
                                                     #'((CA ...) ...))
          ;; get the params and indices in CTY_out
          ;; - dont actually need CTY_out_A
          #:with ((Name-patexpand CTY_out_A ... CTY_out_i ...) ...) #'(CTY_out ...)

          ;; prop / motive
          [⊢ P ≫ P- ⇐ (Π ([j : TYi] ...) (→ (Name A ... j ...) Type))]

          ;; each Ccase consumes 3 nested sets of (possibly empty) args:
          ;; 1) Ci  - indices of the tycon
          ;; 2) x   - args of each constructor `C`
          ;; 3) IHs - for each recur-x ... (which are a subset of x ...)
          ;;
          ;; somewhat of a hack:
          ;; by reusing Ci and CTY_out_i both to match CTY/CTY_out above, and here,
          ;; we automatically unify Ci with the indices in CTY_out
          [⊢ Ccase ≫ Ccase- ⇐ (Π ([Ci : CTYi] ...) ; indices
                                 (Π ([x : CTY_in] ...) ; constructor args
                                    (→ (app (app P- Ci*recur ...) recur-x) ... ; IHs
                                       (app (app P- CTY_out_i ...)
                                            (app (app C A*C ... Ci ...) x ...)))))] ...
          -----------
          [⊢ (match-Name v- P- Ccase- ...) ⇒ (app (app P- i ...) v-)])

        ;; implements reduction of elimator redexes
        (define-syntax match-Name
          (syntax-parser
            #;[(_ . args)
             #:do[(printf "trying to match:\n~a\n" (stx->datum #'args))]
             #:when #f #'(void)]
            [(_ v P Ccase ...)
             #:with ty (typeof this-syntax)
             ;; must local expand because `v` may be unexpanded due to reflection
             (syntax-parse (local-expand #'v 'expression null)
               [((~literal #%plain-app) ((~literal #%plain-app) C-:id CA ... Ci ...) x ...)
                #:with (_ C+ . _) (local-expand #'(C 'CA ...) 'expression null)
                #:when (free-identifier=? #'C+ #'C-)
                ;; can use app instead of app/eval to properly propagate types
                ;; but doesnt quite for in all cases?
                (maybe-assign-type
                 #`(app/eval ;#,(assign-type
                                (app/eval (app Ccase Ci ...) x ...)
                                ;; TODO: is this right?
                              ;       #'(app P Ci ...))
;                             (match-Name recur-x P Ccase ...) ...)
                             #,@(stx-map (lambda (r)
                                           (maybe-assign-type
                                            #`(match-Name #,r P Ccase ...)
                                            #'ty))
                                         #'(recur-x ...)))
                 #'ty)] ...
               [_ ;(maybe-assign-type
                   ;; must be #%app-, not #%plain-app, ow match will not dispatch properly
                   #'(#%app- match/delayed 'match-Name (void v P Ccase ...))
                   ;#'ty)
                  ])]))
        )]])
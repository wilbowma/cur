#lang turnstile+/quicklang
(require turnstile+/eval turnstile+/typedefs turnstile+/more-utils)

;;;; The Calculus of Constructions.
;;;; ------------------------------------------------------------------------

(provide
 Type
 (for-syntax
  (rename-out [~Type* ~Type]))
 (rename-out [Type Prop]) ; TODO: define separate Prop
 Π (for-syntax ~Π)
 λ (for-syntax ~λ)
 (rename-out [app #%app])
 app/eval
 (for-syntax ~#%app)
 define define-for-export ann)

(begin-for-syntax (current-use-stop-list? #f))

;;; Type Definitions
;;; -----------------------------------------------------------

;; Universe hierarchy
;; ------------------------------------------------

; set (Type n) : (Type n+1)
; TODO: Remove Type as an alias for (Type 0)
; Type = (Type 0)
(define-internal-type/new Type- (Type n) #:lazy #:arg-pattern (((~literal quote) n)))

;; To support the Type = (Type 0) alias
(begin-for-syntax
  (define-syntax ~Type*
    (pattern-expander
     (syntax-parser
       [:id
        #'(~and b
                (~parse (~Type _)
                  ((current-type-eval) #'b)))]
       [(_ n)
        #'(~and b
                (~parse (~Type n)
                        ((current-type-eval) #'b)))]))))

(define-typed-syntax Type
  [:id ≫ --- [≻ (Type 0)]]
  [(_ n:exact-nonnegative-integer) ≫
   #:with n+1 (+ (syntax-e #'n) 1)
  -------------
  ;; TODO: Need a lazy attach type... ⇒/lazy ?
  [≻ #,(syntax-property
         (syntax/loc this-syntax (#%plain-app Type- 'n))
         ':
          (syntax/loc this-syntax (Type n+1)))]])

;; Π types
;; ------------------------------------------------

(define-internal-binding-type/new Π-- Π)
(define-simple-macro (Π- (x- : A-) B-) (Π-- A- (λ- (x-) B-)))

;; Given an domain universe level n and co-domain level m, what is the level of
;; the function type?
(define-for-syntax (unv-max n m)
  (if (zero? m) m (max n m)))

(define-typed-syntax Π
  ; Check
  [(_ (x:id (~datum :) A) B) ⇐ (~Type* n:nat) ≫
   [⊢ A ≫ A- ⇐ (Type n)]
   [[x ≫ x-- : A-] ⊢ B ≫ B- ⇐ (Type n)]
   ; TODO: Oh look a pattern. Should be built into [x >> x-] form, or something.
   ; TODO: Why do we need both 'tmp and 'display-as? Can't we use 'display-as as the boolean and the name
   #:with x-
   (transfer-prop 'display-as #'x (transfer-prop 'tmp #'x #'x--))
   ---------
   [⊢ (Π- (x- : A-) B-)]]

  ; impredicativity
  ; TODO: Having this as a separate rule is wayyy too slow.
  ; It causes considerable backtracking in syntax-parse, I suppose?
  ; Leaving this here for future debugging.
  #;[(_ (x:id (~datum :) A) B)  ≫
   [⊢ A ≫ A- ⇒ (~Type n:nat)]
   [[x ≫ x-- : A-] ⊢ B ≫ B- ⇒ (~Type 0)]
   #:with x-
   (transfer-prop 'display-as #'x (transfer-prop 'tmp #'x #'x--))
   ---------
   [⊢ (Π- (x- : A-) B-) ⇒ (Type 0)]]

  [(_ (x:id (~datum :) A) B)  ≫
   ; NB: Expect a type of arbitrary level, for better errors
   [⊢ A ≫ A- ⇒ (~or (~Type* n:nat) U₁)]
   [[x ≫ x-- : A-] ⊢ B ≫ B- ⇒ (~or (~Type* m:nat) U₂)]
   #:fail-unless (attribute n)
   (type-error #:src #'A- #:msg "expected (Type n) (for some n), given ~a" #'U₁)
   #:fail-unless (attribute m)
   (type-error #:src #'B- #:msg "expected (Type m) (for some m), given ~a" #'U₂)
   #:with x-
   (transfer-prop 'display-as #'x (transfer-prop 'tmp #'x #'x--))
   ---------
   [⊢ (Π- (x- : A-) B-) ⇒ (Type #,(unv-max (syntax-e #'n) (syntax-e #'m)))]])

;; Type check relation
;; NB: Must be defined after all types
;; ------------------------------------------------

(begin-for-syntax
  (current-typecheck-relation
   (lambda (t1 t2)
     ; Since universes are type checked lazily, if the type we're checking (t1)
     ; is a universe, force it,
     (define t1+
       (syntax-parse t1
         [((~literal Type) _) ((current-type-eval) t1)]
         [_ t1]))
     (or (type=? t1+ t2) ; equality
         (syntax-parse (list t1+ t2)
           [((~Type n) (~Type m)) (<= (stx-e #'n) (stx-e #'m))]
           [((~Π [x1 : τ_in1] τ_out1) (~Π [x2 : τ_in2] τ_out2))
            (and (type=? #'τ_in1 #'τ_in2)
                 (typecheck? (subst #'x2 #'x1 #'τ_out1) #'τ_out2))]
           ; NB: Overwrite, do not preserve, old relation.
           [_ #f])))))

;;; Term Definitions
;;; -----------------------------------------------------------

;; Function and application
;; ------------------------------------------------
(define-typed-syntax λ
  ; expected ty only
  [(_ y:id e) ⇐ (~Π [x:id : τ_in] τ_out) ≫
   [[x ≫ x- : τ_in] ⊢ #,(subst #'x #'y #'e) ≫ e- ⇐ τ_out]
   ---------
   [⊢ (λ- (x-) e-) ⇒ (Π [x : τ_in] τ_out)]]

  ; both expected ty and annotations
  [(_ [y:id (~datum :) τ_in*] e) ⇐ (~Π [x:id : τ_in] τ_out) ≫
   [⊢ τ_in* ≫ τ_in** ⇒ (~Type _)]
   #:when (typecheck? #'τ_in** #'τ_in)
   [[x ≫ x- : τ_in] ⊢ [#,(subst #'x #'y #'e) ≫ e- ⇐ τ_out]]
   -------
   [⊢ (λ- (x-) e-) ⇒ (Π [x : τ_in] τ_out)]]

  ; annotations only
  [(_ [x:id (~datum :) τ_in] e) ≫
   [[x ≫ x-- : τ_in] ⊢ [e ≫ e- ⇒ τ_out] [τ_in ≫ τ_in- ⇒ _]]
   #:with x-
   (transfer-prop 'display-as #'x (transfer-prop 'tmp #'x #'x--))
   -------
   [⊢ (λ- (x-) e-) ⇒ (Π [x- : τ_in-] τ_out)]])

(begin-for-syntax
  ; Pattern for Racket's #%plain-lambda
  (define-syntax ~λ-
    (pattern-expander
     (syntax-parser
       [(_ (x:id ...) e ...)
        #`(~or ((~literal #%plain-lambda) (x ...) e ...)
               ; TODO: Who adds #%expression?
               ((~literal #%expression) ((~literal #%plain-lambda) (x ...) e ...)))])))

  ; Pattern for Cur's λ
  (define-syntax ~λ
    (pattern-expander
     (syntax-parser
       [(_ (x:id (~datum :) A) e)
        #`(~and (~λ- (x) e) (~parse A (typeof #'x)))]))))

(define-typerule/red (app e_fn e_arg) ≫
  [⊢ e_fn ≫ e_fn- ⇒ (~Π [X : τ_in] τ_out)]
  [⊢ e_arg ≫ e_arg- ⇐ τ_in]
  #:with τ_out- (reflect (subst #'e_arg- #'X #'τ_out)) ; TODO: fix orig
  -----------------------------
  [⊢ (app/eval e_fn- e_arg-) ⇒ τ_out-]
  #:where app/eval
  [(#%plain-app (~λ- (x) e) arg) ~> #,(subst #'arg #'x #'e)])

(begin-for-syntax
  (define-syntax ~#%app
    (pattern-expander
     (syntax-parser
       [(_ e₁ e₂)
        #`((~literal #%plain-app) e₁ e₂)]))))

;;; Other Definitions
;;; -----------------------------------------------------------

(define-typed-syntax (ann e (~datum :) τ) ≫
  [⊢ e ≫ e- ⇐ τ]
  --------
  [⊢ e- ⇒ τ])

(define-typed-syntax (define x:id e) ≫
  ; NB: Exporting x may result in stxprop module problems.
  ; Use define-for-export for ids to be provided.
  [⊢ e ≫ e- ⇒ _]
  -----
  [≻ (define-syntax x (make-variable-like-transformer #'e-))])

(define-typed-syntax (define-for-export x:id e) ≫
  ; NB: Type check but dont use the expanded result or we run into
  ; stxprop module problems.
  [⊢ e ≫ _ ⇒ _]
  -----
  [≻ (define-syntax x (make-variable-like-transformer #'e))])

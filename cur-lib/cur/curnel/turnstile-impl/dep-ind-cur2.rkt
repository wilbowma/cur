#lang turnstile/lang
(require turnstile/eval turnstile/typedefs turnstile/more-utils)

; a basic dependently-typed calculus
; - with inductive datatypes

;; dep-ind-cur2 is dep-ind-cur cleaned up and using better abstractions

; Π  λ ≻ ⊢ ≫ → ∧ (bidir ⇒ ⇐) τ⊑ ⇑
; \Pi \lambda ?? \vdash \gg \rightarrow \land \Rightarrow \Leftarrow \tau\sqsubseteq \Uparrow

(provide Type (for-syntax ~Type) TypeTop (rename-out [Type Prop]) ; TODO: define separate Prop
         Π (for-syntax ~Π)
         (rename-out [λ/1 λ] [app #%app] [app/eval app/eval/1] [typed-define define])
         ann provide module* submod for-syntax begin-for-syntax)

(begin-for-syntax (current-use-stop-list? #f))

;; Universes -----------------------------------------------------------

;; ⊢ (Type n) : (Type n+1)

;; Pre-syntax
;; This is the fully expanded, run-time representation syntax.

;; TODO: This is a pattern I'd like to abstract: creating a pre-syntax, with its
;; pattern-expander, and its unexpander.
;; I almost feel like this ought to be derived from the define-typed-syntax
;; form, but maybe that would be too magical.
(struct Type- (n) #:transparent #:omit-define-syntaxes) ; runtime representation
(begin-for-syntax
  (define Type-id (expand/df #'Type-))

  (define-syntax ~Type
    (pattern-expander
     (syntax-parser
       [:id #'(~Type _)] ; TODO Remove Type alias from core.
       [(_ n)
        ; TODO: This is a pattern I'd like to abstract: pattern-expander for
        ; matching on a fully expanded struct constructor apply to its arguments.
        #'(~or
           ((~literal Type) n)   ; unexpanded
           ((~literal #%plain-app) ; expanded
            (~and C:id ; TODO: this free-id=? sometimes fails
                  (~fail #:unless (stx-datum-equal? #;free-identifier=? #'C Type-id)
                         (format "type mismatch, expected (Type ~a), given ~a"
                                 #'n
                                 (syntax->datum #'C))))
            ((~literal quote) n)))])))

  (define Type-unexpander
    (syntax-parser
      [(~Type 0) ; TODO Remove Type alias from core.
       #'Type]
      [(~Type i)
       #'(Type i)]))

  ; Unexpander and Resugarer
  (define Type- (type-info #f Type-unexpander Type-unexpander)))

;; Syntax
;; The unexpanded, surface, typed representation.

(define-typed-syntax Type
  [:id ≫ ; TODO Remove Type alias from core.
   ---
   [≻ (Type 0)]]
  [(_ n:exact-nonnegative-integer) ≫
   #:with n+1 (+ (syntax-e #'n) 1)
  -------------
  ;; TODO: This should really be:
  ;; [≻ (Type- 'n) ⇒ (Type n+1)]
  ;; But it can't be for inexplicable reasons?
  ;; I think this is because
  ;; - We need to ensure lazy expansion of the type (less infinite expansion)
  ;; - It's hard to preserve source location and resugaring info.
  [≻ #,(syntax-property
        (syntax-property
         (syntax/loc this-syntax
           (Type- 'n)) ':
         (syntax-property
          (syntax/loc this-syntax
            (Type n+1))
          'orig
          (list (syntax/loc this-syntax
                  (Type n+1)))))
        'orig
        (list (syntax/loc this-syntax
                (Type n))))]])

;; for convenience, Type that is a supertype of all (Type n)
;; TODO: get rid of this?
;; TODO WJB: Yes, get rid of this! It's a giant hack, and most uses are inconsistent.
(define-syntax TypeTop (make-variable-like-transformer #'(Type 99)))

;; Π types -----------------------------------------------------------

#|
  ⊢ A : (Type i)      x : A ⊢ B : (Type 0)
  ---------------------------
  ⊢ (Π (x : A) B) : (Type 0)
|#

#|
  ⊢ A : (Type i)      x : A ⊢ B : (Type j)
  ---------------------------
  ⊢ (Π (x : A) B) : (Type (max i j))
|#

;; Pre-syntax
;; This is the fully expanded, run-time representation syntax.

;; TODO: Pre-syntax pattern

(struct Π- (a f) #:transparent #:omit-define-syntaxes) ; runtime representation

(begin-for-syntax
  (define Π-id (expand/df #'Π-))
  (define-syntax ~Π
    (pattern-expander
     (syntax-parser
       [(_ (x:id (~datum :) A) B)
        #'(~or
           ((~literal #%plain-app) ; expanded
            (~and C:id ; TODO: this free-id=? sometimes fails
                  (~fail #:unless (stx-datum-equal? #;free-identifier=? #'C Π-id)
                         (format "type mismatch, expected Π, given ~a"
                                 (syntax->datum #'C))))
            A
            (#%plain-lambda (x) B)))])))

  ;; TODO: This is a pattern I'd like to abstract: easily defining syntax homomorphisms.
  (define Π- (type-info #f
                        (syntax-parser
                             [(~Π (x : A) B)
                              #`(Π (#,(resugar-type #'x) : #,(resugar-type #'A)) #,(resugar-type #'B))])
                        (syntax-parser
                          [(~Π (x : A) B)
                           #`(Π (#,(unexpand #'x) : #,(unexpand #'A)) #,(unexpand #'B))]))))
;; Syntax
;; The unexpanded, surface, typed representation.

(define-typed-syntax Π
  ; Impredicative rule
  [(_ (x:id (~datum :) τₐ) τᵣ) ≫
   [⊢ τₐ ≫ τₐ- ⇒ (~Type j:nat)]
   [[x ≫ x- : τₐ] ⊢ τᵣ ≫ τᵣ- ⇐ (Type 0)]
   ------------------------------
   [⊢ (Π- τₐ- (λ (x-) τᵣ-)) ⇒ (Type 0)]]

  ; Predicative rules
  ;; check/subtyping
  [(_ (x:id (~datum :) τₐ) τᵣ) ⇐ (~Type k:nat) ≫
   [⊢ τₐ ≫ τₐ- ⇒ (~Type j:nat)]
   [[x ≫ x- : τₐ] ⊢ τᵣ ≫ τᵣ- ⇒ (~Type i:nat)]
   #:when (>= (syntax->datum #'k) (max (syntax->datum #'i) (syntax->datum #'j)))
   ------------------------------
   [⊢ (Π- τₐ- (λ (x-) τᵣ-))]]

  ;; infer
  [(_ (x:id (~datum :) τₐ) τᵣ) ≫
   [⊢ τₐ ≫ τₐ- ⇒ (~Type j:nat)]
   [[x ≫ x- : τₐ] ⊢ τᵣ ≫ τᵣ- ⇒ (~Type i:nat)]
   #:with k (max (syntax->datum #'i) (syntax->datum #'j))
   ------------------------------
   [⊢ (Π- τₐ- (λ (x-) τᵣ-)) ⇒ (Type k)]]

  ;; NB: This is a pattern.... but I don't see how to abstract it.
  ;; Anyway, it's local and follows the structure of typing.
  ;; I'd like it to let me know if I missed an error case, but I suspect that
  ;; would require a typed macro language.

  ;; Error rules
  [(_ (x:id (~datum :) τₐ) τᵣ) ≫
   [⊢ τₐ ≫ τₐ- ⇒ (~Type j:nat)]
   [[x ≫ x- : τₐ] ⊢ τᵣ ≫ τᵣ- ⇒ (~Type i:nat)]
   -----------------
   [#:error (type-error #:src #'τₐ #:msg "Π: Universe inconsistency: A function's argument and return types must exist in a consistent universe, but ~s lives in universe \"(Type ~a)\", while ~s lives in universe \"(Type ~a)\"."
                        #'τₐ
                        #'j
                        #'τᵣ
                        #'i)]]

  [(_ (x:id (~datum :) τₐ) τᵣ) ≫
   [⊢ τₐ ≫ τₐ- ⇒ (~Type j:nat)]
   [[x ≫ x- : τₐ] ⊢ τᵣ ≫ τᵣ- ⇒ B]
   -----------------
   [#:error (type-error #:src #'τᵣ #:msg "Π: Universe inconsistency: A function's return types must be a type, i.e., have a type that is a universe (Type i), but ~s has type ~s which is not a universe." #'τᵣ #'B)]]

  [(_ (x:id (~datum :) τₐ) τᵣ) ≫
   [⊢ τₐ ≫ τₐ- ⇒ A]
   -----------------
   [#:error (type-error #:src #'τₐ #:msg "Π: A function's argument and return types must be types, i.e., have a type that is a universe (Type i), but ~s has type ~s which is not a universe." #'τₐ #'A)]]

  [(_ ...) ≫
   -----------------
   [#:error (raise-syntax-error 'Π "A Π type must be of the general form (Π (name : argument-type) result-type). For example, (Π (x : Nat) Nat)." this-syntax)]])

;; type check relation --------------------------------------------------------
;; - must come after type defs

(begin-for-syntax

  (define old-relation (current-typecheck-relation))
  (current-typecheck-relation
   (lambda (t1 t2)
     ;; (printf "t1 = ~a\n" (syntax->datum t1))
     ;; (printf "t2 = ~a\n" (syntax->datum t2))
     (define t1+
       (syntax-parse t1
         [(~Type _) ((current-type-eval) t1)]
         [_ t1]))
     (or (type=? t1+ t2) ; equality
         (syntax-parse (list t1+ t2) ; subtyping
           [((~Type n) (~Type m)) (or (<= (stx-e #'n) (stx-e #'m))
                                      ; TODO: Remove this, it's inconsistent
                                      (and (>= (stx-e #'n) 99) ; both are "TypeTop"
                                           (>= (stx-e #'m) 99)))]
           [((~Π [x1 : τ_in1] τ_out1) (~Π [x2 : τ_in2] τ_out2))
            (and (type=? #'τ_in1 #'τ_in2) ; equi-variant
                 (typecheck? (subst #'x2 #'x1 #'τ_out1) #'τ_out2))]
           [_ #;[(printf "failed to type check: ~a\n" (syntax->datum this-syntax))] #f])))))

;; lambda and #%app -----------------------------------------------------------

;; Pre-syntax for λ is Racket's lambda
;; TODO: Why do we not need ~λ?

;; Syntax

(define-typed-syntax λ/1
  ;; expected ty only
  [(_ y:id e) ⇐ (~Π [x:id : τ_in] τ_out) ≫
   [[x ≫ x- : τ_in] ⊢ #,(subst #'x #'y #'e) ≫ e- ⇐ τ_out]
   ---------
   [⊢ (λ- (x-) e-)]]
  ;; both expected ty and annotations
  [(_ [y:id (~datum :) τ_in*] e) ⇐ (~Π [x:id : τ_in] τ_out) ≫
   [⊢ τ_in* ≫ τ_in** ⇐ Type]
   #:when (typecheck? #'τ_in** #'τ_in)
   [[x ≫ x- : τ_in] ⊢ #,(subst #'x #'y #'e) ≫ e- ⇐ τ_out]
   -------
   [⊢ (λ- (x-) e-)]]
  ;; annotations only
  [(_ [x:id (~datum :) τ_in] e) ≫
   [[x ≫ x- : τ_in] ⊢ [e ≫ e- ⇒ τ_out] [τ_in ≫ τ_in- ⇒ _]]
   -------
   [⊢ (λ- (x-) e-) ⇒ (Π [#,(transfer-prop 'tmp #'x #'x-) : τ_in-] τ_out)]])

;; #%app -----------------------------------------------------------

;; Pre-syntax for #%app is app/eval
;; TODO: Why do we not need ~#%app?

(define-typerule/red (app e_fn e_arg) ≫
  [⊢ e_fn ≫ e_fn- ⇒ (~Π [X : τ_in] τ_out)]
  [⊢ e_arg ≫ e_arg- ⇐ τ_in]
  #:with τ_out- (reflect (subst #'e_arg- #'X #'τ_out)) ; TODO: fix orig
  -----------------------------
  [⊢ (app/eval e_fn- e_arg-) ⇒ τ_out- #;(app/eval (λ- (X) τ_out) e_arg-)]
  #:where app/eval
  [(#%plain-app
    (~or ((~literal #%plain-lambda) (x) e)
         ((~literal #%expression) ((~literal #%plain-lambda) (x) e))) ; TODO: who adds this?
    arg)
   ~> #,(subst #'arg #'x #'e)])

;; TODO: Why is this a core form?
(define-typed-syntax (ann e (~datum :) τ) ≫
  [⊢ e ≫ e- ⇐ τ]
  --------
  [⊢ e- ⇒ τ])

;; top-level define ------------------------------------------------------------------

;; TODO: Pre-syntax is ....????
;; Expected: Racket's define

;; TODO: All definitions are inlined at macro expansion time??
(define-syntax typed-define
  (syntax-parser
    [(_ alias:id τ)
     ; expand τ just to check,
     ; but throw away, otherwise we run into stxprop module problems
     #:with _ ((current-type-eval) #'τ)
     #'(define-syntax alias (make-variable-like-transformer #'τ))]
    [(_ (f [x:id : τ]) e)
     #'(typed-define f (λ/1 [x : τ] body))]))

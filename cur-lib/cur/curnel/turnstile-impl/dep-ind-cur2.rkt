#lang turnstile/lang
(require turnstile/eval turnstile/typedefs turnstile/more-utils)

; a basic dependently-typed calculus
; - with inductive datatypes

;; dep-ind-cur2 is dep-ind-cur cleaned up and using better abstractions

; Π  λ ≻ ⊢ ≫ → ∧ (bidir ⇒ ⇐) τ⊑ ⇑

(provide Type (for-syntax ~Type) TypeTop
         Π (for-syntax ~Π ~Π/1)
         (rename-out [λ/1 λ] [app #%app] [app/eval app/eval/1])
         ann define provide module* submod for-syntax begin-for-syntax)

(begin-for-syntax (current-use-stop-list? #f))

;; type definitions -----------------------------------------------------------

;; set (Type n) : (Type n+1)
;; Type = (Type 0)
(struct Type- (n) #:transparent) ; runtime representation
(begin-for-syntax
  (define Type-id (expand/df #'Type-))
  (define-syntax ~Type
    (pattern-expander
     (syntax-parser
       [:id #'(~Type _)]
       [(_ n)
        #'(~or
           ((~literal Type) n)   ; unexpanded
           ((~literal #%plain-app) ; expanded
            (~and C:id ; TODO: this free-id=? sometimes fails
                  (~fail #:unless (stx-datum-equal? #;free-identifier=? #'C Type-id)
                              (format "type mismatch, expected Type, given ~a"
                                      (syntax->datum #'C))))
            ((~literal quote) n)))]
       ))))

(define-typed-syntax Type
  [:id ≫ --- [≻ (Type 0)]]
  [(_ n:exact-nonnegative-integer) ≫
   #:with n+1 (+ (syntax-e #'n) 1)
  -------------
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
(define-syntax TypeTop (make-variable-like-transformer #'(Type 99)))

;; old Π/c now Π, old Π now Π/1
(define-type Π #:with-binders ([X : TypeTop] #:telescope) : TypeTop -> Type)

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
         [((~literal Type) _) ((current-type-eval) t1)]
         [_ t1]))
     (or (type=? t1+ t2) ; equality
         (syntax-parse (list t1+ t2)
           [((~Type n) (~Type m)) (<= (stx-e #'n) (stx-e #'m))]
           [((~Π/1 [x1 : τ_in1] τ_out1) (~Π/1 [x2 : τ_in2] τ_out2))
            (and (type=? #'τ_in1 #'τ_in2)
                 (typecheck? (subst #'x2 #'x1 #'τ_out1) #'τ_out2))]
           [_ #f])))))

;; lambda and #%app -----------------------------------------------------------
(define-typed-syntax λ/1
  ;; expected ty only
  [(_ y:id e) ⇐ (~Π/1 [x:id : τ_in] τ_out) ≫
   [[x ≫ x- : τ_in] ⊢ #,(subst #'x #'y #'e) ≫ e- ⇐ τ_out]
   ---------
   [⊢ (λ- (x-) e-)]]
  ;; both expected ty and annotations
  [(_ [y:id (~datum :) τ_in*] e) ⇐ (~Π/1 [x:id : τ_in] τ_out) ≫
   [⊢ τ_in* ≫ τ_in** ⇐ Type]
   #:when (typecheck? #'τ_in** #'τ_in)
   [[x ≫ x- : τ_in] ⊢ #,(subst #'x #'y #'e) ≫ e- ⇐ τ_out]
   -------
   [⊢ (λ- (x-) e-)]]
  ;; annotations only
  [(_ [x:id (~datum :) τ_in] e) ≫
   [[x ≫ x- : τ_in] ⊢ [e ≫ e- ⇒ τ_out] [τ_in ≫ τ_in- ⇒ _]]
   -------
   [⊢ (λ- (x-) e-) ⇒ (Π/1 [x- : τ_in-] τ_out)]])

(define-typerule/red (app e_fn e_arg) ≫
  [⊢ e_fn ≫ e_fn- ⇒ (~Π/1 [X : τ_in] τ_out)]
  [⊢ e_arg ≫ e_arg- ⇐ τ_in]
  #:with τ_out- (reflect (subst #'e_arg- #'X #'τ_out))
  -----------------------------
  [⊢ (app/eval e_fn- e_arg-) ⇒ τ_out- #;(app/eval (λ- (X) τ_out) e_arg-)]
  #:where app/eval
  [(#%plain-app
    (~or ((~literal #%plain-lambda) (x) e)
         ((~literal #%expression) ((~literal #%plain-lambda) (x) e))) ; TODO: who adds this?
    arg)
   ~> #,(subst #'arg #'x #'e)])

(define-typed-syntax (ann e (~datum :) τ) ≫
  [⊢ e ≫ e- ⇐ τ]
  --------
  [⊢ e- ⇒ τ])

;; TODO: should this be a stx parameter?
(define-syntax recur
  (λ (stx) (raise-syntax-error 'recur "not allowed to recur" stx)))
(provide recur)
;; top-level ------------------------------------------------------------------
(define-syntax define
  (syntax-parser
    [(_ alias:id τ) #'(define-syntax- alias (make-variable-like-transformer #'τ))]
    [(_ (f [x:id : τ]) e)
     #:with body (subst #'recur #'f #'e)
     #'(define f (λ/1 [x : τ] body))]))

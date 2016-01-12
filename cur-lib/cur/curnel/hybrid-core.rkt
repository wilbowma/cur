#lang racket/base

;; A mostly Redex core, with parts written in Racket for performance reasons

(require
  racket/dict
  racket/function
  racket/list
  redex/reduction-semantics)

(provide
  (all-defined-out))

(set-cache-size! 10000)

(define-language base
  (dict ::= any))
;; TODO: More abstractions for Redex dictionaries.

(define make-dict make-immutable-hash)

#| ttL is the core language of Cur. Very similar to TT (Idirs core) and Luo's UTT. Surface
 | langauge should provide short-hand, such as -> for non-dependent function types, and type
 | inference.
 |#
(define-extended-language ttL base
  (i j k  ::= natural)
  (U ::= (Unv i))
  (t e ::= U (λ (x : t) e) x (Π (x : t) t) (e e) (elim D U))
  (Δ   ::= dict)
  (D x c ::= variable-not-otherwise-mentioned)
  #:binding-forms
  (λ (x : t) e #:refers-to x)
  (Π (x : t_0) t_1 #:refers-to x))

(define x? (redex-match? ttL x))
(define t? (redex-match? ttL t))
(define e? (redex-match? ttL e))
(define U? (redex-match? ttL U))

;; TODO: Constracts
;; An inductive-decl contains the type of the type being declared,
;; a t?, and a dictionary of constructor names (x?) mapped to their
;; types (t?), the original syntax/order of the constructor
;; declaration ((x : t) ...), and the list of constructors in the
;; original order (x ...)
(define-struct inductive-decl (type constr-dict constr-decl constr-ls) #:prefab)

;; A Δ is a dict mapping names x? to inductive-decl?
(define Δ? dict?)
(define make-empty-Δ make-dict)
(define empty-Δ? dict-empty?)

;;; ------------------------------------------------------------------------
;;; Universe typing

(define-judgment-form ttL
  #:mode (unv-type I O)
  #:contract (unv-type U U)

  [(where i_1 ,(add1 (term i_0)))
   -----------------
   (unv-type (Unv i_0) (Unv i_1))])

;; Universe predicativity rules. Impredicative in (Unv 0)
(define-judgment-form ttL
  #:mode (unv-pred I I O)
  #:contract (unv-pred U U U)

  [----------------
   (unv-pred (Unv i) (Unv 0) (Unv 0))]

  [(where i_3 ,(max (term i_1) (term i_2)))
   ----------------
   (unv-pred (Unv i_1) (Unv i_2) (Unv i_3))])

(define-metafunction ttL
  α-equivalent?  : t t -> #t or #f
  [(α-equivalent? t_0 t_1)
   ,(alpha-equivalent? ttL (term t_0) (term t_1))])

;; Replace x by t_1 in t_0
(define-metafunction ttL
  subst : t x t -> t
  [(subst t_0 x t_1)
   (substitute t_0 x t_1)])

(define-metafunction ttL
  subst-all : t (x ...) (e ...) -> t
  [(subst-all t () ()) t]
  [(subst-all t (x_0 x ...) (e_0 e ...))
   (subst-all (subst t x_0 e_0) (x ...) (e ...))])

;;; ------------------------------------------------------------------------
;;; Primitive Operations on signatures Δ (those operations that do not require contexts)

;; TODO: Maybe shouldn't fall back, but maintains redex-core interface.
;; Get the type of x as declared in Δ, as either a constructor or an inductive type
(define-metafunction ttL
  Δ-ref-type : Δ x -> t or #f
  [(Δ-ref-type Δ x)
   ,(cond
      [(dict-ref (term Δ) (term x) (thunk #f))
       => inductive-decl-type]
      [else (term (Δ-ref-constructor-type Δ foo x))])])

;; Get the type of a constructor x in the inductive declaration Δ
;; TODO: Doesn't need x_D anymore
(define-metafunction ttL
  Δ-ref-constructor-type : Δ x x -> t or #f
  [(Δ-ref-constructor-type Δ x_D x)
   ,(cond
     [(for/or ([(D idecl) (in-dict (term Δ))])
       (let ([constr-dict (inductive-decl-constr-dict idecl)])
         (and (dict-has-key? constr-dict (term x)) constr-dict)))
      =>
      (curryr dict-ref (term x))]
     [else #f])])

;; Add an inductive declaration to Δ
(define-metafunction ttL
  Δ-set : Δ x t ((x : t) ...) -> Δ
  [(Δ-set Δ x t (name decl ((c : t_c) ...)))
   ,(dict-set
     (term Δ)
     (term x)
     (inductive-decl
      (term t)
      (for/fold ([d (make-dict)])
                ([constr-decl (term decl)])
        (dict-set d (first constr-decl) (third constr-decl)))
      (term decl)
      (term (c ...))))])

;; Merge two inductive declarations
(define-metafunction ttL
  Δ-union : Δ Δ -> Δ
  [(Δ-union Δ_1 Δ_2)
   ,(for/fold ([d (term Δ_1)])
              ([(k v) (in-dict (term Δ_2))])
      (dict-set d k v))])

(define-metafunction ttL
  Δ-set* : Δ (x t ((x : t) ...)) ... -> Δ
  [(Δ-set* Δ) Δ]
  [(Δ-set* Δ (D t_D ((c : t_c) ...)) any_r ...)
   (Δ-set* (Δ-set Δ D t_D ((c : t_c) ...)) any_r ...)])

;; Returns the inductively defined type that x constructs
(define-metafunction ttL
  Δ-key-by-constructor : Δ x -> x or #f
  [(Δ-key-by-constructor Δ x_c)
   ,(for/or ([(k v) (in-dict (term Δ))])
      (and (dict-has-key? (inductive-decl-constr-dict v) (term x_c)) k))])

;; Returns the constructor map for the inductively defined type x_D in the signature Δ
(define-metafunction ttL
  Δ-ref-constructor-map : Δ x -> ((x : t) ...) or #f
  [(Δ-ref-constructor-map Δ x_D)
   ,(cond
      [(dict-ref (term Δ) (term x_D) (thunk #f)) =>
       inductive-decl-constr-decl]
      [else #f])])

;; Get the list of constructors for the inducitvely defined type x_D
(define-metafunction ttL
  Δ-ref-constructors : Δ x -> (x ...) or #f
  [(Δ-ref-constructors Δ x_D)
   ,(inductive-decl-constr-ls (dict-ref (term Δ) (term x_D)))])

;; NB: Depends on clause order
(define-metafunction ttL
  sequence-index-of : any (any ...) -> natural
  [(sequence-index-of any_0 (any_0 any ...))
   0]
  [(sequence-index-of any_0 (any_1 any ...))
   ,(add1 (term (sequence-index-of any_0 (any ...))))])

;; Get the index of the constructor x_ci in the list of constructors for x_D
(define-metafunction ttL
  Δ-constructor-index : Δ x x -> natural
  [(Δ-constructor-index Δ x_D x_ci)
   (sequence-index-of x_ci (Δ-ref-constructors Δ x_D))])

;;; ------------------------------------------------------------------------
;;; Operations that involve contexts.

(define-extended-language tt-ctxtL ttL
  ;; Telescope.
  ;; NB: There is a bijection between this an a vector of maps from x to t
  (Ξ Φ ::= hole (Π (x : t) Ξ))
  ;; Apply context
  ;; NB: There is a bijection between this an a vector expressions
  (Θ   ::= hole (Θ e)))

(define Ξ? (redex-match? tt-ctxtL Ξ))
(define Φ? (redex-match? tt-ctxtL Φ))
(define Θ? (redex-match? tt-ctxtL Θ))

;; TODO: Might be worth it to actually maintain the above bijections, for performance reasons.

;; Return the parameters of x_D as a telescope Ξ
(define-metafunction tt-ctxtL
  Δ-ref-parameter-Ξ : Δ x -> Ξ
  [(Δ-ref-parameter-Ξ Δ x_D)
   Ξ
   (where (in-hole Ξ U) (Δ-ref-type Δ x_D))])

;; Applies the term t to the telescope Ξ.
;; TODO: Test
#| TODO:
 | This essentially eta-expands t at the type-level. Why is this necessary? Shouldn't it be true
 | that (equivalent t (Ξ-apply Ξ t))?
 | Maybe not. t is a lambda whose type is equivalent to (Ξ-apply Ξ t)? Yes.
 |#
(define-metafunction tt-ctxtL
  Ξ-apply : Ξ t -> t
  [(Ξ-apply hole t) t]
  [(Ξ-apply (Π (x : t) Ξ) t_0) (Ξ-apply Ξ (t_0 x))])

;; Compose multiple telescopes into a single telescope:
(define-metafunction tt-ctxtL
  Ξ-compose : Ξ Ξ ... -> Ξ
  [(Ξ-compose Ξ) Ξ]
  [(Ξ-compose Ξ_0 Ξ_1 Ξ_rest ...)
   (Ξ-compose (in-hole Ξ_0 Ξ_1) Ξ_rest ...)])

;; Compute the number of arguments in a Ξ
(define-metafunction tt-ctxtL
  Ξ-length : Ξ -> natural
  [(Ξ-length hole) 0]
  [(Ξ-length (Π (x : t) Ξ)) ,(add1 (term (Ξ-length Ξ)))])

;; Compute the number of applications in a Θ
(define-metafunction tt-ctxtL
  Θ-length : Θ -> natural
  [(Θ-length hole) 0]
  [(Θ-length (Θ e)) ,(add1 (term (Θ-length Θ)))])

;; Reference an expression in Θ by index; index 0 corresponds to the the expression applied to a hole.
(define-metafunction tt-ctxtL
  Θ-ref : Θ natural -> e or #f
  [(Θ-ref hole natural) #f]
  [(Θ-ref (in-hole Θ (hole e)) 0) e]
  [(Θ-ref (in-hole Θ (hole e)) natural) (Θ-ref Θ ,(sub1 (term natural)))])

;;; ------------------------------------------------------------------------
;;; Computing the types of eliminators

;; Returns the telescope of the arguments for the constructor x_ci of the inductively defined type x_D
(define-metafunction tt-ctxtL
  Δ-constructor-telescope : Δ x x -> Ξ
  [(Δ-constructor-telescope Δ x_D x_ci)
   Ξ
   (where (in-hole Ξ (in-hole Θ x_D))
     (Δ-ref-constructor-type Δ x_D x_ci))])

;; Returns the parameter arguments as an apply context of the constructor x_ci of the inductively
;; defined type x_D
(define-metafunction tt-ctxtL
  Δ-constructor-parameters : Δ x x -> Θ
  [(Δ-constructor-parameters Δ x_D x_ci)
   Θ
   (where (in-hole Ξ (in-hole Θ x_D))
     (Δ-ref-constructor-type Δ x_D x_ci))])

;; Inner loop for Δ-constructor-noninductive-telescope
(define-metafunction tt-ctxtL
  noninductive-loop : x Φ -> Φ
  [(noninductive-loop x_D hole) hole]
  [(noninductive-loop x_D (Π (x : (in-hole Φ (in-hole Θ x_D))) Φ_1))
   (noninductive-loop x_D Φ_1)]
  [(noninductive-loop x_D (Π (x : t) Φ_1))
   (Π (x : t) (noninductive-loop x_D Φ_1))])

;; Returns the noninductive arguments to the constructor x_ci of the inductively defined type x_D
(define-metafunction tt-ctxtL
  Δ-constructor-noninductive-telescope : Δ x x -> Ξ
  [(Δ-constructor-noninductive-telescope Δ x_D x_ci)
   (noninductive-loop x_D (Δ-constructor-telescope Δ x_D x_ci))])

;; Inner loop for Δ-constructor-inductive-telescope
;; NB: Depends on clause order
(define-metafunction tt-ctxtL
  inductive-loop : x Φ -> Φ
  [(inductive-loop x_D hole) hole]
  [(inductive-loop x_D (Π (x : (in-hole Φ (in-hole Θ x_D))) Φ_1))
   (Π (x : (in-hole Φ (in-hole Θ x_D))) (inductive-loop x_D Φ_1))]
  [(inductive-loop x_D (Π (x : t) Φ_1))
   (inductive-loop x_D Φ_1)])

;; Returns the inductive arguments to the constructor x_ci of the inducitvely defined type x_D
(define-metafunction tt-ctxtL
  Δ-constructor-inductive-telescope : Δ x x -> Ξ
  [(Δ-constructor-inductive-telescope Δ x_D x_ci)
   (inductive-loop x_D (Δ-constructor-telescope Δ x_D x_ci))])

;; Returns the inductive hypotheses required for eliminating the inductively defined type x_D with
;; motive t_P, where the telescope Φ are the inductive arguments to a constructor for x_D
(define-metafunction tt-ctxtL
  hypotheses-loop : x t Φ -> Φ
  [(hypotheses-loop x_D t_P hole) hole]
  [(hypotheses-loop x_D t_P (name any_0 (Π (x : (in-hole Φ (in-hole Θ x_D))) Φ_1)))
   ;; TODO: Instead of this nonsense, it might be simpler to pass in the type of t_P and use that
   ;; as/to compute the type of the hypothesis.
   (Π (x_h : (in-hole Φ ((in-hole Θ t_P) (Ξ-apply Φ x))))
      (hypotheses-loop x_D t_P Φ_1))
   (where x_h ,(variable-not-in (term (x_D t_P any_0)) 'x-ih))])

;; Returns the inductive hypotheses required for the elimination method of constructor x_ci for
;; inductive type x_D, when eliminating with motive t_P.
(define-metafunction tt-ctxtL
  Δ-constructor-inductive-hypotheses : Δ x x t -> Ξ
  [(Δ-constructor-inductive-hypotheses Δ x_D x_ci t_P)
   (hypotheses-loop x_D t_P (Δ-constructor-inductive-telescope Δ x_D x_ci))])

(define-metafunction tt-ctxtL
  Δ-constructor-method-telescope : Δ x x t -> Ξ
  [(Δ-constructor-method-telescope Δ x_D x_ci t_P)
   (Π (x_mi : (in-hole Ξ_a (in-hole Ξ_h ((in-hole Θ_p t_P) (Ξ-apply Ξ_a x_ci)))))
      hole)
   (where Θ_p (Δ-constructor-parameters Δ x_D x_ci))
   (where Ξ_a (Δ-constructor-telescope Δ x_D x_ci))
   (where Ξ_h (Δ-constructor-inductive-hypotheses Δ x_D x_ci t_P))
   (where x_mi ,(variable-not-in (term (t_P Δ)) 'x-mi))])

;; fold Ξ-compose over map Δ-constructor-method-telescope over the list of constructors
(define-metafunction tt-ctxtL
  method-loop : Δ x t (x ...) -> Ξ
  [(method-loop Δ x_D t_P ()) hole]
  [(method-loop Δ x_D t_P (x_0 x_rest ...))
   (Ξ-compose (Δ-constructor-method-telescope Δ x_D x_0 t_P) (method-loop Δ x_D t_P (x_rest ...)))])

;; Returns the telescope of all methods required to eliminate the type x_D with motive t_P
(define-metafunction tt-ctxtL
  Δ-methods-telescope : Δ x t -> Ξ
  [(Δ-methods-telescope Δ x_D t_P)
   (method-loop Δ x_D t_P (Δ-ref-constructors Δ x_D))])

;; Computes the type of the eliminator for the inductively defined type x_D with a motive whose result
;; is in universe U.
;;
;; The type of (elim x_D U) is something like:
;;  (∀ (P : (∀ a -> ... -> (D a ...) -> U))
;;     (method_ci ...) -> ... ->
;;     (a -> ... -> (D a ...) ->
;;       (P a ... (D a ...))))
;;
;; x_D   is an inductively defined type
;; U     is the sort the motive
;; x_P   is the name of the motive
;; Ξ_P*D is the telescope of the parameters of x_D and
;;       the witness of type x_D (applied to the parameters)
;; Ξ_m   is the telescope of the methods for x_D
(define-metafunction tt-ctxtL
  Δ-elim-type : Δ x U -> t
  [(Δ-elim-type Δ x_D U)
   (Π (x_P : (in-hole Ξ_P*D U))
      ;; The methods Ξ_m for each constructor of type x_D
      (in-hole Ξ_m
        ;; And finally, the parameters and discriminant
        (in-hole Ξ_P*D
          ;; The result is (P a ... (x_D a ...)), i.e., the motive
          ;; applied to the paramters and discriminant
          (Ξ-apply Ξ_P*D x_P))))
   ;; Get the parameters of x_D
   (where Ξ (Δ-ref-parameter-Ξ Δ x_D))
   ;; A fresh name to bind the discriminant
   (where x ,(variable-not-in (term (Δ Γ x_D Ξ)) 'x-D))
   ;; The telescope (∀ a -> ... -> (D a ...) hole), i.e.,
   ;; of the parameters and the inductive type applied to the
   ;; parameters
   (where Ξ_P*D (in-hole Ξ (Π (x : (Ξ-apply Ξ x_D)) hole)))
   ;; A fresh name for the motive
   (where x_P ,(variable-not-in (term (Δ Γ x_D Ξ Ξ_P*D x)) 'x-P))
   ;; The types of the methods for this inductive.
   (where Ξ_m (Δ-methods-telescope Δ x_D x_P))])

;; TODO: This might belong in the next section, since it's related to evaluation
;; Generate recursive applications of the eliminator for each inductive argument of type x_D.
;; In more detaill, given motive t_P, parameters Θ_p, methods Θ_m, and arguments Θ_i to constructor
;; x_ci for x_D, for each inductively smaller term t_i of type (in-hole Θ_p x_D) inside Θ_i,
;; generate: (elim x_D U t_P  Θ_m ... Θ_p ... t_i)
(define-metafunction tt-ctxtL
  Δ-inductive-elim : Δ x U t Θ Θ Θ -> Θ
  [(Δ-inductive-elim Δ x_D U t_P Θ_p Θ_m (in-hole Θ_i (hole (name t_i (in-hole Θ_r x_ci)))))
   ((Δ-inductive-elim Δ x_D U t_P Θ_p Θ_m Θ_i)
    (in-hole ((in-hole Θ_p Θ_m) t_i) ((elim x_D U) t_P)))
   (side-condition (memq (term x_ci) (term (Δ-ref-constructors Δ x_D))))]
  [(Δ-inductive-elim Δ x_D U t_P Θ_p Θ_m Θ_nr) hole])

;;; ------------------------------------------------------------------------
;;; Dynamic semantics
;;; The majority of this section is dedicated to evaluation of (elim x U), the eliminator for the
;;; inductively defined type x with a motive whose result is in universe U

(define-extended-language tt-redL tt-ctxtL
  ;; NB: (in-hole Θv (elim x U)) is only a value when it's a partially applied elim. However,
  ;; determining whether or not it is partially applied cannot be done with the grammar alone.
  (v   ::= x U (Π (x : t) t) (λ (x : t) t) (elim x U) (in-hole Θv x) (in-hole Θv (elim x U)))
  (Θv  ::= hole (Θv v))
  ;; call-by-value, plus reduce under Π (helps with typing checking)
  (E   ::= hole (E e) (v E) (Π (x : v) E) (Π (x : E) e)))

(define Θv? (redex-match? tt-redL Θv))
(define E? (redex-match? tt-redL E))
(define v? (redex-match? tt-redL v))

(define current-Δ (make-parameter (make-empty-Δ)))
(define tt-->
  (reduction-relation tt-redL
    (--> (in-hole E ((λ (x : t_0) t_1) t_2))
         (in-hole E (subst t_1 x t_2))
         -->β)
    (--> (in-hole E (in-hole Θv ((elim x_D U) v_P)))
         (in-hole E (in-hole Θ_r (in-hole Θv_i v_mi)))
         #|
          | The elim form must appear applied like so:
          | (elim x_D U v_P m_0 ... m_i m_j ... m_n p ... (c_i a ...))
          |
          | Where:
          |   x_D       is the inductive being eliminated
          |   U         is the universe of the result of the motive
          |   v_P       is the motive
          |   m_{0..n}  are the methods
          |   p ...     are the parameters of x_D
          |   c_i       is a constructor of x_d
          |   a ...     are the arguments to c_i
          | Unfortunately, Θ contexts turn all this inside out:
          | TODO: Write better abstractions for this notation
          |#
         (where Δ ,(current-Δ))
         ;; Split Θv into its components: the paramters Θv_P for x_D, the methods Θv_m for x_D, and
         ;; the discriminant: the constructor x_ci applied to its argument Θv_i
         (where (in-hole (Θv_p (in-hole Θv_i x_ci)) Θv_m) Θv)
         ;; Check that Θ_p actually matches the parameters of x_D, to ensure it doesn't capture other
         ;; arguments.
         (side-condition (equal? (term (Θ-length Θv_p)) (term (Ξ-length (Δ-ref-parameter-Ξ Δ x_D)))))
         ;; Ensure x_ci is actually a constructor for x_D
         (where (x_c* ...) (Δ-ref-constructors Δ x_D))
         (side-condition (memq (term x_ci) (term (x_c* ...))))
         ;; There should be a number of methods equal to the number of constructors; to ensure E
         ;; doesn't capture methods and Θv_m doesn't capture other arguments
         (side-condition (equal? (length (term (x_c* ...)))  (term (Θ-length Θv_m))))
         ;; Find the method for constructor x_ci, relying on the order of the arguments.
         (where v_mi (Θ-ref Θv_m (Δ-constructor-index Δ x_D x_ci)))
         ;; Generate the inductive recursion
         (where Θ_r (Δ-inductive-elim Δ x_D U v_P Θv_p Θv_m Θv_i))
         -->elim)))

(define reduce-memoize (make-hash))
(define-metafunction tt-redL
  step : Δ e -> e
  [(step Δ e)
   e_r
   (where e_r ,(dict-ref reduce-memoize (term e)
                         (thunk
                          (parameterize ([current-Δ (term Δ)])
                            (let ([x (car (apply-reduction-relation tt--> (term e)))])
                              (dict-set! reduce-memoize (term e_r) x)
                              x)))))])

(define-metafunction tt-redL
  reduce : Δ e -> e
  [(reduce Δ e)
   e_r
   (where e_r ,(dict-ref reduce-memoize (term e)
                         (thunk
                          (parameterize ([current-Δ (term Δ)])
                            (let ([x (car (apply-reduction-relation* tt--> (term e) #:cache-all? #t))])
                              (dict-set! reduce-memoize (term e_r) x)
                              x)))))])

(define-judgment-form tt-redL
  #:mode (equivalent I I I)
  #:contract (equivalent Δ t t)

  [(where t_2 (reduce Δ t_0))
   (where t_3 (reduce Δ t_1))
   (side-condition (α-equivalent? t_2 t_3))
   ----------------- "≡-αβ"
   (equivalent Δ t_0 t_1)])

;;; ------------------------------------------------------------------------
;;; Type checking and synthesis

(define-extended-language tt-typingL tt-redL
  ;; NB: There may be a bijection between Γ and Ξ. That's interesting.
  ;; NB: Also a bijection between Γ and a list of maps from x to t.
  (Γ   ::= ∅ (Γ x : t)))
(define Γ? (redex-match? tt-typingL Γ))

(define-metafunction tt-typingL
  Γ-union : Γ Γ -> Γ
  [(Γ-union Γ ∅) Γ]
  [(Γ-union Γ_2 (Γ_1 x : t))
   ((Γ-union Γ_2 Γ_1) x : t)])

(define-metafunction tt-typingL
  Γ-set : Γ x t -> Γ
  [(Γ-set Γ x t) (Γ x : t)])

;; NB: Depends on clause order
(define-metafunction tt-typingL
  Γ-ref : Γ x -> t or #f
  [(Γ-ref ∅ x) #f]
  [(Γ-ref (Γ x : t) x) t]
  [(Γ-ref (Γ x_0 : t_0) x_1) (Γ-ref Γ x_1)])

;; NB: Depends on clause order
(define-metafunction tt-typingL
  Γ-remove : Γ x -> Γ
  [(Γ-remove ∅ x) ∅]
  [(Γ-remove (Γ x : t) x) Γ]
  [(Γ-remove (Γ x_0 : t_0) x_1) (Γ-remove Γ x_1)])

(define-metafunction tt-typingL
  nonpositive : x t -> #t or #f
  [(nonpositive x (in-hole Θ x))
   #t]
  [(nonpositive x (Π (x_0 : (in-hole Θ x)) t))
   #f]
  [(nonpositive x (Π (x_0 : t_0) t))
   ,(and (term (positive x t_0)) (term (nonpositive x t)))]
  [(nonpositive x t) #t])

(define-metafunction tt-typingL
  positive : x t -> #t or #f
  [(positive x (in-hole Θ x))
   #f]
  [(positive x (Π (x_0 : (in-hole Θ x)) t))
   (positive x t)]
  [(positive x (Π (x_0 : t_0) t))
   ,(and (term (nonpositive x t_0)) (term (positive x t)))]
  [(positive x t) #t])

(define-metafunction tt-typingL
  positive* : x (t ...) -> #t or #f
  [(positive* x_D ()) #t]
  [(positive* x_D (t_c t_rest ...))
   ;; Replace the result of the constructor with (Unv 0), to avoid the result being considered a
   ;; nonpositive position.
   ,(and (term (positive x_D (in-hole Ξ (Unv 0)))) (term (positive* x_D (t_rest ...))))
   (where (in-hole Ξ (in-hole Θ x_D)) t_c)])

;; Holds when the signature Δ and typing context Γ are well-formed.
(define-judgment-form tt-typingL
  #:mode (wf I I)
  #:contract (wf Δ Γ)

  [(side-condition ,(empty-Δ? (term Δ)))
   ----------------- "WF-Empty"
   (wf Δ ∅)]

  [(type-infer Δ Γ t t_0)
   (wf Δ Γ)
   ----------------- "WF-Var"
   (wf Δ (Γ x : t))]

  [(side-condition ,(not (empty-Δ? (term Δ_1))))
   ;; TODO: Depends on order, but "first" here is nondeterministic/unspecified
   (where x_D ,(dict-iterate-key (term Δ_1) (dict-iterate-first (term Δ_1))))
   (where t_D (Δ-ref-type Δ_1 x_D))
   (where (x_c ...) (Δ-ref-constructors Δ_1 x_D))
   (where ((name t_c (in-hole Ξ (in-hole Θ x_D*))) ...)
          ((Δ-ref-type Δ_1 x_c) ...))
   (where Δ ,(dict-remove (term Δ_1) (term x_D)))
   (wf Δ ∅)
   (type-infer Δ ∅ t_D U_D)
   (type-infer Δ (∅ x_D : t_D) t_c U_c) ...
   ;; NB: Ugh this should be possible with pattern matching alone ....
   (side-condition ,(map (curry equal? (term x_D)) (term (x_D* ...))))
   (side-condition (positive* x_D (t_c ...)))
   ----------------- "WF-Inductive"
   (wf Δ_1 ∅)])

;; TODO: Bi-directional and inference?
;; TODO: http://www.cs.ox.ac.uk/ralf.hinze/WG2.8/31/slides/stephanie.pdf

;; Holds when e has type t under signature Δ and typing context Γ
(define-judgment-form tt-typingL
  #:mode (type-infer I I I O)
  #:contract (type-infer Δ Γ e t)

  [(wf Δ Γ)
   (unv-type U_0 U_1)
   ----------------- "DTR-Unv"
   (type-infer Δ Γ U_0 U_1)]

  [(wf Δ Γ)
   (where t (Δ-ref-type Δ x))
   ----------------- "DTR-Inductive"
   (type-infer Δ Γ x t)]

  [(wf Δ Γ)
   (where t (Γ-ref Γ x))
   ----------------- "DTR-Start"
   (type-infer Δ Γ x t)]

  [(type-infer Δ (Γ x : t_0) e t_1)
   (type-infer Δ Γ (Π (x : t_0) t_1) U)
   ----------------- "DTR-Abstraction"
   (type-infer Δ Γ (λ (x : t_0) e) (Π (x : t_0) t_1))]

  [(type-infer Δ Γ t_0 U_1)
   (type-infer Δ (Γ x : t_0) t U_2)
   (unv-pred U_1 U_2 U)
   ----------------- "DTR-Product"
   (type-infer Δ Γ (Π (x : t_0) t) U)]

  [(type-infer Δ Γ e_0 t)
   ;; Cannot rely on type-infer producing normal forms.
   (where (Π (x_0 : t_0) t_1) (reduce Δ t))
   (type-check Δ Γ e_1 t_0)
   (where t_3 (subst t_1 x_0 e_1))
   ----------------- "DTR-Application"
   (type-infer Δ Γ (e_0 e_1) t_3)]

  [(where t (Δ-elim-type Δ D U))
   (type-infer Δ Γ t U_e)
   ----------------- "DTR-Elim_D"
   (type-infer Δ Γ (elim D U) t)])

(define-judgment-form tt-typingL
  #:mode (type-check I I I I)
  #:contract (type-check Δ Γ e t)

  [(type-infer Δ Γ e t_0)
   (equivalent Δ t t_0)
   ----------------- "DTR-Check"
   (type-check Δ Γ e t)])


(module+ test
  (require rackunit)
  (define-term Δt (Δ-set ,(make-empty-Δ) True (Unv 0) ((T : True))))
  (check-false
   (judgment-holds (type-check ,(make-empty-Δ) ∅ T True)))
  (check-true
   (judgment-holds (type-check Δt ∅ T True)))
  (check-true
   (judgment-holds (type-check Δt ∅ True (Unv 0))))
  (check-true
   (judgment-holds (wf Δt ∅)))
  (check-true
   (judgment-holds (wf Δt (∅ P : (Unv 0)))))
  (check-true
   (judgment-holds (type-infer Δt ∅ (Π (P : (Unv 0)) True) t))))

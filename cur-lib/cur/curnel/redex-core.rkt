#lang racket/base

(require
  racket/function
  racket/list
  redex/reduction-semantics)

(provide
  (all-defined-out))

(set-cache-size! 10000)

#| References:
 |  http://www3.di.uminho.pt/~mjf/pub/SFV-CIC-2up.pdf
 |  https://www.cs.uoregon.edu/research/summerschool/summer11/lectures/oplss-herbelin1.pdf
 |  http://www.emn.fr/z-info/ntabareau/papers/universe_polymorphism.pdf
 |  http://people.cs.kuleuven.be/~jesper.cockx/Without-K/Pattern-matching-without-K.pdf
 |  http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.37.74
 |  http://eb.host.cs.st-andrews.ac.uk/writings/thesis.pdf
 |#

#| ttL is the core language of Cur. Very similar to TT (Idirs core) and Luo's UTT. Surface
 | langauge should provide short-hand, such as -> for non-dependent function types, and type
 | inference.
 |#
(define-language ttL
  (i j k  ::= natural)
  (U ::= (Unv i))
  (D x c ::= variable-not-otherwise-mentioned)
  (Δ   ::= ∅ (Δ (D : t ((c : t) ...))))
  (t e ::= U (λ (x : t) e) x (Π (x : t) t) (e e)
     ;; (elim inductive-type motive (indices ...) (methods ...) discriminant)
     (elim D e (e ...) (e ...) e))
  #:binding-forms
  (λ (x : t) e #:refers-to x)
  (Π (x : t_0) t_1 #:refers-to x))

;;; ------------------------------------------------------------------------
;;; Universe typing

;; Universe types
;; aka Axioms A of a PTS
(define-judgment-form ttL
  #:mode (unv-type I O)
  #:contract (unv-type U U)

  [(where i_1 ,(add1 (term i_0)))
   -----------------
   (unv-type (Unv i_0) (Unv i_1))])

;; Universe predicativity rules. Impredicative in (Unv 0)
;; aka Rules R of a PTS
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

;;; ------------------------------------------------------------------------
;;; Primitive Operations on signatures Δ (those operations that do not require contexts)

;;; TODO: Might be worth maintaining the above bijection between Δ and maps for performance reasons

;; TODO: This is doing too many things
;; NB: Depends on clause order
(define-metafunction ttL
  Δ-ref-type : Δ x -> t or #f
  [(Δ-ref-type ∅ x) #f]
  [(Δ-ref-type (Δ (x : t any)) x) t]
  [(Δ-ref-type (Δ (x_0 : t_0 ((x_1 : t_1) ... (x : t) (x_2 : t_2) ...))) x) t]
  [(Δ-ref-type (Δ (x_0 : t_0 any)) x) (Δ-ref-type Δ x)])

;; TODO: Should not use Δ-ref-type
(define-metafunction ttL
  Δ-ref-constructor-type : Δ x x -> t
  [(Δ-ref-constructor-type Δ x_D x_ci)
   (Δ-ref-type Δ x_ci)])

;; Get the list of constructors for the inducitvely defined type x_D
;; NB: Depends on clause order
(define-metafunction ttL
  Δ-ref-constructors : Δ x -> (x ...) or #f
  [(Δ-ref-constructors ∅ x_D) #f]
  [(Δ-ref-constructors (Δ (x_D : t_D ((x : t) ...))) x_D)
   (x ...)]
  [(Δ-ref-constructors (Δ (x_1 : t_1 any)) x_D)
   (Δ-ref-constructors Δ x_D)])

;; TODO: Mix of pure Redex/escaping to Racket sometimes is getting confusing.
;; TODO: Justify, or stop.

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

;; TODO: Might be worth it to actually maintain the above bijections, for performance reasons.

;; Applies the term t to the telescope Ξ.
;; TODO: Test
#| TODO:
 | This essentially eta-expands t at the type-level. Why is this necessary? Shouldn't it be true
 | that (convert t (Ξ-apply Ξ t))?
 | Maybe not. t is a lambda whose type is convert to (Ξ-apply Ξ t)? Yes.
 |#
(define-metafunction tt-ctxtL
  Ξ-apply : Ξ t -> t
  [(Ξ-apply hole t) t]
  [(Ξ-apply (Π (x : t) Ξ) t_0) (Ξ-apply Ξ (t_0 x))])

(define-metafunction tt-ctxtL
  list->Θ : (e ...) -> Θ
  [(list->Θ ()) hole]
  [(list->Θ (e e_r ...))
   (in-hole (list->Θ (e_r ...)) (hole e))])

(define-metafunction tt-ctxtL
  apply : e e ... -> e
  [(apply e_f e ...)
   (in-hole (list->Θ (e ...)) e_f)])

;;; ------------------------------------------------------------------------
;;; Computing the types of eliminators

;; Return the parameters of x_D as a telescope Ξ
;; TODO: Define generic traversals of Δ and Γ ?
(define-metafunction tt-ctxtL
  Δ-ref-parameter-Ξ : Δ x -> Ξ or #f
  [(Δ-ref-parameter-Ξ (Δ (x_D : (in-hole Ξ U) any)) x_D)
   Ξ]
  [(Δ-ref-parameter-Ξ (Δ (x_1 : t_1 any)) x_D)
   (Δ-ref-parameter-Ξ Δ x_D)]
  [(Δ-ref-parameter-Ξ Δ x)
   #f])

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

;; Returns the inductive hypotheses required for the elimination method of constructor c_i for
;; inductive type D, when eliminating with motive t_P.
(define-metafunction tt-ctxtL
  Δ-constructor-inductive-hypotheses : Δ D c t -> Ξ
  [(Δ-constructor-inductive-hypotheses Δ D c_i t_P)
   (hypotheses-loop D t_P (Δ-constructor-inductive-telescope Δ D c_i))])

;; Returns the type of the method corresponding to c_i
(define-metafunction tt-ctxtL
  Δ-constructor-method-type : Δ D c t -> t
  [(Δ-constructor-method-type Δ D c_i t_P)
   (in-hole Ξ_a (in-hole Ξ_h ((in-hole Θ_p t_P) (Ξ-apply Ξ_a c_i))))
   (where Θ_p (Δ-constructor-parameters Δ D c_i))
   (where Ξ_a (Δ-constructor-telescope Δ D c_i))
   (where Ξ_h (Δ-constructor-inductive-hypotheses Δ D c_i t_P))])

(define-metafunction tt-ctxtL
  Δ-method-types : Δ D e -> (t ...)
  [(Δ-method-types Δ D e)
   ,(map (lambda (c) (term (Δ-constructor-method-type Δ D ,c e))) (term (c ...)))
   (where (c ...) (Δ-ref-constructors Δ D))])

(define-metafunction tt-ctxtL
  Δ-motive-type : Δ D U -> t
  [(Δ-motive-type Δ D U)
   (in-hole Ξ_P*D U)
   (where Ξ (Δ-ref-parameter-Ξ Δ D))
   ;; A fresh name to bind the discriminant
   (where x ,(variable-not-in (term (Δ D Ξ)) 'x-D))
   ;; The telescope (∀ a -> ... -> (D a ...) hole), i.e.,
   ;; of the indices and the inductive type applied to the
   ;; indices
   (where Ξ_P*D (in-hole Ξ (Π (x : (Ξ-apply Ξ D)) hole)))])

;;; ------------------------------------------------------------------------
;;; Dynamic semantics
;;; The majority of this section is dedicated to evaluation of (elim x U), the eliminator for the
;;; inductively defined type x with a motive whose result is in universe U

(define-extended-language tt-redL tt-ctxtL
  (v  ::= x U (Π (x : t) t) (λ (x : t) t) (in-hole Θv c))
  (Θv ::= hole (Θv v))
  (C-elim  ::= (elim D t_P (e_i ...) (e_m ...) hole))
  ;; call-by-value
  (E  ::= hole (E e) (v E)
      (elim D e (e ...) (v ... E e ...) e)
      (elim D e (e ...) (v ...) E)
      ;; reduce under Π (helps with typing checking)
      ;; TODO: Should be done in conversion judgment
      (Π (x : v) E) (Π (x : E) e)))

#|
 | The elim form must appear applied like so:
 | (elim D U v_P m_0 ... m_i m_j ... m_n p ... (c_i a ...))
 |
 | Where:
 |   D       is the inductive being eliminated
 |   U         is the universe of the result of the motive
 |   v_P       is the motive
 |   m_{0..n}  are the methods
 |   p ...     are the parameters of x_D
 |   c_i       is a constructor of x_d
 |   a ...     are the arguments to c_i
 |
 | Using contexts, this appears as (in-hole Θ ((elim D U) v_P))
 |#
(define-metafunction tt-ctxtL
  is-inductive-argument : Δ D t -> #t or #f
  ;; Think this only works in call-by-value. A better solution would
  ;; be to check position of the argument w.r.t. the current
  ;; method. requires more arguments, and more though.q
  [(is-inductive-argument Δ D (in-hole Θ c_i))
   ,(and (memq (term c_i) (term (Δ-ref-constructors Δ D))) #t)])

;; Generate recursive applications of the eliminator for each inductive argument of type x_D.
;; In more detail, given motive t_P, parameters Θ_p, methods Θ_m, and arguments Θ_i to constructor
;; x_ci for x_D, for each inductively smaller term t_i of type (in-hole Θ_p x_D) inside Θ_i,
;; generate: (elim x_D U t_P  Θ_m ... Θ_p ... t_i)
;; TODO TTEESSSSSTTTTTTTT
(define-metafunction tt-redL
  Δ-inductive-elim : Δ D C-elim Θ -> Θ
  ;; NB: If metafunction fails, recursive
  ;; NB: elimination will be wrong. This will introduced extremely sublte bugs,
  ;; NB: inconsistency, failure of type safety, and other bad things.
  ;; NB: It should be tested and audited thoroughly
  [(Δ-inductive-elim any ... hole)
   hole]
  [(Δ-inductive-elim Δ D C-elim (Θ_c t_i))
   ((Δ-inductive-elim Δ D C-elim Θ_c)
    (in-hole C-elim t_i))
   (side-condition (term (is-inductive-argument Δ D t_i)))]
  [(Δ-inductive-elim any ... (Θ_c t_i))
   (Δ-inductive-elim any ... Θ_c)])

(define tt-->
  (reduction-relation tt-redL
    (--> (Δ (in-hole E ((λ (x : t_0) t_1) t_2)))
         (Δ (in-hole E (subst t_1 x t_2)))
         -->β)
    (--> (Δ (in-hole E (elim D e_motive (e_i ...) (v_m ...) (in-hole Θv_c c))))
         (Δ (in-hole E (in-hole Θ_mi v_mi)))
         ;; Find the method for constructor c_i, relying on the order of the arguments.
         (where natural (Δ-constructor-index Δ D c))
         (where v_mi ,(list-ref (term (v_m ...)) (term natural)))
         ;; Generate the inductive recursion
         (where Θ_ih (Δ-inductive-elim Δ D (elim D e_motive (e_i ...) (v_m ...) hole) Θv_c))
         (where Θ_mi (in-hole Θ_ih Θv_c))
         -->elim)))

(define-metafunction tt-redL
  reduce : Δ e -> e
  [(reduce Δ e)
   e_r
   (where (_ e_r)
          ,(car (apply-reduction-relation* tt--> (term (Δ e)) #:cache-all? #t)))])

;;; ------------------------------------------------------------------------
;;; Type checking and synthesis

(define-extended-language tt-typingL tt-redL
  ;; NB: There may be a bijection between Γ and Ξ. That's interesting.
  ;; NB: Also a bijection between Γ and a list of maps from x to t.
  (Γ   ::= ∅ (Γ x : t)))

(define-judgment-form tt-typingL
  #:mode (convert I I I I)
  #:contract (convert Δ Γ t t)

  [(side-condition ,(<= (term i_0) (term i_1)))
   ----------------- "≼-Unv"
   (convert Δ Γ (Unv i_0) (Unv i_1))]

  [(where t_2 (reduce Δ t_0))
   (where t_3 (reduce Δ t_1))
   (side-condition (α-equivalent? t_2 t_3))
   ----------------- "≼-αβ"
   (convert Δ Γ t_0 t_1)]

  [(convert Δ (Γ x : t_0) t_1 t_2)
   ----------------- "≼-Π"
   (convert Δ Γ (Π (x : t_0) t_1) (Π (x : t_0) t_2))])

;; NB: Depends on clause order
(define-metafunction tt-typingL
  Γ-ref : Γ x -> t or #f
  [(Γ-ref ∅ x) #f]
  [(Γ-ref (Γ x : t) x) t]
  [(Γ-ref (Γ x_0 : t_0) x_1) (Γ-ref Γ x_1)])

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

  [----------------- "WF-Empty"
   (wf ∅ ∅)]

  [(type-infer Δ Γ t t_0)
   (wf Δ Γ)
   ----------------- "WF-Var"
   (wf Δ (Γ x : t))]

  [(wf Δ ∅)
   (type-infer Δ ∅ t_D U_D)
   (type-infer Δ (∅ x_D : t_D) t_c U_c) ...
   ;; NB: Ugh this should be possible with pattern matching alone ....
   (side-condition ,(map (curry equal? (term x_D)) (term (x_D* ...))))
   (side-condition (positive* x_D (t_c ...)))
   ----------------- "WF-Inductive"
   (wf (Δ (x_D : t_D
               ;; Checks that a constructor for x actually produces an x, i.e., that
               ;; the constructor is well-formed.
               ((x_c : (name t_c (in-hole Ξ (in-hole Θ x_D*)))) ...))) ∅)])

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

  [(where t (Δ-ref-type Δ x))
   ----------------- "DTR-Inductive"
   (type-infer Δ Γ x t)]

  [(where t (Γ-ref Γ x))
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

  [(type-check Δ Γ e_c (apply D e_i ...))

   (type-infer Δ Γ e_motive (name t_motive (in-hole Ξ U)))
   (convert Δ Γ t_motive (Δ-motive-type Δ D U))

   (where (t_m ...) (Δ-method-types Δ D e_motive))
   (type-check Δ Γ e_m t_m) ...
   ----------------- "DTR-Elim_D"
   (type-infer Δ Γ (elim D e_motive (e_i ...) (e_m ...) e_c)
               (apply e_motive e_i ... e_c))])

(define-judgment-form tt-typingL
  #:mode (type-check I I I I)
  #:contract (type-check Δ Γ e t)

  [(type-infer Δ Γ e t_0)
   (convert Δ Γ t t_0)
   ----------------- "DTR-Check"
   (type-check Δ Γ e t)])

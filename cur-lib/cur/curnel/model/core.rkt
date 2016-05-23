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
  ;; TODO: Might make more sense for methods to come first
  ;; (elim inductive-type motive (indices ...) (methods ...) discriminant)
  (t e ::= U (λ (x : e) e) x (Π (x : e) e) (e e) (elim D e (e ...) (e ...) e))
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

;;; ------------------------------------------------------------------------
;;; Primitive Operations on signatures Δ (those operations that do not require contexts)

(define-metafunction ttL
  Δ-in-dom : Δ D -> #t or #f
  [(Δ-in-dom ∅ D)
   #f]
  [(Δ-in-dom (Δ (D : t any)) D)
   #t]
  [(Δ-in-dom (Δ (D_!_0 : any_D any)) (name D D_!_0))
   (Δ-in-dom Δ D)])

(define-metafunction ttL
  Δ-in-constructor-dom : Δ c -> #t or #f
  [(Δ-in-constructor-dom ∅ c)
   #f]
  [(Δ-in-constructor-dom (Δ (D : any_D ((c_!_0 : any) ... (c_i : any_i) any_r ...))) (name c_i c_!_0))
   #t]
  [(Δ-in-constructor-dom (Δ (D : any_D ((c_!_0 : any) ...))) (name c c_!_0))
   (Δ-in-constructor-dom Δ c)])

(define-metafunction ttL
  Δ-ref-type : Δ_0 D_0 -> t
  #:pre (Δ-in-dom Δ_0 D_0)
  [(Δ-ref-type (Δ (D : t any)) D)
   t]
  [(Δ-ref-type (Δ (D_!_0 : t any)) (name D D_!_0))
   (Δ-ref-type Δ D)])

;; Make D : t ∈ Δ a little easier to use, prettier to render
(define-judgment-form ttL
  #:mode (Δ-type-in I I O)
  #:contract (Δ-type-in Δ D t)

  [(side-condition (Δ-in-dom Δ D))
   (where t (Δ-ref-type Δ D))
   -------------------------------
   (Δ-type-in Δ D t)])

;; Returns the inductively defined type that x constructs
(define-metafunction ttL
  Δ-key-by-constructor : Δ_0 c_0 -> D
  #:pre (Δ-in-constructor-dom Δ_0 c_0)
  [(Δ-key-by-constructor (Δ (D : any_D ((c_!_0 : any_c) ... (c : any_ci) any_r ...))) (name c c_!_0))
   D]
  [(Δ-key-by-constructor (Δ (D : any_D ((c_!_0 : any_c) ...))) (name c c_!_0))
   (Δ-key-by-constructor Δ c)])

;; Returns the constructor map for the inductively defined type D in the signature Δ
(define-metafunction ttL
  Δ-ref-constructor-map : Δ_0 D_0 -> ((c : t) ...)
  #:pre (Δ-in-dom Δ_0 D_0)
  [(Δ-ref-constructor-map (Δ (D : any_D any)) D)
   any]
  [(Δ-ref-constructor-map (Δ (D_!_0 : any_D any)) (name D D_!_0))
   (Δ-ref-constructor-map Δ D)])

;; Return the type of the constructor c_i
(define-metafunction ttL
  Δ-ref-constructor-type : Δ_0 c_0 -> t
  #:pre (Δ-in-constructor-dom Δ_0 c_0)
  [(Δ-ref-constructor-type Δ c)
   t
   (where D (Δ-key-by-constructor Δ c))
   (where (any_1 ... (c : t) any_0 ...)
          (Δ-ref-constructor-map Δ D))])

;; Make c : t ∈ Δ a little easier to use, prettier to render
(define-judgment-form ttL
  #:mode (Δ-constr-in I I O)
  #:contract (Δ-constr-in Δ c t)

  [(side-condition (Δ-in-constructor-dom Δ c))
   (where t (Δ-ref-constructor-type Δ c))
   -------------------------------
   (Δ-constr-in Δ c t)])

(define-metafunction ttL
  Δ-ref-constructors : Δ_0 D_0 -> (c ...)
  #:pre (Δ-in-dom Δ_0 D_0)
  [(Δ-ref-constructors Δ D)
   (c ...)
   (where ((c : any) ...) (Δ-ref-constructor-map Δ D))])

;;; ------------------------------------------------------------------------
;;; Operations that involve contexts.

(define-extended-language tt-ctxtL ttL
  ;; Telescope.
  (Ξ Φ ::= hole (Π (x : t) Ξ))
  ;; Apply context
  (Θ   ::= hole (Θ e)))

;; Applies the term t to the telescope Ξ.
;; TODO: Test
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

;; Return the indices of D as a telescope Ξ
(define-metafunction tt-ctxtL
  Δ-ref-index-Ξ : Δ_0 D_0 -> Ξ
  #:pre (Δ-in-dom Δ_0 D_0)
  [(Δ-ref-index-Ξ any_Δ any_D)
   Ξ
   (where (in-hole Ξ U) (Δ-ref-type any_Δ any_D))])

;; Returns the telescope of the arguments for the constructor c_i of the inductively defined type D
(define-metafunction tt-ctxtL
  Δ-constructor-telescope : Δ_0 c_0 -> Ξ
  #:pre (Δ-in-constructor-dom Δ_0 c_0)
  [(Δ-constructor-telescope Δ c)
   Ξ
   (where D (Δ-key-by-constructor Δ c))
   (where (in-hole Ξ (in-hole Θ D))
     (Δ-ref-constructor-type Δ c))])

;; Returns the index arguments as an apply context of the constructor c_i of the inductively
;; defined type D
(define-metafunction tt-ctxtL
  Δ-constructor-indices : Δ_0 c_0 -> Θ
  #:pre (Δ-in-constructor-dom Δ_0 c_0)
  [(Δ-constructor-indices Δ c)
   Θ
   (where D (Δ-key-by-constructor Δ c))
   (where (in-hole Ξ (in-hole Θ D))
     (Δ-ref-constructor-type Δ c))])

;; Fold over the telescope Φ building a new telescope with only arguments of type D
;; NB: Depends on clause order
(define-metafunction tt-ctxtL
  inductive-loop : D Φ -> Φ
  [(inductive-loop D hole) hole]
  [(inductive-loop D (Π (x : (in-hole Φ (in-hole Θ D))) Φ_1))
   (Π (x : (in-hole Φ (in-hole Θ D))) (inductive-loop D Φ_1))]
  [(inductive-loop D (Π (x : t) Φ_1))
   (inductive-loop D Φ_1)])

;; Returns the inductive arguments to the constructor c_i
(define-metafunction tt-ctxtL
  Δ-constructor-inductive-telescope : Δ_0 c_0 -> Ξ
  #:pre (Δ-in-constructor-dom Δ_0 c_0)
  [(Δ-constructor-inductive-telescope Δ c)
   (inductive-loop D (Δ-constructor-telescope Δ c))
   (where D (Δ-key-by-constructor Δ c))])

;; Fold over the telescope Φ computing a new telescope with all
;; inductive arguments of type D modified to an inductive hypotheses
;; computed from the motive t.
(define-metafunction tt-ctxtL
  hypotheses-loop : D t Φ -> Φ
  [(hypotheses-loop D t_P hole) hole]
  [(hypotheses-loop D t_P (name any_0 (Π (x : (in-hole Φ (in-hole Θ D))) Φ_1)))
   (Π (x_h : (in-hole Φ ((in-hole Θ t_P) (Ξ-apply Φ x))))
      (hypotheses-loop D t_P Φ_1))
   (where x_h ,(variable-not-in (term (D t_P any_0)) 'x-ih))])

;; Returns the inductive hypotheses required for the elimination method of constructor c_i for
;; inductive type D, when eliminating with motive t_P.
(define-metafunction tt-ctxtL
  Δ-constructor-inductive-hypotheses : Δ_0 c_0 t -> Ξ
  #:pre (Δ-in-constructor-dom Δ_0 c_0)
  [(Δ-constructor-inductive-hypotheses Δ c_i t_P)
   (hypotheses-loop D t_P (Δ-constructor-inductive-telescope Δ c_i))
   (where D (Δ-key-by-constructor Δ c_i))])

;; Returns the type of the method corresponding to c_i
(define-metafunction tt-ctxtL
  Δ-constructor-method-type : Δ_0 c_0 t -> t
  #:pre (Δ-in-constructor-dom Δ_0 c_0)
  [(Δ-constructor-method-type Δ c_i t_P)
   (in-hole Ξ_a (in-hole Ξ_h ((in-hole Θ_p t_P) (Ξ-apply Ξ_a c_i))))
   (where Θ_p (Δ-constructor-indices Δ c_i))
   (where Ξ_a (Δ-constructor-telescope Δ c_i))
   (where Ξ_h (Δ-constructor-inductive-hypotheses Δ c_i t_P))])

;; Return the types of the methods required to eliminate D with motive e
(define-metafunction tt-ctxtL
  Δ-method-types : Δ_0 D_0 e -> (t ...)
  #:pre (Δ-in-dom Δ_0 D_0)
  [(Δ-method-types Δ D e)
   ((Δ-constructor-method-type Δ c e) ...)
   (where (c ...) (Δ-ref-constructors Δ D))])

;; Return the type of the motive to eliminate D
(define-metafunction tt-ctxtL
  Δ-motive-type : Δ_0 D_0 U -> t
  #:pre (Δ-in-dom Δ_0 D_0)
  [(Δ-motive-type Δ D U)
   (in-hole Ξ_P*D U)
   (where Ξ (Δ-ref-index-Ξ Δ D))
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
  (C-elim  ::= (elim D t_P (e_i ...) (e_m ...) hole)))

(define-metafunction tt-ctxtL
  is-inductive-argument : Δ_0 D_0 t -> #t or #f
  #:pre (Δ-in-dom Δ_0 D_0)
  ;; Think this only works in call-by-value. A better solution would
  ;; be to check position of the argument w.r.t. the current
  ;; method. requires more arguments, and more though.q
  [(is-inductive-argument Δ D (in-hole Θ c_i))
   ,(and (memq (term c_i) (term (Δ-ref-constructors Δ D))) #t)])

;; Generate recursive applications of the eliminator for each inductive argument in Θ.
;; TODO TTEESSSSSTTTTTTTT
(define-metafunction tt-redL
  Δ-inductive-elim : Δ_0 D_0 C-elim Θ -> Θ
  #:pre (Δ-in-dom Δ_0 D_0)
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

#|
 | The elim form must appear applied like so:
 | (elim D v_P (i ...) (m_0 ... m_i m_j ... m_n) (c_i a ...))
 |
 | Where:
 |   D       is the inductive being eliminated
 |   v_P       is the motive
 |   m_{0..n}  are the methods
 |   i ...     are the indices of D
 |   c_i       is a constructor of D
 |   a ...     are the arguments to c_i
 |
 | Steps to (m_i a ... ih ...), where ih are computed from the recursive arguments to c_i
 |#
(define (tt--> D)
  (term-let ([Δ D])
    (reduction-relation tt-redL
      (--> ((λ (x : t_0) t_1) t_2) (substitute t_1 x t_2)
           "-->β")
      (--> (elim D e_motive (e_i ...) (e_m ...) (in-hole Θ_c c)) (in-hole Θ_mi e_mi)
           (side-condition (term (Δ-in-constructor-dom Δ c)))
           ;; Find the method for constructor c_i, relying on the order of the arguments.
           (where (c_i ...) (Δ-ref-constructors Δ D))
           (where (_ ... (c e_mi) _ ...) ((c_i e_m) ...))
           ;; Generate the inductive recursion
           (where Θ_ih (Δ-inductive-elim Δ D (elim D e_motive (e_i ...) (e_m ...) hole) Θ_c))
           ;; Generate the method arguments, which are the constructor's arguments and the inductive arguments
           (where Θ_mi (in-hole Θ_ih Θ_c))
           "-->elim"))))

(define-extended-language tt-cbvL tt-redL
  ;; NB: Not exactly right; only true when c is a constructor
  (v  ::= x U (Π (x : t) t) (λ (x : t) t) (in-hole Θv c))
  (Θv ::= hole (Θv v))
  (E  ::= hole (E e) (v E)
      (elim D e (e ...) (v ... E e ...) e)
      (elim D e (e ...) (v ...) E)
      ;; NB: Reducing under Π seems necessary
      (Π (x : E) e) (Π (x : v) E)))

(define-extended-language tt-cbnL tt-cbvL
  (E  ::= hole (E e) (elim D e (e ...) (e ...) E)))

;; Trying to model "head reduction"; chpt 4 of Coq manual
(define-extended-language tt-head-redL tt-cbvL
  (C-λ ::= Θ (λ (x : t) C-λ))
  (λv  ::= x U (Π (x : t) t) (elim D e (e ...) (e ...) (in-hole C-λ x)))
  (v ::= (in-hole C-λ λv)))

;; Lazyness has lots of implications, such as on conversion and test suite.
(define (tt-->cbn D) (context-closure (tt--> D) tt-cbnL E))

;; NB: Note that CIC specifies reduction via "contextual closure".
;; Perhaps they mean compatible-closure. Unfortunately, it's too slow.
(define (tt-->full D) (compatible-closure (tt--> D) tt-redL e))

;; Head reduction
(define (tt-->head-red D) (context-closure (tt--> D) tt-head-redL C-λ))

;; CBV, plus under Π
(define (tt-->cbv D) (context-closure (tt--> D) tt-cbvL E))

(define-metafunction tt-redL
  reduce : Δ e -> e
  [(reduce Δ e)
   ,(car (apply-reduction-relation* (tt-->cbv (term Δ)) (term e) #:cache-all? #t))])

;;; ------------------------------------------------------------------------
;;; Type checking and synthesis

(define-extended-language tt-typingL tt-redL
  ;; NB: There may be a bijection between Γ and Ξ. That's interesting.
  ;; NB: Also a bijection between Γ and a list of maps from x to t.
  (Γ   ::= ∅ (Γ x : t)))

(define-judgment-form tt-typingL
  #:mode (convert I I I I)
  #:contract (convert Δ Γ t t)

  [(where (t t) ((reduce Δ t_0) (reduce Δ t_1)))
   ----------------- "≡"
   (convert Δ Γ t_0 t_1)])

(define-judgment-form tt-typingL
  #:mode (subtype I I I I)
  #:contract (subtype Δ Γ t t)

  [(convert Δ Γ t_0 t_1)
   ------------- "≼-≡"
   (subtype Δ Γ t_0 t_1)]

  [(side-condition ,(<= (term i_0) (term i_1)))
   ----------------- "≼-Unv"
   (subtype Δ Γ (Unv i_0) (Unv i_1))]

  [(convert Δ Γ t_0 t_1)
   (subtype Δ (Γ x_0 : t_0) e_0 (substitute e_1 x_1 x_0))
   ----------------- "≼-Π"
   (subtype Δ Γ (Π (x_0 : t_0) e_0) (Π (x_1 : t_1) e_1))])

(define-metafunction tt-typingL
  Γ-in-dom : Γ x -> #t or #f
  [(Γ-in-dom ∅ x)
   #f]
  [(Γ-in-dom (Γ x : t) x)
   #t]
  [(Γ-in-dom (Γ x_!_0 : t) (name x x_!_0))
   (Γ-in-dom Γ x)])

(define-metafunction tt-typingL
  Γ-ref : Γ_0 x_0 -> t
  #:pre (Γ-in-dom Γ_0 x_0)
  [(Γ-ref (Γ x : t) x)
   t]
  [(Γ-ref (Γ x_!_0 : t_0) (name x_1 x_!_0))
   (Γ-ref Γ x_1)])

;; Make ∈ Γ a little easier to use, prettier to render
(define-judgment-form tt-typingL
  #:mode (Γ-in I I O)
  #:contract (Γ-in Γ x t)

  [(side-condition (Γ-in-dom Γ x))
   (where t (Γ-ref Γ x))
   -------------------------------
   (Γ-in Γ x t)])

;; TODO: After reading https://coq.inria.fr/doc/Reference-Manual006.html#sec209, not convinced this is right.

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

;; Holds when the type t is a valid type for a constructor of D
(define-judgment-form tt-typingL
  #:mode (valid-constructor I I)
  #:contract (valid-constructor D t)

  ;; NB TODO: Ignore the "positive" occurrence of D in the result; this is hacky way to do this
  [(side-condition (positive D (in-hole Ξ (Unv 0))))
   ---------------------------------------------------------
   (valid-constructor D (name t_c (in-hole Ξ (in-hole Θ D))))])

;; Holds when the signature Δ is valid
(define-judgment-form tt-typingL
  #:mode (valid I)
  #:contract (valid Δ)

  [-------- "Valid-Empty"
   (valid ∅)]

  [(valid Δ)
   (type-infer Δ ∅ t_D U_D)
   (valid-constructor D t_c) ...
   (type-infer Δ (∅ D : t_D) t_c U_c) ...
   ----------------- "Valid-Inductive"
   (valid (Δ (D : t_D ((c : t_c) ...))))])

;; Holds when the signature Δ and typing context Γ are well-formed.
(define-judgment-form tt-typingL
  #:mode (wf I I)
  #:contract (wf Δ Γ)

  [(valid Δ)
   ----------------- "WF-Empty"
   (wf Δ ∅)]

  [(type-infer Δ Γ t t_0)
   (wf Δ Γ)
   ----------------- "WF-Var"
   (wf Δ (Γ x : t))])

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

  [(Δ-type-in Δ D t)
   (wf Δ Γ)
   ----------------- "DTR-Inductive"
   (type-infer Δ Γ D t)]

  [(Δ-constr-in Δ c t)
   (wf Δ Γ)
   ----------------- "DTR-Constructor"
   (type-infer Δ Γ c t)]

  [(Γ-in Γ x t)
   (wf Δ Γ)
   ----------------- "DTR-Start"
   (type-infer Δ Γ x t)]

  [(type-infer-normal Δ (Γ x : t_0) e t_1)
   (type-infer-normal Δ Γ (Π (x : t_0) t_1) U)
   ----------------- "DTR-Abstraction"
   (type-infer Δ Γ (λ (x : t_0) e) (Π (x : t_0) t_1))]

  [(type-infer Δ Γ t_0 U_1)
   (type-infer Δ (Γ x : t_0) t U_2)
   (unv-pred U_1 U_2 U)
   ----------------- "DTR-Product"
   (type-infer Δ Γ (Π (x : t_0) t) U)]

  [(type-infer-normal Δ Γ e_0 (Π (x_0 : t_0) t_1))
   (type-check Δ Γ e_1 t_0)
   ----------------- "DTR-Application"
   (type-infer Δ Γ (e_0 e_1) (substitute t_1 x_0 e_1))]

  [(type-check Δ Γ e_c (apply D e_i ...))

   (type-infer-normal Δ Γ e_motive (name t_motive (in-hole Ξ U)))
   (subtype Δ Γ t_motive (Δ-motive-type Δ D U))

   (where (t_m ...) (Δ-method-types Δ D e_motive))
   (type-check Δ Γ e_m t_m) ...
   ----------------- "DTR-Elim_D"
   (type-infer Δ Γ (elim D e_motive (e_i ...) (e_m ...) e_c) (apply e_motive e_i ... e_c))])

(define-judgment-form tt-typingL
  #:mode (type-infer-normal I I I O)
  #:contract (type-infer-normal Δ Γ e t)

  [(type-infer Δ Γ e t)
   ----------------- "DTR-Reduce"
   (type-infer-normal Δ Γ e (reduce Δ t))])

(define-judgment-form tt-typingL
  #:mode (type-check I I I I)
  #:contract (type-check Δ Γ e t)

  [(type-infer Δ Γ e t_0)
   (type-infer Δ Γ t U)
   (subtype Δ Γ t_0 t)
   ----------------- "DTR-Check"
   (type-check Δ Γ e t)])

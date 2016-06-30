#lang racket/base

#| NB:
 | Largely copied from the model, then stripped to be faster.
 |#

(require
  redex/reduction-semantics)

(provide
  (all-defined-out))

(set-cache-size! 10000)

(define-language ttL
  (i j k  ::= natural)
  (U ::= (Unv i))
  (D x c ::= variable-not-otherwise-mentioned)
  (Δ   ::= (((D : t) (c : t) ...) ...))
  (t e ::= U (λ (x : e) e) x (Π (x : e) e) (e e)
     ;; TODO: Might make more sense for methods to come first
     ;; (elim inductive-type motive (methods ...) discriminant)
     (elim D e (e ...) e))
  #:binding-forms
  (λ (x : t) e #:refers-to x)
  (Π (x : t_0) t_1 #:refers-to x))

;;; ------------------------------------------------------------------------
;;; Universe typing

;; Universe types
;; aka Axioms A of a PTS
(define-judgment-form ttL
  #:mode (unv-type I O)

  [(where i_1 ,(add1 (term i_0)))
   -----------------
   (unv-type (Unv i_0) (Unv i_1))])

;; Universe predicativity rules. Impredicative in (Unv 0)
;; aka Rules R of a PTS
(define-judgment-form ttL
  #:mode (unv-pred I I O)

  [----------------
   (unv-pred (Unv i) (Unv 0) (Unv 0))]

  [(where i_3 ,(max (term i_1) (term i_2)))
   ----------------
   (unv-pred (Unv i_1) (Unv i_2) (Unv i_3))])

;;; ------------------------------------------------------------------------
;;; Primitive Operations on signatures Δ (those operations that do not require contexts)

;; TODO: Define generic traversals of Δ and Γ ?
(define-metafunction ttL
  Δ-in-dom : Δ D -> #t or #f
  [(Δ-in-dom (((D_0 : t_0) any ...) ...) D)
   ,(and (memq (term D) (term (D_0 ...))) #t)])

(define-metafunction ttL
  Δ-in-constructor-dom : Δ c -> #t or #f
  [(Δ-in-constructor-dom ((any (c_0 : t_0) ...) ...) c)
   ,(and (memq (term c) (term (c_0 ... ...))) #t)])

;;; NB: Might be worth maintaining the above bijection between Δ and maps for performance reasons
;;; Hypothesis tested: Actually, makes things slower if done naively. Best to leave it alone.
(define-metafunction ttL
  [(Δ-ref-type (((D_0 : t_0) any ...) ...) D)
   ,(cdr (assq (term D) (map cons (term (D_0 ...)) (term (t_0 ...)))))])

;; Make D : t ∈ Δ a little easier to use, prettier to render
(define-judgment-form ttL
  #:mode (Δ-type-in I I O)

  [(side-condition (Δ-in-dom Δ D))
   (where t (Δ-ref-type Δ D))
   -------------------------------
   (Δ-type-in Δ D t)])

;; Returns the inductively defined type that x constructs
(define-metafunction ttL
  ;; NB: Assumes constructors are unique across all inductive types
  [(Δ-key-by-constructor (any_0 ...
                          ((D : any_D) any_c ... (c : any_ci) any_r ...)
                          any_1 ...)
                         c)
   D])

;; Returns the constructor map for the inductively defined type D in the signature Δ
(define-metafunction ttL
  [(Δ-ref-constructor-map (any_0 ... ((D : any_D) any ...) any_r ...) D)
   (any ...)])

;; Return the type of the constructor c_i
(define-metafunction ttL
  [(Δ-ref-constructor-type Δ c)
   t
   (where D (Δ-key-by-constructor Δ c))
   (where (any_1 ... (c : t) any_0 ...)
          (Δ-ref-constructor-map Δ D))])

;; Make c : t ∈ Δ a little easier to use, prettier to render
(define-judgment-form ttL
  #:mode (Δ-constr-in I I O)

  [(side-condition (Δ-in-constructor-dom Δ c))
   (where t (Δ-ref-constructor-type Δ c))
   -------------------------------
   (Δ-constr-in Δ c t)])

(define-metafunction ttL
  [(Δ-ref-constructors Δ D)
   (c ...)
   (where ((c : any) ...) (Δ-ref-constructor-map Δ D))])

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
(define-metafunction tt-ctxtL
  [(Ξ-apply hole t) t]
  [(Ξ-apply (Π (x : t) Ξ) t_0) (Ξ-apply Ξ (t_0 x))])

(define-metafunction tt-ctxtL
  [(list->Θ ()) hole]
  [(list->Θ (e e_r ...))
   (in-hole (list->Θ (e_r ...)) (hole e))])

(define-metafunction tt-ctxtL
  [(apply e_f e ...)
   (in-hole (list->Θ (e ...)) e_f)])

;;; ------------------------------------------------------------------------
;;; Dynamic semantics
;;; The majority of this section is dedicated to evaluation of (elim x U), the eliminator for the
;;; inductively defined type x with a motive whose result is in universe U

(define-extended-language tt-redL tt-ctxtL
  (C-elim  ::= (elim D t_P (e_m ...) hole)))

(define-metafunction tt-ctxtL
  ;; Think this only works in call-by-value. A better solution would
  ;; be to check position of the argument w.r.t. the current
  ;; method. requires more arguments, and more though.q
  [(is-inductive-argument Δ D (in-hole Θ c_i))
   ,(and (memq (term c_i) (term (Δ-ref-constructors Δ D))) #t)])

;; Generate recursive applications of the eliminator for each inductive argument in Θ.
;; TODO TTEESSSSSTTTTTTTT
(define-metafunction tt-redL
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
      (--> ((λ (x : t_0) t_1) t_2)
           (substitute t_1 x t_2)
           -->β)
      (--> (elim D e_motive any_m (in-hole Θ_c c))
           (in-hole Θ_mi e_mi)
           (side-condition (term (Δ-in-constructor-dom Δ c)))
           ;; Find the method for constructor c_i, relying on the order of the arguments.
           (where e_mi ,(cdr (assq (term c) (map cons (term (Δ-ref-constructors Δ D)) (term any_m)))))
           ;; Generate the inductive recursion
           (where Θ_ih (Δ-inductive-elim Δ D (elim D e_motive any_m hole) Θ_c))
           (where Θ_mi (in-hole Θ_ih Θ_c))
           -->elim))))

(define-extended-language tt-cbvL tt-redL
  ;; NB: Not exactly right; only true when c is a constructor
  (v  ::= x U (Π (x : t) t) (λ (x : t) t) (in-hole Θv c))
  (Θv ::= hole (Θv v))
  (E  ::= hole (E e) (v E)
      (elim D e (v ... E e ...) e)
      (elim D e (v ...) E)
      ;; NB: Reducing under Π seems necessary
      (Π (x : E) e) (Π (x : v) E)))

(define-extended-language tt-cbnL tt-cbvL
  (E  ::= hole (E e) (elim D e (e ...) E)))

;; Trying to model "head reduction"; chpt 4 of Coq manual
(define-extended-language tt-head-redL tt-cbvL
  (C-λ ::= Θ (λ (x : t) C-λ))
  (λv  ::= x U (Π (x : t) t) (elim D e (e ...) (in-hole C-λ x)))
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

(require
 (for-syntax racket/base)
 racket/match)

(define deconstruct-apply-ctxt
  (term-match/single tt-ctxtL [(in-hole Θ c) (list (term Θ) (term c))]))

(define destructable?
  (redex-match? tt-ctxtL (in-hole Θ c)))

(define ((constructor? Δ) c)
  (term (Δ-in-constructor-dom ,Δ ,c)))

(define-match-expander apply-ctxt
  (lambda (syn)
    (syntax-case syn ()
      [(_ Δ Θ c)
       #'(? destructable? (app deconstruct-apply-ctxt (list Θ (? (constructor? Δ) c))))])))

(define (cbv-eval Δ e)
  (let eval ([e e])
    (match e
      [`(elim ,D ,(app eval motive) ,(list (app eval ms) ...) ,(app eval (apply-ctxt Δ Θ c)))
       (term-let ([e_mi (cdr (assq (term ,c) (map cons (term (Δ-ref-constructors ,Δ ,D)) (term ,ms))))]
                  [Θ_ih (term (Δ-inductive-elim ,Δ ,D (elim ,D ,motive ,ms hole) ,Θ))]
                  [Θ_mi (term (in-hole Θ_ih ,Θ))])
                 (eval (term (in-hole Θ_mi e_mi))))]
      [`(,(app eval `(λ (,x : ,t) ,body)) ,(app eval v))
       (eval (term (substitute ,body ,x ,v)))]
      [`(,(app eval c) ,(app eval v))
       (term (,c ,v))]
      [`(Π (,x : ,(app eval t)) ,(app eval e))
       (term (Π (,x : ,t) ,e))]
      [`(λ (,x : ,t) ,(app eval e))
       (term (λ (,x : ,t) ,e))]
      [_ e])))

(define-metafunction tt-redL
  [(reduce Δ e)
   ,(cbv-eval (term Δ) (term e))])

;;; ------------------------------------------------------------------------
;;; Type checking and synthesis

(define-extended-language tt-typingL tt-redL
  ;; NB: There may be a bijection between Γ and Ξ. That's interesting.
  ;; NB: Also a bijection between Γ and a list of maps from x to t.
  (Γ   ::= ∅ (Γ x : t)))

(define-judgment-form tt-typingL
  #:mode (convert I I I I)

  [(side-condition ,(<= (term i_0) (term i_1)))
   ----------------- "≼-Unv"
   (convert Δ Γ (Unv i_0) (Unv i_1))]

  [(where (t t) ((reduce Δ t_0) (reduce Δ t_1)))
   ----------------- "≼-αβ"
   (convert Δ Γ t_0 t_1)]

  [(convert Δ (Γ x : t_0) t_1 t_2)
   ----------------- "≼-Π"
   (convert Δ Γ (Π (x : t_0) t_1) (Π (x : t_0) t_2))])

(define-metafunction tt-typingL
  [(Γ-in-dom ∅ x)
   #f]
  [(Γ-in-dom (Γ x : t) x)
   #t]
  [(Γ-in-dom (Γ x_!_0 : t) (name x x_!_0))
   (Γ-in-dom Γ x)])

(define-metafunction tt-typingL
  [(Γ-ref (Γ x : t) x)
   t]
  [(Γ-ref (Γ x_!_0 : t_0) (name x_1 x_!_0))
   (Γ-ref Γ x_1)])

;; Make ∈ Γ a little easier to use, prettier to render
(define-judgment-form tt-typingL
  #:mode (Γ-in I I O)

  [(side-condition (Γ-in-dom Γ x))
   (where t (Γ-ref Γ x))
   -------------------------------
   (Γ-in Γ x t)])

;; TODO: After reading https://coq.inria.fr/doc/Reference-Manual006.html#sec209, not convinced this is right.

(define-metafunction tt-typingL
  [(nonpositive x (in-hole Θ x))
   #t]
  [(nonpositive x (Π (x_0 : (in-hole Θ x)) t))
   #f]
  [(nonpositive x (Π (x_0 : t_0) t))
   ,(and (term (positive x t_0)) (term (nonpositive x t)))]
  [(nonpositive x t) #t])

(define-metafunction tt-typingL
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

  ;; NB TODO: Ignore the "positive" occurrence of D in the result; this is hacky way to do this
  [(side-condition (positive D (in-hole Ξ (Unv 0))))
   ---------------------------------------------------------
   (valid-constructor D (name t_c (in-hole Ξ (in-hole Θ D))))])

;; Holds when the signature Δ is valid
(define-judgment-form tt-typingL
  #:mode (valid I)

  [-------- "Valid-Empty"
   (valid ())]

  [(where Δ (any_r ...))
   (valid Δ)
   (type-infer Δ ∅ t_D U_D)
   (valid-constructor D t_c) ...
   (type-infer Δ (∅ D : t_D) t_c U_c) ...
   ----------------- "Valid-Inductive"
   (valid (any_r ... ((D : t_D) (c : t_c) ...)))])

;; Holds when the signature Δ and typing context Γ are well-formed.
(define-judgment-form tt-typingL
  #:mode (wf I I)

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

  [(wf Δ Γ)
   (unv-type U_0 U_1)
   ----------------- "DTR-Unv"
   (type-infer Δ Γ U_0 U_1)]

  [(Δ-type-in Δ x t)
   (wf Δ Γ)
   ----------------- "DTR-Inductive"
   (type-infer Δ Γ x t)]

  [(Δ-constr-in Δ x t)
   (wf Δ Γ)
   ----------------- "DTR-Constructor"
   (type-infer Δ Γ x t)]

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

  [(type-infer-normal Δ Γ e_c (in-hole Θ_i D))

   (type-infer-normal Δ Γ e_P t_B)
   (type-infer Δ Γ D t_D)
   (check-motive D t_D t_B)

   (where ((c : t_c) ...) (Δ-ref-constructor-map Δ D))
   (type-check Δ Γ e_m (method-type D hole c t_c e_P)) ...
   ----------------- "DTR-Elim_D"
   (type-infer Δ Γ (elim D e_P (e_m ...) e_c)
               ((in-hole Θ_i e_P) e_c))])

(define-judgment-form tt-typingL
  #:mode (check-motive I I I)

  [------------------------------------- "Type"
   (check-motive e U_1 (Π (x : e) U_2))]

  [(check-motive (e x) (substitute t_1 x_0 x) t_1^*)
   --------------------------------------------------------- "Prod"
   (check-motive e (Π (x_0 : t_0) t_1) (Π (x : t_0) t_1^*))])

(define-metafunction tt-ctxtL
  method-type : D Ξ e_c e_C t_p -> t
  [(method-type D Ξ e (in-hole Θ D) t_P)
   (in-hole Ξ ((in-hole Θ t_P) e))]
  ;; recursive argument; collect an additional inductive hypothesis
  [(method-type D Ξ e (name any (Π (x : (name t_0 (in-hole Φ (in-hole Θ D)))) t_1)) t_P)
   (Π (x : t_0)
      (method-type
       D
       ;; This is a dense line:
       ;; Add a new inductive hypothesis, x_h, to the end of the IH telescope Ξ.
       ;; This new inductive hypothesis has the type:
       ;; x_φ : t_φ -> ... -> (t_P i ... (x x_φ ...))
       ;; Where x_φ are arguments to the recursive instance of this inductive (implemented by Φ)
       ;; t_P is the motive
       ;; i ... are the indices (implemented by Θ)
       (in-hole Ξ (Π (x_h : (in-hole Φ ((in-hole Θ t_P) (Ξ-apply Φ x)))) hole))
       (e x) t_1 t_P))
   (where x_h ,(variable-not-in (term (D Ξ e t_P any)) 'x-ih))]
  ;; non-recursive argument; keep on going.
  [(method-type D Ξ e (Π (x : t_0) t_1) t_P)
   (Π (x : t_0) (method-type D Ξ (e x) t_1 t_P))])

(define-judgment-form tt-typingL
  #:mode (type-infer-normal I I I O)

  [(type-infer Δ Γ e t)
   ----------------- "DTR-Reduce"
   (type-infer-normal Δ Γ e (reduce Δ t))])

(define-judgment-form tt-typingL
  #:mode (type-check I I I I)

  [(type-infer Δ Γ e t_0)
   (convert Δ Γ t_0 t)
   ----------------- "DTR-Check"
   (type-check Δ Γ e t)])

#lang racket/base

(require
 "../snoc-env.rkt"
  racket/function
  racket/list
  redex/reduction-semantics)

(provide
  (all-defined-out))

(set-cache-size! 10000)
(check-redundancy #t)
;(current-traced-metafunctions '(wf type-infer type-check valid subtype))

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
  (n i j k  ::= natural)
  (U ::= (Unv i))
  (D x c ::= variable-not-otherwise-mentioned)
  (Γc  ::= ∅ (Γc (c : t)))
  (Δ   ::= ∅ (Δ (D : n t Γc)))
  ;; (elim inductive-type motive (methods ...) discriminant)
  (t e ::= U (λ (x : e) e) x (Π (x : e) e) (e e) (elim D e (e ...) e))
  #:binding-forms
  (λ (x : any) any_0 #:refers-to x)
  (Π (x : any) any_0 #:refers-to x))

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
  [(Δ-in-dom Δ D) (snoc-env-in-dom Δ D)])

(define-metafunction ttL
  Δ-in-constructor-dom : Δ c -> #t or #f
  [(Δ-in-constructor-dom Δ c)
   ,(for/fold ([r #f])
              ([e (term (snoc-env->als Δ))])
      #:break r
      (term (snoc-env-in-dom ,(last e) c)))])

(define-metafunction ttL
  Δ-ref-type : Δ_0 D_0 -> t
  #:pre (Δ-in-dom Δ_0 D_0)
  [(Δ-ref-type Δ D)
   t
   (where (D : _ t _) (snoc-env-ref Δ D))])

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
  [(Δ-key-by-constructor (Δ (D : _ _ Γc)) c)
   D
   (side-condition (term (snoc-env-in-dom Γc c)))]
  [(Δ-key-by-constructor (Δ _) c)
   (Δ-key-by-constructor Δ c)])

;; Returns the constructor map for the inductively defined type D in the signature Δ
(define-metafunction ttL
  Δ-ref-constructor-map : Δ_0 D_0 -> ((c : t) ...)
  #:pre (Δ-in-dom Δ_0 D_0)
  [(Δ-ref-constructor-map Δ D)
   ;; NB: Need to return in reverse-dependency order, while ->als returns in dependency order
   ,(reverse (term (snoc-env->als Γc)))
   (where (D : _ _ Γc) (snoc-env-ref Δ D))])

;; Return the type of the constructor c_i
(define-metafunction ttL
  Δ-ref-constructor-type : Δ_0 c_0 -> t
  #:pre (Δ-in-constructor-dom Δ_0 c_0)
  [(Δ-ref-constructor-type Δ c)
   t
   (where D (Δ-key-by-constructor Δ c))
   (where (D : _ _ Γc) (snoc-env-ref Δ D))
   (where (_ _ t) (snoc-env-ref Γc c))])

;; Make c : t ∈ Δ a little easier to use, prettier to render
(define-judgment-form ttL
  #:mode (Δ-constr-in I I O)
  #:contract (Δ-constr-in Δ c t)

  [(side-condition (Δ-in-constructor-dom Δ c))
   (where t (Δ-ref-constructor-type Δ c))
   -------------------------------
   (Δ-constr-in Δ c t)])

(define-metafunction ttL
  Δ-ref-by-constructor : Δ_0 c_0 -> (D : n t Γc)
  #:pre (Δ-in-constructor-dom Δ_0 c_0)
  [(Δ-ref-by-constructor Δ c)
   (snoc-env-ref Δ D)
   (where D (Δ-key-by-constructor Δ c))])

(define-metafunction ttL
  Δ-ref-constructors : Δ_0 D_0 -> (c ...)
  #:pre (Δ-in-dom Δ_0 D_0)
  [(Δ-ref-constructors Δ D)
   (c ...)
   (where ((c _ _) ...) (Δ-ref-constructor-map Δ D))])

(define-metafunction ttL
  Δ-ref-parameter-count : Δ_0 D_0 -> n
  #:pre (Δ-in-dom Δ_0 D_0)
  [(Δ-ref-parameter-count Δ D)
   n
   (where (D : n _ _) (snoc-env-ref Δ D))])

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
  Ξ-apply : Ξ any -> any
  [(Ξ-apply hole any) any]
  [(Ξ-apply (Π (x : t) Ξ) any) (Ξ-apply Ξ (any x))])

(define-metafunction tt-ctxtL
  Θ-flatten : Θ -> (e ...)
  [(Θ-flatten hole)
   ()]
  [(Θ-flatten (Θ e))
   (e_0 ... e)
   (where (e_0 ...) (Θ-flatten Θ))])

(define-metafunction tt-ctxtL
  Θ-length : Θ -> n
  [(Θ-length Θ)
   ,(length (term (Θ-flatten Θ)))])

(define-metafunction tt-ctxtL
  Θ-drop : Θ_0 n_0 -> Θ
  #:pre ,(<= (term n_0) (term (Θ-length Θ_0)))
  [(Θ-drop Θ 0)
   Θ]
  [(Θ-drop (in-hole Θ (hole e)) n)
   (Θ-drop Θ ,(sub1 (term n)))])

(define-metafunction tt-ctxtL
  Θ-take : Θ_0 n_0 -> Θ
  #:pre ,(<= (term n_0) (term (Θ-length Θ_0)))
  [(Θ-take Θ 0)
   hole]
  [(Θ-take (in-hole Θ (hole e)) n)
   (in-hole (Θ-take Θ ,(sub1 (term n))) (hole e))])

(define-metafunction tt-ctxtL
  take-parameters : Δ_0 D_0 Θ -> Θ
  #:pre (Δ-in-dom Δ_0 D_0)
  [(take-parameters Δ D Θ)
   (Θ-take Θ n)
   (where n (Δ-ref-parameter-count Δ D))])

(define-metafunction tt-ctxtL
  take-indices : Δ_0 D_0 Θ -> Θ
  #:pre (Δ-in-dom Δ_0 D_0)
  [(take-indices Δ D Θ)
   (Θ-drop Θ n)
   (where n (Δ-ref-parameter-count Δ D))])

;;; ------------------------------------------------------------------------
;;; Dynamic semantics
;;; The majority of this section is dedicated to evaluation of (elim x U), the eliminator for the
;;; inductively defined type x with a motive whose result is in universe U

(define-extended-language tt-redL tt-ctxtL
  (C-elim  ::= (elim D t_P (e_m ...) hole)))

(define-metafunction tt-ctxtL
  is-inductive-argument : Δ_0 D_0 t -> #t or #f
  #:pre (Δ-in-dom Δ_0 D_0)
  ;; Think this only works in call-by-value. A better solution would
  ;; be to check position of the argument w.r.t. the current
  ;; method. requires more arguments, and more though.
  [(is-inductive-argument Δ D (in-hole Θ c_i))
   ,(and (memq (term c_i) (term (Δ-ref-constructors Δ D))) #t)]
  [(is-inductive-argument _ _ _)
   #f])

;; Generate recursive applications of the eliminator for each inductive argument in Θ.
;; TODO TTEESSSSSTTTTTTTT
(define-metafunction tt-redL
  Δ-inductive-elim : Δ_0 D_0 C-elim Θ -> Θ
  #:pre (Δ-in-dom Δ_0 D_0)
  ;; NB: If metafunction fails, recursive
  ;; NB: elimination will be wrong. This will introduced extremely sublte bugs,
  ;; NB: inconsistency, failure of type safety, and other bad things.
  ;; NB: It should be tested and audited thoroughly
  [(Δ-inductive-elim _ ... hole)
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
           "β")
      (--> (elim D e_motive (e_m ...) (in-hole Θ_c c)) (in-hole Θ_mi e_mi)
           (side-condition/hidden (term (Δ-in-constructor-dom Δ c)))
           ;; Find the method for constructor c_i, relying on the order of the arguments.
           (where/hidden (c_i ...) (Δ-ref-constructors Δ D))
           (where/hidden (_ ... (c e_mi) _ ...) ((c_i e_m) ...))
           ;; Generate the inductive recursion
           (where/hidden Θ_ih (Δ-inductive-elim Δ D (elim D e_motive (e_m ...) hole) Θ_c))
           ;; Generate the method arguments, which are the constructor's arguments and the inductive arguments
           ;; Drop the parameters
           (where/hidden Θ_mi (in-hole Θ_ih (take-indices Δ D Θ_c)))
           "ι"))))

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

#;(define-metafunction tt-redL
  reduce : Δ e -> e
  [(reduce Δ e)
   ,(car (apply-reduction-relation* (tt-->cbv (term Δ)) (term e) #:cache-all? #t))])
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
                  [Θ_mi (term (in-hole Θ_ih (take-indices ,Δ ,D ,Θ)))])
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

(define-judgment-form tt-typingL
  #:mode (valid-parameters I I I)
  #:contract (valid-parameters n t t)

  [-------------------------------
   (valid-parameters 0 t_0 t_1)]

  [(side-condition ,(not (zero? (term n))))
   (valid-parameters ,(sub1 (term n)) t_0 t_1)
   -------------------------------------------------------
   (valid-parameters n (Π (x_0 : t) t_0) (Π (x_1 : t) t_1))])

;; Holds when the type t is a valid type for a constructor of D
(define-judgment-form tt-typingL
  #:mode (valid-constructors I I I)
  #:contract (valid-constructors (Δ (D : n t Γc)) Γ Γc)

  [--------------------------- "VC-Empty"
   (valid-constructors Δ Γ ∅)]

  [;; constructor's type must return the inductive type D
   (where (in-hole Ξ (in-hole Θ D)) t)
   ;; First n arguments (parameters) of the constructor must match those of the inductive
   (valid-parameters n t t_D)
   (side-condition (positive D (in-hole Ξ (Unv 0))))
   (type-infer Δ Γ t U)
   (valid-constructors Δ_0 (Γ c : t) Γc)
   -----------------------------------------------------------------"VC-C"
   (valid-constructors (name Δ_0 (Δ (D : n t_D _))) Γ (Γc (c : t)))])

;; Holds when the signature Δ is valid
(define-judgment-form tt-typingL
  #:mode (valid I)
  #:contract (valid Δ)

  [-------- "Valid-Empty"
   (valid ∅)]

  [(valid-constructors Δ_0 (∅ D : t_D) Γc)
   (type-infer Δ ∅ t_D U_D)
   (valid Δ)
   ----------------- "Valid-Inductive"
   (valid (name Δ_0 (Δ (D : n (name t_D (in-hole Ξ U)) Γc))))])

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

  [(unv-type U_0 U_1) (wf Δ Γ)
   ----------------- "Unv"
   (type-infer Δ Γ U_0 U_1)]

  [(Δ-type-in Δ D t) (wf Δ Γ)
   ----------------- "Inductive"
   (type-infer Δ Γ D t)]

  [(Δ-constr-in Δ c t) (wf Δ Γ)
   ----------------- "Constr"
   (type-infer Δ Γ c t)]

  [(Γ-in Γ x t) (wf Δ Γ)
   ----------------- "Var"
   (type-infer Δ Γ x t)]

  [(type-infer-normal Δ (Γ x : t_0) e t_1)
   (type-infer-normal Δ Γ (Π (x : t_0) t_1) U)
   ----------------- "Fun"
   (type-infer Δ Γ (λ (x : t_0) e) (Π (x : t_0) t_1))]

  [(type-infer Δ Γ t_0 U_1)
   (type-infer Δ (Γ x : t_0) t U_2)
   (unv-pred U_1 U_2 U)
   ----------------- "Prod"
   (type-infer Δ Γ (Π (x : t_0) t) U)]

  [(type-infer-normal Δ Γ e_0 (Π (x_0 : t_0) t_1))
   (type-check Δ Γ e_1 t_0)
   ----------------- "App"
   (type-infer Δ Γ (e_0 e_1) (substitute t_1 x_0 e_1))]

  [(type-infer-normal Δ Γ e_c (in-hole Θ D))
   (where n (Δ-ref-parameter-count Δ D))
   (where Θ_p (Θ-take Θ n))
   (where Θ_i (Θ-drop Θ n))

   (type-infer-normal Δ Γ e_P t_B)
   (type-infer Δ Γ (in-hole Θ_p D) t_D)
   (check-motive (in-hole Θ_p D) t_D t_B)

   (where (c ...) (Δ-ref-constructors Δ D))
   (type-infer-normal Δ Γ (in-hole Θ_p c) t_c) ...
   (where (t_m ...) ((reduce Δ (method-type n D hole (in-hole Θ_p c) t_c e_P)) ...))
   (type-check Δ Γ e_m t_m) ...
   ----------------- "Elim_D"
   (type-infer Δ Γ (elim D e_P (e_m ...) e_c) ((in-hole Θ_i e_P) e_c))])

;; Based on CIC spec "allowed elimination sorts"; except without the Set/Prop rules
;; NB: CIC notation is: [D:t_D|t_B]
(define-judgment-form ttL
  #:mode (check-motive I I I)
  #:contract (check-motive e t t)

  [------------------------------------- "Type"
   (check-motive e U_1 (Π (x : e) U_2))]

  [(check-motive (e x) (substitute t_1 x_0 x) t_1^*)
   --------------------------------------------------------- "Prod"
   (check-motive e (Π (x_0 : t_0) t_1) (Π (x : t_0) t_1^*))])

;; Based on CIC "type of branches", adjusted to handle recursion for folds
;; NB: CIC notation is: {c:C}ᴾ
(define-metafunction tt-ctxtL
  method-type : n D Ξ e_c e_C t_p -> t
  [(method-type n D Ξ e (in-hole Θ D) t_P)
   (in-hole Ξ ((in-hole (Θ-drop Θ n) t_P) e))]
  ;; recursive argument; collect an additional inductive hypothesis
  [(method-type n D Ξ e (name any (Π (x : (name t_0 (in-hole Φ (in-hole Θ D)))) t_1)) t_P)
   (Π (x : t_0)
      (method-type
       n
       D
       ;; This is a dense line:
       ;; Add a new inductive hypothesis, x_h, to the end of the IH telescope Ξ.
       ;; This new inductive hypothesis has the type:
       ;; x_φ : t_φ -> ... -> (t_P i ... (x x_φ ...))
       ;; Where x_φ are arguments to the recursive instance of this inductive (implemented by Φ)
       ;; t_P is the motive
       ;; i ... are the indices (implemented by (Θ-drop Θ n), with n parameters)
       (in-hole Ξ (Π (x_h : (in-hole Φ ((in-hole (Θ-drop Θ n) t_P) (Ξ-apply Φ x)))) hole))
       (e x) t_1 t_P))
   (where x_h ,(variable-not-in (term (D Ξ e t_P any)) 'x-ih))]
  ;; non-recursive argument; keep on going.
  [(method-type n D Ξ e (Π (x : t_0) t_1) t_P)
   (Π (x : t_0) (method-type n D Ξ (e x) t_1 t_P))])

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
   (subtype Δ Γ t_0 t)
   (type-infer Δ Γ t U)
   ----------------- "Conv"
   (type-check Δ Γ e t)])

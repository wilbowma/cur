#lang racket/base

(require
  redex/reduction-semantics)

#;(provide
  define-inductive-type
  match
  define-fun
  define-rec
  lambda)


;; References:
;; http://www3.di.uminho.pt/~mjf/pub/SFV-CIC-2up.pdf
;; https://www.cs.uoregon.edu/research/summerschool/summer11/lectures/oplss-herbelin1.pdf
;; http://www.emn.fr/z-info/ntabareau/papers/universe_polymorphism.pdf

;; Core language. Surface langauge should provide short-hand, such as
;; -> for non-dependent function types, and type inference.
(define-language dtracketL
  (i ::= natural)
  (U ::= Type (Unv i))
  (x ::= variable-not-otherwise-mentioned)
  ;; TODO: Having 2 binders is stupid.
  (v ::= (Π (x : t) t) (λ (x : t) t) x U)
  (t e ::= v (t t)))

(module+ test
  (require (except-in rackunit check))
  (check-true (redex-match? dtracketL U (term Type)))
  (check-true (redex-match? dtracketL U (term (Unv 0))))
  (check-true (redex-match? dtracketL e (term (λ (x_0 : (Unv 0)) x_0))))
  (check-true (redex-match? dtracketL v (term (λ (x_0 : (Unv 0)) x_0))))
  (check-true (redex-match? dtracketL t (term (λ (x_0 : (Unv 0)) x_0)))))

;; 'A'
;; Types of Universes
;; Replace with sub-typing
(define-judgment-form dtracketL
  #:mode (unv-ok I O)
  #:contract (unv-ok U U)

  [-----------------
   (unv-ok Type (Unv 0))]

  [(where i_2 ,(sub1 (term i_0)))
   (unv-ok (Unv i_2) (Unv i_3))
   (where i_1 ,(add1 (term i_3)))
   -----------------
   (unv-ok (Unv i_0) (Unv i_1))])

;; 'R'
;; Kinding, I think
(define-judgment-form dtracketL
  #:mode (unv-kind I I O)
  #:contract (unv-kind U U U)

  [----------------
   (unv-kind Type Type Type)]

  [----------------
   (unv-kind (Unv i) Type Type)]

  [(where i_3 ,(max (term i_1) (term i_2)))
   ----------------
   (unv-kind (Unv i_1) (Unv i_2) (Unv i_3))])

;; NB: Substitution is hard
(define-metafunction dtracketL
  subst : t x t -> t
  [(subst x x t) t]
  [(subst x_0 x t) x]
  [(subst (Π (x : t_0) t_1) x t) (Π (x : t_0) t_1)]
  [(subst (λ (x : t_0) t_1) x t) (λ (x : t_0) t_1)]
  [(subst (Π (x_0 : t_0) t_1) x t) (Π (x_0 : t_0) (subst t_1 x t))]
  [(subst (λ (x_0 : t_0) t_1) x t) (λ (x_0 : t_0) (subst t_1 x t))]
  [(subst (e_0 e_1) x t) ((subst e_0 x t) (subst e_1 x t))])

(define-extended-language dtracket-redL dtracketL
  (E hole (E t) (λ (x : t) E) (Π (x : t) E)))

;; TODO: Congruence-closure instead of β
(define ==β
  (reduction-relation dtracket-redL
    (==> ((Π (x : t_0) t_1) t_2)
         (subst t_1 x t_2))
    (==> ((λ (x : t) e_0) e_1)
         (subst e_0 x e_1))
    with
    [(--> (in-hole E t_0) (in-hole E t_1))
     (==> t_0 t_1)]))

(define-metafunction dtracket-redL
  reduce : e -> e
  [(reduce e) ,(car (apply-reduction-relation* ==β (term e)))])
(module+ test
  (check-equal? (term (reduce Type)) (term Type))
  (check-equal? (term (reduce ((λ (x : t) x) Type))) (term Type))
  (check-equal? (term (reduce ((Π (x : t) x) Type))) (term Type))
  (check-equal? (term (reduce (Π (x : t) ((Π (x_0 : t) x_0) Type))))
                (term (Π (x : t) Type)))
  (check-equal? (term (reduce (Π (x : t) ((Π (x_0 : t) x_0) x))))
                (term (Π (x : t) x))))

;; TODO: Bi-directional and inference?
;; http://www.cs.ox.ac.uk/ralf.hinze/WG2.8/31/slides/stephanie.pdf

(define-extended-language dtracket-typingL dtracketL
  (Γ ∅ (Γ x : t)))

;; NB: Depends on clause order
(define-metafunction dtracket-typingL
  lookup : Γ x -> t or #f
  [(lookup ∅ x) #f]
  [(lookup (Γ x : t) x) t]
  [(lookup (Γ x_0 : t_0) x_1) (lookup Γ x_1)])

;; NB: Depends on clause order
(define-metafunction dtracket-typingL
  remove : Γ x -> Γ
  [(remove ∅ x) ∅]
  [(remove (Γ x : t) x) Γ]
  [(remove (Γ x_0 : t_0) x_1) (remove Γ x_1)])

;; http://www.cs.ox.ac.uk/ralf.hinze/WG2.8/31/slides/stephanie.pdf
#;(define-judgment-form dtracket-typingL
  #:mode (synth I I O)
  #:contract (synth Γ t t)

  [(unv-ok U_0 U_1)
   ----------------- ;; DTR-SAxiom
   (synth ∅ U_0 U_1)]

  [(synth (remove Γ x) t U)
   ----------------- ;; DTR-SStart
   (synth (Γ x : t) x t)]

  [(synth Γ t t_1) (synth Γ t_0 U)
   ----------------- ;; DTR-SWeakening
   (synth (Γ x : t_0) t t_1)]

  [(check Γ e t)
   ----------------- ;; DTR-SSwitch
   (synth Γ (e : t) t)]

  [(synth Γ e_0 (Π (x : t_0) t_1))
   (check Γ e_1 t_0)
   ----------------- ;; DTR-Application
   (synth Γ (e_0 e_1) (subst t_1 x e_1))])

#;(define-judgment-form dtracket-typingL
  #:mode (check I I I)
  #:contract (check Γ t t)


  [(check (Γ x : t_0) e t_1)
   (synth Γ (Π (x : t_0) t_1) U)
   ----------------- ;; DTR-CAbstraction
   (check Γ (λ (x : t_0) e) (Π (x : t_0) t_1))]

  [(synth Γ t_0 U_1)
   (synth (Γ x : t_0) t U_2)
   (unv-kind U_1 U_2 U)
   ----------------- ;; DTR-CProduct
   (check Γ (Π (x : t_0) t) U)]

  [(check Γ t t_1) (synth Γ t_0 U)
   ----------------- ;; DTR-CWeakening
   (check (Γ x : t_0) t t_1)]

  [(synth Γ e t_1)
   (synth Γ t_0 U)
   (side-condition ,(term (first (apply-reduction-relation* ==β (term t_0) (term t_1)))))
   ----------------- ;; DTR-CConversion
   (check Γ e t_0)]

  [(synth Γ e t)
   ----------------- ;; DTR-CSwitch
   (check Γ e t)])

(define-judgment-form dtracket-typingL
  #:mode (types I I O)
  #:contract (types Γ e t)

  [(unv-ok U_0 U_1)
   ----------------- ;; DTR-Axiom
   (types ∅ U_0 U_1)]

  [(where t (lookup Γ x))
   (types (remove Γ x) t U)
   ----------------- ;; DTR-SStart
   (types Γ x t)]

  [(types Γ t t_1) (types Γ t_0 U)
   ----------------- ;; DTR-Weakening
   (types (Γ x : t_0) t t_1)]

  [(types Γ t_0 U_1)
   (types (Γ x : t_0) t U_2)
   (unv-kind U_1 U_2 U)
   ----------------- ;; DTR-Product
   (types Γ (Π (x : t_0) t) U)]

  [(types Γ e_0 (Π (x : t_0) t_1))
   (types Γ e_1 t_0)
   ----------------- ;; DTR-Application
   (types Γ (e_0 e_1) (subst t_1 x e_1))]

  [(types (Γ x : t_0) e t_1)
   (types Γ (Π (x : t_0) t_1) U)
   ----------------- ;; DTR-Abstraction
   (types Γ (λ (x : t_0) e) (Π (x : t_0) t_1))]

  ;; TODO: beta-equiv
  ;; This rule is no good for algorithmic checking; Redex infinitly
  ;; searches it.
  ;; Perhaps something closer to Zombies = type would be better.
  ;; For now, reduce types
  #;[(types Γ e (in-hole E t))
   (where t_0 (in-hole E t))
   (where t_1 ,(car (apply-reduction-relation* ==β (term t_0))))
   (types Γ t_1 U)
   ----------------- ;; DTR-Conversion
   (types Γ e t_1)])
(module+ test
  (check-true (judgment-holds (types ∅ Type (Unv 0))))
  (check-true (judgment-holds (types (∅ x : Type) Type (Unv 0))))
  (check-true (judgment-holds (types (∅ x : Type) x Type)))
  (check-true (judgment-holds (types ((∅ x_0 : Type) x_1 : Type)
                                     (Π (x_3 : x_0) x_1) Type)))

  (check-true (judgment-holds (types ∅ (λ (x : Type) x) (Π (x : Type) Type)))))

(define-judgment-form dtracket-typingL
  #:mode (type-check I I I)
  #:contract (type-check Γ e t)

  [(types Γ e t)
   ---------------
   (type-check Γ e (reduce t))])

;; Infer-core Language
;; A relaxed core where annotation are optional.
(define-extended-language dtracket-surfaceL dtracketL
  (v ::= .... (λ x e) (Π x e))
  (t e ::= .... (e : t)))

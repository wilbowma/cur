#lang racket/base

(require
  (only-in racket/set set=?)
  (only-in racket curry)
  redex/reduction-semantics)

#;(provide
  define-constructor-for
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
  (t e ::= (case e (x e) (x e)...) v (t t)))

(module+ test
  (require rackunit)
  (check-true (redex-match? dtracketL x (term T)))
  (check-true (redex-match? dtracketL x (term truth)))
  (check-true (redex-match? dtracketL x (term zero)))
  (check-true (redex-match? dtracketL x (term s)))
  (check-true (redex-match? dtracketL t (term zero)))
  (check-true (redex-match? dtracketL t (term s)))
  (check-true (redex-match? dtracketL t (term Type)))
  (check-true (redex-match? dtracketL x (term nat)))
  (check-true (redex-match? dtracketL t (term nat)))
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
  [(subst x_0 x t) x_0]
  [(subst (Π (x : t_0) t_1) x t) (Π (x : t_0) t_1)]
  [(subst (λ (x : t_0) t_1) x t) (λ (x : t_0) t_1)]
  [(subst (Π (x_0 : t_0) t_1) x t) (Π (x_0 : t_0) (subst t_1 x t))]
  [(subst (λ (x_0 : t_0) t_1) x t) (λ (x_0 : t_0) (subst t_1 x t))]
  [(subst (e_0 e_1) x t) ((subst e_0 x t) (subst e_1 x t))])
;; NB:
;; TODO: Why do I not have tests for substitutions?!?!?!?!?!?!?!!?!?!?!?!?!?!!??!?!

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
  (Σ Γ ::= ∅ (Γ x : t)))

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

(define-metafunction dtracket-typingL
  result-type : Σ t -> t or #f
  [(result-type Σ (Π (x : t) e)) (result-type Σ e)]
  [(result-type Σ x) ,(and (term (lookup Σ x)) (term x))]
  [(result-type Σ t) #f])
(module+ test
  (define Σ (term (((∅ nat : Type) zero : nat) s : (Π (x : nat) nat))))
  (check-equal? (term nat) (term (result-type ,Σ (Π (x : nat) nat))))
  (check-equal? (term nat) (term (result-type ,Σ nat))))

(define-judgment-form dtracket-typingL
  #:mode (constructor-for I I O)
  #:contract (constructor-for Σ t x)

  [(where t_0 (result-type Σ t))
   -------------
   (constructor-for (Σ x : t) t_0 x)]

  [(constructor-for Σ t_1 x)
   -------------
   (constructor-for (Σ x_0 : t_0) t_1 x)])
(module+ test
  (check-true
    (judgment-holds (constructor-for ((∅ truth : Type) T : truth) truth T)))
  (check-true
    (judgment-holds
      (constructor-for ((∅ nat : Type) zero : nat)
                       nat zero)))
  (check set=?
    (judgment-holds
      (constructor-for (((∅ nat : Type) zero : nat) s : (Π (x : nat) nat))
                       nat x) x)
    (list (term zero) (term s))))
(define-metafunction dtracket-typingL
  constructors-for : Σ t (x ...) -> #t or #f
  [(constructors-for Σ t (x ...))
   ,((lambda (x y) (and (set=? x y) (= (length x) (length y))))
     (term (x ...))
     (judgment-holds (constructor-for Σ t x_00) x_00))])
(module+ test
  (check-true
    (term (constructors-for (((∅ nat : Type) zero : nat) s : (Π (x : nat) nat))
                       nat (zero s))))
  (check-false
    (term (constructors-for (((∅ nat : Type) zero : nat) s : (Π (x : nat) nat))
                       nat (zero)))))

(define-metafunction dtracketL
  branch-type : t t t -> t
  [(branch-type t_ind (Π (x_0 : t) e_0) (Π (x_1 : t) e_1))
   (branch-type t_ind e_0 e_1)]
  [(branch-type t_ind t_ind t) t])
(module+ test
  (check-equal? (term Type) (term (branch-type nat (lookup ,Σ zero) Type)))
  (check-equal? (term nat) (term (branch-type nat nat nat)))
  (check-equal? (term Type) (term (branch-type nat (lookup ,Σ s) (Π (x : nat) Type)))))

(define-metafunction dtracket-typingL
  branch-types-match : Σ (x ...) (t ...) t t -> #t or #f
  [(branch-types-match Σ (x ...) (t_11 ...) t t_1)
   ,(andmap (curry equal? (term t)) (term ((branch-type t_1 (lookup Σ x) t_11) ...)))])
(module+ test
  (check-true
    (term (branch-types-match ((∅ truth : Type) T : truth) () () Type nat)))
  (check-true
    (term (branch-types-match ,Σ (zero s) (Type (Π (x : nat) Type)) Type nat)))
  (check-true
    (term (branch-types-match ,Σ (zero s) (nat (Π (x : nat) nat)) nat nat))))

(define-judgment-form dtracket-typingL
  #:mode (wf I I)
  #:contract (wf Σ Γ)

  [-----------------
   (wf ∅ ∅)]

  [(types Σ Γ t U)
   -----------------
   (wf Σ (Γ x : t))]

  [(types Σ ∅ t U)
   -----------------
   (wf (Σ x : t) ∅)])
(module+ test
  (check-true (judgment-holds (wf ∅ ∅)))
  (check-true (judgment-holds (wf (∅ truth : Type) ∅)))
  (check-true (judgment-holds (wf ∅ (∅ x : Type))))
  (check-true (judgment-holds (wf (∅ nat : Type) (∅ x : nat))))
  (check-true (judgment-holds (wf (∅ nat : Type) (∅ x : (Π (x : nat) nat))))))

(define-judgment-form dtracket-typingL
  #:mode (types I I I O)
  #:contract (types Σ Γ e t)

  [(unv-ok U_0 U_1)
   (wf Σ Γ)
   ----------------- "DTR-Axiom"
   (types Σ Γ U_0 U_1)]

  [(where t (lookup Σ x))
   ----------------- "DTR-Inductive"
   (types Σ Γ x t)]

  [(where t (lookup Γ x))
   ----------------- "DTR-Start"
   (types Σ Γ x t)]

  [(types Σ Γ t_0 U_1)
   (types Σ (Γ x : t_0) t U_2)
   (unv-kind U_1 U_2 U)
   ----------------- "DTR-Product"
   (types Σ Γ (Π (x : t_0) t) U)]

  [(types Σ Γ e_0 (Π (x : t_0) t_1))
   (types Σ Γ e_1 t_0)
   ----------------- "DTR-Application"
   (types Σ Γ (e_0 e_1) (subst t_1 x e_1))]

  [(types Σ (Γ x : t_0) e t_1)
   (types Σ Γ (Π (x : t_0) t_1) U)
   ----------------- "DTR-Abstraction"
   (types Σ Γ (λ (x : t_0) e) (Π (x : t_0) t_1))]

  [(types Σ Γ e t_1)
   (side-condition (constructors-for Σ t_1 (x_0 x_1 ...)))
   (types Σ Γ e_0 t_00)
   (types Σ Γ e_1 t_11) ...
   ;; TODO Some of these meta-functions aren't very consistent in terms
   ;; of interface
   (where t (branch-type t_1 (lookup Σ x_0) t_00))
   (side-condition (branch-types-match Σ (x_1 ...) (t_11 ...) t t_1))
   ----------------- "DTR-Case"
   (types Σ Γ (case e (x_0 e_0) (x_1 e_1) ...) t)]

  ;; TODO: beta-equiv
  ;; This rule is no good for algorithmic checking; Redex infinitly
  ;; searches it.
  ;; Perhaps something closer to Zombies = type would be better.
  ;; For now, reduce types
  #;[(types Γ e (in-hole E t))
   (where t_0 (in-hole E t))
   (where t_1 ,(car (apply-reduction-relation* ==β (term t_0))))
   (types Γ t_1 U)
   ----------------- "DTR-Conversion"
   (types Γ e t_1)])
(module+ test
  (check-true (judgment-holds (types ∅ ∅ Type (Unv 0))))
  (check-true (judgment-holds (types ∅ (∅ x : Type) Type (Unv 0))))
  (check-true (judgment-holds (types ∅ (∅ x : Type) x Type)))
  (check-true (judgment-holds (types ∅ ((∅ x_0 : Type) x_1 : Type)
                                     (Π (x_3 : x_0) x_1) Type)))

  (check-true (judgment-holds (types ∅ ∅ (λ (x : Type) x) (Π (x : Type) Type))))
  (check-true (judgment-holds (types ∅ ∅ (λ (y : Type) (λ (x : y) x))
                                     (Π (y : Type) (Π (x : y) y)))))
  (check-true
    (judgment-holds (types ((∅ truth : Type) T : truth)
                           ∅
                           T
                           truth)))
  (check-true
    (judgment-holds (types ((∅ truth : Type) T : truth)
                           ∅
                           Type
                           (Unv 0))))
  (check-true
    (judgment-holds (types ((∅ truth : Type) T : truth)
                           ∅
                           (case T (T Type))
                           (Unv 0))))

  (check-false
    (judgment-holds (types ((∅ truth : Type) T : truth)
                           ∅
                           (case T (T Type) (T Type))
                           (Unv 0))))
  (define-syntax-rule (nat-test syn ...)
    (check-true (judgment-holds
                  (types (((∅ nat : Type) zero : nat) s : (Π (x : nat) nat))
                         syn ...))))
  (nat-test ∅ (Π (x : nat) nat) Type)
  (nat-test ∅ (λ (x : nat) x) (Π (x : nat) nat))
  (nat-test ∅ (case zero (zero zero) (s (λ (x : nat) x)))
            nat)
  (nat-test ∅ nat Type)
  (nat-test ∅ zero nat)
  (nat-test ∅ s (Π (x : nat) nat))
  (nat-test ∅ (s zero) nat)
  (nat-test ∅ (case zero (zero (s zero)) (s (λ (x : nat) (s (s x)))))
            nat)
  (nat-test ∅ (case zero (zero (s zero)) (s (λ (x : nat) (s (s x)))))
            nat)
  (check-false (judgment-holds
                  (types (((∅ nat : Type) zero : nat) s : (Π (x : nat) nat))
                         ∅
                         (case zero (zero (s zero)))
                         nat))))

(define-judgment-form dtracket-typingL
  #:mode (type-check I I I)
  #:contract (type-check Γ e t)

  [(types Σ ∅ e t)
   ---------------
   (type-check Σ e (reduce t))])

;; Infer-core Language
;; A relaxed core where annotation are optional.
(define-extended-language dtracket-surfaceL dtracketL
  (v ::= .... (λ x e) (Π t e))
  (t e ::= .... (data x (x : t) (x : t) ...) (case e ([e e] ...)) (e : t)))

;; http://www.cs.ox.ac.uk/ralf.hinze/WG2.8/31/slides/stephanie.pdf
#;(define-judgment-form dtracket-typingL
  #:mode (synth I I O)
  #:contract (synth Γ t t)

  [(unv-ok U_0 U_1)
   ----------------- "DTR-SAxiom"
   (synth ∅ U_0 U_1)]

  [(where t (lookup Γ x))
   (synth (remove Γ x) t U)
   ----------------- "DTR-SStart"
   (synth Γ x t)]

  [(synth Γ t t_1) (synth Γ t_0 U)
   ----------------- "DTR-SWeakening"
   (synth (Γ x : t_0) t t_1)]

  [(check (Γ x : t_0) e t_1)
   ----------------- "DTR-SAbstraction"
   (check Γ (λ (x : t_0) e) (Π (x : t_0) t_1))]

  [(synth Γ e_0 (Π (x : t_0) t_1))
   (check Γ e_1 t_0)
   ----------------- "DTR-SApplication"
   (synth Γ (e_0 e_1) (subst t_1 x e_1))]

  [(check Γ e t)
   ----------------- "DTR-SAnnotate"
   (synth Γ (e : t) t)])

#;(define-judgment-form dtracket-typingL
  #:mode (check I I I)
  #:contract (check Γ t t)

  [(check (Γ x : t_0) e t_1)
   ----------------- "DTR-Abstraction"
   (check Γ (λ x e) (Π (x : t_0) t_1))]

  [(synth Γ e t)
   ----------------- "DTR-SSynth"
   (check Γ e t)])
#;(module+ test
  (check-equal?
    (list (term (Unv 0)))
    (judgment-holds (synth ∅ Type U) U))
  (check-equal?
    (list (term Unv 0))
    (judgment-holds (synth (∅ x : Type) Type U)))
  (check-equal?
    (list (term Type))
    (judgment-holds (synth (∅ x : Type) x U)))
  (check-equal?
    (list (term Type))
    (judgment-holds (synth ((∅ x_0 : Type) x_1 : Type) (Π (x_3 : x_0) x_1) U)))

  (check-equal?
    (list ())
    (judgment-holds (synth ∅ (λ (x : Type) x) (Π (x : Type) Type))))
  (check-true (judgment-holds (types ∅ (λ (y : Type) (λ (x : y) x))
                                     (Π (y : Type) (Π (x : y) y))))))

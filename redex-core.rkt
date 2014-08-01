#lang racket

;; This module contains a model of CIC, ish.
;; TODO: Strip to racket/base as much as possible
(module core racket
  (require
    (only-in racket/set set=?)
    redex/reduction-semantics)
  (provide
    (all-defined-out))

  ;; References:
  ;; http://www3.di.uminho.pt/~mjf/pub/SFV-CIC-2up.pdf
  ;; https://www.cs.uoregon.edu/research/summerschool/summer11/lectures/oplss-herbelin1.pdf
  ;; http://www.emn.fr/z-info/ntabareau/papers/universe_polymorphism.pdf

  ;; Core language. Surface langauge should provide short-hand, such as
  ;; -> for non-dependent function types, and type inference.
  (define-language cicL
    (i ::= natural)
    (U ::= Type (Unv i))
    (x ::= variable-not-otherwise-mentioned)
    ;; TODO: Having 2 binders is stupid.
    (v ::= (Π (x : t) t) (λ (x : t) t) x U)
    (t e ::= (case e (x e) (x e)...) v (t t)))

  (module+ test
    (require rackunit)
    (define x? (redex-match? cicL x))
    (define t? (redex-match? cicL t))
    (define e? (redex-match? cicL e))
    (define v? (redex-match? cicL v))
    (define U? (redex-match? cicL U))
    (check-true (x? (term T)))
    (check-true (x? (term truth)))
    (check-true (x? (term zero)))
    (check-true (x? (term s)))
    (check-true (t? (term zero)))
    (check-true (t? (term s)))
    (check-true (t? (term Type)))
    (check-true (x? (term nat)))
    (check-true (t? (term nat)))
    (check-true (U? (term Type)))
    (check-true (U? (term (Unv 0))))
    (check-true (e? (term (λ (x_0 : (Unv 0)) x_0))))
    (check-true (v? (term (λ (x_0 : (Unv 0)) x_0))))
    (check-true (t? (term (λ (x_0 : (Unv 0)) x_0))))
    (check-true (t? (term (λ (x_0 : (Unv 0)) x_0))))
    )

  ;; 'A'
  ;; Types of Universes
  ;; Replace with sub-typing
  (define-judgment-form cicL
    #:mode (unv-ok I O)
    #:contract (unv-ok U U)

    [-----------------
     (unv-ok Type (Unv 0))]

    [(where i_1 ,(add1 (term i_0)))
     -----------------
     (unv-ok (Unv i_0) (Unv i_1))])

  ;; 'R'
  ;; Kinding, I think
  (define-judgment-form cicL
    #:mode (unv-kind I I O)
    #:contract (unv-kind U U U)

    [----------------
     (unv-kind Type Type Type)]

    [----------------
     (unv-kind Type (Unv i) (Unv i))]

    [----------------
     (unv-kind (Unv i) Type Type)]

    [(where i_3 ,(max (term i_1) (term i_2)))
     ----------------
     (unv-kind (Unv i_1) (Unv i_2) (Unv i_3))])

  ;; NB: Substitution is hard
  (define-metafunction cicL
    subst-vars : (x any) ... any -> any
    [(subst-vars (x_1 any_1) x_1) any_1]
    [(subst-vars (x_1 any_1) (any_2 ...)) ((subst-vars (x_1 any_1) any_2) ...)]
    [(subst-vars (x_1 any_1) any_2) any_2]
    [(subst-vars (x_1 any_1) (x_2 any_2) ... any_3) (subst-vars (x_1 any_1) (subst-vars (x_2 any_2) ... any_3))]
    [(subst-vars any) any])

  (define-metafunction cicL
    subst : t x t -> t
    [(subst U x t) U]
    [(subst x x t) t]
    [(subst x_0 x t) x_0]
    [(subst (Π (x : t_0) t_1) x t) (Π (x : (subst t_0 x t)) t_1)]
    [(subst (λ (x : t_0) t_1) x t) (λ (x : (subst t_0 x t)) t_1)]
    ;; TODO: Broken: needs capture avoiding, but currently require
    ;; binders to be the same in term/type, so this is not a local
    ;; change.
    [(subst (Π (x_0 : t_0) t_1) x t) (Π (x_0 : (subst t_0 x t)) (subst t_1 x t)) ]
    [(subst (λ (x_0 : t_0) t_1) x t) (λ (x_0 : (subst t_0 x t)) (subst t_1 x t))]
    [(subst (e_0 e_1) x t) ((subst e_0 x t) (subst e_1 x t))]
    [(subst (case e (x_0 e_0) ...) x t)
     (case (subst e x t)
       (x_0 (subst e_0 x t)) ...)])
  (module+ test
    (check-equal?
      (term (Π (a : S) (Π (b : B) ((and S) B))))
      (term (subst (Π (a : A) (Π (b : B) ((and A) B))) A S))))
  ;; NB:
  ;; TODO: Why do I not have tests for substitutions?!?!?!?!?!?!?!!?!?!?!?!?!?!!??!?!

  (define-extended-language cic-redL cicL
    (E hole (E t) (λ (x : t) E) (Π (x : t) E)))

  (define-metafunction cicL
    inductive-name : t -> x
    [(inductive-name x) x]
    [(inductive-name (t_1 t_2)) (inductive-name t_1)])
  (module+ test
    (check-equal?
      (term and)
      (term (inductive-name ((and A) B)))))

  (define-metafunction cicL
    inductive-apply : t t -> t
    [(inductive-apply e x) e]
    [(inductive-apply e (e_1 e_2))
     ((inductive-apply e e_1) e_2)])

  ;; TODO: Congruence-closure instead of β
  (define ==β
    (reduction-relation cic-redL
      (==> ((Π (x : t_0) t_1) t_2)
           (subst t_1 x t_2))
      (==> ((λ (x : t) e_0) e_1)
           (subst e_0 x e_1))
      (==> (case e_9
             (x_0 e_0) ... (x e) (x_r e_r) ...)
           (inductive-apply e e_9)
           (where x (inductive-name e_9))
           )
      with
      [(--> (in-hole E t_0) (in-hole E t_1))
       (==> t_0 t_1)]))

  (define-metafunction cic-redL
    reduce : e -> e
    [(reduce e) ,(car (apply-reduction-relation* ==β (term e)))])
  (module+ test
    (check-equal? (term (reduce Type)) (term Type))
    (check-equal? (term (reduce ((λ (x : t) x) Type))) (term Type))
    (check-equal? (term (reduce ((Π (x : t) x) Type))) (term Type))
    (check-equal? (term (reduce (Π (x : t) ((Π (x_0 : t) x_0) Type))))
                  (term (Π (x : t) Type)))
    (check-equal? (term (reduce (Π (x : t) ((Π (x_0 : t) x_0) x))))
                  (term (Π (x : t) x)))
    (check-equal? (term (reduce (case (s z) (z (s z)) (s (λ (x : nat)
                                                            (s (s x)))))))
                  (term (s (s z))))
    (check-equal? (term (reduce (case (s (s (s z))) (z (s z)) (s (λ (x : nat)
                                                            (s (s x)))))))
                  (term (s (s (s (s z))))))
    )

  ;; TODO: Bi-directional and inference?
  ;; http://www.cs.ox.ac.uk/ralf.hinze/WG2.8/31/slides/stephanie.pdf

  (define-extended-language cic-typingL cicL
    (Σ Γ ::= ∅ (Γ x : t)))

  ;; NB: Depends on clause order
  (define-metafunction cic-typingL
    lookup : Γ x -> t or #f
    [(lookup ∅ x) #f]
    [(lookup (Γ x : t) x) t]
    [(lookup (Γ x_0 : t_0) x_1) (lookup Γ x_1)])

  ;; NB: Depends on clause order
  (define-metafunction cic-typingL
    remove : Γ x -> Γ
    [(remove ∅ x) ∅]
    [(remove (Γ x : t) x) Γ]
    [(remove (Γ x_0 : t_0) x_1) (remove Γ x_1)])

  (define-metafunction cic-typingL
    result-type : Σ t -> t or #f
    [(result-type Σ (Π (x : t) e)) (result-type Σ e)]
    [(result-type Σ x) ,(and (term (lookup Σ x)) (term x))]
    [(result-type Σ t) #f])
  (module+ test
    (define Σ (term (((∅ nat : Type) zero : nat) s : (Π (x : nat) nat))))
    (check-equal? (term nat) (term (result-type ,Σ (Π (x : nat) nat))))
    (check-equal? (term nat) (term (result-type ,Σ nat))))

  (define-judgment-form cic-typingL
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
  (define-metafunction cic-typingL
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

  (define-metafunction cicL
    branch-type : t t t -> t
    [(branch-type t_ind (Π (x_0 : t) e_0) (Π (x_1 : t) e_1))
     (branch-type t_ind e_0 e_1)]
    ;[(branch-type t_ind t_ind t) t])
    [(branch-type t_ind t_other t) t])
  (module+ test
    (check-equal? (term Type) (term (branch-type nat (lookup ,Σ zero) Type)))
    (check-equal? (term nat) (term (branch-type nat nat nat)))
    (check-equal? (term Type) (term (branch-type nat (lookup ,Σ s) (Π (x : nat) Type))))
    (define Σ3 (term (∅ and : (Π (A : Type) (Π (B : Type) Type)))))
    (define Σ4 (term (,Σ3 conj : (Π (A : Type) (Π (B : Type) (Π (a : A) (Π (b : B) ((and A) B))))))))
    (define Σ? (redex-match? cic-typingL Σ))
    (check-true (Σ? Σ3))
    (check-true (Σ? Σ4))

    (check-equal?
      (term Type)
      (term (branch-type and (lookup ,Σ4 conj)
              (Π (A : Type) (Π (B : Type) (Π (a : A) (Π (b : B) Type))))))))

  (define-metafunction cic-typingL
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

  ;; TODO: I'm pretty sure this is wrong
  (define-metafunction cicL
    positive : t any -> #t or #f
    ;; Type; not a inductive constructor
    [(positive t any) #t]
    ;; nat
    [(positive x_0 x_0) #t]
    ;; nat -> t_1 ... -> nat
    [(positive (Π (x : x_1) t_1) x_0)
     (positive t_1 x_0)]
    ;; Type -> t_1 ... -> nat
    [(positive (Π (x : U) t_1) any)
     (positive t_1 any)]
    ;; (t_0 -> t_2) -> t_1 ... -> nat
    [(positive (Π (x : (Π (x_1 : t_0) t_2)) t_1) x_0)
     ,(and (term (copositive (Π (x_1 : t_0) t_2) x_0)) (term (positive t_1 x_0)))])

  (define-metafunction cicL
    copositive : t any -> #t or #f
    [(copositive U any) #t]
    [(copositive x_0 x_0) #f]
    [(copositive (Π (x : x_0) t_1) x_0) #f]
    ;; x_1 -> t_1 ... -> nat
    [(copositive (Π (x : x_1) t_1) x_0)
     (positive t_1 x_0)]
    [(copositive (Π (x : U) t_1) x_0)
     (positive t_1 x_0)]
    [(copositive (Π (x : (Π (x_1 : t_0) t_2)) t_1) x_0)
     ,(and (term (positive (Π (x_1 : t_0) t_2) x_0)) (term (copositive t_1 x_0)))])

  (module+ test
    (check-true (term (positive nat nat)))
    (check-true (term (positive (Π (x : Type) (Π (y : Type) Type)) #f)))
    (check-true (term (positive (Π (x : nat) nat) nat)))
    ;; (nat -> nat) -> nat
    ;; Not sure if this is actually supposed to pass
    (check-false (term (positive (Π (x : (Π (y : nat) nat)) nat) nat)))
    ;; (Type -> nat) -> nat
    (check-true (term (positive (Π (x : (Π (y : Type) nat)) nat) nat)))
    ;; (((nat -> Type) -> nat) -> nat)
    (check-true (term (positive (Π (x : (Π (y : (Π (x : nat) Type)) nat)) nat) nat)))
    ;; Not sure if this is actually supposed to pass
    (check-false (term (positive (Π (x : (Π (y : (Π (x : nat) nat)) nat)) nat) nat)))

    (check-true (term (positive Type #f)))
    )

  (define-judgment-form cic-typingL
    #:mode (wf I I)
    #:contract (wf Σ Γ)

    [-----------------
     (wf ∅ ∅)]

    [(types Σ Γ t t_0)
     (wf Σ Γ)
     -----------------
     (wf Σ (Γ x : t))]

    [(types Σ ∅ t t_0)
     (wf Σ ∅)
     (side-condition (positive t (result-type Σ t)))
     -----------------
     (wf (Σ x : t) ∅)])
  (module+ test
    (check-true (judgment-holds (wf ∅ ∅)))
    (check-true (judgment-holds (wf (∅ truth : Type) ∅)))
    (check-true (judgment-holds (wf ∅ (∅ x : Type))))
    (check-true (judgment-holds (wf (∅ nat : Type) (∅ x : nat))))
    (check-true (judgment-holds (wf (∅ nat : Type) (∅ x : (Π (x : nat) nat))))))

  (define-judgment-form cic-typingL
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

    [(types Σ Γ e_0 (Π (x_0 : t_0) t_1))
     (types Σ Γ e_1 t_0)
     ----------------- "DTR-Application"
     (types Σ Γ (e_0 e_1) (subst t_1 x_0 e_1))]

    ;; TODO: This restriction that the names be the same is a little annoying
    [(types Σ (Γ x : t_0) e t_1)
     (types Σ Γ (Π (x : t_0) t_1) U)
     ----------------- "DTR-Abstraction"
     (types Σ Γ (λ (x : t_0) e) (Π (x : t_0) t_1))]

    [(types Σ Γ e t_9)
     (where t_1 (inductive-name t_9))
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

    (check-true (judgment-holds (types ∅ (∅ x_0 : Type) x_0 U_1)))
    (check-true (judgment-holds (types ∅ ((∅ x_0 : Type) x_2 : x_0) Type U_2)))
    (check-true (judgment-holds (unv-kind Type (Unv 0) (Unv 0))))
    (check-true (judgment-holds (types ∅ (∅ x_0 : Type) (Π (x_2 : x_0) Type) t)))

    (check-true (judgment-holds (types ∅ ∅ (λ (x : Type) x) (Π (x : Type) Type))))
    (check-true (judgment-holds (types ∅ ∅ (λ (y : Type) (λ (x : y) x))
                                       (Π (y : Type) (Π (x : y) y)))))

    (check-equal? (list (term (Unv 0)))
      (judgment-holds
        (types ∅ ((∅ x1 : Type) x2 : Type) (Π (t6 : x1) (Π (t2 : x2) Type))
               U)
        U))
    (check-true
      (judgment-holds
        (types ∅ ∅ (Π (x2 : Type) (Unv 0))
               U)))
    (check-true
      (judgment-holds
        (types ∅ (∅ x1 : Type) (λ (x2 : Type) (Π (t6 : x1) (Π (t2 : x2) Type)))
               t)))
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
                           nat)))
    (define Σ0 (term ∅))
    (define lam (term (λ (nat : Type) nat)))
    (check-equal?
      (list (term (Π (nat : Type) Type)))
      (judgment-holds (types ,Σ0 ∅ ,lam t) t))
    (define Σ2 (term (((∅ nat : Type) z : nat) s : (Π (x : nat) nat))))
    (check-equal?
      (list (term (Π (nat : Type) Type)))
      (judgment-holds (types ,Σ2 ∅ ,lam t) t))
    (check-equal?
      (list (term (Π (x : (Π (y : Type) y)) nat)))
      (judgment-holds (types (∅ nat : Type) ∅ (λ (x : (Π (y : Type) y)) (x nat))
                            t) t))
    (check-equal?
      (list (term (Π (y : Type) Type)))
      (judgment-holds (types (∅ nat : Type) ∅ (λ (y : Type) y) t) t))
    (check-equal?
      (list (term Type))
      (judgment-holds (types (∅ nat : Type) ∅
                            ((λ (x : (Π (y : Type) Type)) (x nat))
                             (λ (y : Type) y))
                            t) t))
    (check-equal?
      (list (term Type))
      (judgment-holds
        (types ,Σ4 ∅ (Π (S : Type) (Π (B : Type) (Π (a : S) (Π (b : B) ((and S) B)))))
               U) U))
    (check-true
      (judgment-holds (types ,Σ4 (∅ S : Type) conj (Π (A : Type) (Π (B : Type) (Π (a : A) (Π (b : B) ((and A) B))))))))
    (check-true
      (judgment-holds (types ,Σ4 (∅ S : Type) S Type)))
    (check-true
      (judgment-holds (types ,Σ4 (∅ S : Type) (conj S)
                             (Π (B : Type) (Π (a : S) (Π (b : B) ((and S) B)))))))
    (check-true
      (judgment-holds (types ,Σ4 (∅ S : Type) (conj S)
                             (Π (B : Type) (Π (a : S) (Π (b : B) ((and S) B)))))))
    ;; Failing due to lack of unification of case branches
    (check-true
      (judgment-holds (types ,Σ4 ∅ (λ (S : Type) (conj S))
                             (Π (S : Type) (Π (B : Type) (Π (a : S) (Π (b : B) ((and S) B))))))))
    (check-true
      (judgment-holds (types ((,Σ4 true : Type) tt : true) ∅
                             (case ((((conj true) true) tt) tt)
                               (conj (λ (A : Type)
                                        (λ (B : Type)
                                           (λ (a : A)
                                              (λ (b : B) a))))))
                             t) t))
    (define sigma (term (((((((∅ true : Type) T : true) false : Type) equal : (Π (A : Type)
                                                              (Π (B : Type) Type)))
        nat : Type) heap : Type) pre : (Π (temp808 : heap) Type))))
    (define gamma (term (∅ temp863 : pre)))
    (check-true (judgment-holds (wf ,sigma ∅)))
    (check-true (judgment-holds (wf ,sigma ,gamma)))
    (check-true
      (judgment-holds (types ,sigma ,gamma Type t)))
    (check-true
      (judgment-holds (types ,sigma ,gamma pre t)))
    (check-true
      (judgment-holds (types ,sigma (,gamma tmp863 : pre) Type (Unv 0)))))


  (define-judgment-form cic-typingL
    #:mode (type-check I I I)
    #:contract (type-check Γ e t)

    [(types Σ ∅ e t)
     ---------------
     (type-check Σ e (reduce t))])

  ;; Infer-core Language
  ;; A relaxed core where annotation are optional.
  (define-extended-language cic-surfaceL cicL
    (v ::= .... (λ x e) (Π t e))
    (t e ::= .... (data x (x : t) (x : t) ...) (case e ([e e] ...)) (e : t)))

  ;; http://www.cs.ox.ac.uk/ralf.hinze/WG2.8/31/slides/stephanie.pdf
  #;(define-judgment-form cic-typingL
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
     (synth Γ (e : t) t)]) )

;; This module just provide module language sugar over the redex model.

;; TODO: Strip to racket/base as much as possible.
;; TODO: Remove trace,pretty, debugging stuff
(module sugar racket
  (require
    racket/trace
    racket/pretty
    (submod ".." core)
    redex/reduction-semantics
    (for-syntax
      racket
      racket/pretty
      racket/trace
      (except-in (submod ".." core) remove)
      redex/reduction-semantics))
  (provide
    ;; Basic syntax
    begin-for-syntax
    #%module-begin
    #%datum
    require
    for-syntax
    (rename-out
      [dep-lambda lambda]
      [dep-lambda λ]
      [dep-app #%app]

      [dep-forall forall]
      [dep-forall ∀]

      [dep-inductive data]
      [dep-case case]

      [dep-var #%top])
    ;; DYI syntax extension
    define-syntax
    (rename-out [dep-define define])
    syntax-case
    syntax-rules
    define-syntax-rule
    (for-syntax (all-from-out racket)))

  (begin-for-syntax
    (current-trace-notify
      (parameterize ([pretty-print-depth #f]
                     [pretty-print-columns 'infinity])
        (lambda (x)
          (pretty-display x)
          (newline))))
    (current-trace-print-args
      (let ([cwtpr (current-trace-print-args)])
        (lambda (s l kw l2 n)
          (cwtpr s (map syntax->datum l) kw l2 n))))
    (current-trace-print-results
      (let ([cwtpr (current-trace-print-results)])
        (lambda (s l n)
         (cwtpr s (map syntax->datum l) n)))))

  ;; WEEEEEEE
  (define gamma
    (make-parameter (term ∅)
      (lambda (x)
        (unless (redex-match? cic-typingL Γ x)
          (error 'core-error "We build a bad gamma ~s" x))
        x)))
  (define sigma
    (make-parameter (term ∅)#;(term (((∅ nat : Type) z : nat) s : (Π (x : nat) nat)))
      (lambda (x)
        (unless (redex-match? cic-typingL Σ x)
          (error 'core-error "We build a bad sigma ~s" x))
        x)))

  (define-syntax (dep-lambda syn)
    (syntax-case syn (:)
      [(_ (x : t) e)
       #`(let* ([lam (term (λ (x : ,t)
                              ,(let ([x (term x)])
                                 (parameterize ([gamma (term (,(gamma) ,x : ,t))])
                                   e))))])
           (unless (judgment-holds (types ,(sigma) ,(gamma) ,lam t_0))
             (error 'type-checking "Term is ill-typed: ~s" lam))
           lam)]))

  (define-syntax (curry-app syn)
    (syntax-case syn ()
      [(_ e1 e2) #'(term (,e1 ,e2))]
      [(_ e1 e2 e3 ...)
       #'(curry-app (term (,e1 ,e2)) e3 ...)]))

  (define-syntax (dep-app syn)
    (syntax-case syn ()
      [(_ e1 e2 ...)
       #'(term (reduce ,(curry-app e1 e2 ...))) ]))

  (define-syntax-rule (dep-case e (x0 e0) ...)
    (term (reduce (case ,e (,x0 ,e0) ...))))

  (define-syntax (dep-inductive syn)
    (syntax-case syn (:)
      [(_ i : ti (x1 : t1) ...)
       #'(begin
           (sigma (term (,(sigma) i : ,ti)))
           (for ([x (list (term x1) ...)]
                 [t (list (term ,t1) ...)])
             (sigma (term (,(sigma) ,x : ,t)))))]))

  ;; TODO: Lots of shared code with dep-lambda
  (define-syntax (dep-forall syn)
    (syntax-case syn (:)
      [(_ (x : t) e)
       #`(let ([tmp (term (Π (x : ,t)
                             ,(let ([x (term x)])
                                 (parameterize ([gamma (term (,(gamma) ,x : ,t))])
                                   e))))])
           (unless (judgment-holds (types ,(sigma) ,(gamma) ,tmp U_0))
             (error 'type-checking "Term is ill-typed: ~s" tmp))
           tmp)]))

  ;; TODO: Right now, all top level things are variables, so typos can
  ;; result in "unbound variable" errors. Should do something more
  ;; clever.
  (define-syntax (dep-var syn)
    (syntax-case syn ()
      [(_ . id)
       #'(let ()
           (unless (judgment-holds (types ,(sigma) ,(gamma) ,(term id) t_0))
             (error 'unbound "Unbound variable: ~s" (term id)))
           (term id))]))

  (define-syntax (curry-lambda syn)
    (syntax-case syn (:)
      [(_ ((x : t) (xr : tr) ...) e)
       #'(dep-lambda (x : t) (curry-lambda ((xr : tr) ...) e))]
      [(_ () e) #'e]))
  ;; TODO: Syntax-parse
  (define-syntax (dep-define syn)
    (syntax-case syn (:)
      [(_ (name (x : t) ...) e)
       #'(define name (curry-lambda ((x : t) ...) e))]
      [(_ id e)
       #'(define id e)])))

(require 'sugar)
(provide (all-from-out 'sugar))
(module+ test
  (require (submod ".." core test)))

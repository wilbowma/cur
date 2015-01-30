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
    (v ::= (Π (x : t) t) (μ (x : t) t) (λ (x : t) t) x U)
    (t e ::= (case e (x e) ...) v (t t)))

  (module+ test
    (require rackunit)
    (define x? (redex-match? cicL x))
    (define t? (redex-match? cicL t))
    (define e? (redex-match? cicL e))
    (define v? (redex-match? cicL v))
    (define U? (redex-match? cicL U))

    ;; TODO: Rename these signatures, and use them in all future tests.
    (define Σ (term (((∅ nat : Type) zero : nat) s : (Π (x : nat) nat))))

    (define Σ0 (term ∅))
    (define Σ2 (term (((∅ nat : Type) z : nat) s : (Π (x : nat) nat))))
    (define Σ3 (term (∅ and : (Π (A : Type) (Π (B : Type) Type)))))
    (define Σ4 (term (,Σ3 conj : (Π (A : Type) (Π (B : Type) (Π (a : A) (Π (b : B) ((and A) B))))))))
    (define Σ? (redex-match? cic-typingL Σ))

    (check-true (Σ? Σ0))
    (check-true (Σ? Σ2))
    (check-true (Σ? Σ4))
    (check-true (Σ? Σ3))
    (check-true (Σ? Σ4))
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
    [(subst (μ (x : t_0) t_1) x t) (μ (x : (subst t_0 x t)) t_1)]
    ;; TODO: Broken: needs capture avoiding, but currently require
    ;; binders to be the same in term/type, so this is not a local
    ;; change.
    [(subst (Π (x_0 : t_0) t_1) x t) (Π (x_0 : (subst t_0 x t)) (subst t_1 x t)) ]
    [(subst (λ (x_0 : t_0) t_1) x t) (λ (x_0 : (subst t_0 x t)) (subst t_1 x t))]
    [(subst (μ (x_0 : t_0) t_1) x t) (μ (x_0 : (subst t_0 x t)) (subst t_1 x t))]
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
    (E hole (E t) (case E (x e) ...)))

  (define-metafunction cicL
    inductive-name : t -> x or #f
    [(inductive-name x) x]
    [(inductive-name (t_1 t_2)) (inductive-name t_1)]
    [(inductive-name t) #f])
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
      (==> ((μ (x : t) e_0) e_1)
           ((subst e_0 x (μ (x : t) e_0)) e_1))
      (==> (case e_9
             (x_0 e_0) ... (x e) (x_r e_r) ...)
           (inductive-apply e e_9)
           (where x (inductive-name e_9)))
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
                  (term (s (s (s (s z)))))))

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
    [(result-type Σ (e_1 e_2)) (result-type Σ e_1)]
    [(result-type Σ x) ,(and (term (lookup Σ x)) (term x))]
    [(result-type Σ t) #f])
  (module+ test
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
    constructors-for : Σ x (x ...) -> #t or #f
    [(constructors-for Σ x_0 (x ...))
     ,((lambda (x y) (and (set=? x y) (= (length x) (length y))))
       (term (x ...))
       (judgment-holds (constructor-for Σ x_0 x_00) x_00))])
  (module+ test
    (check-true
      (term (constructors-for (((∅ nat : Type) zero : nat) s : (Π (x : nat) nat))
                         nat (zero s))))
    (check-false
      (term (constructors-for (((∅ nat : Type) zero : nat) s : (Π (x : nat) nat))
                         nat (zero))))
    (check-true
      (term (constructors-for ,Σ4 and (conj)))))

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

  ;; TODO: Add positivity checking.
  (define-metafunction cicL
    positive : t any -> #t or #f
    ;; Type; not a inductive constructor
    [(positive any_1 any_2) #t])

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

    (check-true (term (positive Type #f))))

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

  ;; TODO: Add termination checking
  (define-metafunction cicL
    terminates? : t -> #t or #f
    [(terminates? t) #t])
  (module+ test
    (check-false (term (terminates? (μ (x : Type) x))))
    (check-false (term (terminates? (μ (x : Type) (λ (y : Type) (x y))))))
    (check-true (term (terminates? (μ (x : Type) (λ (y : Type) y))))))

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

    [(side-condition (terminates? (μ (x : t_0) e)))
     (types Σ (Γ x : t_0) e t_0)
     (types Σ Γ t_0 U)
     ----------------- "DTR-Fix"
     (types Σ Γ (μ (x : t_0) e) t_0)]

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

    ;; TODO: This shouldn't be a special case, but I failed to forall
    ;; quantify properly over the branches in the above case, and I'm lazy.
    ;; TODO: Seem to need bidirectional checking to pull this off
    #;[(types Σ Γ e t_9)
     (where t_1 (inductive-name t_9))
     (side-condition (constructors-for Σ t_1 ()))
     ----------------- "DTR-Case-Empty"
     (types Σ Γ (case e) t)]

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
    (define lam (term (λ (nat : Type) nat)))
    (check-equal?
      (list (term (Π (nat : Type) Type)))
      (judgment-holds (types ,Σ0 ∅ ,lam t) t))
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
    (check-true
      (judgment-holds (types ,Σ4 ∅ (λ (S : Type) (conj S))
                             (Π (S : Type) (Π (B : Type) (Π (a : S) (Π (b : B) ((and S) B))))))))
    (check-true
      (judgment-holds (types ((,Σ4 true : Type) tt : true) ∅
                             ((((conj true) true) tt) tt)
                             ((and true) true))))
    (check-true
      (judgment-holds (types ((,Σ4 true : Type) tt : true) ∅
                             (case ((((conj true) true) tt) tt)
                               (conj (λ (A : Type)
                                        (λ (B : Type)
                                           (λ (a : A)
                                              (λ (b : B) a))))))
                             A)))
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
      (judgment-holds (types ,sigma (,gamma tmp863 : pre) Type (Unv 0))))
    (check-true
      (judgment-holds (types ,sigma (,gamma x : false) (case x) t)))
    )


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
      syntax/parse
      racket/pretty
      racket/trace
      (except-in (submod ".." core) remove)
      redex/reduction-semantics))
  (provide
    ;; Basic syntax
    require
    provide
    for-syntax
    only-in
    module+
    #%module-begin
    (rename-out
      [dep-lambda lambda]
      [dep-lambda λ]
      [dep-app #%app]

      [dep-fix fix]

      [dep-forall forall]
      [dep-forall ∀]

      [dep-inductive data]
      [dep-case case]

      [dep-var #%top]
;      [dep-datum #%datum]
      [dep-define define])
    ;; DYI syntax extension
    define-syntax
    begin-for-syntax
    (for-syntax (all-from-out syntax/parse))
    syntax-case
    syntax-rules
    define-syntax-rule
    (for-syntax (all-from-out racket))
    ;; reflection
    (for-syntax
      cur-expand
      (rename-out
       [type-infer^ type-infer]
       [type-check? type-check?]
       [reduce^ normalize])))

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
          (cwtpr s (map (lambda (x)
                          (if (syntax? x)
                              (cons 'syntax (syntax->datum x))
                              x)) l) kw l2 n))))
    (current-trace-print-results
      (let ([cwtpr (current-trace-print-results)])
        (lambda (s l n)
         (cwtpr s (map (lambda (x) (if (syntax? x) (cons 'syntax (syntax->datum x)) x)) l) n)))))

  (begin-for-syntax
    ;; TODO: Gamma and Sigma seem to get reset inside a module+
    (define gamma
      (make-parameter (term ∅)
        (lambda (x)
          (unless (redex-match? cic-typingL Γ x)
            (error 'core-error "We built a bad gamma ~s" x))
          x)))

    (define sigma
      (make-parameter (term ∅)
        (lambda (x)
          (unless (redex-match? cic-typingL Σ x)
            (error 'core-error "We built a bad sigma ~s" x))
          x)))

    (define (extend-env/term env x t)
      (term (,(env) ,x : ,t)))

    (define (extend-env/syn env x t)
      (term (,(env) ,(syntax->datum x) : ,(cur->datum t))))

    (define bound (make-parameter '()))

    (define (extend-bound id) (cons id (bound)))

    (define orig-insp (variable-reference->module-declaration-inspector
      (#%variable-reference)))

    (define (disarm syn) (syntax-disarm syn orig-insp))


    (define (core-expand syn) (denote syn (cur->datum syn)))

    (define (denote syn t)
      #`(term (reduce #,(datum->syntax syn t))))

    (define (cur->datum syn)
      (define (expand syn)
        (disarm (if (identifier? syn)
             syn
             (local-expand syn 'expression
                           (append
                             (syntax-e #'(term reduce dep-var #%app λ Π μ case Type)))))))
      (define reified-term
        (let core-expand ([syn syn])
          (syntax-parse (expand syn)
            #:literals (term reduce #%app)
            #:datum-literals (case Π λ μ : Type)
            [x:id (syntax->datum #'x)]
            [(reduce e) (syntax->datum #'e)]
            [(term e) (core-expand #'e)]
            ;; TODO: should really check that b is one of the binders
            ;; Maybe make a syntax class for the binders, core forms,
            ;; etc.
            [(b:id (x:id : t) e)
             (let* ([x (syntax->datum #'x)]
                    [t (core-expand #'t)]
                    [e (parameterize ([gamma (extend-env/term gamma x t)]
                                      [bound (extend-bound x)])
                         (core-expand #'e))])
                   (term (,(syntax->datum #'b) (,x : ,t) ,e)))]
            [(case e (ec eb) ...)
             (term (case ,(core-expand #'e)
                         ,@(map (lambda (c b)
                                  `(,c ,(core-expand b)))
                                (syntax->datum #'(ec ...))
                                (syntax->list #'(eb ...)))))]
            [(#%app e1 e2)
             (term (,(core-expand #'e1) ,(core-expand #'e2)))])))
      (unless (judgment-holds (types ,(sigma) ,(gamma) ,reified-term t_0))
        ;; TODO: is this really a syntax error?
        (raise-syntax-error 'cur "term is ill-typed:"
          (begin (printf "Sigma: ~s~nGamma: ~s~n" (sigma) (gamma))
                 reified-term)
          syn))
      reified-term)

    ;; Reflection tools

    (define (type-infer^ syn)
      (let ([t (judgment-holds (types ,(sigma) ,(gamma) ,(cur->datum syn) t_0) t_0)])
        (and t (denote syn (car t)))))

    (define (type-check? syn type)
      (let ([t (judgment-holds (types ,(sigma) ,(gamma) ,(cur->datum syn) t_0) t_0)])
        (equal? t (cur->datum type))))

    (define (reduce^ syn) (term (reduce (cur->datum syn))))

    (define (cur-expand syn)
      (disarm (local-expand syn 'expression
                (syntax-e #'(Type dep-inductive dep-case dep-lambda dep-app
                             dep-fix dep-forall dep-var))))))

  #;(define-syntax (dep-datum syn) (denote #'syn))

  ;; TODO: Can these be simplified further?
  ;; TODO: Can we make core-expand some kind of parameter that is only
  ;; to ensure type-checking is only done at the outermost level, and
  ;; not in the main loop?
  (define-syntax (dep-lambda syn)
    (syntax-case syn (:)
      [(_ (x : t) e) (core-expand #`(λ (x : t) e))]))

  (define-syntax (dep-app syn)
    (syntax-case syn ()
      [(_ e1 e2) (core-expand #`(#%app e1 e2))]))

  (define-syntax (dep-case syn)
    (syntax-case syn ()
      [(_ e ...) (core-expand #`(case e ...))]))

  (define-syntax (dep-forall syn)
    (syntax-case syn (:)
      [(_ (x : t) e) (core-expand #`(Π (x : t) e))]))

  (define-syntax (dep-fix syn)
   (syntax-case syn (:)
     [(_ (x : t) e) (core-expand #`(μ (x : t) e))]))

  (define-syntax (dep-inductive syn)
    (syntax-case syn (:)
      [(_ i : ti (x1 : t1) ...)
       (begin
         (sigma (extend-env/syn sigma #'i #'ti))
         (bound (extend-bound #'i))
         (for ([x (syntax->list #`(x1 ...))]
               [t (syntax->list #`(t1 ...))])
           (sigma (extend-env/syn sigma x t))
           (bound (extend-bound x)))
         #'(void))]))

  ;; TODO: Not sure if this is the correct behavior for #%top
  (define-syntax (dep-var syn)
    (syntax-case syn ()
      [(_ . id) #`(term (reduce id))]))

  ;; TODO: Syntax-parse
  (define-syntax (dep-define syn)
    (syntax-case syn (:)
      [(_ (name (x : t)) e)
       #'(dep-define name (dep-lambda (x : t) e))]
      [(_ id e)
       ;; TODO: Can't actually run programs until I do something about
       ;; #'e. Maybe denote final terms into Racket. Or keep an
       ;; environment and have denote do a giant substitution
       (let () #;[t (core-expand #'e)]
         (gamma (extend-env/syn gamma #'id (type-infer^ #'e)))
         #'(void))])) )

(require 'sugar)
(provide (all-from-out 'sugar))
(module+ test
  (require (submod ".." core test)))

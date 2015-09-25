#lang racket

;; TODO: Strip to racket/base as much as possible
(module core racket
  (require
    (only-in racket/set set=?)
    redex/reduction-semantics)
  (provide
    (all-defined-out))

  (set-cache-size! 10000)

  (module+ test
    (require rackunit)
    (define-syntax-rule (check-holds (e ...))
      (check-true
        (judgment-holds (e ...))))
    (define-syntax-rule (check-not-holds (e ...))
      (check-false
        (judgment-holds (e ...)))))

  ;; References:
  ;; http://www3.di.uminho.pt/~mjf/pub/SFV-CIC-2up.pdf
  ;; https://www.cs.uoregon.edu/research/summerschool/summer11/lectures/oplss-herbelin1.pdf
  ;; http://www.emn.fr/z-info/ntabareau/papers/universe_polymorphism.pdf
  ;; http://people.cs.kuleuven.be/~jesper.cockx/Without-K/Pattern-matching-without-K.pdf
  ;; http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.37.74
  ;; http://eb.host.cs.st-andrews.ac.uk/writings/thesis.pdf

  ;; cicL is the core language of Cur. Very similar to TT (Idirs core)
  ;; and Luo's UTT. Used to be similar to CIC, hence the name.
  ;; Surface langauge should provide short-hand, such as -> for
  ;; non-dependent function types, and type inference.
  (define-language cicL
    (i ::= natural)
    (U ::= (Unv i))
    (x ::= variable-not-otherwise-mentioned)
    (v ::= (Π (x : t) t) (λ (x : t) t) elim x U)
    (t e ::= v (t t)))

  (define x? (redex-match? cicL x))
  (define t? (redex-match? cicL t))
  (define e? (redex-match? cicL e))
  (define v? (redex-match? cicL v))
  (define U? (redex-match? cicL U))

  (module+ test
    (define-term Type (Unv 0))
    (check-true (x? (term T)))
    (check-true (x? (term A)))
    (check-true (x? (term truth)))
    (check-true (x? (term zero)))
    (check-true (x? (term s)))
    (check-true (t? (term zero)))
    (check-true (t? (term s)))
    (check-true (x? (term nat)))
    (check-true (t? (term nat)))
    (check-true (t? (term A)))
    (check-true (t? (term S)))
    (check-true (U? (term (Unv 0))))
    (check-true (U? (term Type)))
    (check-true (e? (term (λ (x_0 : (Unv 0)) x_0))))
    (check-true (v? (term (λ (x_0 : (Unv 0)) x_0))))
    (check-true (t? (term (λ (x_0 : (Unv 0)) x_0))))
    (check-true (t? (term (λ (x_0 : (Unv 0)) x_0)))))

  ;; 'A'
  ;; Types of Universes
  (define-judgment-form cicL
    #:mode (unv-ok I O)
    #:contract (unv-ok U U)

    [(where i_1 ,(add1 (term i_0)))
     -----------------
     (unv-ok (Unv i_0) (Unv i_1))])

  ;; 'R'
  ;; Kinding, I think
  (define-judgment-form cicL
    #:mode (unv-kind I I O)
    #:contract (unv-kind U U U)

    [----------------
     (unv-kind (Unv 0) (Unv 0) (Unv 0))]

    [----------------
     (unv-kind (Unv 0) (Unv i) (Unv i))]

    [----------------
     (unv-kind (Unv i) (Unv 0) (Unv 0))]

    [(where i_3 ,(max (term i_1) (term i_2)))
     ----------------
     (unv-kind (Unv i_1) (Unv i_2) (Unv i_3))])

  (define-judgment-form cicL
    #:mode (α-equivalent I I)
    #:contract (α-equivalent t t)

    [----------------- "α-x"
     (α-equivalent x x)]

    [----------------- "α-U"
     (α-equivalent U U)]

    [(α-equivalent t_1 (subst t_3 x_1 x_0))
     (α-equivalent t_0 t_2)
     ----------------- "α-binder"
     (α-equivalent (any (x_0 : t_0) t_1)
                   (any (x_1 : t_2) t_3))]

    [(α-equivalent e_0 e_2)
     (α-equivalent e_1 e_3)
     ----------------- "α-app"
     (α-equivalent (e_0 e_1) (e_2 e_3))])
  (module+ test
    (check-holds (α-equivalent x x))
    (check-not-holds (α-equivalent x y))
    (check-holds (α-equivalent (λ (x : A) x)
                               (λ (y : A) y))))

  (define-metafunction cicL
    fresh-x : any ... -> x
    [(fresh-x any ...) ,(variable-not-in (term (any ...)) (term x))])

  ;; NB: Substitution is hard
  ;; NB: Copy and pasted from Redex examples
  (define-metafunction cicL
    subst-vars : (x any) ... any -> any
    [(subst-vars (x_1 any_1) x_1) any_1]
    [(subst-vars (x_1 any_1) (any_2 ...))
     ((subst-vars (x_1 any_1) any_2) ...)]
    [(subst-vars (x_1 any_1) any_2) any_2]
    [(subst-vars (x_1 any_1) (x_2 any_2) ... any_3)
     (subst-vars (x_1 any_1) (subst-vars (x_2 any_2) ... any_3))]
    [(subst-vars any) any])

  (define-metafunction cicL
    subst : t x t -> t
    [(subst U x t) U]
    [(subst x x t) t]
    [(subst x_0 x t) x_0]
    [(subst (any (x : t_0) t_1) x t)
     (any (x : (subst t_0 x t)) t_1)]
    [(subst (any (x_0 : t_0) t_1) x t)
     (any (x_new : (subst (subst-vars (x_0 x_new) t_0) x t))
       (subst (subst-vars (x_0 x_new) t_1) x t))
     ;; TODO: Use "fresh-x" meta-function
     (where x_new
            ,(variable-not-in
               (term (x_0 t_0 x t t_1))
               (term x_0)))]
    [(subst (e_0 e_1) x t) ((subst e_0 x t) (subst e_1 x t))]
    [(subst elim x t) elim])
  (module+ test
    (check-true (t? (term (Π (a : A) (Π (b : B) ((and A) B))))))
    (check-holds
      (α-equivalent
        (Π (a : S) (Π (b : B) ((and S) B)))
        (subst (Π (a : A) (Π (b : B) ((and A) B))) A S))))
  ;; NB:
  ;; TODO: Why do I not have tests for substitutions?!?!?!?!?!?!?!!?!?!?!?!?!?!!??!?!

  (define-metafunction cicL
    subst-all : t (x ...) (e ...) -> t
    [(subst-all t () ()) t]
    [(subst-all t (x_0 x ...) (e_0 e ...))
     (subst-all (subst t x_0 e_0) (x ...) (e ...))])

  (define-extended-language cic-redL cicL
    ;; call-by-value, plus reduce under Π (helps with typing checking)
    (E   ::= hole (v E) (E e)
             (Π (x : (in-hole Θ x)) E)
             (Π (x : v) E)
             (Π (x : E) e))
    ;; Σ (signature). (inductive-name : type ((constructor : type) ...))
    (Σ   ::= ∅ (Σ (x : t ((x : t) ...))))
    (Ξ Φ ::= hole (Π (x : t) Ξ)) ;;(Telescope)
    ;; NB: Does an apply context correspond to a substitution (γ)?
    (Θ   ::= hole (Θ e)))        ;;(Apply context)
  (define Σ? (redex-match? cic-redL Σ))
  (define Ξ? (redex-match? cic-redL Ξ))
  (define Φ? (redex-match? cic-redL Φ))
  (define Θ? (redex-match? cic-redL Θ))
  (define E? (redex-match? cic-redL E))

  (module+ test
    ;; TODO: Rename these signatures, and use them in all future tests.
    (define Σ (term ((∅ (nat : (Unv 0) ((zero : nat) (s : (Π (x : nat) nat)))))
                        (bool : (Unv 0) ((true : bool) (false : bool))))))
    (define Σ0 (term ∅))
    (define Σ3 (term (∅ (and : (Π (A : (Unv 0)) (Π (B : (Unv 0)) (Unv 0))) ()))))
    (define Σ4 (term (∅ (and : (Π (A : (Unv 0)) (Π (B : (Unv 0)) (Unv 0)))
                               ((conj : (Π (A : (Unv 0)) (Π (B : (Unv 0)) (Π (a : A) (Π (b : B) ((and A) B)))))))))))
    (check-true (Σ? Σ0))
    (check-true (Σ? Σ))
    (check-true (Σ? Σ4))
    (check-true (Σ? Σ3))
    (check-true (Σ? Σ4))
    (define sigma (term ((((((∅ (true : (Unv 0) ((T : true))))
                                (false : (Unv 0) ()))
                                (equal : (Π (A : (Unv 0)) (Π (B : (Unv 0)) (Unv 0)))
                                   ()))
                                (nat : (Unv 0) ()))
                                (heap : (Unv 0) ()))
                                (pre : (Π (temp808 : heap) (Unv 0)) ()))))
    (check-true (Σ? (term (∅ (true : (Unv 0) ((T : true)))))))
    (check-true (Σ? (term (∅ (false : (Unv 0) ())))))
    (check-true (Σ? (term (∅ (equal : (Π (A : (Unv 0)) (Π (B : (Unv 0)) (Unv 0)))
                                  ())))))
    (check-true (Σ? (term (∅ (nat : (Unv 0) ())))))
    (check-true (Σ? (term (∅ (pre : (Π (temp808 : heap) (Unv 0)) ())))))

    (check-true (Σ? (term ((∅ (true : (Unv 0) ((T : true)))) (false : (Unv 0) ())))))
    (check-true (Σ? (term (((∅ (true : (Unv 0) ((T : true)))) (false : (Unv 0) ()))
                               (equal : (Π (A : (Unv 0)) (Π (B : (Unv 0)) (Unv 0)))
                                  ())))))
    (check-true (Σ? sigma)))

  (define-metafunction cic-redL
    append-Σ : Σ Σ -> Σ
    [(append-Σ Σ ∅) Σ]
    [(append-Σ Σ_2 (Σ_1 (x : t ((x_c : t_c) ...))))
     ((append-Σ Σ_2 Σ_1) (x : t ((x_c : t_c) ...)))])

  ;; TODO: Test
  ;; TODO: Maybe this should be called "apply-to-telescope"
  (define-metafunction cic-redL
    apply-telescope : t Ξ -> t
    [(apply-telescope t hole) t]
    [(apply-telescope t_0 (Π (x : t) Ξ)) (apply-telescope (t_0 x) Ξ)])

  (define-metafunction cic-redL
    apply-telescopes : t (Ξ ...) -> t
    [(apply-telescopes t ()) t]
    [(apply-telescopes t (Ξ_0 Ξ_rest ...))
     (apply-telescopes (apply-telescope t Ξ_0) (Ξ_rest ...))])

  ;; NB: Depends on clause order
  (define-metafunction cic-redL
    select-arg : x (x ...) (Θ e) -> e
    [(select-arg x (x x_r ...) (in-hole Θ (hole e))) e]
    [(select-arg x (x_1 x_r ...) (in-hole Θ (hole e)))
     (select-arg x (x_r ...) Θ)])

  (define-metafunction cic-redL
    method-lookup : Σ x x (Θ e) -> e
    [(method-lookup Σ x_D x_ci Θ)
     (select-arg x_ci (x_0 ...) Θ)
     (where ((x_0 : t_0) ...) (constructors-for Σ x_D))])
  (module+ test
    (check-equal?
      (term (method-lookup ,Σ nat s
            ((hole (s zero))
             (λ (x : nat) (λ (ih-x : nat) (s (s zero)))))))
      (term (λ (x : nat) (λ (ih-x : nat) (s (s zero)))))))

  ;; Create the recursive applications of elim to the recursive
  ;; arguments of an inductive constructor.
  ;; TODO: Poorly documented, and poorly tested.
  (define-metafunction cic-redL
    elim-recur : x U e Θ Θ Θ (x ...) -> Θ
    [(elim-recur x_D U e_P Θ
       (in-hole Θ_m (hole e_mi))
       (in-hole Θ_i (hole (in-hole Θ_r x_ci)))
       (x_c0 ... x_ci x_c1 ...))
     ((elim-recur x_D U e_P Θ Θ_m Θ_i (x_c0 ... x_ci x_c1 ...))
      (in-hole (Θ (in-hole Θ_r x_ci)) (((elim x_D) U) e_P)))]
    [(elim-recur x_D U e_P Θ Θ_i Θ_nr (x ...)) hole])
  (module+ test
    (check-true
      (redex-match? cic-redL (in-hole Θ_i (hole (in-hole Θ_r zero))) (term (hole zero))))
    (check-equal?
      (term (elim-recur nat Type (λ (x : nat) nat)
              ((hole (s zero)) (λ (x : nat) (λ (ih-x : nat) (s (s x)))))
              ((hole (s zero)) (λ (x : nat) (λ (ih-x : nat) (s (s x)))))
              (hole zero)
              (zero s)))
      (term (hole ((((((elim nat) Type) (λ (x : nat) nat))
                      (s zero))
                      (λ (x : nat) (λ (ih-x : nat) (s (s x)))))
                   zero))))
    (check-equal?
      (term (elim-recur nat Type (λ (x : nat) nat)
              ((hole (s zero)) (λ (x : nat) (λ (ih-x : nat) (s (s x)))))
              ((hole (s zero)) (λ (x : nat) (λ (ih-x : nat) (s (s x)))))
              (hole (s zero))
              (zero s)))
      (term (hole ((((((elim nat) Type) (λ (x : nat) nat))
                      (s zero))
                      (λ (x : nat) (λ (ih-x : nat) (s (s x)))))
                   (s zero))))))

  (define-judgment-form cic-redL
    #:mode (length-match I I)
    #:contract (length-match Θ (x ...))
    [----------------------
     (length-match hole ())]

    [(length-match Θ (x_r ...))
     ----------------------
     (length-match (Θ e) (x x_r ...))])

  (define cic-->
    (reduction-relation cic-redL
      (--> (Σ (in-hole E ((any (x : t_0) t_1) t_2)))
           (Σ (in-hole E (subst t_1 x t_2)))
           -->β)
      (--> (Σ (in-hole E (in-hole Θ (((elim x_D) U) e_P))))
           (Σ (in-hole E (in-hole Θ_r (in-hole Θ_i e_mi))))
           #|
            |
            | The elim form must appear applied like so:
            | (elim x_D U e_P m_0 ... m_i m_j ... m_n p ... (c_i p ... a ...))
            | -->
            |
            | Where:
            |   x_D       is the inductive being eliminated
            |   U         is the sort of the motive
            |   e_P       is the motive
            |   m_{0..n}  are the methods
            |   p ...     are the parameters of x_D
            |   c_i       is a constructor of x_d
            |   a ...     are the non-parameter arguments to c_i
            | Unfortunately, Θ contexts turn all this inside out:
            | TODO: Write better abstractions for this notation
            |#
           (where (in-hole (Θ_p (in-hole Θ_i x_ci)) Θ_m)
                  Θ)
           (where Ξ (parameters-of Σ x_D))
           (judgment-holds (telescope-types Σ ∅ Θ_p Ξ))
           (where (in-hole Θ_a Θ_p)
                  Θ_i)
           (where ((x_c* : t_c*) ...)
                  (constructors-for Σ x_D))
           (where (_ ... x_ci _ ...)
                  (x_c* ...))
           ;; There should be a number of methods equal to the number of
           ;; constructors; to ensure E doesn't capture methods
           (judgment-holds (length-match Θ_m (x_c* ...)))
           (where e_mi (method-lookup Σ x_D x_ci Θ_m))
           (where Θ_r (elim-recur x_D U e_P Θ_m Θ_m Θ_i (x_c* ...)))
           -->elim)))

  (define-metafunction cic-redL
    reduce : Σ e -> e
    [(reduce Σ e) e_r
     (where (_ e_r) ,(car (apply-reduction-relation* cic--> (term (Σ e)))))])
  ;; TODO: Move equivalence up here, and use in these tests.
  (module+ test
    (check-equal? (term (reduce ∅ (Unv 0))) (term (Unv 0)))
    (check-equal? (term (reduce ∅ ((λ (x : t) x) (Unv 0)))) (term (Unv 0)))
    (check-equal? (term (reduce ∅ ((Π (x : t) x) (Unv 0)))) (term (Unv 0)))
    (check-equal? (term (reduce ∅ (Π (x : t) ((Π (x_0 : t) x_0) (Unv 0)))))
                  (term (Π (x : t) (Unv 0))))
    (check-equal? (term (reduce ∅ (Π (x : t) ((Π (x_0 : t) (x_0 x)) x))))
                  (term (Π (x : t) (x x))))
    (check-equal? (term (reduce ,Σ ((((((elim nat) Type) (λ (x : nat) nat))
                                       (s zero))
                                       (λ (x : nat) (λ (ih-x : nat)
                                         (s (s x)))))
                                     zero)))
                  (term (s zero)))
    (check-equal? (term (reduce ,Σ ((((((elim nat) Type) (λ (x : nat) nat))
                                       (s zero))
                                       (λ (x : nat) (λ (ih-x : nat)
                                         (s (s x)))))
                                      (s zero))))
                  (term (s (s zero))))
    (check-equal? (term (reduce ,Σ ((((((elim nat) Type) (λ (x : nat) nat))
                                       (s zero))
                                       (λ (x : nat) (λ (ih-x : nat) (s (s x)))))
                                     (s (s (s zero))))))
                  (term (s (s (s (s zero))))))

    (check-equal?
      (term (reduce ,Σ
        ((((((elim nat) Type) (λ (x : nat) nat))
            (s (s zero)))
            (λ (x : nat) (λ (ih-x : nat) (s ih-x))))
         (s (s zero)))))
      (term (s (s (s (s zero)))))))

  (define-judgment-form cic-redL
    #:mode (equivalent I I I)
    #:contract (equivalent Σ t t)

    [(where t_2 (reduce Σ t_0))
     (where t_3 (reduce Σ t_1))
     (α-equivalent t_2 t_3)
     ----------------- "≡-αβ"
     (equivalent Σ t_0 t_1)])

  (define-extended-language cic-typingL cic-redL
    ;; NB: There may be a bijection between Γ and Ξ. That's
    ;; NB: interesting.
    (Γ   ::= ∅ (Γ x : t)))
  (define Γ? (redex-match? cic-typingL Γ))

  (define-metafunction cic-typingL
    append-Γ : Γ Γ -> Γ
    [(append-Γ Γ ∅) Γ]
    [(append-Γ Γ_2 (Γ_1 x : t))
     ((append-Γ Γ_2 Γ_1) x : t)])

  ;; NB: Depends on clause order
  (define-metafunction cic-typingL
    lookup-Γ : Γ x -> t or #f
    [(lookup-Γ ∅ x) #f]
    [(lookup-Γ (Γ x : t) x) t]
    [(lookup-Γ (Γ x_0 : t_0) x_1) (lookup-Γ Γ x_1)])

  ;; NB: Depends on clause order
  (define-metafunction cic-redL
    lookup-Σ : Σ x -> t or #f
    [(lookup-Σ ∅ x) #f]
    [(lookup-Σ (Σ (x : t ((x_1 : t_1) ...))) x) t]
    [(lookup-Σ (Σ (x_0 : t_0 ((x_1 : t_1) ... (x : t) (x_2 : t_2) ...))) x) t]
    [(lookup-Σ (Σ (x_0 : t_0 ((x_1 : t_1) ...))) x) (lookup-Σ Σ x)])

  ;; NB: Depends on clause order
  (define-metafunction cic-typingL
    remove : Γ x -> Γ
    [(remove ∅ x) ∅]
    [(remove (Γ x : t) x) Γ]
    [(remove (Γ x_0 : t_0) x_1) (remove Γ x_1)])

  ;; TODO: Add positivity checking.
  (define-metafunction cicL
    positive : t any -> #t or #f
    [(positive any_1 any_2) #t])
  (module+ test
    (check-true (term (positive nat nat)))
    (check-true (term (positive (Π (x : (Unv 0)) (Π (y : (Unv 0)) (Unv 0))) #f)))
    (check-true (term (positive (Π (x : nat) nat) nat)))
    ;; (nat -> nat) -> nat
    ;; Not sure if this is actually supposed to pass
    (check-false (term (positive (Π (x : (Π (y : nat) nat)) nat) nat)))
    ;; ((Unv 0) -> nat) -> nat
    (check-true (term (positive (Π (x : (Π (y : (Unv 0)) nat)) nat) nat)))
    ;; (((nat -> (Unv 0)) -> nat) -> nat)
    (check-true (term (positive (Π (x : (Π (y : (Π (x : nat) (Unv 0))) nat)) nat) nat)))
    ;; Not sure if this is actually supposed to pass
    (check-false (term (positive (Π (x : (Π (y : (Π (x : nat) nat)) nat)) nat) nat)))

    (check-true (term (positive (Unv 0) #f))))

  ;; Holds when the signature Σ and typing context Γ are well-formed.
  (define-judgment-form cic-typingL
    #:mode (wf I I)
    #:contract (wf Σ Γ)

    [----------------- "WF-Empty"
     (wf ∅ ∅)]

    [(type-infer Σ Γ t t_0)
     (wf Σ Γ)
     ----------------- "WF-Var"
     (wf Σ (Γ x : t))]

    [(wf Σ ∅)
     (type-infer Σ ∅ t_D U_D)
     (type-infer Σ (∅ x_D : t_D) t_c U_c) ...
     ;; NB: Ugh this should be possible with pattern matching alone ....
     (side-condition ,(map (curry equal? (term Ξ_D)) (term (Ξ_D* ...))))
     (side-condition ,(map (curry equal? (term x_D)) (term (x_D* ...))))
     (side-condition (positive t_D (t_c ...)))
     ----------------- "WF-Inductive"
     (wf (Σ (x_D : (name t_D (in-hole Ξ_D t))
            ;; Checks that a constructor for x actually produces an x, i.e., that
            ;; the constructor is well-formed.
            ((x_c : (name t_c (in-hole Ξ_D* (in-hole Φ (in-hole Θ x_D*))))) ...))) ∅)])
  (module+ test
    (check-true (judgment-holds (wf ,Σ0 ∅)))
    (check-true (redex-match? cic-redL (in-hole Ξ (Unv 0)) (term (Unv 0))))
    (check-true (redex-match? cic-redL (in-hole Ξ (in-hole Φ (in-hole Θ nat)))
                             (term (Π (x : nat) nat))))
    (define (bindings-equal? l1 l2)
      (map set=? l1 l2))
    (check-pred
      (curry bindings-equal?
             (list (list
                     (make-bind 'Ξ (term (Π (x : nat) hole)))
                     (make-bind 'Φ (term hole))
                     (make-bind 'Θ (term hole)))
                   (list
                     (make-bind 'Ξ (term hole))
                     (make-bind 'Φ (term (Π (x : nat) hole)))
                     (make-bind 'Θ (term hole)))))
      (map match-bindings (redex-match cic-redL (in-hole Ξ (in-hole Φ (in-hole Θ nat)))
                    (term (Π (x : nat) nat)))))
    (check-pred
      (curry bindings-equal?
             (list
                   (list
                     (make-bind 'Φ (term (Π (x : nat) hole)))
                     (make-bind 'Θ (term hole)))))
      (map match-bindings (redex-match cic-redL (in-hole hole (in-hole Φ (in-hole Θ nat)))
                    (term (Π (x : nat) nat)))))

    (check-true
      (redex-match? cic-redL
        (in-hole hole (in-hole hole (in-hole hole nat)))
        (term nat)))
    (check-true
      (redex-match? cic-redL
        (in-hole hole (in-hole (Π (x : nat) hole) (in-hole hole nat)))
        (term (Π (x : nat) nat))))
    (check-holds (wf (∅ (nat : (Unv 0) ())) ∅))

    (check-holds (wf ,Σ0 ∅))
    (check-holds (type-infer ∅ ∅ (Unv 0) U))
    (check-holds (type-infer ∅ (∅ nat : (Unv 0)) nat U))
    (check-holds (type-infer ∅ (∅ nat : (Unv 0)) (Π (x : nat) nat) U))
    (check-true (term (positive nat (nat (Π (x : nat) nat)))))
    (check-holds
      (wf (∅ (nat : (Unv 0) ((zero : nat)))) ∅))
    (check-holds
      (wf (∅ (nat : (Unv 0) ((s : (Π (x : nat) nat))))) ∅))
    (check-holds (wf ,Σ ∅))

    (check-holds (wf ,Σ3 ∅))
    (check-holds (wf ,Σ4 ∅))
    (check-holds (wf (∅ (truth : (Unv 0) ())) ∅))
    (check-holds (wf ∅ (∅ x : (Unv 0))))
    (check-holds (wf (∅ (nat : (Unv 0) ())) (∅ x : nat)))
    (check-holds (wf (∅ (nat : (Unv 0) ())) (∅ x : (Π (x : nat) nat)))))

  ;; Returns the inductive hypotheses required for eliminating the
  ;; inductively defined type x_D with motive t_P, where the telescope
  ;; Φ are the inductive arguments to a constructor for x_D
  (define-metafunction cic-redL
    hypotheses-for : x t Φ -> Φ
    [(hypotheses-for x_D t_P hole) hole]
    [(hypotheses-for x_D t_P (Π (x : (in-hole Φ (in-hole Θ x_D))) Φ_1))
     ;; TODO: Thread through Σ for reduce
     (Π (x_h : (in-hole Φ (reduce ∅ ((in-hole Θ t_P) (apply-telescope x Φ)))))
        (hypotheses-for x_D t_P Φ_1))
     ;; NB: Lol hygiene
     (where x_h ,(string->symbol (format "~a-~a" 'ih (term x))))])

  ;; Returns the inductive arguments to a constructor for the
  ;; inducitvely defined type x_D, where the telescope Φ are the
  ;; non-parameter arguments to the constructor.
  (define-metafunction cic-redL
    inductive-args : x Φ -> Φ
    [(inductive-args x_D hole) hole]
    [(inductive-args x_D (Π (x : (in-hole Φ (in-hole Θ x_D))) Φ_1))
     (Π (x : (in-hole Φ (in-hole Θ x_D))) (inductive-args x_D Φ_1))]
    ;; NB: Depends on clause order
    [(inductive-args x_D (Π (x : t) Φ_1))
     (inductive-args x_D Φ_1)])

  ;; Returns the methods required for eliminating the inductively
  ;; defined type x_D, whose parameters/indices are Ξ_pi and whose
  ;; constructors are ((x_ci : t_ci) ...), with motive t_P.
  (define-metafunction cic-redL
    methods-for : x Ξ t ((x : t) ...) -> Ξ
    [(methods-for x_D Ξ_pi t_P ()) hole]
    [(methods-for x_D Ξ_pi t_P ((x_ci : (in-hole Ξ_pi (in-hole Φ (in-hole Θ x_D))))
                                (x_c : t) ...))
     (Π (x_mi : (in-hole Ξ_pi (in-hole Φ (in-hole Φ_h
                  ;; NB: Manually reducing types because no conversion
                  ;; NB: rule
                  ;; TODO: Thread through Σ for reduce
                  ;; TODO: Might be able to remove this now that I have
                  ;; TODO: equivalence in type-check
                  (reduce ∅ ((in-hole Θ t_P) (apply-telescopes x_ci (Ξ_pi Φ))))))))
        (methods-for x_D Ξ_pi t_P ((x_c : t) ...)))
     (where Φ_h (hypotheses-for x_D t_P (inductive-args x_D Φ)))
     ;; NB: Lol hygiene
     (where x_mi ,(string->symbol (format "~a-~a" 'm (term x_ci))))])
  (module+ test
    (check-equal?
      (term (methods-for nat hole P ((zero : nat) (s : (Π (x : nat) nat)))))
      (term (Π (m-zero : (P zero))
          (Π (m-s : (Π (x : nat) (Π (ih-x : (P x)) (P (s x)))))
             hole))))
    (check-equal?
      (term (methods-for nat hole (λ (x : nat) nat) ((zero : nat) (s : (Π (x : nat) nat)))))
      (term (Π (m-zero : nat) (Π (m-s : (Π (x : nat) (Π (ih-x : nat) nat)))
                                     hole))))
    (check-equal?
      (term (methods-for and (Π (A : Type) (Π (B : Type) hole))
              (λ (A : Type) (λ (B : Type) (λ (x : ((and A) B)) true)))
              ((conj : (Π (A : Type) (Π (B : Type) (Π (a : A) (Π (b : B)
                                                                    ((and A) B)))))))))
      (term (Π (m-conj : (Π (A : Type) (Π (B : Type) (Π (a : A) (Π (b : B) true)))))
               hole)))
    (check-true (x? (term false)))
    (check-true (Ξ? (term hole)))
    (check-true (t? (term (λ (y : false) (Π (x : Type) x)))))
    (check-true (redex-match? cicL ((x : t) ...) (term ())))
    (check-equal?
      (term (methods-for false hole (λ (y : false) (Π (x : Type) x))
              ()))
      (term hole)))

  ;; Returns the inductively defined type that x constructs
  ;; NB: Depends on clause order
  (define-metafunction cic-redL
    constructor-of : Σ x -> x
    [(constructor-of (Σ (x : t ((x_0 : t_0) ... (x_c : t_c) (x_1 : t_1) ...)))
                     x_c) x]
    [(constructor-of (Σ (x_1 : t_1 ((x_c : t) ...))) x)
     (constructor-of Σ x)])
  (module+ test
    (check-equal?
      (term (constructor-of ,Σ zero))
      (term nat))
    (check-equal?
      (term (constructor-of ,Σ s))
      (term nat)))

  ;; TODO: inlined at least in type-infer
  ;; TODO: Define generic traversals of Σ and Γ ?
  (define-metafunction cic-redL
    parameters-of : Σ x -> Ξ
    [(parameters-of (Σ (x_D : (in-hole Ξ U) ((x : t) ...))) x_D)
     Ξ]
    [(parameters-of (Σ (x_1 : t_1 ((x : t) ...))) x_D)
     (parameters-of Σ x_D)])

  ;; Returns the constructors for the inductively defined type x_D in
  ;; the signature Σ
  (define-metafunction cic-redL
    constructors-for : Σ x -> ((x : t) ...) or #f
    ;; NB: Depends on clause order
    [(constructors-for ∅ x_D) #f]
    [(constructors-for (Σ (x_D : t_D ((x : t) ...))) x_D)
     ((x : t) ...)]
    [(constructors-for (Σ (x_1 : t_1 ((x : t) ...))) x_D)
     (constructors-for Σ x_D)])
  (module+ test
    (check-equal?
      (term (constructors-for ,Σ nat))
      (term ((zero : nat) (s : (Π (x : nat) nat)))))
    (check-equal?
      (term (constructors-for ,sigma false))
      (term ())))

  ;; Holds when an apply context Θ provides arguments that match the
  ;; telescope Ξ
  (define-judgment-form cic-typingL
    #:mode (telescope-types I I I I)
    #:contract (telescope-types Σ Γ Θ Ξ)

    [----------------- "TT-Hole"
     (telescope-types Σ Γ hole hole)]

    [(type-check Σ Γ e t)
     (telescope-types Σ Γ Θ Ξ)
     ----------------- "TT-Match"
     (telescope-types Σ Γ (in-hole Θ (hole e)) (Π (x : t) Ξ))])
  (module+ test
    (check-holds
      (telescope-types ,Σ ∅ (hole zero) (Π (x : nat) hole)))
    (check-true
      (redex-match? cic-redL (in-hole Θ (hole e))
                    (term ((hole zero) (λ (x : nat) x)))))
    (check-holds
      (telescope-types ,Σ ∅ (hole zero)
                       (methods-for nat hole
                                    (λ (x : nat) nat)
                                    ((zero : nat)))))
    (check-holds
      (type-check ,Σ ∅ (λ (x : nat) (λ (ih-x : nat) x))
             (Π (x : nat) (Π (ih-x : nat) nat))))
    (check-holds
      (telescope-types ,Σ ∅
                       ((hole zero)
                        (λ (x : nat) (λ (ih-x : nat) x)))
                       (methods-for nat hole
                                    (λ (x : nat) nat)
                                    (constructors-for ,Σ nat))))
    (check-holds
      (telescope-types (,Σ4 (true : (Unv 0) ((tt : true))))
                       ∅ (hole (λ (A : (Unv 0)) (λ (B : (Unv 0))
                                                      (λ (a : A) (λ (b : B) tt)))))
                       (methods-for and (Π (A : Type) (Π (B : Type) hole))
                                    (λ (A : Type) (λ (B : Type) (λ (x : ((and A) B)) true)))
                                    (constructors-for ,Σ4 and))))
    (check-holds
      (telescope-types ,sigma (∅ x : false)
                       hole
                       (methods-for false hole (λ (y : false) (Π (x : Type) x))
                                    ()))))

  ;; TODO: Bi-directional and inference?
  ;; TODO: http://www.cs.ox.ac.uk/ralf.hinze/WG2.8/31/slides/stephanie.pdf

  ;; Holds when e has type t under signature Σ and typing context Γ
  (define-judgment-form cic-typingL
    #:mode (type-infer I I I O)
    #:contract (type-infer Σ Γ e t)

    [(unv-ok U_0 U_1)
     (wf Σ Γ)
     ----------------- "DTR-Axiom"
     (type-infer Σ Γ U_0 U_1)]

    [(where t (lookup-Σ Σ x))
     ----------------- "DTR-Inductive"
     (type-infer Σ Γ x t)]

    [(where t (lookup-Γ Γ x))
     ----------------- "DTR-Start"
     (type-infer Σ Γ x t)]

    [(type-infer Σ Γ t_0 U_1)
     (type-infer Σ (Γ x : t_0) t U_2)
     (unv-kind U_1 U_2 U)
     ----------------- "DTR-Product"
     (type-infer Σ Γ (Π (x : t_0) t) U)]

    [(type-infer Σ Γ e_0 (Π (x_0 : t_0) t_1))
     (type-check Σ Γ e_1 t_0)
     (where t_3 (reduce Σ ((Π (x_0 : t_0) t_1) e_1)))
     ----------------- "DTR-Application"
     (type-infer Σ Γ (e_0 e_1) t_3)]

    [(type-infer Σ (Γ x : t_0) e t_1)
     (type-infer Σ Γ (Π (x : t_0) t_1) U)
     ----------------- "DTR-Abstraction"
     (type-infer Σ Γ (λ (x : t_0) e) (Π (x : t_0) t_1))]

    [(type-infer Σ Γ x_D (in-hole Ξ U_D))
     ;; A fresh name to bind the discriminant
     (where x (fresh-x Σ Γ x_D Ξ))
     ;; The telescope (∀ a -> ... -> (D a ...) hole), i.e.,
     ;; of the parameters and the inductive type applied to the
     ;; parameters
     (where Ξ_P*D (in-hole Ξ (Π (x : (apply-telescope x_D Ξ)) hole)))
     ;; A fresh name for the motive
     (where x_P (fresh-x Σ Γ x_D Ξ Ξ_P*D x))
     ;; The types of the methods for this inductive.
     (where Ξ_m (methods-for x_D Ξ x_P (constructors-for Σ x_D)))
     ----------------- "DTR-Elim_D"
     (type-infer Σ Γ ((elim x_D) U)
       ;; The type of ((elim x_D) U) is something like:
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
       (Π (x_P : (in-hole Ξ_P*D U))
          ;; The methods Ξ_m for each constructor of type x_D
          (in-hole Ξ_m
            ;; And finally, the parameters and discriminant
            (in-hole Ξ_P*D
              ;; The result is (P a ... (x_D a ...)), i.e., the motive
              ;; applied to the paramters and discriminant
              (apply-telescope x_P Ξ_P*D)))))])

  (define-judgment-form cic-typingL
    #:mode (type-check I I I I)
    #:contract (type-check Σ Γ e t)

    [(type-infer Σ Γ e t_0)
     (equivalent Σ t t_0)
     ----------------- "DTR-Check"
     (type-check Σ Γ e t)])
  (module+ test
    (check-holds (type-infer ∅ ∅ (Unv 0) (Unv 1)))
    (check-holds (type-infer ∅ (∅ x : (Unv 0)) (Unv 0) (Unv 1)))
    (check-holds (type-infer ∅ (∅ x : (Unv 0)) x (Unv 0)))
    (check-holds (type-infer ∅ ((∅ x_0 : (Unv 0)) x_1 : (Unv 0))
                             (Π (x_3 : x_0) x_1) (Unv 0)))
    (check-holds (type-infer ∅ (∅ x_0 : (Unv 0)) x_0 U_1))
    (check-holds (type-infer ∅ ((∅ x_0 : (Unv 0)) x_2 : x_0) (Unv 0) U_2))
    (check-holds (unv-kind (Unv 0) (Unv 0) (Unv 0)))
    (check-holds (type-infer ∅ (∅ x_0 : (Unv 0)) (Π (x_2 : x_0) (Unv 0)) t))

    (check-holds (type-infer ∅ ∅ (λ (x : (Unv 0)) x) (Π (x : (Unv 0)) (Unv 0))))
    (check-holds (type-infer ∅ ∅ (λ (y : (Unv 0)) (λ (x : y) x))
                             (Π (y : (Unv 0)) (Π (x : y) y))))

    (check-equal? (list (term (Unv 1)))
      (judgment-holds
        (type-infer ∅ ((∅ x1 : (Unv 0)) x2 : (Unv 0)) (Π (t6 : x1) (Π (t2 : x2) (Unv 0)))
               U)
        U))
    ;; ---- Elim
    ;; TODO: Clean up/Reorganize these tests
    (check-true
      (redex-match? cic-typingL
                    (in-hole Θ_m ((((elim x_D) U) e_D) e_P))
                    (term (((((elim truth) Type) T) (Π (x : truth) (Unv 1))) (Unv 0)))))
    (define Σtruth (term (∅ (truth : (Unv 0) ((T : truth))))))
    (check-holds (type-infer ,Σtruth ∅ truth (in-hole Ξ U)))
    (check-holds (type-infer ,Σtruth ∅ T (in-hole Θ_ai truth)))
    (check-holds (type-infer ,Σtruth ∅ (λ (x : truth) (Unv 1))
                        (in-hole Ξ (Π (x : (in-hole Θ truth)) U))))
    (check-equal?
      (term (methods-for truth hole (λ (x : truth) (Unv 1)) ((T : truth))))
      (term (Π (m-T : (Unv 1)) hole)))
    (check-holds (telescope-types ,Σtruth ∅ (hole (Unv 0))
                                  (methods-for truth hole
                                               (λ (x : truth) (Unv 1))
                                               ((T : truth)))))
    (check-holds (type-infer ,Σtruth ∅ ((elim truth) Type) t))
    (check-holds (type-check (∅ (truth : (Unv 0) ((T : truth))))
                            ∅
                            (((((elim truth) (Unv 2)) (λ (x : truth) (Unv 1))) (Unv 0))
                             T)
                            (Unv 1)))
    (check-not-holds (type-check (∅ (truth : (Unv 0) ((T : truth))))
                            ∅
                            (((((elim truth) (Unv 1)) Type) Type) T)
                            (Unv 1)))
    (check-holds
      (type-infer ∅ ∅ (Π (x2 : (Unv 0)) (Unv 0)) U))
    (check-holds
      (type-infer ∅ (∅ x1 : (Unv 0)) (λ (x2 : (Unv 0)) (Π (t6 : x1) (Π (t2 : x2) (Unv 0))))
                  t))
    (check-holds
      (type-infer ,Σ ∅ nat (in-hole Ξ U)))
    (check-holds
      (type-infer ,Σ ∅ zero (in-hole Θ_ai nat)))
    (check-holds
      (type-infer ,Σ ∅ (λ (x : nat) nat)
                  (in-hole Ξ (Π (x : (in-hole Θ nat)) U))))
    (define-syntax-rule (nat-test syn ...)
      (check-holds (type-check ,Σ syn ...)))
    (nat-test ∅ (Π (x : nat) nat) (Unv 0))
    (nat-test ∅ (λ (x : nat) x) (Π (x : nat) nat))
    (nat-test ∅ nat (Unv 0))
    (nat-test ∅ zero nat)
    (nat-test ∅ s (Π (x : nat) nat))
    (nat-test ∅ (s zero) nat)
    ;; TODO: Meta-function auto-currying and such
    (check-holds
      (type-infer ,Σ ∅ (((((elim nat) (Unv 0)) (λ (x : nat) nat))
                           zero)
                           (λ (x : nat) (λ (ih-x : nat) x)))
                  t))
    (nat-test ∅ ((((((elim nat) (Unv 0)) (λ (x : nat) nat))
                    zero)
                    (λ (x : nat) (λ (ih-x : nat) x)))
                   zero)
              nat)
    (nat-test ∅ ((((((elim nat) (Unv 0)) (λ (x : nat) nat))
                    (s zero))
                    (λ (x : nat) (λ (ih-x : nat) (s (s x)))))
                   zero)
              nat)
    (nat-test (∅ n : nat)
      ((((((elim nat) (Unv 0)) (λ (x : nat) nat)) zero) (λ (x : nat) (λ (ih-x : nat) x))) n)
      nat)
    (check-holds
      (type-check (,Σ (bool : (Unv 0) ((btrue : bool) (bfalse : bool))))
             (∅ n2 : nat)
             ((((((elim nat) (Unv 0)) (λ (x : nat) bool))
                  btrue)
                  (λ (x : nat) (λ (ih-x : bool) bfalse)))
                n2)
             bool))
    (check-not-holds
      (type-check ,Σ ∅
             (((((elim nat) (Unv 0)) nat) (s zero)) zero)
             nat))
    (define lam (term (λ (nat : (Unv 0)) nat)))
    (check-equal?
      (list (term (Π (nat : (Unv 0)) (Unv 0))))
      (judgment-holds (type-infer ,Σ0 ∅ ,lam t) t))
    (check-equal?
      (list (term (Π (nat : (Unv 0)) (Unv 0))))
      (judgment-holds (type-infer ,Σ ∅ ,lam t) t))
    (check-equal?
      (list (term (Π (x : (Π (y : (Unv 0)) y)) nat)))
      (judgment-holds (type-infer (∅ (nat : (Unv 0) ())) ∅ (λ (x : (Π (y : (Unv 0)) y)) (x nat))
                            t) t))
    (check-equal?
      (list (term (Π (y : (Unv 0)) (Unv 0))))
      (judgment-holds (type-infer (∅ (nat : (Unv 0) ())) ∅ (λ (y : (Unv 0)) y) t) t))
    (check-equal?
      (list (term (Unv 0)))
      (judgment-holds (type-infer (∅ (nat : (Unv 0) ())) ∅
                            ((λ (x : (Π (y : (Unv 0)) (Unv 0))) (x nat))
                             (λ (y : (Unv 0)) y))
                            t) t))
    (check-equal?
      (list (term (Unv 0)) (term (Unv 1)))
      (judgment-holds
        (type-infer ,Σ4 ∅ (Π (S : (Unv 0)) (Π (B : (Unv 0)) (Π (a : S) (Π (b : B) ((and S) B)))))
               U) U))
    (check-holds
      (type-check ,Σ4 (∅ S : (Unv 0)) conj (Π (A : (Unv 0)) (Π (B : (Unv 0)) (Π (a : A) (Π (b : B) ((and A) B)))))))
    (check-holds
      (type-check ,Σ4 (∅ S : (Unv 0))
        conj (Π (P : (Unv 0)) (Π (Q : (Unv 0)) (Π (x : P) (Π (y : Q) ((and P) Q)))))))
    (check-holds
      (type-check ,Σ4 (∅ S : (Unv 0)) S (Unv 0)))
    (check-holds
      (type-check ,Σ4 (∅ S : (Unv 0)) (conj S)
             (Π (B : (Unv 0)) (Π (a : S) (Π (b : B) ((and S) B))))))
    (check-holds
      (type-check ,Σ4 (∅ S : (Unv 0)) (conj S)
             (Π (B : (Unv 0)) (Π (a : S) (Π (b : B) ((and S) B))))))
    (check-holds
      (type-check ,Σ4 ∅ (λ (S : (Unv 0)) (conj S))
             (Π (S : (Unv 0)) (Π (B : (Unv 0)) (Π (a : S) (Π (b : B) ((and S) B)))))))
    (check-holds
      (type-check (,Σ4 (true : (Unv 0) ((tt : true)))) ∅
             ((((conj true) true) tt) tt)
             ((and true) true)))
    (check-holds
      (type-infer ,Σ4 ∅ and (in-hole Ξ U_D)))
    (check-holds
      (type-infer (,Σ4 (true : (Unv 0) ((tt : true)))) ∅
             ((((conj true) true) tt) tt)
             (in-hole Θ and)))
    (check-holds
      (type-infer (,Σ4 (true : (Unv 0) ((tt : true)))) ∅
             (λ (A : Type) (λ (B : Type) (λ (x : ((and A) B)) true)))
             (in-hole Ξ (Π (x : (in-hole Θ_Ξ and)) U_P))))
    (check-holds
      (type-check (,Σ4 (true : (Unv 0) ((tt : true)))) ∅
             (((((((elim and) (Unv 0))
                  (λ (A : Type) (λ (B : Type) (λ (x : ((and A) B))
                                                 true))))
                 (λ (A : (Unv 0))
                    (λ (B : (Unv 0))
                       (λ (a : A)
                          (λ (b : B) tt)))))
                true) true)
              ((((conj true) true) tt) tt))
             true))
    (check-true (Γ? (term (((∅ P : (Unv 0)) Q : (Unv 0)) ab : ((and P) Q)))))
    (check-holds
      (type-infer ,Σ4 ∅ and (in-hole Ξ U)))
    (check-holds
      (type-infer ,Σ4 (((∅ P : Type) Q : Type) ab : ((and P) Q))
                  ab (in-hole Θ and)))
    (check-true
      (redex-match? cic-redL
        (in-hole Ξ (Π (x : (in-hole Θ and)) U))
        (term (Π (A : (Unv 0)) (Π (B : (Unv 0)) (Π (x : ((and A) B)) (Unv 0)))))))
    (check-holds
      (type-infer ,Σ4 (((∅ P : Type) Q : Type) ab : ((and P) Q))
                  (λ (A : Type) (λ (B : Type) (λ (x : ((and A) B))
                                                 ((and B) A))))
                  (in-hole Ξ (Π (x : (in-hole Θ and)) U))))
    (check-holds
      (equivalent ,Σ4
        (Π (A : (Unv 0)) (Π (B : (Unv 0)) (Π (x : ((and A) B)) (Unv 0))))
        (Π (P : (Unv 0)) (Π (Q : (Unv 0)) (Π (x : ((and P) Q)) (Unv 0))))))
    (check-holds
      (type-infer ,Σ4 ∅
             (λ (A : Type) (λ (B : Type) (λ (x : ((and A) B))
                                            ((and B) A))))
             (in-hole Ξ (Π (x : (in-hole Θ_Ξ and)) U_P))))
    (check-holds
      (type-check ,Σ4
                  (((∅ P : (Unv 0)) Q : (Unv 0)) ab : ((and P) Q))
             (((((((elim and) (Unv 0))
                  (λ (A : Type) (λ (B : Type) (λ (x : ((and A) B))
                                                 ((and B) A)))))
                 (λ (A : (Unv 0))
                    (λ (B : (Unv 0))
                       (λ (a : A)
                          (λ (b : B) ((((conj B) A) b) a))))))
                P) Q) ab)
             ((and Q) P)))
    (check-holds
      (type-check (,Σ4 (true : (Unv 0) ((tt : true)))) ∅
             (λ (A : Type) (λ (B : Type) (λ (x : ((and A) B)) ((and B) A))))
             (Π (A : (Unv 0)) (Π (B : (Unv 0)) (Π (x : ((and A) B)) (Unv 0))))))
    (check-holds
      (type-infer (,Σ4 (true : (Unv 0) ((tt : true))))
             ((∅ A : Type) B : Type)
             (conj B)
             t))
    (check-holds
      (type-check (,Σ4 (true : (Unv 0) ((tt : true)))) ∅
             (((((((elim and) (Unv 0))
                  (λ (A : Type) (λ (B : Type) (λ (x : ((and A) B))
                                                 ((and B) A)))))
                 (λ (A : (Unv 0))
                    (λ (B : (Unv 0))
                       (λ (a : A)
                          (λ (b : B) ((((conj B) A) b) a))))))
                true) true)
              ((((conj true) true) tt) tt))
             ((and true) true)))
    (define gamma (term (∅ temp863 : pre)))
    (check-holds (wf ,sigma ∅))
    (check-holds (wf ,sigma ,gamma))
    (check-holds
      (type-infer ,sigma ,gamma (Unv 0) t))
    (check-holds
      (type-infer ,sigma ,gamma pre t))
    (check-holds
      (type-check ,sigma (,gamma tmp863 : pre) (Unv 0) (Unv 1)))
    (check-holds
      (type-infer ,sigma ,gamma pre t))
    (check-holds
      (type-check ,sigma (,gamma tmp863 : pre) (Unv 0) (Unv 1)))
    (check-holds
      (type-infer ,sigma (,gamma x : false) false (in-hole Ξ U_D)))
    (check-holds
      (type-infer ,sigma (,gamma x : false) x (in-hole Θ false)))
    (check-holds
      (type-infer ,sigma (,gamma x : false) (λ (y : false) (Π (x : Type) x))
             (in-hole Ξ (Π (x : (in-hole Θ false)) U))))
    (check-true
      (redex-match? cic-typingL
        ((in-hole Θ_m (((elim x_D) U) e_P)) e_D)
        (term ((((elim false) (Unv 1)) (λ (y : false) (Π (x : Type) x)))
               x))))
    (check-holds
      (type-check ,sigma (,gamma x : false)
             ((((elim false) (Unv 0)) (λ (y : false) (Π (x : Type) x))) x)
             (Π (x : (Unv 0)) x)))

    ;; nat-equal? tests
    (define zero?
      (term (((((elim nat) Type) (λ (x : nat) bool))
                         true)
                        (λ (x : nat) (λ (x_ih : bool) false)))))
    (check-holds
      (type-check ,Σ ∅ ,zero? (Π (x : nat) bool)))
    (check-equal?
      (term (reduce ,Σ (,zero? zero)))
      (term true))
    (check-equal?
      (term (reduce ,Σ (,zero? (s zero))))
      (term false))
    (define ih-equal?
      (term (((((elim nat) Type) (λ (x : nat) bool))
         false)
        (λ (x : nat) (λ (y : bool) (x_ih x))))))
    (check-holds
      (type-check ,Σ (∅ x_ih : (Π (x : nat) bool))
                  ,ih-equal?
                  (Π (x : nat) bool)))
    (check-holds
      (type-infer ,Σ ∅ nat (Unv 0)))
    (check-holds
      (type-infer ,Σ ∅ bool (Unv 0)))
    (check-holds
      (type-infer ,Σ ∅ (λ (x : nat) (Π (x : nat) bool)) (Π (x : nat) (Unv 0))))
    (define nat-equal?
      (term (((((elim nat) Type) (λ (x : nat) (Π (x : nat) bool)))
         ,zero?)
        (λ (x : nat) (λ (x_ih : (Π (x : nat) bool))
                            ,ih-equal?)))))
    (check-holds
      (type-check ,Σ ∅
                  ,nat-equal?
                  (Π (x : nat) (Π (y : nat) bool))))
    (check-equal?
      (term (reduce ,Σ ((,nat-equal? zero) (s zero))))
      (term false))
    (check-equal?
      (term (reduce ,Σ ((,nat-equal? (s zero)) zero)))
      (term false))))

;; This module just provide module language sugar over the redex model.

;; TODO: Strip to racket/base as much as possible.
;; TODO: Remove trace,pretty, debugging stuff
(module sugar racket
  (require
    racket/trace
    racket/pretty
    (submod ".." core)
    redex/reduction-semantics
    racket/provide-syntax
    (for-syntax
      (except-in racket import)
      syntax/parse
      racket/pretty
      racket/trace
      racket/syntax
      (except-in racket/provide-transform export)
      racket/require-transform
      (except-in (submod ".." core) remove)
      redex/reduction-semantics))
  (provide
    ;; Basic syntax
    for-syntax
    only-in
    all-defined-out
    rename-in
    #%module-begin
    begin
    (rename-out
      [dep-module+ module+]
      [dep-provide provide]
      [dep-require require]

      [dep-lambda lambda]
      [dep-lambda λ]
      [dep-app #%app]

      [dep-forall forall]
      [dep-forall ∀]

      [dep-inductive data]

      [dep-elim elim]

      [dep-var #%top]

;      [dep-datum #%datum]
      [dep-define define])
    Type
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
      type-infer/syn
      type-check/syn?
      normalize/syn)
    run)

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
          (unless (Γ? x)
            (error 'core-error "We built a bad gamma ~s" x))
          x)))

    (define sigma
      (make-parameter (term ∅)
        (lambda (x)
          (unless (Σ? x)
            (error 'core-error "We built a bad sigma ~s" x))
          x)))

    (define (extend-Γ/term env x t)
      (term (,(env) ,x : ,t)))

    (define (extend-Γ/term! env x t) (env (extend-Γ/term env x t)))

    (define (extend-Γ/syn env x t)
      (extend-Γ/term env (syntax->datum x) (cur->datum t)))

    (define (extend-Γ/syn! env x t) (env (extend-Γ/syn env x t)))

    (define (extend-Σ/term env x t c*)
      (term (,(env) (,x : ,t (,@c*)))))

    (define (extend-Σ/term! env x t c*)
      (env (extend-Σ/term env x t c*)))

    (define (extend-Σ/syn env x t c*)
      (extend-Σ/term env (syntax->datum x) (cur->datum t)
        (for/list ([c (syntax->list c*)])
          (syntax-case c ()
            [(c : ct)
             (parameterize ([gamma (extend-Γ/syn gamma x t)])
               (term (,(syntax->datum #'c) : ,(cur->datum #'ct))))]))))

    (define (extend-Σ/syn! env x t c*)
      (env (extend-Σ/syn env x t c*)))

    (define bind-subst (make-parameter (list null null)))

    (define (add-binding/term! x t)
      (let ([vars (first (bind-subst))]
            [exprs (second (bind-subst))])
           (bind-subst (list (cons x vars) (cons t exprs)))))

    ;; TODO: Still absurdly slow. Probably doing n^2 checks of sigma and
    ;; gamma. And lookup on sigma, gamma are linear, so probably n^2 lookup time.
    (define (type-infer/term t)
      (let ([t (judgment-holds (type-infer ,(sigma) ,(gamma) ,t t_0) t_0)])
        (and (pair? t) (car t))))

    (define (type-check/term? e t)
      (and (judgment-holds (type-check ,(sigma) ,(gamma) ,e ,t)) #t))

    (define (syntax->curnel-syntax syn) (denote syn (cur->datum syn)))

    (define (denote syn t)
      (quasisyntax/loc
        syn
        (term (reduce #,(sigma) (subst-all #,(datum->syntax syn t) #,(first (bind-subst)) #,(second (bind-subst)))))))

    ;; TODO: Blanket disarming is probably a bad idea.
    (define orig-insp (variable-reference->module-declaration-inspector
                        (#%variable-reference)))
    (define (disarm syn) (syntax-disarm syn orig-insp))

    ;; Locally expand everything down to core forms.
    (define (core-expand syn)
      (disarm
        (local-expand syn 'expression
          (append (syntax-e #'(term reduce subst-all dep-var #%app λ Π elim
                               Unv #%datum))))))

    ;; Only type-check at the top-level, to prevent exponential
    ;; type-checking. Redex is expensive enough.
    ;; TODO: This results in less good error messages. Add an
    ;; algorithm to find the smallest ill-typed term.
    (define inner-expand? (make-parameter #f))

    ;; Expand a piece of syntax into a curnel redex term
    (define (cur->datum syn)
      ;; Main loop; avoid type
      (define reified-term
        (parameterize ([inner-expand? #t])
          (let cur->datum ([syn syn])
            (syntax-parse (core-expand syn)
              #:literals (term reduce #%app subst-all)
              #:datum-literals (elim Π λ : Unv)
              [x:id (syntax->datum #'x)]
              [(subst-all e _ _) (syntax->datum #'e)]
              [(reduce Σ e) (cur->datum #'e)]
              [(term e) (cur->datum #'e)]
              [(Unv i) (term (Unv ,(syntax->datum #'i)))]
              ;; TODO: should really check that b is one of the binders
              ;; Maybe make a syntax class for the binders, core forms,
              ;; etc.
              [(b:id (x:id : t) e)
               (let* ([x (syntax->datum #'x)]
                      [t (cur->datum #'t)]
                      [e (parameterize ([gamma (extend-Γ/term gamma x t)])
                           (cur->datum #'e))])
                 (term (,(syntax->datum #'b) (,x : ,t) ,e)))]
              [(elim t e P m ...)
               (let* ([t (cur->datum #'t)]
                      [e (cur->datum #'e)]
                      [P (cur->datum #'P)]
                      [e (term (((elim ,t) ,e) ,P))])
                 (for/fold ([e e])
                           ([m (syntax->list #'(m ...))])
                   (term (,e ,(cur->datum m)))))]
              [(#%app e1 e2)
               (term (,(cur->datum #'e1) ,(cur->datum #'e2)))]))))
      (unless (and inner-expand? (type-infer/term reified-term))
        ;; TODO: is this really a syntax error?
        (raise-syntax-error 'cur "term is ill-typed:"
          (begin (printf "Sigma: ~s~nGamma: ~s~n" (sigma) (gamma))
                 reified-term)
          syn))
      reified-term)

    ;; Reflection tools
    (define (normalize/syn syn)
      (denote syn (term (reduce ,(sigma) (subst-all ,(cur->datum syn) ,(first (bind-subst)) ,(second (bind-subst)))))))

    (define (run-cur->datum syn)
      (cur->datum (normalize/syn syn)))

    ;; TODO: OOps, type-infer doesn't return a cur term but a redex term
    ;; wrapped in syntax bla. This is bad.
    (define (type-infer/syn syn)
      (let ([t (type-infer/term (run-cur->datum syn))])
        (and t (datum->syntax syn t))))

    (define (type-check/syn? syn type)
      (type-check/term? (run-cur->datum syn) (run-cur->datum type)))

    ;; Takes a Cur term syn and an arbitrary number of identifiers ls. The cur term is
    ;; expanded until expansion reaches a Curnel form, or one of the
    ;; identifiers in ls.
    (define (cur-expand syn . ls)
      (disarm (local-expand syn 'expression
                (append (syntax-e #'(Type dep-inductive dep-lambda dep-app
                                   dep-elim dep-forall dep-var))
                        ls)))))

    ;; TODO: OOps, run doesn't return a cur term but a redex term
    ;; wrapped in syntax bla. This is bad.
    (define-syntax (run syn)
      (syntax-case syn ()
        [(_ expr) (normalize/syn #'expr)]))

  ;; -----------------------------------------------------------------
  ;; Require/provide macros

  ;; TODO: This is code some of the most hacky awful code I've ever
  ;; written. But it works.
  (begin-for-syntax
    (define envs (list #'(void)))

    (define (cur-identifier-bound? id)
      (let ([x (syntax->datum id)])
        (and (x? x)
             (or (term (lookup-Γ ,(gamma) ,x))
               (term (lookup-Σ ,(sigma) ,x))))))

    (define (filter-cur-exports syn modes)
      (partition (compose cur-identifier-bound? export-local-id)
                 (apply append (map (lambda (e) (expand-export e modes))
                                    (syntax->list syn))))))
  (define-syntax extend-env-and-provide
    (make-provide-transformer
      (lambda (syn modes)
        (syntax-case syn ()
          [(_ e ...)
           (let-values ([(cur ~cur) (filter-cur-exports #'(e ...) modes)])
             ;; TODO: Ignoring the built envs for now
             #;(set! envs (for/list ([e cur])
                       (let* ([x (syntax->datum (export-local-id e))]
                                 [t (type-infer/term x)]
                                 [env (if (term (lookup ,(gamma) ,x)) #'gamma #'sigma)])
                            #`(extend-env/term! #,env #,(export-out-sym e) #,t))))
             ~cur)]))))

  (define-syntax (export-envs syn)
    (syntax-case syn ()
      [(_ gamma-out sigma-out bind-out)
       #`(begin-for-syntax
           (define gamma-out (term #,(gamma)))
           (define sigma-out (term #,(sigma)))
           (define bind-out '#,(bind-subst)))]))

  ;; TODO: This can only handle a single provide form, otherwise
  ;; generates multiple *-out
  (define-syntax (dep-provide syn)
    (syntax-case syn ()
      [(_ e ...)
       (begin
         ;; TODO: Ignoring the built envs above, for now
         ;; The local-lift export seems to get executed before the
         ;; filtered environment is built.
         ;; TODO: rename out will need to rename variables in gamma and
         ;; sigma.
         (syntax-local-lift-module-end-declaration
           #`(export-envs gamma-out sigma-out bind-out))
         #`(provide (extend-env-and-provide e ...)
                    (for-syntax gamma-out sigma-out bind-out)))]))
  (begin-for-syntax
    (define out-gammas #`())
    (define out-sigmas #`())
    (define out-binds #`())
    (define gn 0)
    (define sn 0)
    (define bn 0)
    (define (filter-cur-imports syn)
      (for/fold ([imports '()]
                 [sources '()])
                ([req-spec (syntax->list syn)])
        (let-values ([(more-imports more-sources) (expand-import req-spec)])
          (values (for/fold ([imports imports])
                     ([imp more-imports])
                     (cond
                       [(equal? (import-src-sym imp) 'gamma-out)
                        (let ([new-id (format-id (import-orig-stx imp)
                                                 "gamma-out~a" gn)])
                             ;; TODO: Fewer set!s
                             ;; TODO: Do not DIY gensym
                             (set! gn (add1 gn))
                             (set! out-gammas
                               #`(#,@out-gammas (gamma (term (append-Γ
                                                               ,(gamma)
                                                               ,#,new-id)))))
                             (cons (struct-copy import imp [local-id new-id])
                                   imports))]
                       ;; TODO: Many shared code between these two clauses
                       [(equal? (import-src-sym imp) 'sigma-out)
                        (let ([new-id (format-id (import-orig-stx imp)
                                                 "sigma-out~a" sn)])
                             ;; TODO: Fewer set!s
                             ;; TODO: Do not DIY gensym
                             (set! sn (add1 sn))
                             (set! out-sigmas
                               #`(#,@out-sigmas (sigma (term (append-Σ
                                                               ,(sigma)
                                                               ,#,new-id)))))
                             (cons (struct-copy import imp [local-id new-id])
                                   imports))]
                       ;; TODO: Many shared code between these two clauses
                       [(equal? (import-src-sym imp) 'bind-out)
                        (let ([new-id (format-id (import-orig-stx imp)
                                                 "bind-out~a" bn)])
                             ;; TODO: Fewer set!s
                             ;; TODO: Do not DIY gensym
                             (set! bn (add1 bn))
                             (set! out-binds
                               #`(#,@out-binds (bind-subst (list (append
                                                                   (first #,new-id)
                                                                   (first (bind-subst)))
                                                                 (append
                                                                   (second #,new-id)
                                                                   (second (bind-subst)))))))
                             (cons (struct-copy import imp [local-id new-id])
                                   imports))]
                       [else (cons imp imports)]))
                  (append sources more-sources))))))

  (define-syntax extend-env-and-require
    (make-require-transformer (lambda (syn)
                                (syntax-case syn ()
                                  [(_ e ...) (filter-cur-imports #'(e ...))]))))

    ;; TODO: rename in will need to rename variables in gamma and
    ;; sigma.
    (define-syntax (import-envs syn)
      (syntax-case syn ()
        [(_) #`(begin-for-syntax #,@out-gammas #,@out-sigmas
                                 #,@out-binds)]))

  (define-syntax (dep-require syn)
    (syntax-case syn ()
      [(_ e ...)
       #`(begin
          (require (extend-env-and-require e ...))
          (import-envs))]))

  (define-syntax (dep-module+ syn)
    (syntax-case syn ()
      [(_ name body ...)
       #`(module+ name
           (begin-for-syntax
             (gamma (term #,(gamma)))
             (sigma (term #,(sigma)))
             (bind-subst '#,(bind-subst)))
           body ...)]))

  ;; -----------------------------------------------------------------
  ;; Core wrapper macros
  ;;
  ;; TODO: Can these be simplified further?
  ;; TODO: Can we make core-expand some kind of parameter that is only
  ;; to ensure type-checking is only done at the outermost level, and
  ;; not in the main loop?
  #;(define-syntax (dep-datum syn) (denote #'syn))
  (define-syntax (dep-lambda syn)
    (syntax-case syn (:)
      [(_ (x : t) e)
       (syntax->curnel-syntax
         (quasisyntax/loc syn (λ (x : t) e)))]))

  (define-syntax (dep-app syn)
    (syntax-case syn ()
      [(_ e1 e2)
       (syntax->curnel-syntax
         (quasisyntax/loc syn (#%app e1 e2)))]))

  (define-syntax (dep-forall syn)
    (syntax-case syn (:)
      [(_ (x : t) e)
       (syntax->curnel-syntax
         (quasisyntax/loc syn (Π (x : t) e)))]))

  (define-syntax (Type syn)
    (syntax-case syn ()
      [(_ i)
       (syntax->curnel-syntax
         (quasisyntax/loc syn (Unv i)))]
      [_ (quasisyntax/loc syn (Type 0))]))

  (define-syntax (dep-inductive syn)
    (syntax-case syn (:)
      [(_ i : ti (x1 : t1) ...)
       (begin
         (extend-Σ/syn! sigma #'i #'ti #'((x1 : t1) ...))
         #'(void))]))

  (define-syntax (dep-elim syn)
    (syntax-case syn (:)
      [(_ D e P method ...)
       (syntax->curnel-syntax
         (quasisyntax/loc syn (elim D e P method ...)))]))

  ;; TODO: Not sure if this is the correct behavior for #%top
  (define-syntax (dep-var syn)
    (syntax-case syn ()
      [(_ . id) #`(term (reduce #,(sigma) id))]))

  ;; TODO: Syntax-parse
  (define-syntax (dep-define syn)
    (syntax-case syn (:)
      [(_ (name (x : t)) e)
       #'(dep-define name (dep-lambda (x : t) e))]
      [(_ id e)
       ;; TODO: Can't actually run programs until I do something about
       ;; #'e. Maybe denote final terms into Racket. Or keep an
       ;; environment and have denote do a giant substitution
       (let ([e (cur->datum #'e)]
             [id (syntax->datum #'id)])
         (extend-Γ/term! gamma id (type-infer/term e))
         (add-binding/term! id e)
         #'(void))])))

(require (rename-in 'sugar [module+ dep-module+]))
(provide (rename-out [dep-module+ module+]) (all-from-out 'sugar))
(module+ test
  (require (submod ".." core test)))

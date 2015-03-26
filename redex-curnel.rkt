#lang racket

;; TODO: Strip to racket/base as much as possible
(module core racket
  (require
    (only-in racket/set set=?)
    redex/reduction-semantics)
  (provide
    (all-defined-out))

  (set-cache-size! 10000)

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
    (v ::= (Π (x : t) t) (λ (x : t) t) x U)
    (t e ::= v (t t) (elim e ...)))
  (define x? (redex-match? cicL x))
  (define t? (redex-match? cicL t))
  (define e? (redex-match? cicL e))
  (define v? (redex-match? cicL v))
  (define U? (redex-match? cicL U))

  (module+ test
    (require rackunit)
    (define-term Type (Unv 0))
    (check-true (x? (term T)))
    (check-true (x? (term truth)))
    (check-true (x? (term zero)))
    (check-true (x? (term s)))
    (check-true (t? (term zero)))
    (check-true (t? (term s)))
    (check-true (x? (term nat)))
    (check-true (t? (term nat)))
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
    [(subst (any (x : t_0) t_1) x t) (any (x : (subst t_0 x t)) t_1)]
    ;; TODO: Broken: needs capture avoiding, but currently require
    ;; binders to be the same in term/type, so this is not a local
    ;; change.
    [(subst (any (x_0 : t_0) t_1) x t) (any (x_0 : (subst t_0 x t)) (subst t_1 x t))]
    [(subst (e_0 e_1) x t) ((subst e_0 x t) (subst e_1 x t))])
  (module+ test
    (check-equal?
      (term (Π (a : S) (Π (b : B) ((and S) B))))
      (term (subst (Π (a : A) (Π (b : B) ((and A) B))) A S))))
  ;; NB:
  ;; TODO: Why do I not have tests for substitutions?!?!?!?!?!?!?!!?!?!?!?!?!?!!??!?!

  (define-metafunction cicL
    subst-all : t (x ...) (e ...) -> t
    [(subst-all t () ()) t]
    [(subst-all t (x_0 x ...) (e_0 e ...))
     (subst-all (subst t x_0 e_0) (x ...) (e ...))])

  (define-extended-language cic-redL cicL
    (E   ::= hole (E t)) ;; Call-by-name??
    ;; Σ (signature). (inductive-name : type ((constructor : type) ...))
    (Σ   ::= ∅ (Σ (x : t ((x : t) ...))))
    (Ξ Φ ::= hole (Π (x : t) Ξ)) ;;(Telescope)
    ;; NB: Does an apply context correspond to a substitution (γ) in a de
    ;; NB: Bruijn setting?
    (Θ   ::= hole (Θ e)))        ;;(Apply context)
  (define Σ? (redex-match? cic-redL Σ))
  (define Ξ? (redex-match? cic-redL Ξ))
  (define Φ? (redex-match? cic-redL Φ))
  (define Θ? (redex-match? cic-redL Θ))
  (define E? (redex-match? cic-redL E))

  (module+ test
    ;; TODO: Rename these signatures, and use them in all future tests.
    (define Σ (term (∅ (nat : (Unv 0) ((zero : nat) (s : (Π (x : nat) nat)))))))
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

  ;; TODO: Test
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
    [(select-arg x (x x_r ...) (Θ e)) e]
    [(select-arg x (x_1 x_r ...) (Θ e))
     (select-arg x (x_r ...) Θ)])

  (define-metafunction cic-redL
    method-lookup : Σ x x (Θ e) -> e
    [(method-lookup Σ x_D x_ci Θ)
     (select-arg x_ci (x_0 ...) Θ)
     (where ((x_0 : t_0) ...) (constructors-for Σ x_D)) ])

  ;; TODO: This should be a helper, as it has a weird invariant about
  ;; TODO: the first two Θs that should not be exposed to caller
  (define-metafunction cic-redL
    elim-recur : x e Θ Θ Θ (x ...) -> Θ
    [(elim-recur x_D e_P Θ hole hole () e_P) hole]
    [(elim-recur x_D e_P Θ (in-hole Θ_m (hole e_mi)) (in-hole Θ_t (in-hole Θ_r x_ci))
       (x_ci x_c  ...) e_P )
     ((elim-recur x_D e_P Θ Θ_m Θ_i (x_c ...))
      (in-hole Θ (((elim x_D) (in-hole Θ_r x_ci)) e_P)))])

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
      ;; TODO: This doesn't seem right; need to check that x not bound in e_f
      #;(--> (Σ (in-hole E (any (x : t_0) (e_f x))))
           (Σ (in-hole E e_f))
           -->η)
      (--> (Σ (in-hole E (in-hole Θ_m (((elim x_D) (in-hole Θ_i x_ci)) e_P))))
           (Σ (in-hole E (in-hole Θ_r (in-hole Θ_i e_mi))))
           (where ((x_c : t_c) ...) (constructors-for Σ x_D))
           ;; There should be a number of methods equal to the number of
           ;; constructors; to ensure E doesn't capture methods
           (judgment-holds (length-match Θ_m (x_c ...)))
           (where e_mi (method-lookup Σ x_D x_ci Θ_m))
           (where Θ_r (elim-recur x_D e_P Θ_m Θ_m Θ_i (x_c ...)))
           -->elim)))

  ;; Reducing elim:
  ;; (in-hole Θ_m (((elim D) (in-hole Θ_i c_i)) v_P)) ->
  ;;   (in-hole Θ_r (in-hole Θ_i m_i) ...)
  ;;   (where m_i (method-lookup D c_i Θ_m))
  ;;   (where Θ_r (elim-recur D Θ_m Θ_i (constructors-for D) v_P Θ_m))
  ;;
  ;; (elim-recur D Θ_m hole () v_P hole) = hole
  ;; Not so sure about the (in-hole Θ_t ) bit. Trying to ignore the
  ;; non-recursive parameters.
  ;; (elim-recur D Θ (in-hole Θ_t (Θ_i (in-hole Θ_r c_i))) (c_i c ...) v_P (Θ_m m_i)) =
  ;;   ((elim-recur D Θ Θ_i (c ...) v_P Θ_m) (in-hole Θ (((elim D) (in-hole Θ_r c_i)) v_P))

  (define-metafunction cic-redL
    reduce : Σ e -> e
    [(reduce Σ e) e_r
     (where (_ e_r) ,(car (apply-reduction-relation* cic--> (term (Σ e)))))])
  (module+ test
    (check-equal? (term (reduce ∅ (Unv 0))) (term (Unv 0)))
    (check-equal? (term (reduce ∅ ((λ (x : t) x) (Unv 0)))) (term (Unv 0)))
    (check-equal? (term (reduce ∅ ((Π (x : t) x) (Unv 0)))) (term (Unv 0)))
    ;; NB: Currently not reducing under binders. I forget why.
    (check-equal? (term (reduce ∅ (Π (x : t) ((Π (x_0 : t) x_0) (Unv 0)))))
                  (term (Π (x : t) (Unv 0))))
    (check-equal? (term (reduce ∅ (Π (x : t) ((Π (x_0 : t) x_0) x))))
                  (term (Π (x_0 : t) x_0)))
    (check-equal? (term (reduce ∅ (Π (x : t) ((Π (x_0 : t) (x_0 x)) x))))
                  (term (Π (x : t) ((Π (x_0 : t) (x_0 x)) x))))
    (check-equal? (term (reduce ,Σ (((((elim nat) (s z)) (λ (x : nat) nat))
                                    (s z))
                                    (λ (x : nat) (λ (ih-x : nat) (s (s x)))))))
                  (term (s (s z))))
    (check-equal? (term (reduce ,Σ (elim nat (s (s (s z))) nat (s z) (λ (x : nat)
                                                                     (s (s
                                                                          x))))))
                  (term (s (s (s (s z)))))))


  (define-extended-language cic-typingL cic-redL
    ;; NB: There may be a bijection between Γ and Ξ. That's
    ;; NB: interesting.
    (Γ   ::= ∅ (Γ x : t)))
  (define Γ? (redex-match? cic-typingL Γ))

  (define-metafunction cic-typingL
    append-env : Γ Γ -> Γ
    [(append-env Γ ∅) Γ]
    [(append-env Γ_2 (Γ_1 x : t))
     ((append-env Γ_2 Γ_1) x : t)])

  ;; NB: Depends on clause order
  (define-metafunction cic-typingL
    lookup-Γ : Γ x -> t or #f
    [(lookup-Γ ∅ x) #f]
    [(lookup-Γ (Γ x : t) x) t]
    [(lookup-Γ (Γ x_0 : t_0) x_1) (lookup-Γ Γ x_1)])

  ;; NB: Depends on clause order
  (define-metafunction cic-typingL
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

    [(types Σ Γ t t_0)
     (wf Σ Γ)
     ----------------- "WF-Var"
     (wf Σ (Γ x : t))]

    [(wf Σ ∅)
     (types Σ ∅ t_D U_D)
     (types Σ (∅ x_D : t_D) t_c U_c) ...
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
    (check-true (judgment-holds (wf (∅ (nat : (Unv 0) ())) ∅)))

    (check-true (judgment-holds (wf ,Σ0 ∅)))
    (check-true (judgment-holds (types ∅ ∅ (Unv 0) U)))
    (check-true (judgment-holds (types ∅ (∅ nat : (Unv 0)) nat U)))
    (check-true (judgment-holds (types ∅ (∅ nat : (Unv 0)) (Π (x : nat) nat) U)))
    (check-true (term (positive nat (nat (Π (x : nat) nat)))))
    (check-true
      (judgment-holds (wf (∅ (nat : (Unv 0) ((zero : nat)))) ∅)))
    (check-true
      (judgment-holds (wf (∅ (nat : (Unv 0) ((s : (Π (x : nat) nat))))) ∅)))
    (check-true (judgment-holds (wf ,Σ ∅)))

    (check-true (judgment-holds (wf ,Σ3 ∅)))
    (check-true (judgment-holds (wf ,Σ4 ∅)))
    (check-true (judgment-holds (wf (∅ (truth : (Unv 0) ())) ∅)))
    (check-true (judgment-holds (wf ∅ (∅ x : (Unv 0)))))
    (check-true (judgment-holds (wf (∅ (nat : (Unv 0) ())) (∅ x : nat))))
    (check-true (judgment-holds (wf (∅ (nat : (Unv 0) ())) (∅ x : (Π (x : nat) nat))))))

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

    [(types Σ Γ e t)
     (telescope-types Σ Γ Θ Ξ)
     ----------------- "TT-Match"
     (telescope-types Σ Γ (in-hole Θ (hole e)) (Π (x : t) Ξ))])
  (module+ test
    (check-true
      (judgment-holds (telescope-types ,Σ ∅ (hole zero) (Π (x : nat) hole))))
    (check-true
      (redex-match? cic-redL (in-hole Θ (hole e))
                    (term ((hole zero) (λ (x : nat) x)))))
    (check-true
      (judgment-holds (telescope-types ,Σ ∅ (hole zero)
                                       (methods-for nat hole
                                         (λ (x : nat) nat)
                                         ((zero : nat))))))
    (check-true
      (judgment-holds (types ,Σ ∅ (λ (x : nat) (λ (ih-x : nat) x))
                             (Π (x : nat) (Π (ih-x : nat) nat)))))
    (check-true
      (judgment-holds (telescope-types ,Σ ∅
                        ((hole zero)
                         (λ (x : nat) (λ (ih-x : nat) x)))
                        (methods-for nat hole
                                     (λ (x : nat) nat)
                                     (constructors-for ,Σ nat)))))
    (check-true
      (judgment-holds
        (telescope-types (,Σ4 (true : (Unv 0) ((tt : true))))
          ∅ (hole (λ (A : (Unv 0)) (λ (B : (Unv 0))
                        (λ (a : A) (λ (b : B) tt)))))
          (methods-for and (Π (A : Type) (Π (B : Type) hole))
            (λ (A : Type) (λ (B : Type) (λ (x : ((and A) B)) true)))
            (constructors-for ,Σ4 and)))))
    (check-true
      (judgment-holds
        (telescope-types ,sigma (∅ x : false)
          hole
          (methods-for false hole (λ (y : false) (Π (x : Type) x))
            ())))))

  ;; TODO: Bi-directional and inference?
  ;; TODO: http://www.cs.ox.ac.uk/ralf.hinze/WG2.8/31/slides/stephanie.pdf

  ;; Holds when e has type t under signature Σ and typing context Γ
  (define-judgment-form cic-typingL
    #:mode (types I I I O)
    #:contract (types Σ Γ e t)

    [(unv-ok U_0 U_1)
     (wf Σ Γ)
     ----------------- "DTR-Axiom"
     (types Σ Γ U_0 U_1)]

    [(where t (lookup-Σ Σ x))
     ----------------- "DTR-Inductive"
     (types Σ Γ x t)]

    ;; TODO: Require alpha-equiv here, at least.
    [(where t (lookup-Γ Γ x))
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

    [(types Σ Γ x_D (in-hole Ξ U_D))
     (types Σ Γ e_D (in-hole Θ_ai x_D))
     (types Σ Γ e_P (in-hole Ξ (Π (x : (in-hole Θ_Ξ x_D)) U_P)))
     ;; methods
     (telescope-types Σ Γ Θ_m (methods-for x_D Ξ e_P (constructors-for Σ x_D)))
     ----------------- "DTR-Elim_D"
     (types Σ Γ (in-hole Θ_m (((elim x_D) e_D) e_P)) (reduce Σ ((in-hole Θ_ai e_P) e_D)))]

    ;; TODO: beta-equiv
    ;; TODO: This rule is no good for algorithmic checking; Redex infinitly
    ;; TODO: searches it.
    ;; TODO: Perhaps something closer to Zombies = type would be better.
    ;; TODO: For now, reduce types manually
    #;[(types Σ Γ e t)
     (types Σ Γ t U)
     (converts Σ t t_1)
     (types Σ Γ t_1 U)
     ----------------- "DTR-Conversion"
     (types Σ Γ e t_1)])
  (module+ test
    (check-true (judgment-holds (types ∅ ∅ (Unv 0) (Unv 1))))
    (check-true (judgment-holds (types ∅ (∅ x : (Unv 0)) (Unv 0) (Unv 1))))
    (check-true (judgment-holds (types ∅ (∅ x : (Unv 0)) x (Unv 0))))
    (check-true (judgment-holds (types ∅ ((∅ x_0 : (Unv 0)) x_1 : (Unv 0))
                                       (Π (x_3 : x_0) x_1) (Unv 0))))

    (check-true (judgment-holds (types ∅ (∅ x_0 : (Unv 0)) x_0 U_1)))
    (check-true (judgment-holds (types ∅ ((∅ x_0 : (Unv 0)) x_2 : x_0) (Unv 0) U_2)))
    (check-true (judgment-holds (unv-kind (Unv 0) (Unv 0) (Unv 0))))
    (check-true (judgment-holds (types ∅ (∅ x_0 : (Unv 0)) (Π (x_2 : x_0) (Unv 0)) t)))

    (check-true (judgment-holds (types ∅ ∅ (λ (x : (Unv 0)) x) (Π (x : (Unv 0)) (Unv 0)))))
    (check-true (judgment-holds (types ∅ ∅ (λ (y : (Unv 0)) (λ (x : y) x))
                                       (Π (y : (Unv 0)) (Π (x : y) y)))))

    (check-equal? (list (term (Unv 1)))
      (judgment-holds
        (types ∅ ((∅ x1 : (Unv 0)) x2 : (Unv 0)) (Π (t6 : x1) (Π (t2 : x2) (Unv 0)))
               U)
        U))
    (check-true
      (judgment-holds
        (types ∅ ∅ (Π (x2 : (Unv 0)) (Unv 0))
               U)))
    (check-true
      (judgment-holds
        (types ∅ (∅ x1 : (Unv 0)) (λ (x2 : (Unv 0)) (Π (t6 : x1) (Π (t2 : x2) (Unv 0))))
               t)))
    (check-true
      (judgment-holds (types (∅ (truth : (Unv 0) ((T : truth))))
                             ∅
                             T
                             truth)))
    (check-true
      (judgment-holds (types (∅ (truth : (Unv 0) ((T : truth))))
                             ∅
                             (Unv 0)
                             (Unv 1))))

    ;; ---- Elim
    ;; TODO: Clean up/Reorganize these tests
    (check-true
      (redex-match? cic-typingL
                    (in-hole Θ_m (((elim x_D) e_D) e_P))
                    (term ((((elim truth) T) (Π (x : truth) (Unv 1))) (Unv 0)))))
    (define Σtruth (term (∅ (truth : (Unv 0) ((T : truth))))))
    (check-true
      (judgment-holds (types ,Σtruth ∅ truth (in-hole Ξ U))))
    (check-true
      (judgment-holds (types ,Σtruth ∅ T (in-hole Θ_ai truth))))
    (check-true
      (judgment-holds (types ,Σtruth ∅ (λ (x : truth) (Unv 1))
                             (in-hole Ξ (Π (x : (in-hole Θ truth)) U)))))
    (check-equal?
      (term (methods-for truth hole (λ (x : truth) (Unv 1)) ((T : truth))))
      (term (Π (m-T : (Unv 1)) hole)))
    (check-true
      (judgment-holds (telescope-types ,Σtruth ∅ (hole (Unv 0))
                                       (methods-for truth hole
                                         (λ (x : truth) (Unv 1))
                                         ((T : truth))))))
    (check-true
      (judgment-holds (types (∅ (truth : (Unv 0) ((T : truth))))
                             ∅
                             ((((elim truth) T) (λ (x : truth) (Unv 1))) (Unv 0))
                             (Unv 1))))

    (check-false
      (judgment-holds (types (∅ (truth : (Unv 0) ((T : truth))))
                             ∅
                             (((((elim truth) T) (Unv 1)) Type) Type)
                             (Unv 1))))
    (define-syntax-rule (nat-test syn ...)
      (check-true (judgment-holds (types ,Σ syn ...))))
    (nat-test ∅ (Π (x : nat) nat) (Unv 0))
    (nat-test ∅ (λ (x : nat) x) (Π (x : nat) nat))

    (check-true
      (judgment-holds (types ,Σ ∅ nat (in-hole Ξ U))))
    (check-true
      (judgment-holds (types ,Σ ∅ zero (in-hole Θ_ai nat))))
    (check-true
      (judgment-holds (types ,Σ ∅ (λ (x : nat) nat)
                             (in-hole Ξ (Π (x : (in-hole Θ nat)) U)))))


    (nat-test ∅ (((((elim nat) zero) (λ (x : nat) nat)) zero)
                 (λ (x : nat) (λ (ih-x : nat) x)))
              nat)
    (nat-test ∅ nat (Unv 0))
    (nat-test ∅ zero nat)
    (nat-test ∅ s (Π (x : nat) nat))
    (nat-test ∅ (s zero) nat)
    (nat-test ∅ (((((elim nat) zero) (λ (x : nat) nat))
                  (s zero))
                  (λ (x : nat) (λ (ih-x : nat) (s (s x)))))
              nat)
    (check-false (judgment-holds
                    (types ,Σ
                           ∅
                           (elim nat zero nat (s zero))
                           nat)))
    (define lam (term (λ (nat : (Unv 0)) nat)))
    (check-equal?
      (list (term (Π (nat : (Unv 0)) (Unv 0))))
      (judgment-holds (types ,Σ0 ∅ ,lam t) t))
    (check-equal?
      (list (term (Π (nat : (Unv 0)) (Unv 0))))
      (judgment-holds (types ,Σ ∅ ,lam t) t))
    (check-equal?
      (list (term (Π (x : (Π (y : (Unv 0)) y)) nat)))
      (judgment-holds (types (∅ (nat : (Unv 0) ())) ∅ (λ (x : (Π (y : (Unv 0)) y)) (x nat))
                            t) t))
    (check-equal?
      (list (term (Π (y : (Unv 0)) (Unv 0))))
      (judgment-holds (types (∅ (nat : (Unv 0) ())) ∅ (λ (y : (Unv 0)) y) t) t))
    (check-equal?
      (list (term (Unv 0)))
      (judgment-holds (types (∅ (nat : (Unv 0) ())) ∅
                            ((λ (x : (Π (y : (Unv 0)) (Unv 0))) (x nat))
                             (λ (y : (Unv 0)) y))
                            t) t))
    (check-equal?
      (list (term (Unv 0)) (term (Unv 1)))
      (judgment-holds
        (types ,Σ4 ∅ (Π (S : (Unv 0)) (Π (B : (Unv 0)) (Π (a : S) (Π (b : B) ((and S) B)))))
               U) U))
    (check-true
      (judgment-holds (types ,Σ4 (∅ S : (Unv 0)) conj (Π (A : (Unv 0)) (Π (B : (Unv 0)) (Π (a : A) (Π (b : B) ((and A) B))))))))
    (check-true
      (judgment-holds (types ,Σ4 (∅ S : (Unv 0)) S (Unv 0))))
    (check-true
      (judgment-holds (types ,Σ4 (∅ S : (Unv 0)) (conj S)
                             (Π (B : (Unv 0)) (Π (a : S) (Π (b : B) ((and S) B)))))))
    (check-true
      (judgment-holds (types ,Σ4 (∅ S : (Unv 0)) (conj S)
                             (Π (B : (Unv 0)) (Π (a : S) (Π (b : B) ((and S) B)))))))
    (check-true
      (judgment-holds (types ,Σ4 ∅ (λ (S : (Unv 0)) (conj S))
                             (Π (S : (Unv 0)) (Π (B : (Unv 0)) (Π (a : S) (Π (b : B) ((and S) B))))))))
    (check-true
      (judgment-holds (types (,Σ4 (true : (Unv 0) ((tt : true)))) ∅
                             ((((conj true) true) tt) tt)
                             ((and true) true))))
    (check-true
      (judgment-holds
        (types ,Σ4 ∅ and (in-hole Ξ U_D))))
    (check-true
      (judgment-holds
        (types (,Σ4 (true : (Unv 0) ((tt : true)))) ∅
          ((((conj true) true) tt) tt)
          (in-hole Θ and))))
    (check-true
      (judgment-holds
        (types (,Σ4 (true : (Unv 0) ((tt : true)))) ∅
          (λ (A : Type) (λ (B : Type) (λ (x : ((and A) B)) true)))
          (in-hole Ξ (Π (x : (in-hole Θ_Ξ and)) U_P)))))
    (check-true
      (judgment-holds (types (,Σ4 (true : (Unv 0) ((tt : true)))) ∅
                             ((((elim and) ((((conj true) true) tt) tt))
                               (λ (A : Type) (λ (B : Type) (λ (x : ((and A) B))
                                                              true))))
                               (λ (A : (Unv 0))
                                  (λ (B : (Unv 0))
                                     (λ (a : A)
                                        (λ (b : B) tt)))))
                             true)))
    (define gamma (term (∅ temp863 : pre)))
    (check-true (judgment-holds (wf ,sigma ∅)))
    (check-true (judgment-holds (wf ,sigma ,gamma)))
    (check-true
      (judgment-holds (types ,sigma ,gamma (Unv 0) t)))
    (check-true
      (judgment-holds (types ,sigma ,gamma pre t)))
    (check-true
      (judgment-holds (types ,sigma (,gamma tmp863 : pre) (Unv 0) (Unv 1))))
    (check-true
      (judgment-holds
        (types ,sigma (,gamma x : false) false (in-hole Ξ U_D))))
    (check-true
      (judgment-holds
        (types ,sigma (,gamma x : false) x (in-hole Θ false))))
    (check-true
      (judgment-holds
        (types ,sigma (,gamma x : false) (λ (y : false) (Π (x : Type) x))
          (in-hole Ξ (Π (x : (in-hole Θ false)) U)))))
    (check-true
      (redex-match? cic-typingL (in-hole Θ_m (((elim x_D) e_D) e_P))
                    (term (((elim false) x) (λ (y : false) (Π (x : Type) x))))))
    (check-true
      (judgment-holds (types ,sigma (,gamma x : false)
                        (((elim false) x) (λ (y : false) (Π (x : Type) x)))
                        (Π (x : (Unv 0)) x))))))

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

    (define (extend-env/term env x t)
      (term (,(env) ,x : ,t)))

    (define (extend-env/term! env x t) (env (extend-env/term env x t)))

    (define (extend-env/syn env x t)
      (term (,(env) ,(syntax->datum x) : ,(cur->datum t))))

    (define (extend-env/syn! env x t) (env (extend-env/syn env x t)))

    (define bind-subst (make-parameter (list null null)))

    (define (add-binding/term! x t)
      (let ([vars (first (bind-subst))]
            [exprs (second (bind-subst))])
           (bind-subst (list (cons x vars) (cons t exprs)))))

    ;; TODO: Still absurdly slow. Probably doing n^2 checks of sigma and
    ;; gamma. And lookup on sigma, gamma are linear, so probably n^2 lookup time.
    (define (type-infer/term t)
      (let ([t (judgment-holds (types ,(sigma) ,(gamma) ,t t_0) t_0)])
        (and (pair? t) (car t))))

    (define (syntax->curnel-syntax syn) (denote syn (cur->datum syn)))

    (define (denote syn t)
      #`(term (reduce (subst-all #,(datum->syntax syn t) #,(first (bind-subst)) #,(second (bind-subst))))))

    ;; TODO: Blanket disarming is probably a bad idea.
    (define orig-insp (variable-reference->module-declaration-inspector
                        (#%variable-reference)))
    (define (disarm syn) (syntax-disarm syn orig-insp))

    ;; Locally expand everything down to core forms.
    (define (core-expand syn)
      (disarm
        (local-expand syn 'expression
          (append (syntax-e #'(term reduce subst-all dep-var #%app λ Π μ case
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
              #:datum-literals (case Π λ μ : Unv)
              [x:id (syntax->datum #'x)]
              [(subst-all e _ _) (syntax->datum #'e)]
              [(reduce e) (cur->datum #'e)]
              [(term e) (cur->datum #'e)]
              [(Unv i) (term (Unv ,(syntax->datum #'i)))]
              ;; TODO: should really check that b is one of the binders
              ;; Maybe make a syntax class for the binders, core forms,
              ;; etc.
              [(b:id (x:id : t) e)
               (let* ([x (syntax->datum #'x)]
                      [t (cur->datum #'t)]
                      [e (parameterize ([gamma (extend-env/term gamma x t)])
                           (cur->datum #'e))])
                 (term (,(syntax->datum #'b) (,x : ,t) ,e)))]
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

    ;; TODO: OOps, type-infer doesn't return a cur term but a redex term
    ;; wrapped in syntax bla. This is bad.
    (define (type-infer/syn syn)
      (let ([t (type-infer/term (cur->datum syn))])
        (and t (datum->syntax syn t))))

    (define (type-check/syn? syn type)
      (let ([t (type-infer/term (cur->datum syn))])
        (equal? t (cur->datum type))))

    (define (normalize/syn syn)
      (denote syn (term (reduce (subst-all ,(cur->datum syn) ,(first (bind-subst)) ,(second (bind-subst)))))))

    ;; Takes a Cur term syn and an arbitrary number of identifiers ls. The cur term is
    ;; expanded until expansion reaches a Curnel form, or one of the
    ;; identifiers in ls.
    (define (cur-expand syn . ls)
      (disarm (local-expand syn 'expression
                (append (syntax-e #'(Type dep-inductive dep-lambda dep-app
                                   dep-forall dep-var))
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
             (or (term (lookup ,(gamma) ,x))
               (term (lookup ,(sigma) ,x))))))

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
             (set! envs (for/list ([e cur])
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
                               #`(#,@out-gammas (gamma (term (append-env
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
                               #`(#,@out-sigmas (sigma (term (append-env
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
      [(_ (x : t) e) (syntax->curnel-syntax #`(λ (x : t) e))]))

  (define-syntax (dep-app syn)
    (syntax-case syn ()
      [(_ e1 e2) (syntax->curnel-syntax #`(#%app e1 e2))]))

  (define-syntax (dep-forall syn)
    (syntax-case syn (:)
      [(_ (x : t) e) (syntax->curnel-syntax #`(Π (x : t) e))]))

  (define-syntax (Type syn)
    (syntax-case syn ()
      [(_ i) (syntax->curnel-syntax #'(Unv i))]
      [_ #'(Type 0)]))

  (define-syntax (dep-fix syn)
   (syntax-case syn (:)
     [(_ (x : t) e) (syntax->curnel-syntax #`(μ (x : t) e))]))

  (define-syntax (dep-inductive syn)
    (syntax-case syn (:)
      [(_ i : ti (x1 : t1) ...)
       (begin
         (extend-env/syn! sigma #'i #'ti)
         (for ([x (syntax->list #`(x1 ...))]
               [t (syntax->list #`(t1 ...))])
           (extend-env/syn! sigma x t))
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
       (let ([e (cur->datum #'e)]
             [id (syntax->datum #'id)])
         (extend-env/term! gamma id (type-infer/term e))
         (add-binding/term! id e)
         #'(void))])))

(require (rename-in 'sugar [module+ dep-module+]))
(provide (rename-out [dep-module+ module+]) (all-from-out 'sugar))
(module+ test
  (require (submod ".." core test)))

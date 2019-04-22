#lang cur
(require cur/stdlib/sugar
         cur/stdlib/equality
         cur/ntac/base
         cur/ntac/standard
         cur/ntac/rewrite
         rackunit/turnstile
         "../rackunit-ntac.rkt")

; Software Foundations Tactics.v, part 3 of 5

;; copied from Poly-pairs.rkt
(data bool : 0 Type
      (true : bool)
      (false : bool))

(data nat : 0 Type
      (O : nat) ; letter capital "O"
      (S : (-> nat nat)))

(define/rec/match plus : nat [m : nat] -> nat
  [O => m]
  [(S n-1) => (S (plus n-1 m))])

(define/rec/match beq-nat : nat nat -> bool
  [O O => true]
  [O (S _) => false]
  [(S _) O => false]
  [(S n*) (S m*) => (beq-nat n* m*)])

;; re-define #%datum to use the new `nat`
(define-syntax #%datum
  (syntax-parser
    [(_ . n:exact-nonnegative-integer)
     #:when (zero? (syntax-e #'n))
     #'O]
    [(_ . n:exact-nonnegative-integer)
     #`(S (#%datum . #,(- (syntax-e #'n) 1)))]))

;; continuing Tactics.v --------------------

(define-theorem f-equal
  (∀ [A B : Type] [f : (-> A B)] [x y : A]
     (-> (== x y) (== (f x) (f y))))
  (by-intros A B f x y H)
  (by-rewrite H)
  reflexivity)

(define-theorem S_inj
  (forall (n m : nat) (b : bool)
          (-> (== (beq-nat (S n) (S m)) b)
              (== (beq-nat n m) b)))
  (by-intros n m b H)
  ;; simpl in H ; unneeded
  (by-apply H))

(define-theorem silly3b
  (forall (n : nat)
          (-> (-> (== (beq-nat n 5) true) ; eq
                  (== (beq-nat (S (S n)) 7) true))
              (== true (beq-nat n 5)) ; H
              (== true (beq-nat (S (S n)) 7))))
  (by-intros n eq H)
  (by-symmetry #:in H)
  (by-apply eq #:in H)
  (by-symmetry #:in H)
  by-assumption)

(check-type
 silly3b
 :   (forall (n : nat)
          (-> (-> (== (beq-nat n 5) true) ; eq
                  (== (beq-nat (S (S n)) 7) true))
              (== true (beq-nat n 5)) ; H
              (== true (beq-nat (S (S n)) 7)))))

(define-theorem plus-n-Sm
  (∀ [n : nat] [m : nat]
     (== nat (S (plus n m)) (plus n (S m))))
  (by-intro n)
  (by-intro m)
  simpl
  (by-induction n #:as [() (n-1 IH)])
  ;; subgoal 1
  simpl
  reflexivity
  ;; subgoal 1
  simpl
  (by-rewrite IH)
  reflexivity)

(define-theorem plus-n-n-injective
 (∀ [n m : nat]
    (-> (== (plus n n) (plus m m))
        (== n m)))
 (by-intro n)
 (by-induction n #:as [() (n-1 IH)])
 ;; n = 0
 (by-intros m H)
 (by-destruct m #:as [() (m-1)])
 reflexivity
 (by-inversion H)
 ;; n = S n-1
 (by-intros m H)
 (by-destruct m #:as [() (m-1)])
 (by-inversion H)
 (by-rewriteL plus-n-Sm #:in H)
 (by-rewriteL plus-n-Sm #:in H)
 (by-inversion H #:as H2)
 (by-apply IH #:in H2)
 (by-rewrite H2)
 reflexivity)

(check-type plus-n-n-injective
 : (∀ [n m : nat]
    (-> (== (plus n n) (plus m m))
        (== n m))))

(require cur/stdlib/prop)

;; plus-n-n-injective CORRECT raw term:
(λ (n : nat)
   ((new-elim
     n
     (λ n (Π (Π (m : nat) (→ (== nat (plus n n) (plus m m)) (== nat n m)))))
     (λ (λ
         (λ (m : nat)
           (λ (H : (== nat O (plus m m)))
             ((match
               m
               #:as
               m
               #:with-indices
               #:in
               nat
               #:return
               (Π (H : (== nat O (plus m m))) (== nat O m))
               (O (λ (H : (== nat O (plus (O) (O)))) (λ (refl nat O))))
               ((S m-1)
                (λ (H : (== nat O (plus (S m-1) (S m-1))))
                  ((new-elim
                    H
                    (λ y61
                      H
                      (-> (== y61 (S (plus m-1 (S m-1)))) (== nat O (S m-1))))
                    (λ eq52
                      (new-elim
                       (elim-==
                        eq52
                        (λ y54
                          _
                          (match y54 #:return Type ((O) True) ((S X7) False)))
                        I)
                       (λ _ (== nat O (S m-1))))))
                   (refl nat (S (plus m-1 (S m-1))))))))
              H)))))
     (λ n-1
       IH
       (λ (λ
           (m : nat)
           (λ (H : (== nat (S (plus n-1 (S n-1))) (plus m m)))
             ((match
               m
               #:as
               m
               #:with-indices
               #:in
               nat
               #:return
               (Π
                (H : (== nat (S (plus n-1 (S n-1))) (plus m m)))
                (== nat (S n-1) m))
               (O
                (λ (H : (== nat (S (plus n-1 (S n-1))) (plus (O) (O))))
                  ((new-elim
                    H
                    (λ y62 H (-> (== y62 O) (== nat (S n-1) O)))
                    (λ eq55
                      (new-elim
                       (elim-==
                        eq55
                        (λ y57
                          _
                          (match y57 #:return Type ((O) False) ((S X7) True)))
                        I)
                       (λ _ (== nat (S n-1) O)))))
                   (refl nat O))))
               ((S m-1)
                (λ (H : (== nat (S (plus n-1 (S n-1))) (plus (S m-1) (S m-1))))
                  ((λ (H
                       :
                       (== nat (S (S (plus n-1 n-1))) (S (plus m-1 (S m-1)))))
                     ((λ (H
                          :
                          (==
                           nat
                           (S (S (plus n-1 n-1)))
                           (S (S (plus m-1 m-1)))))
                        ((new-elim
                          H
                          (λ y65
                            H
                            (->
                             (== y65 (S (S (plus m-1 m-1))))
                             (== nat (S n-1) (S m-1))))
                          (λ eq58
                            ((λ (H2 : (== nat (plus n-1 n-1) (plus m-1 m-1)))
                               ((λ (H2 : (== nat n-1 m-1))
                                  (new-elim
                                   (sym nat n-1 m-1 (H2))
                                   (λ (g63 : nat)
                                     (λ (g64 : (== nat m-1 g63))
                                       (== nat (S g63) (S m-1))))
                                   (λ (refl nat (S m-1)))))
                                (IH m-1 H2)))
                             (f-equal
                              nat
                              nat
                              (λ x59
                                (match
                                 (match
                                  x59
                                  #:return
                                  nat
                                  ((O) (S (plus n-1 n-1)))
                                  ((S X7) X7))
                                 #:return
                                 nat
                                 ((O) (plus n-1 n-1))
                                 ((S X7) X7)))
                              (S (S (plus n-1 n-1)))
                              (S (S (plus m-1 m-1)))
                              eq58))))
                         (refl nat (S (S (plus m-1 m-1))))))
                      (new-elim ; WANT: (== nat (S (S (plus n-1 n-1))) (S (S (plus m-1 m-1))))
                       (sym nat (S (plus m-1 m-1)) (plus m-1 (S m-1)) (plus-n-Sm m-1 m-1)) ; (== nat (S (plus m-1 m-1)) (plus m-1 (S m-1)))
                       (λ (g66 : nat)
                         (λ (g67 : (== nat (plus m-1 (S m-1)) g66))
                           (==
                            nat
                            (S (S (plus n-1 n-1)))
                            (S g66))))
                       H ; (== nat (S (S (plus n-1 n-1))) (S (plus m-1 (S m-1))))
                       ))) 
                   (new-elim ; WANT: (== nat (S (S (plus n-1 n-1))) (S (plus m-1 (S m-1))))
                    (sym nat (S (plus n-1 n-1)) (plus n-1 (S n-1)) (plus-n-Sm n-1 n-1)) ; (== nat (S (plus n-1 n-1)) (plus n-1 (S n-1)))
                    (λ (g68 : nat)
                      (λ (g69 : (== nat (plus n-1 (S n-1)) g68))
                        (== nat (S g68) (S (plus m-1 (S m-1))))))
                    H ; (== nat (S (plus n-1 (S n-1))) (plus (S m-1) (S m-1)))
                      ; simpl (== nat (S (plus n-1 (S n-1))) (S (plus m-1 (S m-1))))
                    )))))
              H))))))))

(define/rec/match double : nat -> nat
  [O => O]
  [(S n-1) => (S (S (double n-1)))])

;; tests inversion of H with non-id base cases
(define-theorem double-injective
  (forall (n m : nat)
          (-> (== (double n) (double m))
              (== n m)))
  (by-intro n)
  (by-induction n #:as [() (n-1 IH)])
  (by-intros m H) ; 1
  (by-destruct m #:as [() (m-1)])
  reflexivity ; 1a
  (by-inversion H #:as H1) ; 1b
  (by-intros m H) ; 2
  (by-destruct m #:as [() (m-1)])
  (by-inversion H #:as H1) ; 2a
  (by-apply f-equal #:with nat nat S n-1 m-1) ; 2b ; unify doesnt find f-equal's A arg
  (by-apply IH)
  (by-inversion H #:as H2)
  (by-rewrite H2)
  reflexivity)

(check-type double-injective
 : (forall (n m : nat)
          (-> (== (double n) (double m))
              (== n m))))

(define-theorem beq-nat-true
  (∀ [n m : nat]
     (-> (== (beq-nat n m) true)
         (== n m)))
  (by-intro n)
  (by-induction n #:as [() (n-1 IH)])
  (by-intros m H) ; 1
  (by-destruct m #:as [() (m-1)])
  reflexivity ; 1a
  (by-inversion H) ; 1b
  (by-intros m H) ; 2
  (by-destruct m #:as [() (m-1)])
  (by-inversion H) ; 2a
  (by-apply f-equal #:with nat nat S n-1 m-1) ; 2b
  (by-apply IH)
  (by-inversion H #:as H1)
  (by-rewrite H1)
  reflexivity)

(define-theorem double-injective-take2
  (∀ [n m : nat]
     (-> (== (double n) (double m))
         (== n m)))
  (by-intros n m)
  (by-generalize n)
  (by-induction m #:as [() (m-1 IH)])
  (by-intros n H) ; 1
  (by-destruct n #:as [() (n-1)])
  reflexivity ; 1a
  (by-inversion H) ; 1b
  (by-intros n H) ; 2
  (by-destruct n #:as [() (n-1)])
  (by-inversion H) ; 2a
  (by-apply f-equal #:with nat nat S n-1 m-1) ; 2b
  (by-apply IH)
  (by-inversion H #:as H1)
  (by-rewrite H1)
  reflexivity)

(data id : 0 Type [Id : (-> nat id)])

(define/rec/match beq-id : id id -> bool
  [(Id n1) (Id n2) => (beq-nat n1 n2)])

;; TODO: support auto-destructing by-intros
(define-theorem beq-id-true
  (forall [x y : id]
          (-> (== (beq-id x y) true)
              (== x y)))
  (by-intros x y)
  (by-destruct x #:as [(m)])
  (by-destruct y #:as [(n)])
  (by-intro H)
  (by-assert H1 (== m n))
  (by-apply beq-nat-true) ; prove m = n
  (by-apply H)
  (by-rewrite H1) ; return to orig goal
  reflexivity)

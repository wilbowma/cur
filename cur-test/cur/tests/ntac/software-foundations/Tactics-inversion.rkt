#lang cur
(require cur/stdlib/sugar
         cur/stdlib/equality
         cur/ntac/base
         cur/ntac/standard
         cur/ntac/rewrite
         rackunit/turnstile
         "../rackunit-ntac.rkt")

; Software Foundations Tactics.v, part 2 of 5

;; copied from Poly-pairs.rkt
(data bool : 0 Type
      (true : bool)
      (false : bool))

(data nat : 0 Type
      (O : nat) ; letter capital "O"
      (S : (-> nat nat)))

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

;; * = "full" version; as opposed to hidden-arg version
(define-datatype list [X : Type] : -> Type
  [nil* : (list X)]
  [cons* : X (list X) -> (list X)])

(define-implicit nil = nil* 1)
(define-implicit :: = cons* 1 _ inf)

(define-syntax lst
  (syntax-parser
    [(_) #'nil]
    [(_ x . rst) #'(:: x (lst . rst))]))

;; continuing Tactics.v --------------------

;; inversion tactic --------------------------------------------------

(define-theorem S-injective
  (forall (n m : nat) (-> (== (S n) (S m)) (== n m)))
  (by-intros n m H)
  (by-inversion H)
  by-assumption)

;; inversion infers H0 = H
(define-theorem S-injective-backwards
  (forall (n m : nat) (-> (== n m) (== (S n) (S m))))
  (by-intros n m H)
  (by-inversion H #:as H0)
  (by-rewrite H0)
  reflexivity)

;; check inversion-ex1 raw terms
(check-type
 (λ g55
   (match g55 #:return nat
    [(nil*) 0]
    [(cons* g17 g18) g17]))
 : (-> (list nat) nat))

(check-type
 (f-equal
  (list nat)
  nat
  (λ g55
   (match g55 #:return nat
          ((nil*) 0)
          ((cons* g17 g18) g17)))
  (cons* nat 1 (nil* nat))
  (cons* nat 1 (nil* nat)) 
  (refl (list nat) (lst 1)))
 : (== 1 1))

(check-type
 (λ (n : nat)
   (λ (m : nat)
     (λ (o : nat)
       (λ (H
           :
           (==
            (list nat)
            (cons* nat n (cons* nat m (nil* nat)))
            (cons* nat o (cons* nat o (nil* nat)))))
         ((λ (H1 : (== nat m o))
            (H2 : (== nat n o))
            (new-elim
             (sym nat m o (H1))
             (λ (g56 : nat)
               (λ (g57 : (== nat o g56))
                 (==
                  (list nat)
                  (cons* nat n (nil* nat))
                  (cons* nat g56 (nil* nat)))))
             (new-elim
              (sym nat n o (H2))
              (λ (g58 : nat)
                (λ (g59 : (== nat o g58))
                  (==
                   (list nat)
                   (cons* nat g58 (nil* nat))
                   (cons* nat o (nil* nat)))))
              (refl (list nat) (cons* nat o (nil* nat))))))
          (f-equal
           (list nat) nat
           (λ g55
             (match
                 g55
               #:return nat
               ((nil*) O)
               ((cons* g17 g18)
                (match
                    g18
                  #:return nat
                  ((nil*) m)
                  ((cons* g17 g18) g17)))))
           (cons* nat n (cons* nat m (nil* nat)))
           (cons* nat o (cons* nat o (nil* nat)))
           H)
          (f-equal
           (list nat)
           nat
           (λ g55
             (match
                 g55
               #:return nat
               ((nil*) n)
               ((cons* g17 g18) g17)))
           (cons* nat n (cons* nat m (nil* nat)))
           (cons* nat o (cons* nat o (nil* nat)))
           H))))))
 :   (forall (n m o : nat)
             (-> (== (lst n m) (lst o o))
                 (== (lst n) (lst m)))))

;; inversion infers two equalities from list structure
(define-theorem inversion-ex1
  (forall (n m o : nat)
          (-> (== (lst n m) (lst o o))
              (== (lst n) (lst m))))
  (by-intros n m o H)
  (by-inversion H #:as H1 H2)
  (by-rewrite H1)
  (by-rewrite H2)
  reflexivity)

(check-type inversion-ex1
  : (forall (n m o : nat)
            (-> (== (lst n m) (lst o o))
                (== (lst n) (lst m)))))


(define-theorem inversion-ex2
  (forall (n m : nat) (-> (== (lst n) (lst m)) (== n m)))
  (by-intros n m H)
  (by-inversion H #:as H0)
  (by-rewrite H0)
  reflexivity)

(define-theorem inversion-ex3
  (forall (X : Type) (x y z : X) (l j : (list X))
          (-> (== (:: x (:: y l)) (:: z j))
              (== (:: y l) (:: x j))
              (== x y)))
  (by-intros X x y z l j H1 H2)
  (by-inversion H2 #:as H3 H4)
  (by-rewrite H4)
  reflexivity)

;; beq-nat-0l raw term
(require cur/stdlib/prop)
(check-type
 (λ (n : nat)
   (λ (H : (== bool (beq-nat O n) true))
     ((match n #:as n #:in nat
             #:return (Π (H : (== bool (beq-nat O n) true)) (== nat n O))
       (O (λ (H : (== bool (beq-nat O O) true)) (refl nat O)))
       ((S n-1)
        (λ (H : (== bool (beq-nat O (S n-1)) true))
          ((λ (H0 : False)
             (new-elim
              H0
              (λ y (== nat (S n-1) O))))
           (new-elim
            H
            (λ x h (new-elim x (λ x Type) False True))
            I)))))
      H)))
 : (forall [n : nat] [H : (== bool (beq-nat O n) true)]
           (== nat n O)))

(define-theorem beq-nat-0l
  (forall [n : nat]
          (-> (== (beq-nat 0 n) true)
              (== n 0)))
  (by-intros n H)
  (by-destruct n #:as [() (n-1)])
  reflexivity ; 1
  (by-inversion H #:as H0) ; 2
  elim-False
  by-assumption)

(check-type beq-nat-0l
 :  (forall [n : nat]
          (-> (== (beq-nat 0 n) true)
              (== n 0))))

(define/rec/match plus : nat [m : nat] -> nat
  [O => m]
  [(S n-1) => (S (plus n-1 m))])

(define-theorem inversion-ex4
  (forall (n : nat)
          (-> (== (S n) O)
              (== (plus 2 2) 5)))
  (by-intros n H)
  (by-inversion H)
  elim-False
  by-assumption)

(define-theorem inversion-ex5
  (forall (n m : nat)
          (-> (== false true) (== (lst n) (lst m))))
  (by-intros n m H)
  (by-inversion H)
  elim-False
  by-assumption)

;; generates False proof term for lists
(define-theorem inversion-ex6
;(ntac/trace
  (forall (X : Type)
          (x y z : X) (l j : (list X))
          (-> (== (:: x (:: y l)) (nil* X))
              (== (:: y l) (:: z j))
              (== x z)))
  (by-intros X x y z l j H1 H2)
  (by-inversion H1)
  elim-False
  by-assumption)

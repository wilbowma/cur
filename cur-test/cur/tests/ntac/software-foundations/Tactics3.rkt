#lang cur
(require cur/stdlib/sugar
         cur/stdlib/equality
         cur/ntac/base
         cur/ntac/standard
         cur/ntac/rewrite
         rackunit/turnstile
         "../rackunit-ntac.rkt")

; Software Foundations Tactics.v, part 3 of 3
;; tests the "#:in" variant of many tactics

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
  elim-False
  by-assumption
  (by-intros m H) ; 2
  (by-destruct m #:as [() (m-1)])
  (by-inversion H #:as H1) ; 2a
  elim-False
  by-assumption
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
  elim-False
  by-assumption
  (by-intros m H) ; 2
  (by-destruct m #:as [() (m-1)])
  (by-inversion H) ; 2a
  elim-False
  by-assumption
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
  elim-False
  by-assumption
  (by-intros n H) ; 2
  (by-destruct n #:as [() (n-1)])
  (by-inversion H) ; 2a
  elim-False
  by-assumption
  (by-apply f-equal #:with nat nat S n-1 m-1) ; 2b
  (by-apply IH)
  (by-inversion H #:as H1)
  (by-rewrite H1)
  reflexivity)

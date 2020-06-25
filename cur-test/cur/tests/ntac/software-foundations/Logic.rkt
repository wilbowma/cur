#lang cur
(require cur/stdlib/sugar
         cur/stdlib/equality
         (except-in cur/stdlib/prop Not)
         (only-in cur/stdlib/prop [Not Not-orig])
         cur/stdlib/bool
         cur/stdlib/axiom
         cur/ntac/base
         cur/ntac/standard
         cur/ntac/rewrite
         rackunit/turnstile+
         "../rackunit-ntac.rkt")

; Software Foundations Logic.v

(define Not Not-orig)

(data nat : 0 Type
      (O : nat) ; letter capital "O"
      (S : (-> nat nat)))

;; re-define #%datum to use the new `nat`
(define-syntax #%datum
  (syntax-parser
    [(_ . n:exact-nonnegative-integer)
     #:when (zero? (syntax-e #'n))
     #'O]
    [(_ . n:exact-nonnegative-integer)
     #`(S (#%datum . #,(- (syntax-e #'n) 1)))]))

(define/rec/match plus : nat [m : nat] -> nat
  [O => m]
  [(S n-1) => (S (plus n-1 m))])

(define/rec/match pred : nat -> nat
  [O => O]
  [(S n-1) => n-1])

(define-theorem plus-n-0
  (∀ [n : nat] (== (plus n 0) n))
  (by-intros n) (by-induction n #:as [() (n-1 IH)])
  reflexivity (by-rewrite IH) reflexivity)

(define-theorem plus-n-Sm
  (∀ [n : nat] [m : nat] (== (plus n (S m)) (plus (S n) m)))
  (by-intros n m) (by-induction n #:as [() (n-1 IH)])
  reflexivity (by-rewrite IH) reflexivity)

(define/rec/match mult : nat [m : nat] -> nat
  [O => O]
  [(S n-1) => (plus m (mult n-1 m))])

(define-theorem mult-n-O
  (∀ [n : nat] (== (mult n O) O))
  (by-intros n)
  (by-induction n #:as [() (n-1 Hn)])
  reflexivity
  (by-apply Hn))

;; ----------------
;; Logical connectives
;; ----------------

;; === Conjuction

(define-theorem and-intro
  (∀ [A : Prop] [B : Prop]
     (-> A B (And A B)))
  (by-intros A B HA HB)
  by-split
  (by-apply HA)
  (by-apply HB))

(define-theorem and-example
  (And (== (plus 3 4) 7)
       (== (plus 2 2) 4))
  by-split
  reflexivity
  reflexivity)

(define-theorem and-exercise
  (∀ [n : nat] [m : nat]
     (-> (== (plus n m) 0)
         (And (== n 0)
              (== m 0))))
  (by-intros n m H)
  (by-destruct n)
  ;; subgoal 1
  by-split
  reflexivity
  by-assumption
  ;; subgoal 2
  (by-discriminate H))

(define-theorem and-example2
  (∀ [n m : nat] (-> (And (== n 0) (== m 0))
                     (== (plus n m) 0)))
  (by-intros n m H)
  (by-destruct H #:as [(Hn Hm)])
  (by-rewrite Hn)
  (by-rewrite Hm)
  reflexivity)

(define-theorem proj1
  (∀ [P : Prop] [Q : Prop]
     (-> (And P Q) P))
  (by-intros P Q HPQ)
  (by-destruct HPQ #:as [(HP HQ)])
  (by-apply HP))

(define-theorem proj2
  (∀ [P : Prop] [Q : Prop]
     (-> (And P Q) Q))
  (by-intros P Q HPQ)
  (by-destruct HPQ #:as [(HP HQ)])
  (by-apply HQ))

(define-theorem and-assoc
  (∀ [P : Prop] [Q : Prop] [R : Prop]
     (-> (And P (And Q R))
         (And (And P Q) R)))
  (by-intros P Q R HPQR)
  (by-destruct HPQR #:as [(HP HQR)])
  (by-destruct HQR #:as [(HQ HR)])
  by-split
  by-split
  (by-apply HP)
  (by-apply HQ)
  (by-apply HR))

(:: And (-> Prop Prop Prop))

;; === Disjuction

(define-theorem or-example
  (∀ [n : nat] [m : nat]
     (-> (Or (== n 0) (== m 0))
         (== (mult n m) 0)))
  (by-intros n m H)
  (by-destruct H #:as [(Hn) (Hm)])
  ;; subgoal 1
  (by-rewrite Hn)
  reflexivity
  ;; subgoal 2
  (by-rewrite Hm)
  (by-rewrite mult-n-O)
  reflexivity)

(define-theorem or-intro
  (∀ [P : Prop] [Q : Prop]
     (-> P (Or P Q)))
  (by-intros P Q H)
  by-left
  (by-apply H))

(define-theorem zero-or-succ
  (∀ [n : nat]
     (Or (== n O) (== n (S (pred n)))))
  (by-intro n)
  (by-destruct n #:as [() (n-1)])
  by-left reflexivity
  by-right reflexivity)

;; === Falsehood and Negation

(:: Not (-> Prop Prop))

(define-theorem ex-falso-quodlibet
  (∀ [P : Prop] (-> False P))
  (by-intros P contra)
  (by-destruct contra))

(define-theorem not-implies-our-not
  (∀ [P : Prop]
     (-> (Not P) (∀ [Q : Prop] (-> P Q))))
  (by-intros P HNP Q HP)
  (by-assert contra False)
  ;; proof of contra
  (by-apply HNP)
  by-assumption
  ;; proof of rest
  (by-apply ex-falso-quodlibet #:with Q contra))

(define-syntax /=
  (syntax-parser
    [(_ x y) #'(Not (== x y))]))

(define-theorem zero-not-one
  (/= 0 1)
  (by-intros contra)
  (by-discriminate contra))

(define-theorem not-False
  (Not False)
  (by-intro H)
  (by-destruct H))

(define-theorem contradiction-implies-anything
  (∀ [P : Prop] [Q : Prop] (-> (And P (Not P)) Q))
  (by-intros P Q H)
  (by-destruct H #:as [(HP HNP)])
  (by-apply HNP #:in HP)
  (by-destruct HP))

(define-theorem double-neg
  (∀ [P : Prop] (-> P (Not (Not P))))
  (by-intros P H G)
  (by-apply G)
  (by-apply H))

(define-theorem contrapositive
  (∀ [P : Prop] [Q : Prop]
     (-> (-> P Q) (-> (Not Q) (Not P))))
  (by-intros P Q H HNQ HP)
  (by-apply HNQ)
  (by-apply H)
  (by-apply HP))

(define-theorem not-both-true-and-false
  (∀ [P : Prop]
     (Not (And P (Not P))))
  (by-intros P H)
  (by-destruct H #:as [(HP HNP)])
  (by-apply HNP)
  (by-apply HP))

(define-theorem not-true-is-false
  (∀ [b : Bool]
     (-> (/= b true)
         (== b false)))
  (by-intros b H)
  (by-destruct b)
  ;; subgoal 1 (b = true)
  elim-False    ; TODO: rename to exfalso?
  (by-apply H)
  reflexivity
  ;; subgoal 2 (b = false)
  reflexivity)

;; ==== Truth

(define-theorem true-is-true
  True
  (by-apply I))

;; ==== Logical Equivalence

(define-theorem or-distributes-over-and
  (∀ [P : Prop] [Q : Prop] [R : Prop]
     (iff (Or P (And Q R))
          (And (Or P Q) (Or P R))))
  (by-intros P Q R)
  by-split
  ;; subgoal 1: ->
  (by-intros H)
  (by-destruct H #:as [(HP) (HQR)])
  ;; - given P
  by-split by-left (by-apply HP) by-left (by-apply HP)
  ;; - given Q∧R
  (by-destruct HQR #:as [(HQ HR)])
  by-split by-right (by-apply HQ) by-right (by-apply HR)
  ;; subgoal 2: <-
  (by-intros H)
  (by-destruct H #:as [(HPQ HPR)])
  (by-destruct HPQ #:as [(HP) (HQ)])
  ;; - given P
  by-left (by-apply HP)
  ;; - given Q
  (by-destruct HPR #:as [(HP) (HR)])
  by-left (by-apply HP)
  by-right by-split (by-apply HQ) (by-apply HR))

;; ==== Function Extensionality

(define-theorem function-equality1
  (== (λ [x : nat] (plus 3 x))
      (λ [x : nat] (plus (pred 4) x)))
  reflexivity)

;; needs functional extensionality axiom
#;(define-theorem function-equality2
  (== (λ [x : nat] (plus x 1))
      (λ [x : nat] (plus 1 x)))
  #;stuck)

(define-axiom function-extensionality
  (∀ [X : Type] [Y : Type]
     [f : (-> X Y)] [g : (-> X Y)]
     (-> (∀ [x : X] (== (f x) (g x)))
         (== f g))))

(define-theorem function-equality2
  (== (λ [x : nat] (plus x 1))
      (λ [x : nat] (plus 1 x)))
  (by-apply function-extensionality #:with
            nat nat
            (λ [x : nat] (plus x 1))
            (λ [x : nat] (plus 1 x)))
  (by-intros x)
  (by-rewrite plus-n-Sm)
  (by-rewrite plus-n-0)
  reflexivity)

(print-assumptions function-equality2)

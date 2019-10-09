#lang cur
(require cur/stdlib/sugar
         cur/stdlib/equality
         cur/ntac/base
         cur/ntac/standard
         cur/ntac/rewrite
         rackunit/turnstile+
         "../rackunit-ntac.rkt")

; Software Foundations Tactics.v, part 4 of 5

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

(define/rec/match mult : nat [m : nat] -> nat
  [O => O]
  [(S n-1) => (plus m (mult n-1 m))])

(define (square [n : nat]) (mult n n))

(define/rec/match beq-nat : nat nat -> bool
  [O O => true]
  [O (S _) => false]
  [(S _) O => false]
  [(S n*) (S m*) => (beq-nat n* m*)])

(define/rec/match pred : nat -> nat
  [O => O]
  [(S n-1) => n-1])

;; re-define #%datum to use the new `nat`
(define-syntax #%datum
  (syntax-parser
    [(_ . n:exact-nonnegative-integer)
     #:when (zero? (syntax-e #'n))
     #'O]
    [(_ . n:exact-nonnegative-integer)
     #`(S (#%datum . #,(- (syntax-e #'n) 1)))]))

;; * = "full" version; as opposed to hidden-arg version
(define-datatype list [X : Type] : Type
  [nil* : (list X)]
  [cons* : (-> X (list X) (list X))])

(define-implicit nil = nil* 1)
(define-implicit :: = cons* 1 _ inf)

(define-datatype option [X : Type] : Type
  [Some* : (-> X (option X))]
  [None* : (option X)])

(define-implicit Some = Some* 1)
(define-implicit None = None* 1)

(define-typed-syntax (if tst e1 e2) ≫
  [⊢ e1 ≫ e1- ⇒ τ]
  [⊢ e2 ≫ e2- ⇐ τ]
  ----------
  [≻ (match tst #:return τ [true e1-] [false e2-])])

(define/rec/match nth/error_ : [X : Type] [n : nat] (list X) -> (option X)
  [nil => None]
  [(:: a xs) => (if (beq-nat n 0) (Some a) (nth/error_ X (pred n) xs))])

(define-implicit nth/error = nth/error_ 1)

(define/rec/match app_ : [X : Type] (list X) (list X) -> (list X)
  [nil l2 => l2]
  [(:: h t) l2 => (:: h (app_ X t l2))])

(define-implicit app = app_ 1)

(define/rec/match rev_ : [X : Type] (list X) -> (list X)
  [nil => nil]
  [(:: h t) => (app (rev_ X t) (:: h nil))])

(define/rec/match length_ : [X : Type] (list X) -> nat
  [nil => 0]
  [(:: h t) => (S (length_ X t))])

(define-implicit rev = rev_ 1)
(define-implicit length = length_ 1)

;; continuing Tactics.v --------------------

(define-theorem error-after-last
  (∀ (n : nat) (X : Type) (l : (list X))
     (-> (== (length l) n)
         (== (nth/error n l) (None* X))))
  (by-intros n X l)
  (by-generalize n)
  (by-induction l #:as [() (h t IH)])
  (by-intros n H) ; 1
  (by-rewriteL H)
  reflexivity
  (by-intros n H) ; 2
  (by-rewriteL H)
  (by-apply IH)
  reflexivity)

;; mult/plus thms needed for square mult ----------
(define-theorem mult_0_r
  (forall [n : nat] (== (mult n 0) 0))
  (by-intro n)
  (by-induction n #:as [() (n-1 IH)])
  reflexivity ; 1
  (by-rewrite IH) ; 2
  reflexivity)

(define-theorem plus_n_Sm
  (forall [n m : nat]
          (== (S (plus n m)) (plus n (S m))))
  (by-intros n m)
  (by-induction n #:as [() (n-1 IH)])
  reflexivity ;1
  (by-rewrite IH) ;2
  reflexivity)

(define-theorem plus_0_r
  (forall [n : nat] (==  (plus n 0) n))
  (by-intro n)
  (by-induction n #:as [() (n-1 IH)])
  reflexivity ; 1
  (by-rewrite IH) ; 2
  reflexivity)

(define-theorem plus_comm
  (forall [n m : nat] (== (plus n m) (plus m n)))
  (by-intros n m)
  (by-induction n #:as [() (n-1 IH)])
  (by-rewrite plus_0_r) ;1
  reflexivity
  (by-rewriteL plus_n_Sm) ; 2
  (by-rewriteL IH)
  reflexivity)

(define-theorem plus_assoc
  (forall [n m p : nat]
          (== (plus n (plus m p))
              (plus (plus n m) p)))
  (by-intros n m p)
  (by-induction n #:as [() (n-1 IH)])
  reflexivity ;1
  (by-rewrite IH) ;2
  reflexivity)

(define-theorem plus_swap
  (forall [n m p : nat]
          (== (plus n (plus m p))
              (plus m (plus n p))))
  (by-intros n m p)
  (by-rewrite plus_assoc)
  (by-rewrite plus_assoc)
  (by-assert H (== (plus n m) (plus m n)))
  (by-rewrite plus_comm) ; prove H
  reflexivity
  (by-rewrite H) ; return
  reflexivity)

(define-theorem mult_n_Sm
  (forall [n m : nat]
          (== (mult n (S m))
              (plus n (mult n m))))
  (by-intros n m)
  (by-induction n #:as [() (n-1 IH)])
  reflexivity ;1
  (by-rewrite IH) ;2
  (by-rewrite plus_swap)
  reflexivity)

(define-theorem mult_comm
  (forall [m n : nat]
          (== (mult m n)
              (mult n m)))
  (by-intros m n)
  (by-induction n #:as [() (n-1 IH)])
  (by-rewrite mult_0_r) ;1
  reflexivity
  (by-rewriteL IH) ;2
  (by-rewrite mult_n_Sm)
  reflexivity)

(define-theorem mult_plus_distr_r
  (forall [n m p : nat]
          (== (mult (plus n m) p)
              (plus (mult n p) (mult m p))))
  (by-intros n m p)
  (by-induction n #:as [() (n-1 IH)])
  reflexivity ;1
  (by-rewrite IH) ;2
  (by-rewrite plus_assoc)
  reflexivity)

(define-theorem mult_assoc
  (forall [n m p : nat]
          (== (mult n (mult m p))
              (mult (mult n m) p)))
  (by-intros n m p)
  (by-induction n #:as [() (n-1 IH)])
  reflexivity ;1
  (by-rewrite IH) ;2
  (by-rewrite mult_plus_distr_r)
  reflexivity)

;; TODO: why is this slow? ~30sec
(define-theorem square-mult
  (forall [n m : nat]
          (== (square (mult n m))
              (mult (square n) (square m))))
  (by-intros n m)
  ;  (unfold square) ; unneeded
  (by-rewrite mult_assoc)
  (by-assert H (== (mult (mult n m) n)
                   (mult (mult n n) m)))
  ; prove H
    (by-rewrite mult_comm)
    (by-apply mult_assoc)
  (by-rewrite H)
  (by-rewrite mult_assoc)
  reflexivity)

(define (foo (x : nat)) 5)

(define-theorem silly_fact_1
  (forall [m : nat]
          (== (plus (foo m) 1)
              (plus (foo (plus m 1)) 1)))
  (by-intros m)
  reflexivity)

(define (bar [x : nat])
  (match x #:return nat
   [O 5]
   [(S _) 5]))

(define-theorem silly_fact_2
  (forall [m : nat]
          (== (plus (bar m) 1)
              (plus (bar (plus m 1)) 1)))
  (by-intros m)
  ;(unfold bar) ; automatic
  (by-destruct m)
  reflexivity ;1
  reflexivity) ;2

(define (sillyfun (n : nat))
  (if (beq-nat n 3)
      false
      (if (beq-nat n 5)
          false
          false)))
(check-type sillyfun : (-> nat bool))
(check-type (sillyfun 1) : bool)
;; TODO: why does this == require an annotation?
(check-type (forall (n : nat) (== bool (sillyfun n) false)) : Type)

#lang cur
(require cur/stdlib/sugar
         cur/stdlib/equality
         cur/ntac/base
         cur/ntac/standard
         cur/ntac/rewrite
         rackunit/turnstile
         "../rackunit-ntac.rkt")

; Software Foundations Tactics.v, part 5 of 5
;; Using destruct on Compound Expressions

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
(define-datatype list [X : Type] : -> Type
  [nil* : (list X)]
  [cons* : X (list X) -> (list X)])

(define-implicit nil = nil* 1)
(define-implicit :: = cons* 1 _ inf)

(define-datatype option [X : Type] : -> Type
  [Some* : X -> (option X)]
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

(define-datatype prod [X : Type] [Y : Type] : -> Type
  [pair* : X Y -> (prod X Y)])

(define-implicit pair = pair* 2)

(define/rec/match fst* : [X : Type] [Y : Type] (prod X Y) -> X
  [(pair x _) => x])
(define/rec/match snd* : [X : Type] [Y : Type] (prod X Y) -> Y
  [(pair _ y) => y])

(define-implicit fst = fst* 2)
(define-implicit snd = snd* 2)

(define/rec/match combine_ : [X : Type] [Y : Type] (list X) (list Y)
  -> (list (prod X Y))
  [nil _ => (nil* (prod X Y))]
  [_ nil => (nil* (prod X Y))]
  [(:: x tx) (:: y ty) => (:: (pair x y) (combine_ X Y tx ty))])

(check-type combine_
  : (∀ [X : Type] [Y : Type] (-> (list X) (list Y) (list (prod X Y)))))

(define-implicit combine = combine_ 2)

(define/rec/match split_ : [X : Type] [Y : Type] (list (prod X Y))
  -> (prod (list X) (list Y))
  [nil => (pair (nil* X) (nil* Y))]
  [(:: (pair m n) xs)
   => (pair (:: m (fst (split_ X Y xs)))
            (:: n (snd (split_ X Y xs))))])

(define-implicit split = split_ 2)

;; continuing Tactics.v --------------------

(define (sillyfun (n : nat))
  (if (beq-nat n 3)
      false
      (if (beq-nat n 5)
          false
          false)))

(define-theorem sillyfun_false
  (forall (n : nat) (== bool (sillyfun n) false))
  (by-intro n)
  ;(unfold sillyfun) ; automatic
  (by-destruct (beq-nat n 3))
  reflexivity ;1
  (by-destruct (beq-nat n 5)) ;2
  reflexivity ;2a
  reflexivity) ;2b

(define-theorem eq-remove-cons
  (forall (X : Type) (l1 l2 : (list X)) (x : X)
          (-> (== l1 l2)
              (== (:: x l1) (:: x l2))))
  (by-intros X l1 l2 x H)
  (by-rewrite H)
  reflexivity)

(define-theorem combine-split
  (∀ [X Y : Type] (l : (list (prod X Y))) [l1 : (list X)] [l2 : (list Y)]
     (-> (== (split l) (pair l1 l2))
         (== (combine l1 l2) l)))

  (by-intros X Y l)
  (by-induction l #:as [() (h tl IH)])
  (by-intros l1 l2 H) ;1
  (by-inversion H #:as H0 H1)
  (by-rewriteL H0)
;  (by-rewriteL H1)
  reflexivity
  (by-destruct h #:as [(x y)]) ;2
  (by-intros l1 l2 H)
  (by-inversion H #:as H0 H1)
  (by-rewriteL H0)
  (by-rewriteL H1)
  (by-apply eq-remove-cons)
  (by-apply IH)
  (by-destruct (split tl) #:as [(l3 l4)])
  reflexivity)

(check-type
 combine-split
 : (∀ [X Y : Type] (l : (list (prod X Y))) [l1 : (list X)] [l2 : (list Y)]
      (-> (== (split l) (pair l1 l2))
          (== (combine l1 l2) l))))

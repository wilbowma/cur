#lang cur
(require cur/stdlib/sugar
         cur/stdlib/equality
         cur/ntac/base
         cur/ntac/standard
         cur/ntac/rewrite
         rackunit/turnstile
         "../rackunit-ntac.rkt")

; Software Foundations Tactics.v

;; copied from Poly-pairs.rkt
(data bool : 0 Type
      (true : bool)
      (false : bool))

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

(define/rec/match beq-nat : nat nat -> bool
  [O O => true]
  [O (S _) => false]
  [(S _) O => false]
  [(S n*) (S m*) => (beq-nat n* m*)])

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

;; pairs --------------------

(define-datatype prod [X : Type] [Y : Type] : -> Type
  [pair* : X Y -> (prod X Y)])

(define-implicit pair = pair* 2)

(define/rec/match fst* : [X : Type] [Y : Type] (prod X Y) -> X
  [(pair x _) => x])
(define/rec/match snd* : [X : Type] [Y : Type] (prod X Y) -> Y
  [(pair _ y) => y])

(define-implicit fst = fst* 2)
(define-implicit snd = snd* 2)


;; start of Tactics.v --------------------
(define-theorem silly1
  (∀ [n : nat] [m : nat] [o : nat] [p : nat]
     (-> (== n m)
         (== (lst n o) (lst n p))
         (== (lst n o) (lst m p))))
  (by-intros n m o p eq1 eq2)
  (by-rewriteL eq1)
  (by-apply eq2))

(define-theorem silly2
  (∀ [n : nat] [m : nat] [o : nat] [p : nat]
     (-> (== n m)
         (∀ [q : nat] [r : nat]
            (-> (== q r)
                (== (lst q o) (lst r p))))
         (== (lst n o) (lst m p))))
  (by-intros n m o p eq1 eq2)
  (by-apply eq2)
  (by-apply eq1))

(define-theorem silly2a
  (∀ [n : nat] [m : nat]
     (-> (== (pair n n) (pair m m))
         (∀ [q : nat] [r : nat]
            (-> (== (pair q q) (pair r r))
                (== (lst q) (lst r))))
         (== (lst n) (lst m))))
  (by-intros n m eq1 eq2)
  (by-apply eq2)
  (by-apply eq1))

(define/rec/match negb : bool -> bool
  [true => false]
  [false => true])

(define/rec/match evenb : nat -> bool
  [O => true]
  [(S O) => false]
  [(S (S n-1)) => (evenb n-1)])

(define (oddb [n : nat]) (negb (evenb n)))

(define-theorem silly_ex
  (-> (∀ [n : nat] (-> (== (evenb n) true)
                       (== (oddb (S n)) true)))
      (== (evenb 3) true)
      (== (oddb 4) true))
  by-intros
  by-assumption)

(define-theorem silly3a
  (∀ [n : nat] (-> (== true (beq-nat n 5))
                   (== (beq-nat (S (S n)) 7) true)))
  (by-intros n H)
  by-symmetry
  by-assumption)

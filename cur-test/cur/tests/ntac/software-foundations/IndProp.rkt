#lang cur
(require cur/stdlib/sugar
         cur/stdlib/equality
         cur/stdlib/prop
         cur/ntac/base
         cur/ntac/standard
         cur/ntac/rewrite
         rackunit/turnstile
         "../rackunit-ntac.rkt")

; examples from Software Foundations IndProp.v

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

(define-datatype ev : [i : nat] -> Prop
  [ev0 : (ev 0)]
  [evSS : [n : nat] (ev n) -> (ev (S (S n)))])

;; TODO: this wrong version, with param instead of index, should have better err msg
#;(define-datatype ev [i : nat] : Type
  [ev0 : (ev 0)]
  [evSS : [n : nat] [x : (ev n)] -> (ev (S (S n)))])

(check-type ev0 : (ev 0))
(check-type (ev0) : (ev 0))

(check-type (evSS 2 (evSS 0 ev0)) : (ev 4))
(check-not-type (evSS 2 (evSS 0 ev0)) : (ev 0))
(check-not-type (evSS 2 (evSS 0 ev0)) : (ev 2))
(check-not-type (evSS 2 (evSS 0 ev0)) : (ev 6))

(define-theorem ev4
  (ev 4)
  (by-apply evSS)
  (by-apply evSS)
  (by-apply ev0))

(check-type ev4 : (ev 4))

(define-theorem ev4b
  (ev 4)
  (by-apply (evSS 2 (evSS 0 ev0))))

(check-type ev4b : (ev 4))

(define/rec/match plus : nat [m : nat] -> nat
  [O => m]
  [(S n-1) => (S (plus n-1 m))])

(define-theorem ev+4
  (forall [n : nat] (-> (ev n) (ev (plus 4 n))))
  (by-intros n H)
  (by-apply evSS)
  (by-apply evSS)
  (by-apply H))

(check-type ev+4 : (forall [n : nat] (-> (ev n) (ev (plus 4 n)))))

(define/rec/match double : nat -> nat
  [O => O]
  [(S n-1) => (S (S (double n-1)))])

(define/rec/match pred : nat -> nat
  [O => O]
  [(S n-1) => n-1])

(define-theorem ev-double
  (forall [n : nat] (ev (double n)))
  (by-intro n)
  (by-induction n #:as [() (n-1 IH)])
  (by-apply ev0) ; 1
  (by-apply evSS) ;2
  (by-apply IH))

;; TODO: support inversion of arbitrary datatypes
#;(define-theorem ev-minus2
  (forall [n : nat] (-> (ev n) (ev (pred (pred n)))))
  (by-intros n E)
  (by-inversion E #:as [() (n1 E1)])
  (by-apply ev0) ;1
  (by-apply E1)) ;2

;; ev-minus2 raw term:

;; 1a) with elim:
(check-type
 (λ (n : nat) (E : (ev n))
    (new-elim E
          (λ [n0 : nat] [E0 : (ev n0)] (ev (pred (pred n0))))
          ev0
          (λ [n1 : nat] [E1 : (ev n1)] [ih : (ev (pred (pred n1)))]
             E1)))
 : (forall [n : nat] (-> (ev n) (ev (pred (pred n))))))

;; 1b) with elim, no type annos
(check-type
 (λ n E
    (new-elim E
          (λ n0 E0 (ev (pred (pred n0))))
          ev0
          (λ n1 E1 ih E1)))
 : (forall [n : nat] (-> (ev n) (ev (pred (pred n))))))

;; 1c) with specific elim-ev
(check-type
 (λ [n : nat] [E : (ev n)]
    (elim-ev
     E
     (λ (n : nat) (E : (ev n)) (ev (pred (pred n))))
     ev0
     (λ (n : nat) (g11 : (ev n)) (g1174 : (ev (pred (pred n)))) g11)))
 : (forall [n : nat] (-> (ev n) (ev (pred (pred n))))))

;; 2) with match: tests dependent matching
(check-type
 (λ (n : nat) (E : (ev n))
   (match E #:as E
            #:with-indices n
            #:in (ev n)
            #:return (ev (pred (pred n)))
     [ev0 ev0]
     [(evSS n1 E1) E1]))
 : (forall [n : nat] (-> (ev n) (ev (pred (pred n))))))

(define-theorem ev-minus2/destruct
  (forall [n : nat] (-> (ev n) (ev (pred (pred n)))))
  (by-intros n E)
  (by-destruct E #:as [() (n1 E1)])
  (by-apply ev0) ;1
  (by-apply E1)) ;2

(check-type ev-minus2/destruct
  : (forall [n : nat] (-> (ev n) (ev (pred (pred n))))))

;; more than 1 index
(define-datatype le : [n : nat] [m : nat] -> Prop
  [le-n : [n : nat] -> (le n n)]
  [le-S : [n : nat] [m : nat] (le n m) -> (le n (S m))])

(define-theorem test-le1
  (le 3 3)
  (by-apply le-n))

(define-theorem test-le2
  (le 3 6)
  (by-apply le-S)
  (by-apply le-S)
  (by-apply le-S)
  (by-apply le-n))  

(define-datatype reflect [P : Prop] : [b : bool] -> Prop
  [ReflectT : P -> (reflect P true)]
  [ReflectF : (-> P False) -> (reflect P false)])

(define-theorem iff-reflect
 (∀ [P : Prop] [b : bool]
     (-> (iff P (== b true))
         (reflect P b)))
  (by-intros P b H)
  (by-destruct b)
  (by-apply ReflectT) ;1
  (by-rewrite H)
  reflexivity
  (by-apply ReflectF) ;2
  (by-destruct H #:as [(H1 H2)])
  (by-intro p)
  (by-apply H1 #:in p)
  (by-discriminate p))

(check-type iff-reflect
 : (∀ [P : Prop] [b : bool]
     (-> (iff P (== b true))
         (reflect P b))))

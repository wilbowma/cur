#lang cur

(require
 "../rackunit-ntac.rkt"
 cur/stdlib/equality
 cur/stdlib/sugar
 cur/ntac/base
 cur/ntac/standard
 cur/ntac/ML-rewrite)

(provide (all-defined-out))

;; examples from SF Ch 1: Basics, using only Martin-Lof equality

(data day : 0 Type
      (mon : day)
      (tues : day)
      (wed : day)
      (thurs : day)
      (fri : day)
      (sat : day)
      (sun : day))

(define next-weekday
  (λ [d : day]
    (new-elim d
              (λ [x : day] day)
              tues
              wed
              thurs
              fri
              mon
              mon
              mon)))

(check-equal? (next-weekday fri) mon)
(check-equal? (next-weekday (next-weekday sat)) tues)

(define-theorem test-next-weekday
  (ML-= day (next-weekday (next-weekday sat)) tues)
  simpl
  reflexivity)

(data bool : 0 Type
      (true : bool)
      (false : bool))

(define negb
  (λ [b : bool]
    (new-elim b (λ [b : bool] bool) false true)))

(define andb
  (λ [b1 : bool] [b2 : bool]
     (new-elim b1 (λ [b : bool] bool) b2 false)))

(define orb
  (λ [b1 : bool] [b2 : bool]
     (new-elim b1 (λ [b : bool] bool) true b2)))

(define-theorem test-orb1
  (ML-= bool (orb true false) true)
  simpl
  reflexivity)

(define-theorem test-orb2
  (ML-= bool (orb false false) false)
  simpl
  reflexivity)

(define-theorem test-orb3
  (ML-= bool (orb false true) true)
  simpl
  reflexivity)

(define-theorem test-orb4
  (ML-= bool (orb true true) true)
  simpl
  reflexivity)

(define-syntax ||
  (syntax-parser
    [(_) #'true]
    [(_ x . rst) #'(orb x (|| . rst))]))

(define-syntax &&
  (syntax-parser
    [(_) #'false]
    [(_ x . rst) #'(andb x (&& . rst))]))

(define-theorem test-orb5
  (ML-= bool (|| false false true) true)
  simpl
  reflexivity)

(define nandb
  (λ [b1 : bool] [b2 : bool]
     (negb (andb b1 b2))))

(define-theorem test-nanb1
  (ML-= bool (nandb true false) true)
  simpl
  reflexivity)
(define-theorem test-nanb2
  (ML-= bool (nandb false false) true)
  simpl
  reflexivity)
(define-theorem test-nanb3
  (ML-= bool (nandb false true) true)
  simpl
  reflexivity)
(define-theorem test-nanb4
  (ML-= bool (nandb true true) false)
  simpl
  reflexivity)

(define andb3
  (λ [b1 : bool] [b2 : bool] [b3 : bool]
     (andb b1 (andb b2 b3))))

(define-theorem test-andb31
  (ML-= bool (andb3 true true true) true)
  simpl
  reflexivity)
(define-theorem test-andb32
  (ML-= bool (andb3 false true true) false)
  simpl
  reflexivity)
(define-theorem test-andb33
  (ML-= bool (andb3 true false true) false)
  simpl
  reflexivity)
(define-theorem test-andb34
  (ML-= bool (andb3 true true false) false)
  simpl
  reflexivity)

(:: true bool)
(:: (negb true) bool)
(:: negb (-> bool bool))

(data rgb : 0 Type
      (red : rgb)
      (green : rgb)
      (blue : rgb))

(data color : 0 Type
      (black : color)
      (white : color)
      (primary : (-> rgb color)))

(define monochrome
  (λ [c : color]
    (new-elim c
              (λ [c : color] bool)
              true
              true
              (λ [p : rgb] false))))

(define isred
  (λ [c : color]
    (new-elim c (λ [c : color] bool)
              false
              false
              (λ [r : rgb]
                (new-elim r (λ [r : rgb] bool)
                          true
                          false
                          false)))))
(check-equal? (isred black) false)
(check-equal? (isred white) false)
(check-equal? (isred (primary red)) true)
(check-equal? (isred (primary blue)) false)

(data nat : 0 Type
      (O : nat) ; letter capital "O"
      (S : (-> nat nat)))
(data nat* : 0 Type
      (stop : nat*)
      (tick : nat*))

(define pred
  (λ [n : nat]
    (new-elim n (λ [n : nat] nat)
              O
              (λ [n* : nat] [ih : nat] n*))))

;; re-define #%datum to use the new `nat`
(define-syntax #%datum
  (syntax-parser
    [(_ . n:exact-nonnegative-integer)
     #:when (zero? (syntax-e #'n))
     #'O]
    [(_ . n:exact-nonnegative-integer)
     #`(S (#%datum . #,(- (syntax-e #'n) 1)))]))

(check-equal? (S (S (S (S O)))) 4)

(define minustwo
  (λ [n : nat]
    (new-elim n (λ [n : nat] nat)
              O
              (λ [n* : nat] [ih : nat]
                 (new-elim n*
                           (λ [n : nat] nat)
                           O
                           (λ [n* : nat] [ih : nat]
                              n*))))))

(check-equal? (minustwo 4) 2)
(:: S (-> nat nat))
(:: pred (-> nat nat))
(:: minustwo (-> nat nat))

(define evenb
  (λ [n : nat]
    (new-elim n (λ [n : nat] bool)
              true
              (λ [n* : nat] [ih : bool]
                 (new-elim n* (λ [n : nat] bool)
                           false
                           (λ [n** : nat] [ih* : bool]
                              (negb ih*)))))))


(define oddb (λ [n : nat] (negb (evenb n))))

(define-theorem test-oddb1
  (ML-= bool (oddb 1) true)
  simpl
  reflexivity)

(define-theorem test-oddb2
  (ML-= bool (oddb 4) false)
  simpl
  reflexivity)

(ntac (ML-= bool (oddb 0) false) reflexivity)
(ntac (ML-= bool (oddb 2) false) reflexivity)
(ntac (ML-= bool (oddb 3) true) reflexivity)
(ntac (ML-= bool (oddb 5) true) reflexivity)

(define plus
  (λ [n : nat] [m : nat]
     (new-elim n
               (λ [n : nat] nat)
               m
               (λ [n* : nat] [ih : nat]
                  (S ih)))))

(check-equal? (plus 2 3) 5)

(define mult
  (λ [n : nat]
    (λ [m : nat]
      (new-elim n
                (λ [x : nat] nat)
                O
                (λ [n* : nat] [ih : nat]
                   (plus m ih))))))

(check-equal? (mult 1 1) 1)
(check-equal? (mult 2 1) 2)
(check-equal? (mult 3 2) 6)
(check-equal? (mult 4 6) 24)
(check-equal? (mult 5 24) 120)

(define-theorem test-mult1
  (ML-= nat (mult 3 3) 9)
  simpl
  reflexivity)

(define minus
  (λ [n : nat] [m : nat]
     (new-elim n (λ [n : nat] nat)
               O
               (λ [m* : nat][ih : nat]
                  (new-elim m
                            (λ [n : nat] nat)
                            n
                            (λ [m* : nat] [ih* : nat]
                               (new-elim ih*
                                         (λ [n : nat] nat)
                                         O
                                         (λ [n* : nat] [ih : nat]
                                            n*))))))))
(check-equal? (minus 4 1) 3)
(check-equal? (minus 0 0) 0)
(check-equal? (minus 1 1) 0)
(check-equal? (minus 1 0) 1)
(check-equal? (minus 2 0) 2)
(check-equal? (minus 2 1) 1)
(check-equal? (minus 3 1) 2)

(define exp
  (λ [base : nat] [power : nat]
     (new-elim power
               (λ [n : nat] nat)
               1
               (λ [p : nat][ih : nat]
                  (mult base ih)))))
#;(define factorial
  (λ [n : nat]
    (new-elim n
              (λ [n : nat] nat)
              (S O)
              (λ [n* : nat] [ih : nat]
                 (mult (S n*) ih)))))

(define/rec/match factorial : nat -> nat
  [O => 1]
  [(S n*) => (mult (S n*) (factorial n*))])

(check-equal? (mult (S (S O)) (S O)) (S (S O)))

(check-equal? (factorial 0) 1)
(check-equal? (factorial 1) 1)
(check-equal? 2 (S (S O)))
(check-equal? (factorial 2) 2)
(check-equal? (factorial (S (S O))) (S (S O)))
(check-equal? (factorial 3) 6)
(check-equal? (factorial 5) 120)
(define-theorem test-factorial1
  (ML-= nat (factorial 3) 6)
  simpl
  reflexivity)

(define-theorem test-factorial2
  (ML-= nat (factorial 5) 120)
  simpl
  reflexivity)

(define-syntax +
  (syntax-parser
    [(_) #'0]
    [(_ x . rst) #'(plus x (+ . rst))]))

(define-syntax *
  (syntax-parser
    [(_) #'1]
    [(_ x . rst) #'(mult x (* . rst))]))

(define-syntax -
  (syntax-parser
    [(_ x y) #'(minus x y)]))

(check-equal? (+ 0 1 1) 2)

(define/rec/match beq-nat : nat nat -> bool
  [O O => true]
  [O (S _) => false]
  [(S _) O => false]
  [(S n*) (S m*) => (beq-nat n* m*)])

(check-equal? (beq-nat 0 0) true)
(check-equal? (beq-nat 0 1) false)
(check-equal? (beq-nat 1 0) false)
(check-equal? (beq-nat 1 1) true)
(check-equal? (beq-nat 1 2) false)
(check-equal? (beq-nat 2 1) false)

(define/rec/match leb : nat nat -> bool
  [O O => true]
  [O (S _) => true]
  [(S _) O => false]
  [(S n*) (S m*) => (leb n* m*)])

(check-equal? ((leb 2) 2) true)
(:: ((leb 2) 2) bool)
(:: (ML-refl bool true)
    (ML-= bool (leb 2 2) true))
(define-theorem test-leb1
  (ML-= bool (leb 2 2) true)
  simpl
  reflexivity)
(define-theorem test-leb2
  (ML-= bool (leb 2 4) true)
  simpl
  reflexivity)
(define-theorem test-leb3
  (ML-= bool (leb 4 2) false)
  simpl
  reflexivity)

(define (blt-nat [n : nat] [m : nat])
  (andb (leb n m) (negb (beq-nat n m))))
(define-theorem test-blt-nat1
  (ML-= bool (blt-nat 2 2) false)
  simpl
  reflexivity)
(define-theorem test-blt-nat2
  (ML-= bool (blt-nat 2 4) true)
  simpl
  reflexivity)
(define-theorem test-blt-nat3
  (ML-= bool (blt-nat 4 2) false)
  simpl
  reflexivity)

(define-theorem plus-0-n
  (forall [n : nat] (ML-= nat (plus 0 n) n))
  by-intro
  simpl
  reflexivity)

(define-theorem plus-0-n*
  (forall [n : nat] (ML-= nat (plus 0 n) n))
  by-intro
  reflexivity)

(define-theorem plus-1-l
  (∀ [n : nat] (ML-= nat (plus 1 n) (S n)))
  by-intro
  simpl
  reflexivity)

(define-theorem mult-0-l
  (∀ [n : nat] (ML-= nat (mult 0 n) 0))
  by-intro
  simpl
  reflexivity)

(define-theorem plus-id-example
  (∀ [n : nat] [m : nat]
     (-> (ML-= nat n m)
         (ML-= nat (plus n n) (plus m m))))
  by-intro
  by-intro
  (by-intro H)
  (by-rewrite H)
  reflexivity)

(define-theorem plus-id-exercise
  (∀ [n : nat] [m : nat] [o : nat]
     (-> (ML-= nat n m)
         (ML-= nat m o)
         (ML-= nat (plus n m) (plus m o))))
  by-intro
  by-intro
  by-intro
  (by-intro H1)
  (by-intro H2)
  (by-rewriteR H1)
  (by-rewriteL H2)
  reflexivity)

(define-theorem mult-0-plus
  (∀ [n : nat] [m : nat]
     (ML-= nat (mult (plus 0 n) m) (mult n m)))
  (by-intro n)
  by-intro
  (by-rewrite plus-0-n n)
  reflexivity)

;; uses plus-0-n*
(define-theorem mult-0-plus*
  (∀ [n : nat] [m : nat]
     (ML-= nat (mult (plus 0 n) m) (mult n m)))
  (by-intro n)
  by-intro
  (by-rewrite plus-0-n* n)
  reflexivity)

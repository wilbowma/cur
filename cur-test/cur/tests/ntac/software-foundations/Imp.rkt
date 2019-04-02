#lang cur

(require
 cur/stdlib/nat
 cur/stdlib/bool
 cur/stdlib/sugar
 cur/stdlib/equality
 cur/ntac/base
 cur/ntac/standard
 cur/ntac/rewrite
 rackunit/turnstile
 "../rackunit-ntac.rkt")

(define-datatype aexp : Type
  [ANum (n : Nat)]
  [APlus (a1 a2 : aexp)]
  [AMinus (a1 a2 : aexp)]
  [AMult (a1 a2 : aexp)])

(define-datatype bexp : Type
  [BTrue]
  [BFalse]
  [BEq (a1 a2 : aexp)]
  [BLe (a1 a2 : aexp)]
  [BNot (b : bexp)]
  [BAnd (b1 b2 : bexp)])

(define/rec/match aeval : aexp -> Nat
  [(ANum n) => n]
  [(APlus  a1 a2) => (plus (aeval a1) (aeval a2))]
  [(AMinus a1 a2) => (minus (aeval a1) (aeval a2))]
  [(AMult  a1 a2) => (mult (aeval a1) (aeval a2))])

(define-theorem test_aeval1
  (== (aeval (APlus (ANum 2) (ANum 2))) 4)
  reflexivity)

(define/rec/match beval : bexp -> Bool
  [BTrue       => true]
  [BFalse      => false]
  [(BEq a1 a2)   => (nat-equal? (aeval a1) (aeval a2))]
  [(BLe a1 a2)   => (<= (aeval a1) (aeval a2))]
  [(BNot b1)     => (not (beval b1))]
  [(BAnd b1 b2)  => (and (beval b1) (beval b2))])

(define/rec/match optimize_0plus : aexp -> aexp
  [(ANum n) => (ANum n)]
  [(APlus (ANum z) e2) => (optimize_0plus e2)]
  [(APlus  e1 e2) => (APlus  (optimize_0plus e1) (optimize_0plus e2))]
  [(AMinus e1 e2) => (AMinus (optimize_0plus e1) (optimize_0plus e2))]
  [(AMult  e1 e2) => (AMult  (optimize_0plus e1) (optimize_0plus e2))])

(define-theorem test_optimize_0plus
  (== (optimize_0plus (APlus (ANum 2)
                             (APlus (ANum 0)
                                    (APlus (ANum 0) (ANum 1)))))
      (APlus (ANum 2) (ANum 1)))
  reflexivity)

;; with explicit names
(define-theorem optimize_0plus_sound
  (forall [a : aexp] (== (aeval (optimize_0plus a)) (aeval a)))
  (by-intro a)
  (by-induction a #:as [(n) (a1 a2 ih1 ih2) (a1 a2 ih1 ih2) (a1 a2 ih1 ih2)])
  ; ANum ----------
  reflexivity
  ; APlus ----------
  (by-destruct a1 #:as [(n) (a3 a4) (a3 a4) (a3 a4)])
  ; a1 = ANum
  (by-destruct n)
  ; n=0
  (by-apply ih2)
  ; n neq 0
  (by-rewrite ih2)
  reflexivity
  ; a1 = APlus
  (by-rewrite ih1)
  (by-rewrite ih2)
  reflexivity
  ; a1 = AMinus
  (by-rewrite ih1)
  (by-rewrite ih2)
  reflexivity
  ; a1 = AMult
  (by-rewrite ih1)
  (by-rewrite ih2)
  reflexivity
  ; AMinus ----------
  (by-rewrite ih1)
  (by-rewrite ih2)
  reflexivity
  ; AMult ----------
  (by-rewrite ih1)
  (by-rewrite ih2)
  reflexivity)

(check-type optimize_0plus_sound
  : (forall [a : aexp] (== (aeval (optimize_0plus a)) (aeval a))))

  ;; allow destruct to generate names, test non-shadowing (was previously failing)
(define-theorem optimize_0plus_sound2
  (forall [a : aexp] (== (aeval (optimize_0plus a)) (aeval a)))
  (by-intro a)
  (by-induction a #:as [(n) (a1 a2 ih1 ih2) (a1 a2 ih1 ih2) (a1 a2 ih1 ih2)])
  ; ANum ----------
  reflexivity
  ; APlus ----------
  (by-destruct a1) ; generates n136
  ; a1 = ANum
  (by-destruct n136)
  ; n=0
  (by-apply ih2)
  ; n neq 0
  (by-rewrite ih2)
  reflexivity
  ; a1 = APlus
  (by-rewrite ih1)
  (by-rewrite ih2)
  reflexivity
  ; a1 = AMinus
  (by-rewrite ih1)
  (by-rewrite ih2)
  reflexivity
  ; a1 = AMult
  (by-rewrite ih1)
  (by-rewrite ih2)
  reflexivity
  ; AMinus ----------
  (by-rewrite ih1)
  (by-rewrite ih2)
  reflexivity
  ; AMult ----------
  (by-rewrite ih1)
  (by-rewrite ih2)
  reflexivity)

;; test tacticals --------------------
(define-theorem silly1
  (forall (ae : aexp) (== (aeval ae) (aeval ae)))
;  by-intro
  (try reflexivity))

(define-theorem silly2
  (forall (P : Prop) (-> P P))
  (by-intros P HP)
  (try reflexivity) ; Just [reflexivity] would have failed
  (by-apply HP)) ; We can still finish the proof in some other way.

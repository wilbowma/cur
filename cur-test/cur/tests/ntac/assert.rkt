#lang cur
(require cur/stdlib/equality
         cur/stdlib/sugar
         cur/stdlib/nat
         cur/ntac/base
         cur/ntac/standard
         cur/ntac/rewrite
         "../rackunit-ntac.rkt")

;; basic assert examples

(check-ntac-trace
 (∀ [x : Nat] [y : Nat]
    (-> (== Nat x y)
        (== Nat y x)))
 (by-intros x y x=y)
 (by-assert y=x (== Nat y x))
 ;; proving y=x
 (by-rewriteR x=y)
 reflexivity
 ;; proving goal
 (by-assumption y=x)
 ~>
 
 --------------------------------
 (Π (x : Nat) (y : Nat) (temp1 : (== Nat x y)) (== Nat y x))

 x : Nat
 y : Nat
 x=y : (== Nat x y)
 --------------------------------
 (== Nat y x)

 x : Nat
 y : Nat
 x=y : (== Nat x y)
 --------------------------------
 (== Nat y x)

 x : Nat
 y : Nat
 x=y : (== Nat x y)
 --------------------------------
 (== Nat y y)

 x : Nat
 y : Nat
 x=y : (== Nat x y)
 y=x : (== Nat y x)
 --------------------------------
 (== Nat y x))

#lang cur
(require cur/stdlib/equality
         cur/stdlib/sugar
         cur/stdlib/nat
         cur/ntac/base
         cur/ntac/standard
         cur/ntac/rewrite
         rackunit)

;; basic assert examples

(define-theorem m=n
  (∀ [x : Nat] [y : Nat]
     (-> (== Nat x y)
         (== Nat y x)))
  (by-intros x y x=y)
  (by-assert y=x (== Nat y x))
  ;; proving y=x
  (by-rewriteR x=y)
  reflexivity
  ;; proving goal
  (by-assumption y=x))

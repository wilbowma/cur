#lang cur
(require cur/stdlib/sugar
         cur/stdlib/equality
         cur/ntac/base
         cur/ntac/standard
         cur/ntac/rewrite
         "rackunit-ntac.rkt")

;; tests for reflexivity with polymorphic functions

;; * = "full" version; as opposed to hidden-arg version
(define-datatype list [X : Type] : -> Type
  [nil* : (list X)]
  [cons* : X (list X) -> (list X)])

;; no user-supplied intro name
 (check-ntac-trace
 (∀ [X : Type] (== (list X) (nil* X) (nil* X)))
 by-intro
 reflexivity
 ~>
 --------------------------------
 (Π (X : Type) (== (list X) (nil* X) (nil* X)))
 
 X : Type
 --------------------------------
 (== (list X) (nil* X) (nil* X)))

;; user-supplied intro name: same
(check-ntac-trace
 (∀ [X : Type] (== (list X) (nil* X) (nil* X)))
 (by-intro X)
 reflexivity
 ~>
 --------------------------------
 (Π (X : Type) (== (list X) (nil* X) (nil* X)))
 
 X : Type
 --------------------------------
 (== (list X) (nil* X) (nil* X)))

;; user-supplied intro name: different
(check-ntac-trace
 (∀ [X : Type] (== (list X) (nil* X) (nil* X)))
 (by-intro Y)
 reflexivity
 ~>
 --------------------------------
 (Π (X : Type) (== (list X) (nil* X) (nil* X)))
 
 Y : Type
 --------------------------------
 (== (list Y) (nil* Y) (nil* Y)))

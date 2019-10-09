#lang cur
(require cur/stdlib/sugar
         cur/ntac/base
         cur/ntac/standard
         rackunit/turnstile+
         "rackunit-ntac.rkt")

;; test generalize introduces proper scopes
(define-theorem id
  (Π [X : Type] (-> X X))
  by-intro
  (by-generalize X)
  by-intro
  (by-generalize X)
  by-intro by-intro
  by-assumption)

(check-type id : (Π [X : Type] (-> X X)))

(check-type
 (λ (X : Type)
   ((λ (X : Type)
      ((λ (X : Type)
         (λ (x : X) x))
       X))
    X))
 : (Π [X : Type] (-> X X)))

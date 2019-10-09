#lang cur
(require cur/stdlib/nat
         cur/stdlib/bool
         cur/stdlib/sugar
         cur/stdlib/equality
         cur/ntac/base
         cur/ntac/standard
         cur/ntac/ML-rewrite
         rackunit/turnstile+)

;; <= (example needing recursion on more than on arg)
(define/rec/match leb : Nat Nat -> Bool
  [z z => true]
  [z (s _) => true]
  [(s _) z => false]
  [(s n-1) (s m-1) => (leb n-1 m-1)])

(check-type ((leb 2) 2) : Bool -> true)
(check-type ((leb 2) 2) : Bool)
(check-type (ML-refl Bool true)
            : (ML-= Bool (leb 2 2) true))

(define-theorem test-leb1
  (ML-= Bool (leb 2 2) true)
  simpl
  reflexivity)
(define-theorem test-leb2
  (ML-= Bool (leb 2 4) true)
  simpl
  reflexivity)
(define-theorem test-leb3
  (ML-= Bool (leb 4 2) false)
  simpl
  reflexivity)

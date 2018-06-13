#lang cur
(require cur/stdlib/nat
         cur/stdlib/bool
         cur/stdlib/sugar
         cur/stdlib/equality
         cur/ntac/base
         cur/ntac/standard
         cur/ntac/ML-rewrite
         rackunit)

;; example that needs double recursion
(define (leb [n : Nat])
  (match n #:in Nat #:return (-> Nat Bool)
    [z
     (λ [m : Nat] true)]
    [(s n*)
     (λ [m : Nat]
       (match m #:in Nat #:return Bool
         [z false]
         [(s m*) ((leb n*) m*)]))]))

(check-equal? ((leb 2) 2) true)
(:: ((leb 2) 2) Bool)
(:: (ML-refl Bool true)
    (ML-= Bool (leb 2 2) true))

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

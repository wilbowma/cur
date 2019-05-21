#lang cur
(require
 cur/stdlib/sugar
 cur/stdlib/nat
 cur/stdlib/bool
 rackunit/turnstile)

;; tests for dependent pattern matching; from Cockx thesis

(define-datatype Vect [A : Type] : (-> [i : Nat] Type)
  [nil : (Vect A z)]
  [cns [k : Nat] [x : A] [xs : (Vect A k)] : (Vect A (s k))])

;; TODO: enable this pattern by unifying return type (ty-out) with indices of constructor in each branch
#;(define/rec/match replicate : [A : Type] [x : A] [n : Nat] -> (Vect A n)
  [z => (nil A)]
  [(s m) => (cns A m x (replicate A x m))])
  

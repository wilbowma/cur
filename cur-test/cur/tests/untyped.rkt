#lang racket/base

(module A cur
  (require cur/stdlib/nat)
  (provide z)
  z)


(module B cur/untyped
  (data Nat (z) (s n #:recursive))
  z
  (provide Nat z s))

(module C cur/untyped
  (require (submod ".." A))
  z)

#;(module D cur
  (require (submod ".." B))
  ((λ (x : Nat) x) z) )

(module E cur/untyped
  ((λ (x) (x x))
   (λ (x) (x x))))

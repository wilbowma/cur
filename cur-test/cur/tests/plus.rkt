#lang cur

(require
 cur/stdlib/sugar
 rackunit/turnstile+)

(data Nat : 0 Type
  (z : Nat)
  (s : (Π (x : Nat) Nat)))

;(plus . : . (-> Nat Nat Nat))
(define/rec/match plus : Nat [m : Nat] -> Nat
  [z => m]
  [(s n-1) => (s (plus n-1 m))])

(check-type (plus z z) : Nat -> z)

(check-type (plus (s z) z) : Nat -> (s z))

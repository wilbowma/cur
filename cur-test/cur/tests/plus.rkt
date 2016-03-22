#lang cur

(require
 cur/stdlib/sugar
 rackunit)

(data Nat : Type
  (z : Nat)
  (s : (Π (x : Nat) Nat)))

(plus . : . (-> Nat Nat Nat))
(define (plus n m)
  (match n
    [z m]
    [(s (x : Nat))
     (s (recur x))]))

(check-equal?
 (plus z z)
 z)

(check-equal?
 (plus (s z) z)
 (s z))

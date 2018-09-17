#lang cur

(require
 cur/stdlib/sugar
 turnstile/rackunit-typechecking)

(data Nat : 0 Type
  (z : Nat)
  (s : (Π (x : Nat) Nat)))

;; ;(plus . : . (-> Nat Nat Nat))
;; (define (plus [n : Nat] [m : Nat] -> Nat)
;;   (match n
;;     [z m]
;;     [(s (x : Nat))
;;      (s (recur x))]))

;; (check-type (plus z z) : Nat -> z)

;; (check-type (plus (s z) z) : Nat -> (s z))

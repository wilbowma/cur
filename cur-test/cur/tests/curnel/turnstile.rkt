#lang cur/turnstile

;; Subtyping
;; should type check
((λ (f : (Π (x : (Type 0)) (Type 1))) f) (λ (x : (Type 0)) x))

;; Zero arity constructors
(data Nat : 0 (Type 0)
  (z : Nat)
  (s : (Π (x : Nat) Nat)))

(define add1 (λ (x : Nat) (s x)))

(add1 z)

;; should  yield
;; (s (z))

;; Delta reduction

(data == : 2 (Π (A : (Type 0)) (Π (a : A) (Π (b : A) (Type 0))))
      (refl : (Π (A : (Type 0)) (Π (a : A) (((== A) a) a)))))

(((== Nat) (add1 z)) (s z))

;; should  yield
;; (== (Nat) (s (z)) (s (z)))

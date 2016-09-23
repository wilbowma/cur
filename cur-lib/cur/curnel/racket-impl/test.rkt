#lang s-exp "lang.rkt"

(Type 1)

(define x (Type 1))

x

(Π (x : (Type 1)) (Type 1))
(define id (λ (x : (Type 2)) x))
id
(λ (x : (Type 2)) x)
((λ (x : (Type 2)) x) (Type 1))

(define id2 (λ (A : (Type 3)) (λ (a : A) a)))
; id2
((λ (A : (Type 3)) (λ (a : A) a)) (Type 2))

#;(((λ (Nat : (Type 3))
     (λ (z : Nat)
       (λ (s : (Π (n : Nat) Nat))
         z)))
  (Type 2))
 (Type 1))

#;((
 (Type 1))
 (λ (n : Nat) (Type 1)))

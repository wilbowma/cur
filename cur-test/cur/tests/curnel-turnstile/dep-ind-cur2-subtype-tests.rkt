#lang s-exp cur/curnel/turnstile-impl/dep-ind-cur2
(require rackunit/turnstile)

(check-type
 ((λ (f : (Π (x : (Type 0)) (Type 1))) f)
  (λ (x : (Type 0)) x))
 : (Π (x : (Type 0)) (Type 1)))

;; result can have body type at higher universe
(check-type
 ((λ (f : (Π (x : (Type 0)) (Type 1))) f)
  (λ (x : (Type 0)) x))
 : (Π (x : (Type 0)) (Type 2)))

#lang s-exp "lang.rkt"

;(Type 1)
;;
;(define x (Type 1))
;;
;x
;
;(Π (x : (Type 1)) (Type 1))
;(define id (λ (x : (Type 2)) x))
;((λ (x : (Type 2)) x) (Type 1))
;
;(id (Type 1))
;
;(define id2 (λ (A : (Type 3)) (λ (a : A) a)))
;((id2 (Type 2)) (Type 1))
;
;(((λ (Nat : (Type 3))
;     (λ (z : Nat)
;       (λ (s : (Π (n : Nat) Nat))
;         z)))
;  (Type 2))
; (Type 1))

(axiom Nat : (Type 0))
(axiom z : Nat)
(axiom s : (Π (y : Nat) Nat))
(axiom meow : (Π (x : (Type 1)) (Type 0)))

z
; should fail with good error, does
;(z (Type 0))
(meow (Type 0))
; Should fail with good error, does
;(meow 1)
;meow

(axiom Vec : (Π (A : (Type 0)) (Π (n : Nat) (Type 0))))
(axiom nil : (Π (A : (Type 0)) ((Vec A) z)))
(nil Nat)
;
((λ (a : ((Vec Nat) z)) z) (nil Nat))
(axiom NotVec : (Π (A : (Type 0)) (Π (n : Nat) (Type 0))))
;; Should fail, does
;;((λ (a : ((NotVec Nat) z)) z) (nil Nat))
;
(define test1 (λ (a : (Π (x : Nat) Nat)) (a z)))
s
; should fail; does, with good error
;(test1 z)
(test1 s)

; TODO this is bad:
; looks like #%app gets redefined by racket/base...
; but this behavior is consistent with typed/racket... redefine require to emit warnings when base
; forms are redefined
;(require racket/base)
;(meow (list 1))

;; Should fail with good error, does
#;(data Nat : 0 (Type 0)
      (z : Nat)
      (s : (Π (x : Nat) Nat)))

#;(data Nat2 : 0 (Type 0)
      (z : Nat2)
      (s : (Π (x : Nat) Nat)))

(data Nat2 : 0 (Type 0)
      (z2 : Nat2)
      (s2 : (Π (x : Nat2) Nat2))
      )

z2

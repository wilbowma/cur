#lang s-exp "lang.rkt"

(Type 1)

;; Should fail with good error, does
;(Type z)

(define x (Type 1))

; Should fail with good error, does
;(define y (define z (Type 1)) z)
;(define y (define z (Type 1) x) z)

(λ (y : x) x)

;; Should fail with good error, do
; (define x Type)
; (define x (Type 1) (Type 1))

x

(Π (x : (Type 1)) (Type 1))

(Π (x : (Type 1)) (Type 2))

;; Should fail with good error, do (TODO Ish. Error messages still need polish)
;(Π (x : (x (Type 1))) (Type 1))
;(Π (x : (Type 1)) (x (Type 1)))
;(Π (y : (Type 1)) (x (Type 1)))
;(Π (y : (λ (x : (Type 0)) x)) (x (Type 1)))

(define id (λ (x : (Type 2)) x))
((λ (x : (Type 2)) x) (Type 1))

;; Should fail with good error, do (ish; see above)
;((λ (x : (Type 2)) x) (Type 2))
;((Type 1) (Type 2))

(id (Type 1))

(define id2 (λ (A : (Type 3)) (λ (a : A) a)))
((id2 (Type 2)) (Type 1))

; Should fail with good error, does
;((id2 (Type 2)) (Type 2))

(((λ (Nat : (Type 3))
     (λ (z : Nat)
       (λ (s : (Π (n : Nat) Nat))
         z)))
  (Type 2))
 (Type 1))

(axiom Nat : (Type 0))
(axiom z : Nat)
(axiom s : (Π (y : Nat) Nat))
(axiom meow : (Π (x : (Type 1)) (Type 0)))

;; should fail with good error, does
;(axiom meow2 : ((Type 1) (Type 2)))

;; should fail, does
;(axiom meow3 : (λ (x : (Type 0)) x))

; Should fail with good error, does
;(define y (axiom Nat : (Type 0)))

z
; should fail with good error, does
;(z (Type 0))
(meow (Type 0))
; Should fail with good error, does
;(meow 1)
meow

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
; (require racket/base)
; looks like #%app gets redefined by racket/base...
; but this behavior is consistent with typed/racket... redefine require to emit warnings when base
; forms are redefined

;; should fail with good error, does
;(require (only-in racket/base list))
;(meow (list 1))

;; Should fail with good error, does
#;(data Nat : 0 (Type 0)
      (z : Nat)
      (s : (Π (x : Nat) Nat)))

#;(data Nat2 : 0 (Type 0)
      (z : Nat2)
      (s : (Π (x : Nat) Nat)))

;; TODO: Should fail, does but with wrong error.
#;(data Nat2 : 0 (id (Type 1))
      (z2 : Nat2)
      (s2 : (Π (x : Nat) Nat)))

(data Nat2 : 0 (Type 0)
      (z2 : Nat2)
      (s2 : (Π (x : Nat2) Nat2)))

z2

;; should fail with good error, does
#;(elim z (λ (x : Nat) Nat)
      (z (λ (n : Nat) n)))

(elim z2 (λ (x : Nat2) Nat2)
      (z2 (λ (n : Nat2) n)))

(elim (s2 z2) (λ (x : Nat2) Nat2)
      (z2 (λ (n : Nat2) n)))

;; should fail with good error, does
#;(elim (s2 z2) Nat2
      (z2 (λ (n : Nat2) n)))

;; should fail with good error, does
#;(elim (s2 z2) (λ (x : Nat2) Nat2)
      (z2))

(data Maybe : 1 (Π (A : (Type 0)) (Type 0))
      (none : (Π (A : (Type 0)) (Maybe A)))
      (just : (Π (A : (Type 0)) (Π (a : A) (Maybe A)))))

((λ (f : (Π (A : (Type 0)) (Type 0))) z) Maybe)

;; TODO Causes runtime error because parameters not supported, and method typing not yet implemented.
(elim (none Nat) (λ (x : (Maybe Nat)) Nat)
      (z (λ (A : (Type 0)) (λ (a : A) a))))

((λ (x : (elim z2 (λ (x : Nat2) (Type 1))
              (Nat (λ (x : Nat2) Nat)))) x) z)

((λ (x : (elim (s2 z2) (λ (x : Nat2) (Type 1))
              (Nat (λ (x : Nat2) Nat)))) x) z)

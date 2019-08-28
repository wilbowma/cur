#lang cur
(require
 cur/stdlib/sugar
 rackunit/turnstile)

(define-datatype Nat : Type
  [Z : Nat]
  [S : (→ Nat Nat)])

(define/rec/match plus : Nat [n : Nat] -> Nat
  [Z => n]
  [(S x) => (S (plus x n))])

(define/rec/match minus : Nat Nat -> Nat
  [Z _ => Z]
  [(S n-1) z => (S n-1)]
  [(S n-1) (S m-1) => (minus n-1 m-1)])

(define/rec/match mult : Nat [n : Nat] -> Nat
  [Z => Z]
  [(S x) => (plus n (mult x n))])

(check-type
 (λ (x : (Type 1)) x)
 : (-> (Type 1) (Type 1)))

(check-type
 ((λ (x : (Type 1)) x) Type)
 : (Type 1))

(check-type
 (λ (x : (Type 1)) (y : (Π (x : (Type 1)) (Type 1))) (y x))
 : (-> (Type 1) (Π (x : (Type 1)) (Type 1)) (Type 1)))

;; TODO: Missing tests for match, others
(check-type
 ((λ (x : (Type 1)) (y : (Π (x : (Type 1)) (Type 1))) (y x))
  Type
  (λ (x : (Type 1)) x))
 : (Type 1)
 -> Type)

(check-type
 ((λ (x : (Type 1)) (y : (→ (Type 1) (Type 1))) (y x))
  Type
  (λ (x : (Type 1)) x))
 : (Type 1)
 -> Type)

(check-type
 (let ([x Type]
       [y (λ (x : (Type 1)) x)])
   (y x))
 : (Type 1)
 -> Type)

(check-type ; with 1 anno
 (let ([(x : (Type 1)) Type]
       [y (λ (x : (Type 1)) x)])
   (y x))
 : (Type 1)
 -> Type)

;; check that raises decent syntax error
(typecheck-fail
 (let ([x : (Type 1) Type]
       [y (λ (x : (Type 1)) x)])
   (y x))
 #:with-msg "unexpected term.*at: \\(Type 1\\)")

(typecheck-fail
 (let ([x (λ x x)]
       [y (λ (x : (Type 1)) x)])
   (y x))
 #:with-msg "λ: no expected type, add annotations")

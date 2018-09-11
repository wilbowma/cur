#lang cur
(require
 turnstile/rackunit-typechecking
 cur/stdlib/sugar)

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

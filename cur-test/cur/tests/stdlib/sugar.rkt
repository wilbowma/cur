#lang cur
(require
 rackunit
 cur/stdlib/sugar)

;; TODO: Missing tests for match, others
(check-equal?
 ((λ* (x : (Type 1)) (y : (∀* (x : (Type 1)) (Type 1))) (y x))
  Type
  (λ (x : (Type 1)) x))
 Type)

(check-equal?
 ((λ* (x : (Type 1)) (y : (→* (Type 1) (Type 1))) (y x))
  Type
  (λ (x : (Type 1)) x))
 Type)

(check-equal?
 ((λ* (x : (Type 1)) (y : (→ (Type 1) (Type 1))) (y x))
  Type
  (λ (x : (Type 1)) x))
 Type)

(check-equal?
 (let ([x Type]
       [y (λ (x : (Type 1)) x)])
   (y x))
 Type)

(check-equal?
 (let ([(x : (Type 1)) Type]
       [y (λ (x : (Type 1)) x)])
   (y x))
 Type)

;; check that raises decent syntax error
;; Can't use this because (lambda () ...) and thunk are not things in Cur at runtime
#;(check-exn
   exn:fail:syntax?
   (let ([x : (Type 1) Type]
         [y (λ (x : (Type 1)) x)])
     (y x)))

;; check that raises type error
#;(check-exn
   exn:fail:syntax?
   (let ([x uninferrable-expr]
         [y (λ (x : (Type 1)) x)])
     (y x)))


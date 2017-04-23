#lang cur

(require
 "sugar.rkt"
 "prop.rkt"
 "nat.rkt")

(data Σ0 : 2 (-> (A : (Type 0)) (P : (-> A (Type 0))) (Type 0))
      (pair0 : (-> (A : (Type 0)) (P : (-> A (Type 0))) (a : A) (b : (P a)) (Σ0 A P))))

(data Σ1 : 2 (-> (A : (Type 1)) (P : (-> A (Type 1))) (Type 1))
      (pair1 : (-> (A : (Type 1)) (P : (-> A (Type 1))) (a : A) (b : (P a)) (Σ1 A P))))

;; TODO: As demo, write macro that generates version of Σ for every universe level
(define-syntax (Σ syn)
  (syntax-parse syn
    #:datum-literals (:)
    #:literals (Type)
    [(_ (x:id : A) B)
     #:with (typed-Type i) (cur-type-infer #'A)
     #:with name (format-id syn "Σ~a" (syntax->datum #'i))
     #`(name A (λ (x : A) B))]))

(:: (pair0 Nat (λ (x : Nat) (== Nat x 5)) 5 (refl Nat 5)) (Σ (x : Nat) (== Nat x 5)))

(define (fst0 (A : (Type 0)) (P : (-> A (Type 0))) (p : (Σ0 A P)))
  (match p
    #:return A
    [(pair0 a _) a]))

(define (fst1 (A : (Type 1)) (P : (-> A (Type 1))) (p : (Σ1 A P)))
  (match p
    #:return A
    [(pair1 a _) a]))

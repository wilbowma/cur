#lang s-exp "../main.rkt"
(require "sugar.rkt" "nat.rkt")
(provide coq= coq-refl coq=-sym-nat coq=-sym)

(data coq= : 2 (forall (A : Type) (x : A) [y : A] Type)
  (coq-refl : (forall (A : Type) (x : A) (coq= A x x))))

(define coq=-sym-nat
  (λ [n : Nat] [m : Nat]
     (λ [n=m : (coq= Nat n m)]
       (new-elim
        n=m
        (λ [m : Nat]
           (λ [n=m : (coq= Nat n m)]
             (coq= Nat m n)))
        (coq-refl Nat n)))))

(define coq=-sym
  (λ [A : Type]
    (λ [n : A] [m : A]
     (λ [n=m : (coq= A n m)]
       (new-elim
        n=m
        (λ [m : A]
           (λ [n=m : (coq= A n m)]
             (coq= A m n)))
        (coq-refl A n))))))

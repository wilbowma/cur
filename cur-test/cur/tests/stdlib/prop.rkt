#lang cur
(require
 cur/stdlib/prop
 (submod cur/stdlib/prop tauto)
 cur/stdlib/sugar
 cur/stdlib/bool
 cur/stdlib/nat
 cur/stdlib/equality
 rackunit/turnstile)

(check-type False : Type)
(check-type True : Type)
(check-type I : True)
(check-type (And True False) : Type)

(check-type (conj True True I I) : (And True True))

(check-type (left True False I) : (Or True False))
(check-type (left True True I) : (Or True True))
(typecheck-fail (left False True I) #:with-msg "expected.*False.*given.*True")
(check-type (right False True I) : (Or False True))
(check-type (right True True I) : (Or True True))
(typecheck-fail (right True False I) #:with-msg "expected.*False.*given.*True")

(check-type (tauto True) : True)
(check-type (tauto (And True True)) : (And True True))
(typecheck-fail (tauto (And False True)) #:with-msg "no proof")
(typecheck-fail (tauto (And True False)) #:with-msg "no proof")
(typecheck-fail (tauto (And False False)) #:with-msg "no proof")

(check-type (tauto (Or True False)) : (Or True False))
(check-type (tauto (Or False True)) : (Or False True))
(typecheck-fail (tauto (Or False False)) #:with-msg "no proof")

(check-type True : Type -> True)
(check-type pf:anything-implies-true : thm:anything-implies-true)
(check-type pf:and-is-symmetric : thm:and-is-symmetric)
(check-type pf:proj1 : thm:proj1)
(check-type pf:proj2 : thm:proj2)

;; test infer
(check-type (conj (conj I I) I)
            : (And (And True True) True)
            -> (conj (And True True) True (conj True True I I) I))

;; A or A

(define thm:A-or-A
  (Π (A : Type) (o : (Or A A)) A))

(define proof:A-or-A
  (lambda (A : Type) (c : (Or A A))
          (new-elim c (lambda (c : (Or A A)) A)
                (lambda (a : A) a)
                 (lambda (b : A) b))))

(check-type proof:A-or-A : thm:A-or-A)

;; False implies 0=1
(check-type
 (λ [x : False] (elim-False x (λ y (== Nat 0 1))))
 : (-> False (== Nat 0 1)))

;; false implies anything
(define falsey
  (λ [X : Type] [x : False] (elim-False x (λ y X))))
(check-type falsey : (Π [X : Type] (-> False X)))

;; falsey with general elim
(check-type
 (λ [X : Type] [x : False] (new-elim x (λ y X)))
 : (Π [X : Type] (-> False X)))

(check-type
 ((λ [X : Type] [x : False] (elim-False x (λ y X)))
  (== Nat 0 1))
 : (-> False (== Nat 0 1)))


(check-type
 (λ [n : Nat]
   (elim-Nat n (λ m Type) True (λ x y False)))
 : (-> Nat Type))

(define 0neq1
 (λ [h1 : (== Nat 0 1)]
   (elim-==
    h1
    (λ [b : Nat] ; isZero?
      (λ H
        (elim-Nat b (λ n Type) True (λ x y False))))
    I))) ; proof of (isZero 0)
(check-type 0neq1 : (-> (== Nat 0 1) False))

(check-type
 (λ [H : (== Nat 0 1)]
   (falsey (== Nat 2 3) (0neq1 H)))
 : (-> (== Nat 0 1) (== Nat 2 3)))

;; successors-equal-implies-equal
(check-type
 (λ [n : Nat] [m : Nat]
    (λ [H : (== Nat (s n) (s m))]
      (f-equal
       Nat Nat
       (λ [n : Nat]
         (elim-Nat
          n
          (λ n Nat)
          n
          (λ n-1 IH n-1)))
       (s n) (s m)
       H)))
 : (Π [n : Nat] [m : Nat]
      (-> (== Nat (s n) (s m)) (== Nat n m))))

(check-type iff-sym : (∀ [P Q : Prop] (-> (iff P Q) (iff Q P))))

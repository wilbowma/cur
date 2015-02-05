#lang s-exp "../redex-curnel.rkt"
(require "sugar.rkt")
;; TODO: Handle multiple provide forms properly
;; TODO: Handle (all-defined-out) properly
(provide
  true T
  thm:anything-implies-true
  false
  not
  and
  conj
  thm:and-is-symmetric proof:and-is-symmetric
  thm:proj1 proof:proj1
  thm:proj2 proof:proj2
  == refl)

(data true : Type (T : true))

(define-theorem thm:anything-implies-true (forall (P : Type) true))

(qed (run thm:anything-implies-true) (lambda (P : Type) T))

(data false : Type)

(define-type (not (A : Type)) (-> A false))

(data and : (forall* (A : Type) (B : Type) Type)
  (conj : (forall* (A : Type) (B : Type)
            (x : A) (y : B) (and A B))))

(define-theorem thm:and-is-symmetric
  (forall* (P : Type) (Q : Type) (ab : (and P Q)) (and Q P)))

;; TODO: BAH! pattern matching on inductive families is still broken.
(define proof:and-is-symmetric
  (lambda* (P : Type) (Q : Type) (ab : (and P Q))
    (case* ab
      ((conj (P : Type) (Q : Type) (x : P) (y : Q)) (conj Q P y x)))))

#;(qed thm:and-is-symmetric proof:and-is-symmetric)

(define-theorem thm:proj1
  (forall* (A : Type) (B : Type) (c : (and A B)) A))

(define proof:proj1
  (lambda* (A : Type) (B : Type) (c : (and A B))
    (case c (conj (lambda* (A : Type) (B : Type) (a : A) (b : B) a)))))

(qed thm:proj1 proof:proj1)

(define-theorem thm:proj2
  (forall* (A : Type) (B : Type) (c : (and A B)) B))

(define proof:proj2
  (lambda* (A : Type) (B : Type) (c : (and A B))
    (case c (conj (lambda* (A : Type) (B : Type) (a : A) (b : B) b)))))

(qed thm:proj2 proof:proj2)

(data == : (forall* (A : Type) (x : A) (-> A Type))
  (refl : (forall* (A : Type) (x : A) (== A x x))))

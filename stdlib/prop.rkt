#lang s-exp "../cur.rkt"
(require "sugar.rkt")
;; TODO: Handle multiple provide forms properly
;; TODO: Handle (all-defined-out) properly
(provide
  True T
  thm:anything-implies-true
  False
  Not
  And
  conj
  thm:and-is-symmetric proof:and-is-symmetric
  thm:proj1 proof:proj1
  thm:proj2 proof:proj2
  == refl)

(data True : Type (T : True))

(define-theorem thm:anything-implies-true (forall (P : Type) True))

(qed thm:anything-implies-true (lambda (P : Type) T))

(data False : Type)

(define-type (Not (A : Type)) (-> A False))

(data And : (forall* (A : Type) (B : Type) Type)
  (conj : (forall* (A : Type) (B : Type)
            (x : A) (y : B) (And A B))))

(define-theorem thm:and-is-symmetric
  (forall* (P : Type) (Q : Type) (ab : (And P Q)) (And Q P)))

(define proof:and-is-symmetric
  (lambda* (P : Type) (Q : Type) (ab : (And P Q))
    (case* And Type ab (P Q)
      (lambda* (P : Type) (Q : Type) (ab : (And P Q))
         (And Q P))
      ((conj (P : Type) (Q : Type) (x : P) (y : Q)) IH: () (conj Q P y x)))))

(qed thm:and-is-symmetric proof:and-is-symmetric)

(define-theorem thm:proj1
  (forall* (A : Type) (B : Type) (c : (And A B)) A))

(define proof:proj1
  (lambda* (A : Type) (B : Type) (c : (And A B))
    (case* And Type c (A B)
      (lambda* (A : Type) (B : Type) (c : (And A B)) A)
      ((conj (A : Type) (B : Type) (a : A) (b : B)) IH: () a))))

(qed thm:proj1 proof:proj1)

(define-theorem thm:proj2
  (forall* (A : Type) (B : Type) (c : (And A B)) B))

(define proof:proj2
  (lambda* (A : Type) (B : Type) (c : (And A B))
    (case* And Type c (A B)
      (lambda* (A : Type) (B : Type) (c : (And A B)) B)
      ((conj (A : Type) (B : Type) (a : A) (b : B)) IH: () b))))

(qed thm:proj2 proof:proj2)

#| TODO: Disabled until #22 fixed
(data Or : (forall* (A : Type) (B : Type) Type)
  (left : (forall* (A : Type) (B : Type) (a : A) (Or A B)))
  (right : (forall* (A : Type) (B : Type) (b : B) (Or A B))))

(define-theorem thm:A-or-A
  (forall* (A : Type) (o : (Or A A)) A))

(define proof:A-or-A
  (lambda* (A : Type) (c : (Or A A))
    ;; TODO: What should the motive be?
    (elim Or Type (lambda* (A : Type) (B : Type) (c : (Or A B)) A)
      (lambda* (A : Type) (B : Type) (a : A) a)
      ;; TODO: How do we know B is A?
      (lambda* (A : Type) (B : Type) (b : B) b)
      A A c)))

(qed thm:A-or-A proof:A-or-A)
|#

(data == : (forall* (A : Type) (x : A) (-> A Type))
  (refl : (forall* (A : Type) (x : A) (== A x x))))

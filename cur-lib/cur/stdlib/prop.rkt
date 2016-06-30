#lang s-exp "../main.rkt"
(require "sugar.rkt")
;; TODO: Handle multiple provide forms properly
;; TODO: Handle (all-defined-out) properly
(provide
  True T
  thm:anything-implies-true
  pf:anything-implies-true
  False
  Not
  And
  conj conj/i
  thm:and-is-symmetric pf:and-is-symmetric
  thm:proj1 pf:proj1
  thm:proj2 pf:proj2
  == refl)

(data True : 0 Type (T : True))

(define thm:anything-implies-true (forall (P : Type) True))
(define pf:anything-implies-true (lambda (P : Type) T))

(data False : 0 Type)

(define-type (Not (A : Type)) (-> A False))

(data And : 2 (forall (A : Type) (B : Type) Type)
  (conj : (forall (A : Type) (B : Type)
            (x : A) (y : B) (And A B))))

(define-syntax (conj/i syn)
  (syntax-case syn ()
    [(_ a b)
     (let ([a-type (cur-type-infer #'a)]
           [b-type (cur-type-infer #'b)])
       #`(conj #,a-type #,b-type a b))]))

(define thm:and-is-symmetric
  (forall (P : Type) (Q : Type) (ab : (And P Q)) (And Q P)))

(define pf:and-is-symmetric
  (lambda (P : Type) (Q : Type) (ab : (And P Q))
          (match ab
            [(conj (x : P) (y : Q))
             (conj/i y x)])))

(define thm:proj1
  (forall (A : Type) (B : Type) (c : (And A B)) A))

(define pf:proj1
  (lambda (A : Type) (B : Type) (c : (And A B))
          (match c
            [(conj (a : A) (b : B)) a])))

(define thm:proj2
  (forall (A : Type) (B : Type) (c : (And A B)) B))

(define pf:proj2
  (lambda (A : Type) (B : Type) (c : (And A B))
          (match c
            [(conj (a : A) (b : B)) b])))

(data Or : 2 (forall (A : Type) (B : Type) Type)
  (left : (forall (A : Type) (B : Type) (a : A) (Or A B)))
  (right : (forall (A : Type) (B : Type) (b : B) (Or A B))))

(define thm:A-or-A
  (forall (A : Type) (o : (Or A A)) A))

(define proof:A-or-A
  (lambda (A : Type) (c : (Or A A))
    ;; TODO: What should the motive be?
    (elim Or (lambda (c : (Or A A)) A)
          ((lambda (a : A) a)
           (lambda (b : A) b))
          c)))

(:: proof:A-or-A thm:A-or-A)

(data == : 1 (forall (A : Type) (x : A) (-> A Type))
  (refl : (forall (A : Type) (x : A) (== A x x))))

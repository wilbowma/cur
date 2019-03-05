#lang s-exp "../main.rkt"

(provide
 (except-out (all-from-out cur/curnel/turnstile-impl/dep-ind-cur2+bool) conj)
 (rename-out [I T]
             [conj/i conj]
             [or_introL left]
             [or_introR right])
 ;; curnel/turnstile-impl/dep-ind-cur2+bool defines these:
 ;; True T
 ;; False
 ;; Not
 ;; And
 ;; conj
 iff iff-sym
 thm:anything-implies-true
 pf:anything-implies-true
 thm:and-is-symmetric pf:and-is-symmetric
 thm:proj1 pf:proj1
 thm:proj2 pf:proj2)

(require "sugar.rkt"
         cur/curnel/turnstile-impl/dep-ind-cur2+bool)

;; inferring version of conj
(define-implicit conj/i = conj 2)

(define thm:anything-implies-true (Π (P : Type) True))
(define pf:anything-implies-true (λ (P : Type) I))

(define thm:and-is-symmetric
  (Π (P : Type) (Q : Type) (ab : (And P Q)) (And Q P)))

(define pf:and-is-symmetric
  (lambda (P : Type) (Q : Type) (ab : (And P Q))
          (match ab #:return (And Q P)
            [(conj (x : P) (y : Q))
             (conj Q P y x)])))

(define thm:proj1
  (Π (A : Type) (B : Type) (c : (And A B)) A))

(define pf:proj1
  (lambda (A : Type) (B : Type) (c : (And A B))
          (match c #:return A
            [(conj (a : A) (b : B)) a])))

(define thm:proj2
  (Π (A : Type) (B : Type) (c : (And A B)) B))

(define pf:proj2
  (lambda (A : Type) (B : Type) (c : (And A B))
          (match c #:return B
            [(conj (a : A) (b : B)) b])))

(define (iff [A : Prop] [B : Prop])
  (And (-> A B) (-> B A)))

(define iff-sym
  (λ (P : Prop) (Q : Prop) (H : (iff P Q))
     (match H #:as H
            #:in (iff P Q)
            #:return (iff Q P)
      [(conj H1 H2) (conj (-> Q P) (-> P Q) H2 H1)])))

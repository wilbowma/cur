#lang racket/base
(require
 redex/reduction-semantics
 cur/curnel/model/core-api
 rackunit
 racket/function
 (only-in racket/set set=?))
(define-syntax-rule (check-holds (e ...))
  (check-true
   (judgment-holds (e ...))))
(define-syntax-rule (check-not-holds (e ...))
  (check-false
   (judgment-holds (e ...))))
(define-syntax-rule (check-equiv? e1 e2)
  (check (default-equiv) e1 e2))
(define-syntax-rule (check-not-equiv? e1 e2)
  (check (compose not (default-equiv)) e1 e2))

(default-equiv (curry alpha-equivalent? ttL))

(check-redundancy #t)

;; Syntax tests
;; ------------------------------------------------------------------------

(define-term Type (Unv 0))
(check-true (x? (term T)))
(check-true (x? (term A)))
(check-true (x? (term truth)))
(check-true (x? (term z)))
(check-true (x? (term s)))
(check-true (t? (term z)))
(check-true (t? (term s)))
(check-true (x? (term Nat)))
(check-true (t? (term Nat)))
(check-true (t? (term A)))
(check-true (t? (term S)))
(check-true (U? (term (Unv 0))))
(check-true (U? (term Type)))
(check-true (e? (term (λ (x_0 : (Unv 0)) x_0))))
(check-true (t? (term (λ (x_0 : (Unv 0)) x_0))))
(check-true (t? (term (λ (x_0 : (Unv 0)) x_0))))

(define-term ΔT (∅ (True : 0 (Unv 0) (∅ (tt : True)))))
(define-term Δ⊥ (ΔT (False : 0 (Unv 0) ∅)))
(define-term ΔBool (Δ⊥ (Bool : 0 (Unv 0) ((∅ (true : Bool)) (false : Bool)))))
(define-term ΔNat (ΔBool (Nat : 0 (Unv 0) ((∅ (z : Nat)) (s : (Π (x : Nat) Nat))))))
(define-term ΔAnd
  (ΔNat (And : 2 (Π (A : (Unv 0)) (Π (B : (Unv 0)) (Unv 0)))
             (∅ (conj : (Π (A : (Unv 0)) (Π (B : (Unv 0)) (Π (a : A) (Π (b : B) ((And A) B))))))))))
(define-term Δ=
  (ΔAnd (= : 1 (Π (A : (Unv 0)) (Π (a : A) (Π (b : A) (Unv 0))))
           (∅ (refl : (Π (A : (Unv 0)) (Π (a : A) (((= A) a) a))))))))

(check-true (Δ? (term ΔT)))
(check-true (Δ? (term Δ⊥)))
(check-true (Δ? (term ΔBool)))
(check-true (Δ? (term ΔNat)))
(check-true (Δ? (term ΔAnd)))
(check-true (Δ? (term Δ=)))

;; alpha-equivalent And subst tests
(default-language ttL)
(check-equiv?
 (term (substitute (Π (a : A) (Π (b : B) ((And A) B))) A S))
 (term (Π (a : S) (Π (b : B) ((And S) B)))))

;; Misc tests
;; ------------------------------------------------------------------------ 
(check-equal?
 (term (Θ-length hole))
 0)

(check-equal?
 (term (Δ-ref-parameter-count ΔNat Nat))
 0)

;; Telescope tests
;; ------------------------------------------------------------------------
;; Are these telescopes the same when filled with alpha-equivalent, And equivalently renamed, termed
(define (telescope-equiv x y)
  (alpha-equivalent? ttL (term (in-hole ,x (Unv 0))) (term (in-hole ,y (Unv 0)))))
(define-syntax-rule (check-telescope-equiv? e1 e2)
  (check telescope-equiv e1 e2))
(define-syntax-rule (check-telescope-not-equiv? e1 e2)
  (check (compose not telescope-equiv) e1 e2))

(check-true (x? (term false)))
(check-true (Ξ? (term hole)))
(check-true (t? (term (λ (y : false) (Π (x : Type) x)))))

;; Tests for inductive elimiNation
;; ------------------------------------------------------------------------
;; TODO: Insufficient tests, no tests of inductives with parameters, indices, or complex induction.
(check-true
 (redex-match? tt-ctxtL (in-hole Θ_i (hole (in-hole Θ_r z))) (term (hole z))))
(check-telescope-equiv?
 (term (Δ-inductive-elim ΔNat Nat
                         (elim Nat (λ (x : Nat) Nat)
                               ((s z) (λ (x : Nat) (λ (ih-x : Nat) (s (s x)))))
                               hole)
                         (hole z)))
 (term (hole (elim Nat (λ (x : Nat) Nat)
                   ((s z)
                    (λ (x : Nat) (λ (ih-x : Nat) (s (s x)))))
                   z))))
(check-telescope-equiv?
 (term (Δ-inductive-elim ΔNat Nat
                         (elim Nat (λ (x : Nat) Nat)
                               ((s z) (λ (x : Nat) (λ (ih-x : Nat) (s (s x)))))
                               hole)
                         (hole (s z))))
 (term (hole (elim Nat (λ (x : Nat) Nat)
                   ((s z) (λ (x : Nat) (λ (ih-x : Nat) (s (s x)))))
                   (s z)))))
(check-telescope-equiv?
 (term (Δ-inductive-elim ΔNat Nat
                         (elim Nat (λ (x : Nat) Nat)
                               ((s z) (λ (x : Nat) (λ (ih-x : Nat) (s (s x)))))
                               hole)
                         hole))
 (term hole))

;; Tests for dynamic semantics
;; ------------------------------------------------------------------------

(check-true (v? (term (λ (x_0 : (Unv 0)) x_0))))
(check-true (v? (term (refl Nat))))
(check-true (v? (term ((refl Nat) z))))
(check-true (v? (term z)))
(check-true (v? (term (s z))))

;; TODO: Move equivalence up here, And use in these tests.
(check-equiv? (term (reduce ∅ (Unv 0))) (term (Unv 0)))
(check-equiv? (term (reduce ∅ ((λ (x : t) x) (Unv 0)))) (term (Unv 0)))
(check-not-equiv? (term (reduce ∅ ((Π (x : t) x) (Unv 0)))) (term (Unv 0)))
(check-not-equiv? (term (reduce ∅ (Π (x : t) ((Π (x_0 : t) x_0) (Unv 0)))))
                  (term (Π (x : t) (Unv 0))))
(check-not-equiv? (term (reduce ∅ (Π (x : t) ((Π (x_0 : t) (x_0 x)) x))))
                  (term (Π (x : t) (x x))))

(check-equiv? (term (reduce ΔNat (elim Nat (λ (x : Nat) Nat)
                                     ((s z)
                                      (λ (x : Nat) (λ (ih-x : Nat) (s (s x)))))
                                     z)))
              (term (s z)))
(check-equiv? (term (reduce ΔNat (elim Nat (λ (x : Nat) Nat)
                                     ((s z)
                                      (λ (x : Nat) (λ (ih-x : Nat) (s (s x)))))
                                     (s z))))
              (term (s (s z))))
(check-equiv? (term (reduce ΔNat (elim Nat (λ (x : Nat) Nat)
                                     ((s z)
                                      (λ (x : Nat) (λ (ih-x : Nat) (s (s x)))))
                                (s (s (s z))))))
              (term (s (s (s (s z))))))

(check-equiv?
 (term (reduce ΔNat
               (elim Nat (λ (x : Nat) Nat)
                     ((s (s z))
                      (λ (x : Nat) (λ (ih-x : Nat) (s ih-x))))
                     (s (s z)))))
 (term (s (s (s (s z))))))
(check-equiv?
 (term (step ΔNat
             (elim Nat (λ (x : Nat) Nat)
                     ((s (s z))
                      (λ (x : Nat) (λ (ih-x : Nat) (s ih-x))))
                     (s (s z)))))
 (term
  (((λ (x : Nat) (λ (ih-x : Nat) (s ih-x)))
    (s z))
   (elim Nat (λ (x : Nat) Nat)
         ((s (s z))
          (λ (x : Nat) (λ (ih-x : Nat) (s ih-x))))
         (s z)))))
(check-equiv?
 (term (step ΔNat (step ΔNat
                      (((λ (x : Nat) (λ (ih-x : Nat) (s ih-x)))
                        (s z))
                       (elim Nat (λ (x : Nat) Nat)
                             ((s (s z))
                              (λ (x : Nat) (λ (ih-x : Nat) (s ih-x))))
                             (s z))))))
 (term
  ((λ (ih-x1 : Nat) (s ih-x1))
   (((λ (x : Nat) (λ (ih-x : Nat) (s ih-x)))
     z)
    (elim Nat (λ (x : Nat) Nat)
          ((s (s z))
           (λ (x : Nat) (λ (ih-x : Nat) (s ih-x))))
          z)))))

(define-syntax-rule (check-equivalent e1 e2)
  (check-holds (subtype ∅ ∅ e1 e2)))
(check-equivalent
 (λ (x : Type) x) (λ (y : Type) y))
(check-equivalent
 (Π (x : Type) x) (Π (y : Type) y))

;; Test static semantics
;; ------------------------------------------------------------------------

;; TODO: Rewrite these tests. Not critical, since they are implicitly tested by wf tests
;(check-holds
; (valid-constructor Nat Nat))
;(check-holds
; (valid-constructor Nat (Π (x : (Unv 0)) (Π (y : (Unv 0)) Nat))))
;(check-holds
; (valid-constructor Nat (Π (x : Nat) Nat)))
;;; (Nat -> Nat) -> Nat
;;; Not sure if this is actually supposed to pass
;(check-not-holds
; (valid-constructor Nat (Π (x : (Π (y : Nat) Nat)) Nat)))
;;; ((Unv 0) -> Nat) -> Nat
;(check-holds
; (valid-constructor Nat (Π (x : (Π (y : (Unv 0)) Nat)) Nat)))
;;; (((Nat -> (Unv 0)) -> Nat) -> Nat)
;(check-holds
; (valid-constructor Nat (Π (x : (Π (y : (Π (x : Nat) (Unv 0))) Nat)) Nat)))
;;; Not sure if this is actually supposed to pass
;;; ((Nat -> Nat) -> Nat) -> Nat
;(check-not-holds
; (valid-constructor Nat (Π (x : (Π (y : (Π (x : Nat) Nat)) Nat)) Nat)))

(check-true (judgment-holds (wf ΔT ∅)))
(check-true (judgment-holds (wf Δ⊥ ∅)))
(check-true (judgment-holds (wf ΔNat ∅)))
(check-true (judgment-holds (wf ΔBool ∅)))
(check-true (judgment-holds (wf ΔAnd ∅)))
(check-true (judgment-holds (wf Δ= ∅)))
(check-true (redex-match? tt-redL (in-hole Ξ (Unv 0)) (term (Unv 0))))
(check-true (redex-match? tt-redL (in-hole Ξ (in-hole Φ (in-hole Θ Nat)))
                          (term (Π (x : Nat) Nat))))
(define (bindings-equal? l1 l2)
  (map set=? l1 l2))
(check-pred
 (curry bindings-equal?
        (list (list
               (make-bind 'Ξ (term (Π (x : Nat) hole)))
               (make-bind 'Φ (term hole))
               (make-bind 'Θ (term hole)))
              (list
               (make-bind 'Ξ (term hole))
               (make-bind 'Φ (term (Π (x : Nat) hole)))
               (make-bind 'Θ (term hole)))))
 (map match-bindings (redex-match tt-redL (in-hole Ξ (in-hole Φ (in-hole Θ Nat)))
                                  (term (Π (x : Nat) Nat)))))
(check-pred
 (curry bindings-equal?
        (list
         (list
          (make-bind 'Φ (term (Π (x : Nat) hole)))
          (make-bind 'Θ (term hole)))))
 (map match-bindings (redex-match tt-redL (in-hole hole (in-hole Φ (in-hole Θ Nat)))
                                  (term (Π (x : Nat) Nat)))))

(check-true
 (redex-match? tt-redL
               (in-hole hole (in-hole hole (in-hole hole Nat)))
               (term Nat)))
(check-true
 (redex-match? tt-redL
               (in-hole hole (in-hole (Π (x : Nat) hole) (in-hole hole Nat)))
               (term (Π (x : Nat) Nat))))

(check-holds (type-infer ∅ ∅ (Unv 0) U))
(check-holds (type-infer ∅ (∅ Nat : (Unv 0)) Nat U))
(check-holds (type-infer ∅ (∅ Nat : (Unv 0)) (Π (x : Nat) Nat) U))

(check-holds (type-infer ∅ ∅ (Unv 0) (Unv 1)))
(check-holds (type-infer ∅ (∅ x : (Unv 0)) (Unv 0) (Unv 1)))
(check-holds (type-infer ∅ (∅ x : (Unv 0)) x (Unv 0)))
(check-holds (type-infer ∅ ((∅ x_0 : (Unv 0)) x_1 : (Unv 0))
                           (Π (x_3 : x_0) x_1) (Unv 0)))
(check-holds (type-infer ∅ (∅ x_0 : (Unv 0)) x_0 U_1))
(check-holds (type-infer ∅ ((∅ x_0 : (Unv 0)) x_2 : x_0) (Unv 0) U_2))
(check-holds (unv-pred (Unv 0) (Unv 0) (Unv 0)))
(check-holds (type-infer ∅ (∅ x_0 : (Unv 0)) (Π (x_2 : x_0) (Unv 0)) t))

(check-holds (type-check ∅ ∅ (λ (x : (Unv 0)) x) (Π (x : (Unv 0)) (Unv 0))))
(check-holds (type-check ∅ ∅ (λ (y : (Unv 0)) (λ (x : y) x))
                             (Π (y : (Unv 0)) (Π (x : y) y))))

(check-equal? (list (term (Unv 1)))
              (judgment-holds
               (type-infer ∅ ((∅ x1 : (Unv 0)) x2 : (Unv 0)) (Π (t6 : x1) (Π (t2 : x2) (Unv 0)))
                             U)
               U))
;; ---- Elim
;; TODO: Clean up/Reorganize these tests
(check-holds (type-infer ΔT ∅ True (in-hole Ξ U)))
(check-holds (type-infer ΔT ∅ tt (in-hole Θ_ai True)))
(check-holds (type-infer ΔT ∅ (λ (x : True) (Unv 1))
                         (in-hole Ξ (Π (x : (in-hole Θ True)) U))))

(check-holds
 (check-motive True (Unv 0) (Π (x : True) (Unv 2))))

(check-holds (type-check ΔT ∅ (λ (x : True) (Unv 1)) (Π (x : True) (Unv 2))))

(require (only-in cur/curnel/model/core apply))
(check-equiv?
 (term (apply (λ (x : True) (Unv 1)) T))
 (term ((λ (x : True) (Unv 1)) T)))

(check-holds
 (subtype ΔT ∅ (apply (λ (x : True) (Unv 1)) T) (Unv 1)))

(check-holds (type-infer ΔT
                         ∅
                         (elim True (λ (x : True) (Unv 1))
                               ((Unv 0)) tt)
                         t))

(check-holds (type-check ΔT
                         ∅
                         (elim True (λ (x : True) (Unv 1))
                               ((Unv 0)) tt)
                         (Unv 1)))
(check-not-holds (type-check ΔT
                             ∅
                             (elim True Type (Type) tt)
                             (Unv 1)))
(check-holds
 (type-infer ∅ ∅ (Π (x2 : (Unv 0)) (Unv 0)) U))
(check-holds
 (type-infer ∅ (∅ x1 : (Unv 0)) (λ (x2 : (Unv 0)) (Π (t6 : x1) (Π (t2 : x2) (Unv 0))))
               t))
(check-holds
 (type-infer ΔNat ∅ Nat (in-hole Ξ U)))
(check-holds
 (type-infer ΔNat ∅ z (in-hole Θ_ai Nat)))
(check-holds
 (type-infer ΔNat ∅ (λ (x : Nat) Nat)
             (in-hole Ξ (Π (x : (in-hole Θ Nat)) U))))
(define-syntax-rule (Nat-test syn ...)
  (check-holds (type-check ΔNat syn ...)))
(Nat-test ∅ (Π (x : Nat) Nat) (Unv 0))
(Nat-test ∅ (λ (x : Nat) x) (Π (x : Nat) Nat))
(Nat-test ∅ (elim Nat (λ (x : Nat) Nat)
                  (z (λ (x : Nat) (λ (ih-x : Nat) x)))
                  z)
            Nat)
(Nat-test ∅ Nat (Unv 0))
(Nat-test ∅ z Nat)
(Nat-test ∅ s (Π (x : Nat) Nat))
(Nat-test ∅ (s z) Nat)
(check-holds
 (type-infer ΔNat ∅ (λ (x : Nat)
                    (elim Nat (λ (x : Nat) Nat)
                          (z
                           (λ (x : Nat) (λ (ih-x : Nat) x)))
                          x))
             t))
(Nat-test ∅ (elim Nat (λ (x : Nat) Nat)
                  (z (λ (x : Nat) (λ (ih-x : Nat) x)))
                  z)
            Nat)
(Nat-test ∅ (elim Nat (λ (x : Nat) Nat)
                  ((s z) (λ (x : Nat) (λ (ih-x : Nat) (s (s x)))))
                  z)
            Nat)
(Nat-test ∅ (elim Nat (λ (x : Nat) Nat)
                  ((s z) (λ (x : Nat) (λ (ih-x : Nat) (s (s x)))))
                  z)
            Nat)
(Nat-test (∅ n : Nat)
          (elim Nat (λ (x : Nat) Nat)
                (z (λ (x : Nat) (λ (ih-x : Nat) x)))
                n)
          Nat)
(check-holds
 (type-check ΔNat
             (∅ n2 : Nat)
             (elim Nat (λ (x : Nat) Bool)
                   (true (λ (x : Nat) (λ (ih-x : Bool) false)))
                   n2)
             Bool))
(check-not-holds
 (type-check ΔNat ∅
             (elim Nat Nat ((s z)) z)
             Nat))
(define lam (term (λ (Nat : (Unv 0)) Nat)))
(check-equivalent
 (Π (Nat : (Unv 0)) (Unv 0))
 ,(car (judgment-holds (type-infer ΔNat ∅ ,lam t) t)))
(check-equivalent
 (Π (Nat : (Unv 0)) (Unv 0))
 ,(car (judgment-holds (type-infer ΔNat ∅ ,lam t) t)))
(check-equivalent
 (Π (x : (Π (y : (Unv 0)) y)) Nat)
 ,(car (judgment-holds (type-infer (∅ (Nat : 0 (Unv 0) ∅)) ∅ (λ (x : (Π (y : (Unv 0)) y)) (x Nat))
                                   t) t)))
(check-equivalent
 (Π (y : (Unv 0)) (Unv 0))
 ,(car (judgment-holds (type-infer (∅ (Nat : 0 (Unv 0) ∅)) ∅ (λ (y : (Unv 0)) y) t) t)))
(check-equivalent
 (Unv 0)
 ,(car (judgment-holds (type-infer (∅ (Nat : 0 (Unv 0) ∅)) ∅
                                   ((λ (x : (Π (y : (Unv 0)) (Unv 0))) (x Nat))
                                    (λ (y : (Unv 0)) y))
                                   t) t)))
(check-equal?
 (list (term (Unv 0)) (term (Unv 1)))
 (judgment-holds
  (type-infer ΔAnd ∅ (Π (S : (Unv 0)) (Π (B : (Unv 0)) (Π (a : S) (Π (b : B) ((And S) B)))))
              U) U))
(check-holds
 (type-check ΔAnd (∅ S : (Unv 0)) conj (Π (A : (Unv 0)) (Π (B : (Unv 0)) (Π (a : A) (Π (b : B) ((And A) B)))))))
(check-holds
 (type-check ΔAnd (∅ S : (Unv 0))
             conj (Π (P : (Unv 0)) (Π (Q : (Unv 0)) (Π (x : P) (Π (y : Q) ((And P) Q)))))))
(check-holds
 (type-check ΔAnd (∅ S : (Unv 0)) S (Unv 0)))
(check-holds
 (type-check ΔAnd (∅ S : (Unv 0)) (conj S)
             (Π (B : (Unv 0)) (Π (a : S) (Π (b : B) ((And S) B))))))
(check-holds
 (type-check ΔAnd (∅ S : (Unv 0)) (conj S)
             (Π (B : (Unv 0)) (Π (a : S) (Π (b : B) ((And S) B))))))
(check-holds
 (type-check ΔAnd ∅ (λ (S : (Unv 0)) (conj S))
             (Π (S : (Unv 0)) (Π (B : (Unv 0)) (Π (a : S) (Π (b : B) ((And S) B)))))))
(check-holds
 (type-check ΔAnd ∅
             ((((conj True) True) tt) tt)
             ((And True) True)))
(check-holds
 (type-infer ΔAnd ∅ And (in-hole Ξ U_D)))
(check-holds
 (type-infer ΔAnd ∅
             ((((conj True) True) tt) tt)
             (in-hole Θ And)))
(check-holds
 (type-infer ΔAnd ∅
             (λ (A : Type) (λ (B : Type) (λ (x : ((And A) B)) True)))
             (in-hole Ξ (Π (x : (in-hole Θ_Ξ And)) U_P))))
(check-holds
 (type-check ΔAnd ∅
             (elim And
                   (λ (x : ((And True) True)) True)
                   ((λ (a : True)
                      (λ (b : True) tt)))
                   ((((conj True) True) tt) tt))
             True))
(check-true (Γ? (term (((∅ P : (Unv 0)) Q : (Unv 0)) ab : ((And P) Q)))))
(check-holds
 (type-infer ΔAnd (((∅ P : Type) Q : Type) ab : ((And P) Q))
             ab (in-hole Θ And)))
(check-true
 (redex-match? tt-redL
               (in-hole Ξ (Π (x : (in-hole Θ And)) U))
               (term (Π (A : (Unv 0)) (Π (B : (Unv 0)) (Π (x : ((And A) B)) (Unv 0)))))))
(check-holds
 (type-infer ΔAnd (((∅ P : Type) Q : Type) ab : ((And P) Q))
             (λ (A : Type) (λ (B : Type) (λ (x : ((And A) B))
                                           ((And B) A))))
             (in-hole Ξ (Π (x : (in-hole Θ And)) U))))
(check-holds
 (subtype ΔAnd ∅
             (Π (A : (Unv 0)) (Π (B : (Unv 0)) (Π (x : ((And A) B)) (Unv 0))))
             (Π (P : (Unv 0)) (Π (Q : (Unv 0)) (Π (x : ((And P) Q)) (Unv 0))))))
(check-holds
 (type-infer ΔAnd ∅
             (λ (A : Type) (λ (B : Type) (λ (x : ((And A) B))
                                           ((And B) A))))
             (in-hole Ξ (Π (x : (in-hole Θ_Ξ And)) U_P))))
(check-holds
 (type-check ΔAnd
             (((∅ P : (Unv 0)) Q : (Unv 0)) ab : ((And P) Q))
             (elim And
                   (λ (x : ((And P) Q)) ((And Q) P))
                   ((λ (a : P)
                      (λ (b : Q) ((((conj Q) P) b) a))))
                   ab)
             ((And Q) P)))
(check-holds
 (type-check ΔAnd ∅
             (λ (A : Type) (λ (B : Type) (λ (x : ((And A) B)) ((And B) A))))
             (Π (A : (Unv 0)) (Π (B : (Unv 0)) (Π (x : ((And A) B)) (Unv 0))))))
(check-holds
 (type-infer ΔAnd
             ((∅ A : Type) B : Type)
             (conj B)
             t))
(check-holds
 (type-check ΔAnd ∅
             (elim And
                   (λ (x : ((And True) True))
                     ((And True) True))
                 ((λ (a : True)
                    (λ (b : True) ((((conj True) True) b) a))))
              ((((conj True) True) tt) tt))
             ((And True) True)))

;; Nat-equal? tests
(define z?
  (term (λ (n : Nat)
          (elim Nat (λ (x : Nat) Bool)
              (true (λ (x : Nat) (λ (x_ih : Bool) false)))
              n))))
(check-holds
 (type-check ΔNat ∅ ,z? (Π (x : Nat) Bool)))
(check-equal?
 (term (reduce ΔNat (,z? z)))
 (term true))
(check-equal?
 (term (reduce ΔNat (,z? (s z))))
 (term false))
(define ih-equal?
  (term (λ (ih : Nat)
          (elim Nat (λ (x : Nat) Bool)
              (false
               (λ (x : Nat) (λ (y : Bool) (x_ih x))))
              ih))))
(check-holds
 (type-check ΔNat (∅ x_ih : (Π (x : Nat) Bool))
             ,ih-equal?
             (Π (x : Nat) Bool)))
(check-holds
 (type-infer ΔNat ∅ Nat (Unv 0)))
(check-holds
 (type-infer ΔNat ∅ Bool (Unv 0)))
(check-holds
 (type-infer ΔNat ∅ (λ (x : Nat) (Π (x : Nat) Bool)) (Π (x : Nat) (Unv 0))))
(define Nat-equal?
  (term (λ (n : Nat)
          (elim Nat (λ (x : Nat) (Π (x : Nat) Bool))
              (,z?
              (λ (x : Nat) (λ (x_ih : (Π (x : Nat) Bool))
                             ,ih-equal?)))
              n))))
(check-holds
 (type-check ΔNat (∅ Nat-equal? : (Π (x-D«4158» : Nat) ((λ (x«4159» : Nat) (Π (x«4160» : Nat) Bool)) x-D«4158»)))
             ((Nat-equal? z) z)
             Bool))
(check-holds
 (type-check ΔNat ∅
             ,Nat-equal?
             (Π (x : Nat) (Π (y : Nat) Bool))))
(check-equal?
 (term (reduce ΔNat ((,Nat-equal? z) (s z))))
 (term false))
(check-equal?
 (term (reduce ΔNat ((,Nat-equal? (s z)) z)))
 (term false))

;; = tests
(define-term refl-elim
  (elim = (λ (x1 : Bool) (λ (y1 : Bool) (λ (p2 : (((= Bool) x1) y1)) Nat)))
        ((λ (x1 : Bool) z))
        ((refl Bool) true)))
(check-holds
 (type-check Δ= ∅ refl-elim Nat))
(check-true
 (redex-match?
  tt-redL
  (in-hole (Θ_p (in-hole Θ_i x_ci)) Θ_m)
  (term (((((hole
             (λ (A1 : (Unv 0)) (λ (x1 : A1) z))) Bool) true) true) ((refl Bool) true)))))
(check-equal?
 (term (reduce Δ= refl-elim))
 (term z))

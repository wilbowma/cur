#lang s-exp "../main.rkt"

(provide
 (except-out (all-from-out cur/curnel/turnstile-impl/dep-ind-cur2+bool) conj)
 (rename-out [I T]
             [conj/i conj]
             [or_introL left]
             [or_introR right])
  ;; True T
  ;; False
  ;; Not
  ;; And
  ;; conj
  thm:anything-implies-true
  pf:anything-implies-true
  thm:and-is-symmetric pf:and-is-symmetric
  thm:proj1 pf:proj1
  thm:proj2 pf:proj2
  )

(require "sugar.rkt"
         cur/curnel/turnstile-impl/dep-ind-cur2+bool)

;; (data True : 0 Type (T : True))

(define thm:anything-implies-true (Π (P : Type) True))
(define pf:anything-implies-true (λ (P : Type) I))

;; (data False : 0 Type)

;; (define-type (Not (A : Type)) (-> A False))

;; (data And : 2 (forall (A : Type) (B : Type) Type)
;;   (conj : (forall (A : Type) (B : Type)
;;             (x : A) (y : B) (And A B))))

;; inferring version of conj
; Π  λ ≻ ⊢ ≫ → ∧ (bidir ⇒ ⇐) τ⊑ ⇑
(define-typed-syntax conj/i
  [(_ A B a b) ≫ --- [≻ (conj A B a b)]]
  [(_ a b) ≫
   [⊢ a ≫ a- ⇒ A]
   [⊢ b ≫ b- ⇒ B]
   ---------------
   [≻ (conj A B a- b-)]])
   
   
#;(define-syntax (conj/i syn)
  (syntax-case syn ()
    [(_ a b)
     ;; TODO: This should fail if cur-type-infer fails; I think cur-type-infer interface must have changed
     (let ([a-type (cur-type-infer #'a)]
           [b-type (cur-type-infer #'b)])
       #`(conj #,a-type #,b-type a b))]))

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

;; (data Or : 2 (forall (A : Type) (B : Type) Type)
;;   (left : (forall (A : Type) (B : Type) (a : A) (Or A B)))
;;   (right : (forall (A : Type) (B : Type) (b : B) (Or A B))))

;; (define thm:A-or-A
;;   (forall (A : Type) (o : (Or A A)) A))

;; (define proof:A-or-A
;;   (lambda (A : Type) (c : (Or A A))
;;     (elim Or (lambda (c : (Or A A)) A)
;;           ((lambda (a : A) a)
;;            (lambda (b : A) b))
;;           c)))

;; (:: proof:A-or-A thm:A-or-A)

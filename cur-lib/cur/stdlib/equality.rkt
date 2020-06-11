#lang s-exp "../main.rkt"

(provide elim-== PM-sym PM-trans
         ML-= ML-refl elim-ML-=
         f-equal
         (for-syntax ~== ~ML-= (rename-out [~== ~PM-=]))
         (rename-out [==/i PM-=]
                     [==/i ==]
                     [refl/i PM-refl]
                     [refl/i refl]
                     [elim-== elim-PM-=]
                     [PM-sym sym]
                     [PM-trans trans]))

(require "sugar.rkt")

; Paulin-Mohring (coq) equality
(data == : 2 (forall (A : Type) (x : A) (y : A) Type)
  (refl : (forall (A : Type) (x : A) (== A x x))))

(define-implicit refl/i = refl 1)
(define-implicit ==/i = == 1)

;; pm symmetry
(define PM-sym
  (λ [A : Type]
    (λ [x : A] [y : A]
       (λ [e : (== A x y)]
         (new-elim
          e
          (λ [b : A]
            (λ [e2 : (== A x b)]
              (== A b x)))
          (refl A x))))))

;; pm transitivity (using pm-sym)
(define PM-trans
 (λ [A : Type]
   (λ [x : A] [y : A] [z : A]
      (λ [e1 : (== A x y)] [e2 : (== A y z)]
         (new-elim
          (PM-sym A x y e1)
          (λ [b : A]
            (λ [e : (== A y b)]
              (== A b z)))
          e2)))))

;; coq f_equal
(define f-equal
  (λ [A : Type] [B : Type]
     [f : (-> A B)]
     [x : A] [y : A]
     [H : (== A x y)]
     (elim-==
      H
      (λ b h (== B (f x) (f b)))
      (refl B (f x)))))

;; Martin-Lof equality, I think
(data ML-= : 1 (forall (A : Type) (x : A) (y : A) Type)
  (ML-refl : (forall (A : Type) (x : A) (ML-= A x x))))

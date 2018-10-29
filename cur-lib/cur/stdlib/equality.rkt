#lang s-exp "../main.rkt"

(provide == refl elim-== PM-sym PM-trans
         ML-= ML-refl elim-ML-=
         (for-syntax ~== ~ML-= (rename-out [~== ~PM-=]))
         (rename-out [== PM-=]
                     [refl PM-refl]
                     [elim-== elim-PM-=]
                     [PM-sym sym]
                     [PM-trans trans]))

(require "sugar.rkt")

; Paulin-Mohring (coq) equality
(data == : 2 (forall (A : Type) (x : A) (y : A) Type)
  (refl : (forall (A : Type) (x : A) (== A x x))))

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

;; Martin-Lof equality, I think
(data ML-= : 1 (forall (A : Type) (x : A) (y : A) Type)
  (ML-refl : (forall (A : Type) (x : A) (ML-= A x x))))

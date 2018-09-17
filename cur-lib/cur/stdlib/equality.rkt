#lang s-exp "../main.rkt"


(require "sugar.rkt")
(provide PM-= PM-refl PM-sym PM-trans ML-= ML-refl
         elim-ML-= elim-PM-=
         (rename-out
          [PM-= ==]
          [PM-refl refl]
          [PM-sym sym]
          [PM-trans trans]))

; Paulin-Mohring (coq) equality
(define-datatype PM-= [A : (Type 0)] [a : A] : [b : A] -> (Type 0)
  (PM-refl : -> (PM-= A a a)))
#;(data PM-= : 2 (forall (A : Type) (x : A) [y : A] Type)
  (PM-refl : (forall (A : Type) (x : A) (PM-= A x x))))

;; pm symmetry
(define PM-sym
  (λ [A : (Type 0)]
    (λ [x : A] [y : A]
       (λ [e : (PM-= A x y)]
         (elim-PM=
          e
          (λ [b : A]
            (λ [e2 : (PM-= A x b)]
              (PM-= A b x)))
          (PM-refl A x))))))
#;(define PM-sym
  (λ [A : Type]
    (λ [n : A] [m : A]
     (λ [n=m : (PM-= A n m)]
       (new-elim
        n=m
        (λ [m : A]
           (λ [n=m : (PM-= A n m)]
             (PM-= A m n)))
        (PM-refl A n))))))

;; pm transitivity (using pm-sym)
(define PM-trans
 (λ [A : (Type 0)]
   (λ [x : A] [y : A] [z : A]
      (λ [e1 : (PM-= A x y)] [e2 : (PM-= A y z)]
         (elim-PM-=
          (PM-sym A x y e1)
          (λ [b : A]
            (λ [e : (PM-= A y b)]
              (PM-= A b z)))
          e2)))))
#;(: PM-trans (-> (A : Type) (a : A) (b : A) (c : A)
                (PM-= A a b) (PM-= A b c)
                (PM-= A a c)))
#;(define (PM-trans A a b c H1 H2)
  ((new-elim
    H1
    (λ [b : A] [a=b : (PM-= A a b)]
       (-> (PM-= A b c) (PM-= A a c)))
    (λ (H3 : (PM-= A a c)) H3)) H2))

;; Martin-Lof equality, I think
(define-datatype ML-= [A : (Type 0)] : [a : A] [b : A] -> (Type 0)
  (ML-refl : [a : A] -> (ML-= A a a)))

#;(data ML-= : 1 (forall (A : Type) (x : A) (-> A Type))
      (ML-refl : (forall (A : Type) (x : A) (ML-= A x x))))

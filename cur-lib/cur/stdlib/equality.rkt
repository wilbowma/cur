#lang s-exp "../main.rkt"
(require "sugar.rkt")
(provide PM-= PM-refl PM-sym PM-trans ML-= ML-refl
         (rename-out
          [PM-= ==]
          [PM-refl refl]
          [PM-sym sym]
          [PM-trans trans]))

; Paulin-Mohring equality
(data PM-= : 2 (forall (A : Type) (x : A) [y : A] Type)
  (PM-refl : (forall (A : Type) (x : A) (PM-= A x x))))

(define PM-sym
  (λ [A : Type]
    (λ [n : A] [m : A]
     (λ [n=m : (PM-= A n m)]
       (new-elim
        n=m
        (λ [m : A]
           (λ [n=m : (PM-= A n m)]
             (PM-= A m n)))
        (PM-refl A n))))))

(: PM-trans (-> (A : Type) (a : A) (b : A) (c : A)
                (PM-= A a b) (PM-= A b c)
                (PM-= A a c)))
(define (PM-trans A a b c H1 H2)
  ((new-elim
    H1
    (λ [b : A] [a=b : (PM-= A a b)]
       (-> (PM-= A b c) (PM-= A a c)))
    (λ (H3 : (PM-= A a c)) H3)) H2))

;; Martin-Lof equality, I think
(data ML-= : 1 (forall (A : Type) (x : A) (-> A Type))
      (ML-refl : (forall (A : Type) (x : A) (ML-= A x x))))

#lang cur
(require cur/stdlib/sugar)

;; Paulin-Mohring equality. A good test of proper parameter/index handling
(data pm= : 2 (Π (A : (Type 0)) (Π (a : A) (Π (b : A) (Type 0))))
      (pm-refl : (Π (A : (Type 0)) (Π (a : A) (pm= A a a)))))

;; pm= symmetric
(::
 (λ [A : (Type 0)]
   (λ [x : A] [y : A]
      (λ [e : (pm= A x y)]
        (new-elim
         e
         (λ [b : A]
           (λ [e2 : (pm= A x b)]
                (pm= A b x)))
         (pm-refl A x)))))
 (Π [A : (Type 0)]
    (Π [x : A] [y : A]
       (→ (pm= A x y) (pm= A y x)))))

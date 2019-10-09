#lang cur
(require cur/stdlib/sugar
         rackunit/turnstile+)

;; Paulin-Mohring equality. A good test of proper parameter/index handling
(data pm= : 2 (Π (A : (Type 0)) (Π (a : A) (Π (b : A) (Type 0))))
      (pm-refl : (Π (A : (Type 0)) (Π (a : A) (pm= A a a)))))

(define pm-sym
  (λ [A : (Type 0)]
    (λ [x : A] [y : A]
       (λ [e : (pm= A x y)]
         (new-elim
          e
          (λ [b : A]
            (λ [e2 : (pm= A x b)]
              (pm= A b x)))
          (pm-refl A x))))))

;; pm= symmetric
(check-type pm-sym : (Π [A : (Type 0)]
                        (Π [x : A] [y : A]
                           (→ (pm= A x y) (pm= A y x)))))

;; pm= transitive (using sym)
(check-type
 (λ [A : (Type 0)]
   (λ [x : A] [y : A] [z : A]
      (λ [e1 : (pm= A x y)] [e2 : (pm= A y z)]
         (new-elim
          (pm-sym A x y e1)
          (λ [b : A]
            (λ [e : (pm= A y b)]
              (pm= A b z)))
          e2))))
 : (Π (A : (Type 0))
      (Π [x : A] [y : A] [z : A]
         (→ (pm= A x y)
            (pm= A y z)
            (pm= A x z)))))

#lang cur
(require
 cur/stdlib/prop
 cur/stdlib/sugar
 cur/stdlib/bool
 cur/stdlib/nat
 "curunit.rkt")

(check-equal? And And)
(check-equal? True True)
(:: pf:anything-implies-true thm:anything-implies-true)
(:: pf:and-is-symmetric thm:and-is-symmetric)
(:: pf:proj1 thm:proj1)
(:: pf:proj2 thm:proj2)
(check-equal?
 (elim == (λ (x : Bool) (y : Bool) (p : (== Bool x y)) Nat)
       ((λ (x : Bool) z))
       (refl Bool true))
 z)

(check-equal?
 (conj/i (conj/i T T) T)
 (conj (And True True) True (conj True True T T) T))

(define (id (A : Type) (x : A)) x)

(check-equal?
 ((id (== True T T))
  (refl True (run (id True T))))
 (refl True T))

(check-equal?
 ((id (== True T T))
  (refl True (id True T)))
 (refl True T))

;; prove some properties of equality
;; - with both built-in and user-defined datatypes

;; == symmetric
(check-type
 (λ [A : (Type 0)]
   (λ [x : A]
     (λ [y : A]
       (λ [e : (== A x y)]
         (new-elim e
                   (λ (a : A) (λ (b : A) (λ (e : (== A a b)) (== A b a))))
                   (λ (c : A) (refl A c)))))))
 : (Π (A : (Type 0))
      (Π (x : A)
         (Π (y : A)
            (-> (== A x y)
                (== A y x))))))

;; == transitive (partial)
(check-type
 (λ [A : (Type 0)]
   (λ [x : A] [y : A] [z : A]
      (λ [e1 : (== A x y)] [e2 : (== A y z)]
         (new-elim
          e1
          (λ [a : A] [b : A]
             (λ [e : (== A a b)]
               (Π [c : A] (→ (== A b c) (== A a c)))))
          (λ [a : A]
            (λ [c : A]
              (λ [e : (== A a c)] e)))))))
 : (Π (A : (Type 0))
      (Π [x : A] [y : A] [z : A]
         (→ (== A x y)
            (== A y z)
            (Π [a : A]
               (→ (== A y a) (== A x a)))))))

;; == transitive
(check-type
 (λ [A : (Type 0)]
   (λ [x : A] [y : A] [z : A]
      (λ [e1 : (== A x y)] [e2 : (== A y z)]
         ((new-elim
           e1
           (λ [a : A] [b : A]
              (λ [e : (== A a b)]
                (Π [c : A] (→ (== A b c) (== A a c)))))
           (λ [a : A]
             (λ [c : A]
               (λ [e : (== A a c)] e))))
          z e2))))
 : (Π (A : (Type 0))
      (Π [x : A] [y : A] [z : A]
         (→ (== A x y)
            (== A y z)
            (== A x z)))))

;; plus 0 (left)
(check-type (λ [x : Nat] (refl Nat x)) : (Π [x : Nat] (== Nat (plus 0 x) x)))

;; plus 0 (right)
(check-type
 (λ [x : Nat]
   (new-elim
    x
    (λ [n : Nat] (== Nat (plus n 0) n))
    (refl Nat 0)
    (λ [x-1 : Nat]
      (λ [ih : (== Nat (plus x-1 0) x-1)]
        (new-elim
         ih
         ;; a=b => a+1=b+1
         (λ [a : Nat] [b : Nat]
            (λ [e : (== Nat a b)]
              (== Nat (s a) (s b))))
         (λ [c : Nat]
           (refl Nat (s c))))))))
 : (Π [x : Nat] (== Nat (plus x 0) x)))

;; new my= equality

(data my= : 1 (Π (A : (Type 0)) (Π (a : A) (Π (b : A) (Type 0))))
      (my-refl : (Π (A : (Type 0)) (Π (a : A) (my= A a a)))))

(check-type (my-refl Nat 1) : (my= Nat 1 1))
(check-type (my-refl Nat 1) : (my= Nat 1 (plus 1 0)))
(check-type (my-refl Nat 1) : (my= Nat (plus 1 0) (plus 1 0)))
(check-type (my-refl Nat 2) : (my= Nat (plus 1 1) (plus 1 (plus 1 0))))

;; my= symmetric
(check-type
 (λ [A : (Type 0)]
   (λ [x : A] [y : A]
       (λ [e : (my= A x y)]
         (new-elim 
          e
          (λ [a : A] [b : A]
             (λ [e : (my= A a b)]
               (my= A b a)))
          (λ [c : A]
            (my-refl A c))))))
 : (Π [A : (Type 0)]
      (Π [x : A] [y : A]
         (→ (my= A x y) (my= A y x)))))

;; = transitive
(check-type
 (λ [A : (Type 0)]
   (λ [x : A] [y : A] [z : A]
      (λ [e1 : (my= A x y)] [e2 : (my= A y z)]
         ((new-elim
           e1
           (λ [a : A] [b : A]
              (λ [e : (my= A a b)]
                (Π [c : A] (→ (my= A b c) (my= A a c)))))
           (λ [a : A]
             (λ [c : A]
               (λ [e : (my= A a c)] e))))
          z e2))))
 : (Π (A : (Type 0))
      (Π [x : A] [y : A] [z : A]
         (→ (my= A x y)
            (my= A y z)
            (my= A x z)))))


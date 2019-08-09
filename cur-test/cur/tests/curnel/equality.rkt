#lang s-exp cur/curnel/cic-saccharata
(require rackunit/turnstile)

;; Testing the identity type.

(define-datatype my= (A : (Type 0)) : (-> [a : A] [b : A] (Type 0))
  (my-refl (a : A) : (my= A a a)))

(define-datatype Nat : Type
  [Z : Nat]
  [S : (→ Nat Nat)])

(define plus
  (λ [n : Nat][m : Nat]
    (elim-Nat n
              (λ [k : Nat] Nat)
              m
              (λ [k : Nat] (λ [IH : Nat] (S IH))))))

(check-type (my-refl Nat Z) : (my= Nat Z Z)) ; 0=0
(check-not-type (my-refl Nat (S Z)) : (my= Nat Z Z)) ; 1 \neq 0
(check-type (my-refl Nat (S Z)) : (my= Nat (S Z) (S Z))) ; 1=1
(check-type (my-refl Nat (S Z)) : (my= Nat (S Z) (plus (S Z) Z))) ; 1=1+0
(check-type (my-refl Nat (S Z)) : (my= Nat (plus (S Z) Z) (plus (S Z) Z))) ; 1+0=1+0
(check-type (my-refl Nat (S Z)) : (my= Nat (plus Z (S Z)) (plus (S Z) Z))) ; 1+0=0+1
(check-type
 (my-refl Nat (S (S Z)))
 : (my= Nat (plus (S Z) (S Z)) (plus (S Z) (plus (S Z) Z)))) ; 1+1=1+1+0

; = id
(check-type
 (λ [A : (Type 0)]
   (λ [x : A] [y : A]
      (λ [e1 : (my= A x y)]
         (elim-my=
          e1
          (λ [a : A] [b : A] ; a = x, b = z
             (λ [e : (my= A a b)]
               (my= A a b)))
          (λ [c : A]
            (my-refl A c))))))
 : (Π [A : (Type 0)]
      (Π [x : A] [y : A]
         (→ (my= A x y)
            (my= A x y)))))

; = id (same as above) but combined λs
(check-type
 (λ [A : (Type 0)] [x : A] [y : A] [e1 : (my= A x y)]
    (elim-my=
     e1
     (λ [a : A] [b : A] [e : (my= A a b)]
        (my= A a b))
     (λ [c : A] (my-refl A c))))
 : (Π [A : (Type 0)] [x : A] [y : A] (→ (my= A x y) (my= A x y))))

;; = symmetric
(check-type
 (λ [B : (Type 0)]
   (λ [x : B] [y : B]
       (λ [e : (my= B x y)]
         (elim-my=
          e
          (λ [a : B] [b : B]
             (λ [e : (my= B a b)]
               (my= B b a)))
            (λ [c : B]
              (my-refl B c))))))
 : (Π [A : (Type 0)]
      (Π [x : A] [y : A]
         (→ (my= A x y) (my= A y x)))))

;; = transitive (partial 1)
(check-type
 (λ [A : (Type 0)]
   (λ [x : A] [y : A] [z : A]
      (λ [e1 : (my= A x y)] [e2 : (my= A y z)]
         (elim-my=
          e1
          (λ [a : A] [b : A] ; a = x, b = z
             (λ [e : (my= A a b)]
               (Π [c : A] (→ (my= A b c) (my= A a c)))))
            (λ [c : A]
              (λ [d : A]
                (λ [e : (my= A c d)] e)))))))
 : (Π [A : (Type 0)]
      (Π [x : A] [y : A] [z : A]
         (→ (my= A x y)
            (my= A y z)
            (Π [c : A] (→ (my= A y c) (my= A x c)))))))

;; = transitive (partial 2)
(check-type
 (λ [A : (Type 0)]
   (λ [x : A] [y : A] [z : A]
      (λ [e1 : (my= A x y)] [e2 : (my= A y z)]
         ((elim-my= ;; TODO: this must be separate app?
           e1
           (λ [a : A] [b : A] ; a = x, b = z
             (λ [e : (my= A a b)]
               (Π [c : A] (→ (my= A b c) (my= A a c)))))
           (λ [c : A]
             (λ [d : A]
                   (λ [e : (my= A c d)] e))))
          z))))
 : (Π [A : (Type 0)]
      (Π [x : A] [y : A] [z : A]
         (→ (my= A x y)
            (my= A y z)
            (→ (my= A y z) (my= A x z))))))

;; = transitive
(check-type
 (λ [A : (Type 0)]
   (λ [x : A] [y : A] [z : A]
      (λ [e1 : (my= A x y)] [e2 : (my= A y z)]
        ((elim-my=
           e1
           (λ [a : A] [b : A] ; a = x, b = z
             (λ [e : (my= A a b)]
               (Π [c : A] (→ (my= A b c) (my= A a c)))))
           (λ [c : A]
             (λ [d : A]
               (λ [e : (my= A c d)] e))))
          z e2))))
 : (Π [A : (Type 0)]
      (Π [x : A] [y : A] [z : A]
         (→ (my= A x y)
            (my= A y z)
            (my= A x z)))))


;; Paulin-Mohring (ie, coq-like) equality (2 params, 1 index)

(define-datatype pm= [A : (Type 0)] [a : A] : (-> [b : A] (Type 0))
  (pm-refl : (pm= A a a))) ; constructor consumes params but 0 args

(check-type (pm-refl Nat Z) : (pm= Nat Z Z))
(check-type (pm-refl Nat (S Z)) : (pm= Nat (S Z) (S Z)))
(check-type (λ [A : Type] (λ [x : A][y : A] (pm-refl A x)))
            : (Π [A : Type] (Π [x : A][y : A] (pm= A x x))))
;; same as above but less parens and λs
(check-type (λ [A : Type] [x : A] (pm-refl A x))
            : (Π [A : Type] [x : A] (pm= A x x)))
(check-type (λ [A : Type] (λ [x : A] [y : A] (pm-refl A y)))
            : (Π [A : Type] (Π [x : A][y : A] (pm= A y y))))

(check-type
 (elim-pm=
  (pm-refl Nat Z)
  (λ [b : Nat]
    (λ [e : (pm= Nat Z b)]
      (pm= Nat Z b)))
  (pm-refl Nat Z))
 : (pm= Nat Z Z))

; pm= id
(check-type
 (λ [A : (Type 0)]
   (λ [x : A] [y : A]
      (λ [e1 : (pm= A x y)]
         (elim-pm=
          e1
          (λ [b : A] ; a = x, b = z
             (λ [e : (pm= A x b)]
               (pm= A x b)))
          (pm-refl A x)))))
 : (Π [A : (Type 0)]
      (Π [x : A] [y : A]
         (→ (pm= A x y)
            (pm= A x y)))))

(define pm-sym
  (λ [A : (Type 0)]
    (λ [x : A] [y : A]
       (λ [e : (pm= A x y)]
         (elim-pm=
          e
          (λ [b : A]
            (λ [e2 : (pm= A x b)]
              (pm= A b x)))
          (pm-refl A x))))))

;; pm= symmetric
(check-type
 pm-sym
  : (Π [A : (Type 0)]
       (Π [x : A] [y : A]
          (→ (pm= A x y) (pm= A y x)))))

;; pm= transitive (using sym)
(check-type
 (λ [A : (Type 0)]
   (λ [x : A] [y : A] [z : A]
      (λ [e1 : (pm= A x y)] [e2 : (pm= A y z)]
         (elim-pm=
          (pm-sym A x y e1)
          (λ [b : A]
            (λ [e : (pm= A y b)]
              (pm= A b z)))
          e2))))
 :
 (Π [A : (Type 0)]
    (Π [x : A] [y : A] [z : A]
       (→ (pm= A x y)
          (pm= A y z)
          (pm= A x z)))))

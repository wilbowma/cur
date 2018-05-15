#lang cur
(require cur/stdlib/prop
         cur/stdlib/sugar
         cur/stdlib/nat
         cur/ntac/base
         cur/ntac/standard
         cur/ntac/prop)
 


;; raw term and type for plus-id-theorem below
;; rewriteR (->)
(::
 (λ (n : Nat) (m : Nat)
    (λ (H : (== Nat n m))
      (new-elim
       H
       (λ (n : Nat)
         (λ (m : Nat)
           (λ [p : (== Nat n m)]
             (== Nat (plus n n) (plus m m)))))
       ;; somehow, z as variable doesnt work here
       (λ (m : Nat)
         (refl Nat (plus m m))))))
 (forall [n : Nat] [m : Nat]
         (-> (== Nat n m)
             (== Nat (plus n n) (plus m m)))))

;; unique var names
(::
 (λ (n : Nat) (m : Nat)
    (λ (pf : (== Nat n m))
      (new-elim
       pf
       (λ (n1 : Nat)
         (λ (m1 : Nat)
           (λ [p1 : (== Nat n1 m1)]
             (== Nat (plus n1 n1) (plus m1 m1)))))
       ;; somehow, z as variable doesnt work here
       (λ (x : Nat)
         (refl Nat (plus x x))))))
 (forall [n : Nat] [m : Nat]
         (-> (== Nat n m)
             (== Nat (plus n n) (plus m m)))))

(define-theorem plus-id-example
  (forall [n : Nat] [m : Nat]
     (-> (== Nat n m)
         (== Nat (plus n n) (plus m m))))
  by-intro
  by-intro
  (by-intro H)
  display-focus
  (by-rewrite H)
  display-focus
  reflexivity)

;; raw term and type for plus-id-theorem below
;; testing, rewriteL (<-)
(::
 (λ (n : Nat) (m : Nat)
    (λ (H : (== Nat n m))
      (new-elim
       H
       (λ (n : Nat)
         (λ (m : Nat)
           (λ [p : (== Nat n m)]
             (== Nat (plus n n) (plus m m)))))
       ;; somehow, z as variable doesnt work here
       (λ (n : Nat)
         (refl Nat (plus n n))))))
 (forall [n : Nat] [m : Nat]
         (-> (== Nat n m)
             (== Nat (plus n n) (plus m m)))))
(define-theorem plus-id-exampleL
  (forall [n : Nat] [m : Nat]
     (-> (== Nat n m)
         (== Nat (plus n n) (plus m m))))
  by-intro
  by-intro
  (by-intro H)
  display-focus
  (by-rewriteL H)
  display-focus
  reflexivity)


;; transivitity example
;; - using pattern of propagating unused vars from here
;; - why is this necessary?
(::
 (λ [A : (Type 0)]
   (λ [x : A] [y : A] [z : A]
      (λ [x=y : (== A x y)] [y=z : (== A y z)]
         ((new-elim
           x=y
           (λ [x1 : A] [y1 : A]
              (λ [x1=y1 : (== A x1 y1)]
                (Π [z1 : A]
                   (-> (== A y1 z1)
                       (== A x1 z1)))))
           (λ [a : A]
             (λ [z2 : A]
               (λ [a=z2 : (== A a z2)]
                 a=z2))))
          z y=z))))
 (Π [A : (Type 0)]
    (Π [x : A] [y : A] [z : A]
       (→ (== A x y)
          (== A y z)
          (== A x z)))))

;; transivitity example, reuse vars
(::
 (λ [A : (Type 0)]
   (λ [x : A] [y : A] [z : A]
      (λ [x=y : (== A x y)] [y=z : (== A y z)]
         ((new-elim
           x=y
           (λ [x : A] [y : A]
              (λ [x=y : (== A x y)]
                (Π [z : A]
                   (-> (== A y z)
                       (== A x z)))))
           (λ [a : A]
             (λ [z : A]
               (λ [a=z : (== A a z)]
                 a=z))))
          z y=z))))
 (Π [A : (Type 0)]
    (Π [x : A] [y : A] [z : A]
       (→ (== A x y)
          (== A y z)
          (== A x z)))))

;; plus-id-exercise
;; raw term
(:: 
 (λ [n : Nat] [m : Nat] [o : Nat]
    (λ [n=m : (== Nat n m)]
       [m=o : (== Nat m o)]
       ((new-elim
         n=m
         (λ [n : Nat] [m : Nat]
            (λ [n=m : (== Nat n m)]
              (Π [o : Nat]
                 (-> (== Nat m o)
                     (== Nat (plus n m) (plus m o))))))
         (λ [m : Nat]
           (λ [o : Nat]
             (λ [m=o : (== Nat m o)]
               (new-elim
                m=o
                (λ [m : Nat] [o : Nat]
                   (λ [m=o : (== Nat m o)]
                     (== Nat (plus m m) (plus m o))))
                (λ [m : Nat]
                  (refl Nat (plus m m))))))))
        o m=o)))
 (∀ [n : Nat] [m : Nat] [o : Nat]
    (-> (== Nat n m)
        (== Nat m o)
        (== Nat (plus n m) (plus m o)))))

(define-theorem plus-id-exercise
  (∀ [n : Nat] [m : Nat] [o : Nat]
     (-> (== Nat n m)
         (== Nat m o)
         (== Nat (plus n m) (plus m o))))
  by-intro
  by-intro
  by-intro
  (by-intro H1)
  (by-intro H2)
  display-focus
  (by-rewriteR H1)
  display-focus
  (by-rewriteL H2)
  display-focus
  reflexivity)

(define eq-sym-nat
  (λ [n : Nat] [m : Nat]
     (λ [n=m : (== Nat n m)]
       (new-elim
        n=m
        (λ [n : Nat] [m : Nat]
           (λ [n=m : (== Nat n m)]
             (== Nat m n)))
        (λ [m : Nat]
          (refl Nat m))))))
(:: eq-sym-nat
    (∀ [n : Nat] [m : Nat]
     (-> (== Nat n m)
         (== Nat m n))))

;; test eq-sym-nat
(::
 (λ [n : Nat] [m : Nat]
    (λ [m=sn : (== Nat m (s n))]
      (eq-sym-nat m (s n) m=sn)))
 (Π [n : Nat] [m : Nat]
    (-> (== Nat m (s n))
        (== Nat (s n) m))))


;; raw terms for mult-S-1 theorem below
;; mult-S-1, lift out plus1
(::
 (λ [n : Nat] [m : Nat]
    (λ [m=sn : (== Nat m (s n))]
      (new-elim
       m=sn
       (λ [m : Nat] [sn : Nat]
          (λ [m=sn : (== Nat m sn)]
            (== Nat (mult m sn) (mult m m))))
       (λ [m : Nat]
         (refl Nat (mult m m))))))
 (Π [n : Nat] [m : Nat]
    (-> (== Nat m (s n))
        (== Nat (mult m (plus 1 n)) (mult m m)))))

;; mult-S-1, leave plus-1-n as-is, still broken
#;(::
 (λ [n : Nat] [m : Nat]
    (λ [H : (== Nat (s n) m)]
      (new-elim
       H
       (λ [sn : Nat] [m : Nat]
          (λ [H : (== Nat sn m)]
            (== Nat (mult m (plus 1 n)) (mult m m))))
       (λ [sn : Nat]
           (refl Nat (mult sn sn))))))
 (Π [n : Nat] [m : Nat]
    (-> (== Nat (s n) m)
        (== Nat (mult m (plus 1 n)) (mult m m)))))

;; still not working
;; - rewriteR: how to replace id with non-id? (see coq examples)
;; - rewriteL: normalized (expanded) term doesnt match term in prop (even expanded)
#;(define-theorem mult-S-1
  (∀ [n : Nat] [m : Nat]
     (-> (== Nat m (s n))
         (== Nat (mult m (plus 1 n)) (mult m m))))
  (by-intros n m H)
  display-focus
  ;; simpl
  ;; (by-rewriteL H)
  (by-rewriteR H)
  display-focus
  reflexivity)

;; TODO: how to find (typed-ann s n) in here?
#;(typed-app
 (typed-app
  (typed-app == Nat)
  (typed-elim
   m
   (typed-λ (anon-discriminant615 : Nat) Nat)
   z
   (typed-λ
    (x : Nat)
    (typed-λ
     (ih-x : Nat)
     (typed-app
      s
      (typed-elim
       n
       (typed-λ (anon-discriminant371 : Nat) Nat)
       ih-x
       (typed-λ (x : Nat) (typed-λ (ih-x : Nat) (typed-app s ih-x)))))))))
 (typed-elim
  m
  (typed-λ (anon-discriminant615 : Nat) Nat)
  z
  (typed-λ
   (x : Nat)
   (typed-λ
    (ih-x : Nat)
    (typed-elim
     m
     (typed-λ (anon-discriminant371 : Nat) Nat)
     ih-x
     (typed-λ (x : Nat) (typed-λ (ih-x : Nat)
       (typed-app s ih-x))))))))

#lang cur
(require cur/stdlib/prop
         cur/stdlib/sugar
         cur/stdlib/nat
         cur/ntac/base
         cur/ntac/standard
         cur/ntac/prop)
 


 
(::
(λ (n : Nat) (m : Nat)
  (λ (pf : (== Nat n m))
     (new-elim pf
       (λ (n : Nat)
         (λ (m : Nat)
           (λ [p : (== Nat n m)]
             (== Nat (plus n n) (plus m m)))))
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


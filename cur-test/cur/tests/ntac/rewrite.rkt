#lang cur
(require cur/stdlib/equality
         cur/stdlib/sugar
         cur/stdlib/nat
         cur/ntac/base
         cur/ntac/standard
         cur/ntac/rewrite)

;; these proofs require PM equality instead of ML equality

;; mult-S-1, with ==

(::
 (λ [n : Nat] [m : Nat]
    (λ [H : (== Nat m (s n))]
      (new-elim
       H
       (λ [sn : Nat]
         (λ [H : (== Nat m sn)]
           (== Nat (mult m sn) (mult m m))))
       (refl Nat (mult m m)))))
 (Π [n : Nat] [m : Nat]
    (-> (== Nat m (s n))
        (== Nat (mult m (plus 1 n)) (mult m m)))))

;; ;; mult-S-1 (flipped H) leave plus-1-n as-is
;; ;; - requires ==

(::
 (λ [n : Nat] [m : Nat]
    (λ [H : (== Nat (s n) m)]
      (new-elim
       H
       (λ [m : Nat]
         (λ [H : (== Nat (s n) m)]
           (== Nat (mult m (plus 1 n)) (mult m m))))
       (refl Nat (mult (plus 1 n) (plus 1 n))))))
 (Π [n : Nat] [m : Nat]
    (-> (== Nat (s n) m)
        (== Nat (mult m (plus 1 n)) (mult m m)))))

;; mult-S-1 (not flipped H) leave plus-1-n as-is
;; - requires == and sym

(::
 (λ [n : Nat] [m : Nat]
    (λ [H : (== Nat m (s n))]
      (new-elim
       (sym Nat m (s n) H)
       (λ [m : Nat]
         (λ [H : (== Nat (s n) m)]
           (== Nat (mult m (plus 1 n)) (mult m m))))
       (refl Nat (mult (plus 1 n) (plus 1 n))))))
 (Π [n : Nat] [m : Nat]
    (-> (== Nat m (s n))
        (== Nat (mult m (plus 1 n)) (mult m m)))))

(define-theorem mult-S-1-rev
  (∀ [n : Nat] [m : Nat]
     (-> (== Nat (s n) m)
         (== Nat (mult m (plus 1 n)) (mult m m))))
  (by-intros n m H)
  (by-rewriteL H)
  reflexivity)

(define-theorem mult-S-1
  (∀ [n : Nat] [m : Nat]
     (-> (== Nat m (s n))
         (== Nat (mult m (plus 1 n)) (mult m m))))
  (by-intros n m H)
  (by-rewrite H)
  reflexivity)

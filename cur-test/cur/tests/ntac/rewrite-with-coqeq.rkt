#lang cur
(require cur/stdlib/coqeq
         cur/stdlib/sugar
         cur/stdlib/nat
         cur/ntac/base
         cur/ntac/standard
         cur/ntac/coqrewrite)

;; these proofs require coq= instead of ==

;; mult-S-1, with coq=

(::
 (λ [n : Nat] [m : Nat]
    (λ [H : (coq= Nat m (s n))]
      (new-elim
       H
       (λ [sn : Nat]
         (λ [H : (coq= Nat m sn)]
           (coq= Nat (mult m sn) (mult m m))))
       (coq-refl Nat (mult m m)))))
 (Π [n : Nat] [m : Nat]
    (-> (coq= Nat m (s n))
        (coq= Nat (mult m (plus 1 n)) (mult m m)))))

;; ;; mult-S-1 (flipped H) leave plus-1-n as-is
;; ;; - requires coq=

(::
 (λ [n : Nat] [m : Nat]
    (λ [H : (coq= Nat (s n) m)]
      (new-elim
       H
       (λ [m : Nat]
         (λ [H : (coq= Nat (s n) m)]
           (coq= Nat (mult m (plus 1 n)) (mult m m))))
       (coq-refl Nat (mult (plus 1 n) (plus 1 n))))))
 (Π [n : Nat] [m : Nat]
    (-> (coq= Nat (s n) m)
        (coq= Nat (mult m (plus 1 n)) (mult m m)))))

;; mult-S-1 (not flipped H) leave plus-1-n as-is
;; - requires coq= and coq=-sym-nat

(::
 (λ [n : Nat] [m : Nat]
    (λ [H : (coq= Nat m (s n))]
      (new-elim
       (coq=-sym-nat m (s n) H)
       (λ [m : Nat]
         (λ [H : (coq= Nat (s n) m)]
           (coq= Nat (mult m (plus 1 n)) (mult m m))))
       (coq-refl Nat (mult (plus 1 n) (plus 1 n))))))
 (Π [n : Nat] [m : Nat]
    (-> (coq= Nat m (s n))
        (coq= Nat (mult m (plus 1 n)) (mult m m)))))

(define-theorem mult-S-1-rev
  (∀ [n : Nat] [m : Nat]
     (-> (coq= Nat (s n) m)
         (coq= Nat (mult m (plus 1 n)) (mult m m))))
  (by-intros n m H)
  (by-coq-rewriteL H)
  coq-reflexivity)

(define-theorem mult-S-1
  (∀ [n : Nat] [m : Nat]
     (-> (coq= Nat m (s n))
         (coq= Nat (mult m (plus 1 n)) (mult m m))))
  (by-intros n m H)
  (by-coq-rewrite H)
  coq-reflexivity)

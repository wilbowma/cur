#lang cur

(require
 cur/stdlib/sugar
 cur/stdlib/nat
 cur/stdlib/prop)


(assume f_equal
        (-> (A : Type) (a1 : A) (a2 : A) (B : Type) (f : (-> A B))
            (== A a1 a2)
            (== B (f a1) (f a2))))
(define plus_0_n
  (elim Nat Type
        (lambda (n : Nat) (== Nat n (plus z n)))
        (refl Nat z)
        (lambda (n : Nat) (ih : (== Nat n (plus z n)))
                (f_equal Nat n (plus z n) Nat s ih))))

;; TODO: implicits
;; No way to define axioms in Cur, yet, although it is a simple change.
;; No implicits in Cur, yet
#;(define (plus_0_n  (n : Nat))
  (match n
    ;; TODO: This should work
    #:return (== Nat n (plus z n))
    [z (refl Nat z)]
    [(s (n : Nat))
     (f_equal Nat n (plus z n) Nat s (recur n))]))
(:: plus_0_n (forall (n : Nat) (== Nat n (plus z n))))

#;(define (plus_n_Sm (n : Nat) (m : Nat))
  (elim Nat Type
        (lambda (n : Nat) (== Nat (plus n m) (plus m n)))
        (plus_n_0 m)
        (lambda (y : Nat) (ih : ))
        (elim == Type)))
#;(:: plus_n_Sm (forall (n : Nat) (m : Nat) (== (s (plus n m)) (plus n (s m)))))

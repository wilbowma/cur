#lang cur
(require
 cur/stdlib/nat
 cur/stdlib/sugar
 rackunit/turnstile)

(data Vect : 1 (Π (A : (Type 0)) (Π (n : Nat) (Type 0)))
      [nil : (Π (A : (Type 0)) (Vect A 0))]
      [cns : (Π (A : (Type 0)) (Π (n : Nat) (Π (x : A) (Π (xs : (Vect
A n)) (Vect A (s n))))))])

(check-type
 (λ (A : (Type 0))
   (λ (n : Nat)
     (λ (m : Nat)
       (λ (xs : (Vect A n))
         (λ (ys : (Vect A m))
           (new-elim xs
                     (λ (k : Nat)
                       (λ (vs : (Vect A k))
                         (Vect A (plus k m))))
                     ys
                     (λ (k : Nat)
                       (λ (v : A)
                         (λ (vs : (Vect A k))
                           (λ (IH : (Vect A (plus k m)))
                             ((cns A (plus k m)) v IH)))))))))))

 : (Π [A : Type] [n : Nat] [m : Nat] [xs : (Vect A n)] [ys : (Vect A m)]
      (Vect A (plus n m))))

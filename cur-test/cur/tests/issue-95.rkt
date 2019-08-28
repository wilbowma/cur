#lang cur

(require
 cur/stdlib/nat
 cur/stdlib/sugar
 cur/ntac/base
 cur/ntac/standard)

(define-datatype even : (-> Nat Type)
  [even-O : (even 0)]
  [even-SS : (forall [n : Nat] (-> (even n) (even (s (s n)))))])

(define-theorem even-plus-even-is-even
  (∀ [n : Nat] [m : Nat] (-> (even n) (even m) (even (plus n m))))
  (by-intros n m Hn Hm)

  display-focus

  (by-induction Hn #:as [() (n* IHn)])
  by-assumption
  (by-exact (even-SS (plus n19 m) IH20)))

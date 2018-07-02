#lang cur
(require
 cur/stdlib/sugar
 cur/stdlib/nat
 cur/ntac/base
 cur/ntac/standard)

(ntac Nat
      (by-exact
       ((ntac (forall (A : Type) (a : A) A)
              (by-intros A a)
              (by-assumption))
        Nat
        z)))

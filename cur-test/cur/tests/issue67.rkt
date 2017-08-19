#lang cur

(data Nat : 0 (Type 0)
      (z : Nat)
      (s : (Π (x : Nat) Nat)))

(data Nat2 : 0 (Type 0)
      (zz : Nat2)
      (ss : (Π (x : Nat2) Nat2)))

(begin-for-syntax
  (require chk racket/base)
  (chk
   #:x
   (local-expand #'(new-elim z
                             (λ (x : Nat) Nat)
                             zz
                             (λ (x : Nat2) (λ (ih : Nat2) ih)))
                 'expression
                 '())
   "Expected type Nat, but found type Nat2 while checking method for z"))


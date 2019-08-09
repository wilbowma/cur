#lang s-exp cur/curnel/cic-saccharata
(require rackunit/turnstile)


;; Some tests with non-trivial inductive types

(define-datatype Nat : Type
  [Z : Nat]
  [S : (→ Nat Nat)])

;; (→ Nat) same as Nat
(define-datatype Nat2 : Type
  [Z2 : (→ Nat2)]
  [S2 : (→ Nat2 Nat2)])

;; some basic tests
(check-type Nat : Type)
;; this test wont work if define-datatype uses define-base-type
(check-type (λ [x : Nat] Nat) : (→ Nat Type))

;; some basic tests
(check-type Nat2 : Type)
;; this test wont work if define-datatype uses define-base-type
(check-type (λ [x : Nat2] Nat2) : (→ Nat2 Type))

;; constructors require 3 sets of args:
;; 1) params
;; 2) indices
;; 3) constructor args, split into
;;    - non-recursive
;;    - recursive
(define-datatype List [A : (Type 0)] : (Type 0)
  [null : (List A)]
  [cons : (→ A (List A) (List A))])

(check-type null : (∀ [A : (Type 0)] (List A)))
;; TODO? null \neq null right now
;; bc each reference expands to a different fn
(check-type null : (∀ [A : (Type 0)] (List A)) );-> null)
(check-type cons : (∀ [A : (Type 0)] (→ A (List A) (List A))))
(check-type (null Nat) : (List Nat))
(check-type (null Nat) : (List Nat) -> (null Nat))
; TODO: should these next 2 work?
; Odd behavior due to auto currying macros...
(check-type (null Nat) : (→ (List Nat)))
(check-type ((null Nat)) : (List Nat))
(check-type (cons Nat) : (→ Nat (List Nat) (List Nat)))
(check-type ((cons Nat) (Z) ((null Nat))) : (List Nat))
;; less parens
(check-type (cons Nat Z (null Nat)) : (List Nat))

;; length 0
(check-type
 (elim-List (null Nat)
            (λ [l : (List Nat)] Nat)
            Z
            (λ [x : Nat][xs : (List Nat)]
               (λ [IH : Nat]
                 (S IH))))
 : Nat
 -> Z)

;; length 1
(check-type
 (elim-List (cons Nat Z (null Nat))
            (λ [l : (List Nat)] Nat)
            Z
            (λ [x : Nat][xs : (List Nat)]
                (λ [IH : Nat]
                  (S IH))))
 : Nat
 -> (S Z))

;; length 2
(check-type
 (elim-List ((cons Nat) (S (Z)) ((cons Nat) (Z) ((null Nat))))
            (λ [l : (List Nat)] Nat)
            Z
            (λ [x : Nat][xs : (List Nat)]
                (λ [IH : Nat]
                  (S IH))))
 : Nat
 -> (S (S (Z))))

(define len/Nat
  (λ [lst : (List Nat)]
    (elim-List lst
               (λ [l : (List Nat)] Nat)
               Z
               (λ [x : Nat][xs : (List Nat)]
                   (λ [IH : Nat]
                     (S IH))))))

(check-type (len/Nat ((null Nat))) : Nat -> (Z))
(check-type (len/Nat ((cons Nat) (Z) ((null Nat)))) : Nat -> (S (Z)))
;; less parens
(check-type (len/Nat (null Nat)) : Nat -> (Z))
(check-type (len/Nat (cons Nat Z (null Nat))) : Nat -> (S (Z)))

(define len
  (λ [A : Type]
    (λ [lst : (List A)]
      (elim-List lst
                 (λ [l : (List A)] Nat)
                 Z
                 (λ [x : A][xs : (List A)]
                     (λ [IH : Nat]
                       (S IH)))))))
(check-type (len Nat) : (→ (List Nat) Nat))
(check-type ((len Nat) ((null Nat))) : Nat -> (Z))
(check-type ((len Nat) ((cons Nat) (Z) ((null Nat)))) : Nat -> (S (Z)))

;; test that elim matches on constructor name, and not arity
(define-datatype Test : Type
  [A : (→ Test)]
  [B : (→ Test)])

(check-type
 (elim-Test (A)
            (λ [x : Test] Nat)
            Z
            (S (Z)))
 : Nat -> (Z))

;; should match second branch, but just arity-checking would match 1st
(check-type
 (elim-Test (B)
            (λ [x : Test] Nat)
            Z
            (S (Z)))
 : Nat -> (S (Z)))

;; Vect: indexed "lists" parameterized over length --------------------
(define-datatype Vect [A : (Type 0)] : (-> [i : Nat] (Type 0))
  [nil : (Vect A Z)]
  [cns : (Π [k : Nat] (→ A (Vect A k) (Vect A (S k))))])

(check-type nil : (Π [A : Type] (Vect A Z)))
(check-type cns : (Π [A : Type] [k : Nat] (→ A (Vect A k) (Vect A (S k)))))

(check-type (nil Nat) : (→ (Vect Nat (Z))))
(check-type (nil Nat) : (Vect Nat Z))
(check-type (cns Nat Z) : (→ Nat (Vect Nat Z) (Vect Nat (S Z))))

(check-type ((cns Nat Z) Z (nil Nat)) : (Vect Nat (S Z)))
(check-type (cns Nat Z Z (nil Nat)) : (Vect Nat (S Z)))
(check-type (cns Nat (S Z) Z (cns Nat Z Z (nil Nat)))
            : (Vect Nat (S (S Z))))

(define mtNatVec (nil Nat))
(check-type mtNatVec : (Vect Nat Z))

(check-not-type (nil Nat) : (Vect Nat (S Z))) ; not length 1

;; length

(check-type
 (elim-Vect (nil Nat)
            (λ [k : Nat] [v : (Vect Nat k)] Nat)
            Z
            (λ [k : Nat]
              (λ [x : Nat][xs : (Vect Nat k)]
                (λ [IH : Nat]
                  (S IH)))))
 : Nat -> Z)

(check-type
 (elim-Vect (cns Nat Z Z (nil Nat))
            (λ [k : Nat] [v : (Vect Nat k)] Nat)
            Z
            (λ [k : Nat]
              (λ [x : Nat] [xs : (Vect Nat k)]
                (λ [IH : Nat]
                  (S IH)))))
 : Nat -> (S Z))

(check-type
 (elim-Vect (((cns Nat) (S (Z))) (Z) (((cns Nat) (Z)) (Z) (nil Nat)))
            (λ [k : Nat] [v : (Vect Nat k)] Nat)
            Z
            (λ [k : Nat]
              (λ [x : Nat] [xs : (Vect Nat k)]
                (λ [IH : Nat]
                  (S IH)))))
 : Nat -> (S (S (Z))))

;; same as above but with less parens in target
(check-type
 (elim-Vect (cns Nat (S Z) Z (cns Nat Z Z (nil Nat)))
            (λ [k : Nat] [v : (Vect Nat k)] Nat)
            Z
            (λ [k : Nat]
              (λ [x : Nat] [xs : (Vect Nat k)]
                (λ [IH : Nat]
                  (S IH)))))
 : Nat -> (S (S (Z))))

(define plus
  (λ [n : Nat] [m : Nat]
    (elim-Nat n
              (λ [k : Nat] Nat)
              m
              (λ [k : Nat] (λ [IH : Nat] (S IH))))))

(check-type plus : (→ Nat Nat Nat))

(check-type (plus Z (S (S Z))) : Nat -> (S (S Z)))
(check-type (plus (S (S Z)) Z) : Nat -> (S (S Z)))
(check-type (plus (S (S Z)) (S (S (S Z))))
            : Nat -> (S (S (S (S (S Z))))))

;; vappend
(check-type
 (elim-Vect (nil Nat)
  (λ [k : Nat]
    (λ [v : (Vect Nat k)]
      (Vect Nat k)))
  (nil Nat)
  (λ [k : Nat]
    (λ [x : Nat][v : (Vect Nat k)]
      (λ [IH : (Vect Nat k)]
        (cns Nat k x IH)))))
 : (Vect Nat Z)
 -> (nil Nat))

(define vappend
  (λ [A : Type]
    (λ [n : Nat][m : Nat]
      (λ [xs : (Vect A n)][ys : (Vect A m)]
        (elim-Vect xs
         (λ [k : Nat]
           (λ [v : (Vect A k)]
             (Vect A (plus k m))))
         ys
         (λ [k : Nat]
           (λ [x : A][v : (Vect A k)]
             (λ [IH : (Vect A (plus k m))]
               (cns A (plus k m) x IH)))))))))

(check-type
 vappend
 : (∀ [B : (Type 0)]
      (Π [n : Nat][m : Nat]
         (→ (Vect B n) (Vect B m) (Vect B (plus n m))))))

(check-type
 (vappend Nat)
 : (Π [n : Nat][m : Nat]
      (→ (Vect Nat n) (Vect Nat m) (Vect Nat (plus n m)))))

(check-type
 (vappend Nat Z Z)
 : (→ (Vect Nat Z) (Vect Nat Z) (Vect Nat Z)))

;; append nil + nil
(check-type
 (vappend Nat Z Z (nil Nat) (nil Nat))
 : (Vect Nat Z)
 -> (nil Nat))

;; append 1 + 0
(check-type
 (vappend Nat (S Z) Z (cns Nat Z Z (nil Nat)) (nil Nat))
 : (Vect Nat (S Z))
 -> (cns Nat Z Z (nil Nat)))

;; m and n flipped
(typecheck-fail (vappend Nat (S Z) Z (nil Nat) (cns Nat Z Z (nil Nat))))
(typecheck-fail (vappend Nat Z (S Z) (cns Nat Z Z (nil Nat) (nil Nat))))

;; append 1 + 1
(check-type
 (vappend Nat (S Z) (S Z) (cns Nat Z Z (nil Nat)) (cns Nat Z Z (nil Nat)))
 : (Vect Nat (S (S Z)))
 -> (cns Nat (S Z) Z (cns Nat Z Z (nil Nat))))

;; append 1 + 2
(check-type
 (vappend Nat (S Z) (S (S Z))
  (cns Nat Z Z (nil Nat))
  (cns Nat (S Z) Z (cns Nat Z Z (nil Nat))))
 : (Vect Nat (S (S (S Z))))
-> (cns Nat (S (S Z)) Z (cns Nat (S Z) Z (cns Nat Z Z (nil Nat)))))

;; append 2 + 1
(check-type
 (vappend Nat (S (S Z)) (S Z)
  (cns Nat (S Z) Z (cns Nat Z Z (nil Nat)))
  (cns Nat Z Z (nil Nat)))
 : (Vect Nat (S (S (S Z))))
-> (cns Nat (S (S Z)) Z (cns Nat (S Z) Z (cns Nat Z Z (nil Nat)))))

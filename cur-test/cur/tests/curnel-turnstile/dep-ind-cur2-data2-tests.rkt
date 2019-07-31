#lang cur
(require cur/stdlib/sugar
         rackunit/turnstile)

;; flat type --------------------

;; datacons: no out type
(define-datatype Nat1 : Type
  [z1]
  [s1 (n-1 : Nat1)])
(check-type Nat1 : Type)
(check-type z1 : Nat1)
(check-type s1 : (-> Nat1 Nat1))
(check-type (s1 z1) : Nat1)

;; datacons: 1 out type
(define-datatype Nat2 : Type
  [z2]
  [s2 (n-1 : Nat2) : Nat2])
(check-type Nat2 : Type)
(check-type z2 : Nat2)
(check-type s2 : (-> Nat2 Nat2))
(check-type (s2 z2) : Nat2)

;; datacons: 1 out type
(define-datatype Nat3 : Type
  [z3 : Nat3]
  [s3 (n-1 : Nat3)])
(check-type Nat3 : Type)
(check-type z3 : Nat3)
(check-type s3 : (-> Nat3 Nat3))
(check-type (s3 z3) : Nat3)

;; datacons: 2 out types, non-HO
(define-datatype Nat4 : Type
  [z4 : Nat4]
  [s4 (n-1 : Nat4) : Nat4])
(check-type Nat4 : Type)
(check-type z4 : Nat4)
(check-type s4 : (-> Nat4 Nat4))
(check-type (s4 z4) : Nat4)

;; datacons: 2 out types, HO
(define-datatype Nat5 : Type
  [z5 : Nat5]
  [s5 : (-> Nat5 Nat5)])
(check-type Nat5 : Type)
(check-type z5 : Nat5)
(check-type s5 : (-> Nat5 Nat5))
(check-type (s5 z5) : Nat5)

;; poly type --------------------
;; no out type
(define-datatype List1 (A : Type) : Type
  [null1]
  [cons1 (x : A) (xs : (List1 A))])
(check-type List1 : (-> Type Type))
(check-type (List1 Nat1) : Type)
(check-type null1 : (∀ [A : Type] (List1 A)))
(check-type cons1 : (∀ [A : Type] (-> A (List1 A) (List1 A))))
(check-type (cons1 Nat1 z1 (null1 Nat1)) : (List1 Nat1))

;; 1 out type
(define-datatype List2 (A : Type) : Type
  [null2 : (List2 A)]
  [cons2 (x : A) (xs : (List2 A))])
(check-type List2 : (-> Type Type))
(check-type (List2 Nat2) : Type)
(check-type null2 : (∀ [A : Type] (List2 A)))
(check-type cons2 : (∀ [A : Type] (-> A (List2 A) (List2 A))))
(check-type (cons2 Nat2 z2 (null2 Nat2)) : (List2 Nat2))

;; 1 out type
(define-datatype List3 (A : Type) : Type
  [null3]
  [cons3 (x : A) (xs : (List3 A)) : (List3 A)])
(check-type List3 : (-> Type Type))
(check-type (List3 Nat3) : Type)
(check-type null3 : (∀ [A : Type] (List3 A)))
(check-type cons3 : (∀ [A : Type] (-> A (List3 A) (List3 A))))
(check-type (cons3 Nat3 z3 (null3 Nat3)) : (List3 Nat3))

;; 2 out types
(define-datatype List4 (A : Type) : Type
  [null4 : (List4 A)]
  [cons4 (x : A) (xs : (List4 A)) : (List4 A)])
(check-type List4 : (-> Type Type))
(check-type (List4 Nat4) : Type)
(check-type null4 : (∀ [A : Type] (List4 A)))
(check-type cons4 : (∀ [A : Type] (-> A (List4 A) (List4 A))))
(check-type (cons4 Nat4 z4 (null4 Nat4)) : (List4 Nat4))

;; 2 out types, HO1
(define-datatype List5 (A : Type) : Type
  [null5 : (List5 A)]
  [cons5 (x : A) : (-> (xs : (List5 A)) (List5 A))])
(check-type List5 : (-> Type Type))
(check-type (List5 Nat5) : Type)
(check-type null5 : (∀ [A : Type] (List5 A)))
(check-type cons5 : (∀ [A : Type] (-> A (List5 A) (List5 A))))
(check-type (cons5 Nat5 z5 (null5 Nat5)) : (List5 Nat5))

;; 2 out types, HO2
(define-datatype List6 (A : Type) : Type
  [null6 : (List6 A)]
  [cons6 : (-> A (List6 A) (List6 A))])
(check-type List6 : (-> Type Type))
(check-type (List6 Nat5) : Type)
(check-type null6 : (∀ [A : Type] (List6 A)))
(check-type cons6 : (∀ [A : Type] (-> A (List6 A) (List6 A))))
(check-type (cons6 Nat5 z5 (null6 Nat5)) : (List6 Nat5))

;; indexed types --------------------
;; err: must explicitly declare datacons out type with indices
;; TODO: improve err msg
(typecheck-fail/toplvl
 (define-datatype Vect1 (A : Type) : (-> [i : Nat1] Type)
   [nil1]
   [cns1 (k : Nat1) (x : A) (xs : (Vect1 A k))]))

;; labeled index
(define-datatype Vect1 (A : Type) : (-> [i : Nat1] Type)
  [nil1 : (Vect1 A z1)]
  [cns1 (k : Nat1) (x : A) (xs : (Vect1 A k)) : (Vect1 A (s1 k))])
(check-type Vect1 : (-> Type Nat1 Type))
(check-type (Vect1 Nat1) : (-> Nat1 Type))
(check-type (Vect1 Nat1 z1) : Type)
(check-type nil1 : (∀ (A : Type) (Vect1 A z1)))
(check-type cns1 : (∀ (A : Type) (k : Nat1) (-> A (Vect1 A k) (Vect1 A (s1 k)))))
(check-type (nil1 Nat1) : (Vect1 Nat1 z1))
(check-type (cns1 Nat1 z1 z1 (nil1 Nat1)) : (Vect1 Nat1 (s1 z1)))

;; unlabeled index
(define-datatype Vect2 (A : Type) : (-> Nat2 Type)
  [nil2 : (Vect2 A z2)]
  [cns2 (k : Nat2) (x : A) (xs : (Vect2 A k)) : (Vect2 A (s2 k))])
(check-type Vect2 : (-> Type Nat2 Type))
(check-type (Vect2 Nat2) : (-> Nat2 Type))
(check-type (Vect2 Nat2 z2) : Type)
(check-type nil2 : (∀ (A : Type) (Vect2 A z2)))
(check-type cns2 : (∀ (A : Type) (k : Nat2) (-> A (Vect2 A k) (Vect2 A (s2 k)))))
(check-type (nil2 Nat2) : (Vect2 Nat2 z2))
(check-type (cns2 Nat2 z2 z2 (nil2 Nat2)) : (Vect2 Nat2 (s2 z2)))

;; HO data cons type
(define-datatype Vect3 (A : Type) : (-> Nat3 Type)
  [nil3 : (Vect3 A z3)]
  [cns3 (k : Nat3) (x : A) : (-> (Vect3 A k) (Vect3 A (s3 k)))])
(check-type Vect3 : (-> Type Nat3 Type))
(check-type (Vect3 Nat3) : (-> Nat3 Type))
(check-type (Vect3 Nat3 z3) : Type)
(check-type nil3 : (∀ (A : Type) (Vect3 A z3)))
(check-type cns3 : (∀ (A : Type) (k : Nat3) (-> A (Vect3 A k) (Vect3 A (s3 k)))))
(check-type (nil3 Nat3) : (Vect3 Nat3 z3))
(check-type (cns3 Nat3 z3 z3 (nil3 Nat3)) : (Vect3 Nat3 (s3 z3)))

;; even more HO data cons type
(define-datatype Vect4 (A : Type) : (-> Nat4 Type)
  [nil4 : (Vect4 A z4)]
  [cns4 : (-> (k : Nat4) (x : A) (Vect4 A k) (Vect4 A (s4 k)))])
(check-type Vect4 : (-> Type Nat4 Type))
(check-type (Vect4 Nat4) : (-> Nat4 Type))
(check-type (Vect4 Nat4 z4) : Type)
(check-type nil4 : (∀ (A : Type) (Vect4 A z4)))
(check-type cns4 : (∀ (A : Type) (k : Nat4) (-> A (Vect4 A k) (Vect4 A (s4 k)))))
(check-type (nil4 Nat4) : (Vect4 Nat4 z4))
(check-type (cns4 Nat4 z4 z4 (nil4 Nat4)) : (Vect4 Nat4 (s4 z4)))

(define-datatype nat : Type
  [z]
  [s (n-1 : nat)])

;; grammar example
(define-datatype aexp : Type
  [ANum (n : nat)]
  [APlus (a1 a2 : aexp)]
  [AMinus (a1 a2 : aexp)]
  [AMult (a1 a2 : aexp)])
;; Inductive aexp : Type :=
;;   | ANum (n : nat)
;;   | APlus (a1 a2 : aexp)
;;   | AMinus (a1 a2 : aexp)
;;   | AMult (a1 a2 : aexp).
(check-type aexp : Type)
(check-type ANum : (-> nat aexp))
(check-type APlus : (-> aexp aexp aexp))
(check-type AMinus : (-> aexp aexp aexp))
(check-type AMult : (-> aexp aexp aexp))
(check-type (ANum z) : aexp)
(check-type (APlus (ANum z) (ANum z)) : aexp)
(check-type (AMinus (ANum z) (ANum z)) : aexp)
(check-type (AMult (ANum z) (ANum z)) : aexp)

(define/rec/match plus : nat [n : nat] -> nat
  [z => n]
  [(s x) => (s (plus x n))])

(define/rec/match minus : nat nat -> nat
  [z _ => z]
  [(s n-1) z => (s n-1)]
  [(s n-1) (s m-1) => (minus n-1 m-1)])

(define/rec/match mult : nat [n : nat] -> nat
  [z => z]
  [(s x) => (plus n (mult x n))])

(define-datatype aevalR : (-> aexp nat Type)
  [E_ANum [n : nat] :
          (aevalR (ANum n) n)]
  [E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
           (-> (aevalR e1 n1)
               (aevalR e2 n2)
               (aevalR (APlus e1 e2) (plus n1 n2)))]
  [E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
            (-> (aevalR e1 n1)
                (aevalR e2 n2)
                (aevalR (AMinus e1 e2) (minus n1 n2)))]
  [E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
            (-> (aevalR e1 n1)
                (aevalR e2 n2)
                (aevalR (AMult e1 e2) (mult n1 n2)))])
;; Inductive aevalR : aexp -> nat -> Prop :=
;;   | E_ANum n :
;;       aevalR (ANum n) n
;;   | E_APlus (e1 e2: aexp) (n1 n2: nat) :
;;       aevalR e1 n1 ->
;;       aevalR e2 n2 ->
;;       aevalR (APlus e1 e2) (n1 + n2)
;;   | E_AMinus (e1 e2: aexp) (n1 n2: nat) :
;;       aevalR e1 n1 ->
;;       aevalR e2 n2 ->
;;       aevalR (AMinus e1 e2) (n1 - n2)
;;   | E_AMult (e1 e2: aexp) (n1 n2: nat) :
;;       aevalR e1 n1 ->
;;       aevalR e2 n2 ->
;;       aevalR (AMult e1 e2) (n1 * n2).

(check-type aevalR : (-> aexp nat Type))
(check-type E_ANum : (∀ [n : nat] (aevalR (ANum n) n)))
(check-type E_APlus : (∀ [e1 e2 : aexp] [n1 n2 : nat]
                         (-> (aevalR e1 n1)
                             (aevalR e2 n2)
                             (aevalR (APlus e1 e2) (plus n1 n2)))))
(check-type E_AMinus : (∀ [e1 e2 : aexp] [n1 n2 : nat]
                          (-> (aevalR e1 n1)
                              (aevalR e2 n2)
                              (aevalR (AMinus e1 e2) (minus n1 n2)))))
(check-type E_AMult : (∀ [e1 e2 : aexp] [n1 n2 : nat]
                         (-> (aevalR e1 n1)
                             (aevalR e2 n2)
                             (aevalR (AMult e1 e2) (mult n1 n2)))))



;; define-datatype TODO:
;; - not specifying constructors results in define-red err

;; error description: same binder for param and index
;; data1 err: stx parse dup attr
;; (require "../dep-ind-cur2+data2.rkt")
#;(define-datatype T [A : Type] : [A : Type] -> Type
  [C : (∀ [A : Type] [B : Type] (T A B))])

;; data2 err: stx parse dup attr
#;(define-datatype T [A : Type] : [A : Type] -> Type
  [C : [B : Type] -> (T A B)])

;; error description: constructor re-binds param
;; data2 err: stx parse dup attr
#;(define-datatype T [A : Type] : [B : Type] -> Type
  [C : [A : Type] -> (T A A)])

;; error description: A : A
#;(define-datatype T [A : A] : -> Type
  [C : (T A)])

;(C Type) ; data2 err: expected T given A
;(T Type)  ; data2 err: expected Type 1, given Type

;; ;; error description: another binder uses A
;; (define-datatype TY [A : (Π [A : Type] Type)] : -> Type
;;   [C : (TY A)])

;; (check-type (C (λ [x : Type] x)) : (TY (λ [x : Type] x)))

;; ;; data2 err: A gets subst with arg, eg (Π [(λ [x : Type] x) : Type] Type)
;; ;; due to pattern-var-sub trick, use expanded/fresh vars to avoid this
;; (check-type (TY (λ [x : Type] x)) : Type) ; BAD ; 2018-06-24: fixed

;; (check-type (λ [x : Type]  x) : (Π [A : Type] Type))

; Strict positivity test
(typecheck-fail/toplvl
 ; Curry's paradox
 (define-datatype Bad : (Type 0)
   [intro_B : (-> (-> Bad Bad) Bad)])
 #:with-msg "does not satisfy strict positivity")

(typecheck-fail/toplvl
 (define-datatype A : Prop
   [intro_A : (-> (-> (-> A Prop) Prop) A)])
 #:with-msg "does not satisfy strict positivity")

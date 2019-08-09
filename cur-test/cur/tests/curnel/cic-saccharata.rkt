#lang cur
(require rackunit/turnstile rackunit)

;; Check (Type n) : (Type n+1)
(check-type Type : (Type 1) -> (Type 0))
(check-type (Type 0) : (Type 1) -> (Type 0))
(check-not-type (Type 0) : (Type 0))
(check-type (Type 1) : (Type 2) -> (Type 1))
(check-type (Type 3) : (Type 4) -> (Type 3))

; TODO: Negative tests?


;; Check predicativity rules
(typecheck-fail ((λ [x : Type] x) Type)
  #:with-msg "expected \\(Type 0\\), given \\(Type 1\\)")
(check-type ((λ [x : (Type 1)] x) Type) : (Type 1))
(check-type ((λ [x : (Type 2)] x) (Type 1)) : (Type 2))

(check-type (λ [y : (Type 0)] y) : (→ (Type 0) (Type 0)))
(check-type (λ [y : (Type 0)] (Type 0)) : (→ (Type 0) (Type 1)))
(check-type (λ [y : (Type 0)] (Type 1)) : (→ (Type 0) (Type 2)))

; TODO: Negative tests?

;; Check syntactic sugar for λ
;; TODO: make this err?
(check-type (λ (λ [x : Type] x)) : (→ Type Type))

;; Cumulativity/subtyping tests
(check-type
 ((λ (f : (Π (x : (Type 0)) (Type 1))) f)
  (λ (x : (Type 0)) x))
 : (Π (x : (Type 0)) (Type 1)))

;; result can have body type at higher universe
(check-type
 ((λ (f : (Π (x : (Type 0)) (Type 1))) f)
  (λ (x : (Type 0)) x))
 : (Π (x : (Type 0)) (Type 2)))

;; Peano nums -----------------------------------------------------------------

(define-datatype Nat : Type
  [Z : Nat]
  [S : (→ Nat Nat)])

(check-type Z : Nat)
(check-type (Z) : Nat)
(check-type Z : (→ Nat)) ;; TODO: make this err?
(check-type S : (→ Nat Nat))
(check-type Z : Nat -> Z)
(check-type (Z) : Nat -> (Z)) ;; TODO?
(check-type (S (Z)) : Nat)
(check-type (S (Z)) : Nat -> (S (Z)))
(check-type (S (S (Z))) : Nat -> (S (S (Z))))
(check-type (S Z) : Nat)
(check-type (S Z) : Nat -> (S Z))
(check-type (S (S Z)) : Nat -> (S (S Z)))

(define nat-rec
  (λ [C : Type]
    (λ [zc : C][sc : (→ C C)]
      (λ [n : Nat]
        (elim-Nat n
                  (λ [x : Nat] C)
                  zc
                  (λ [x : Nat] sc))))))
;; (→ C) same as C
(check-type nat-rec : (∀ [C : (Type 0)] (→ (→ C) (→ C C) (→ Nat C))))
(check-type nat-rec : (∀ [C : (Type 0)] (→ C (→ C C) (→ Nat C))))

;; nat-rec with no annotations
(check-type
  (λ C
    (λ zc sc
      (λ n
        (elim-Nat n
                  (λ x C)
                  zc
                  (λ x sc)))))
  : (∀ [C : (Type 0)] (→ C (→ C C) (→ Nat C))))
;; (λ zc) same as zc
(check-type
  (λ C
    (λ zc sc
      (λ n
        (elim-Nat n
                  (λ x C)
                  (λ zc)
                  (λ x sc)))))
  : (∀ [C : (Type 0)] (→ C (→ C C) (→ Nat C))))

(check-type (nat-rec Nat) : (→ (→ Nat) (→ Nat Nat) (→ Nat Nat)))
(check-type (nat-rec Nat) : (→ Nat (→ Nat Nat) (→ Nat Nat)))
(check-type ((nat-rec Nat) Z (λ [n : Nat] (S n))) : (→ Nat Nat))
(check-type (nat-rec Nat Z (λ [n : Nat] (S n))) : (→ Nat Nat))

;; basic identity example, to test eval
(define id (nat-rec Nat Z (λ [n : Nat] (S n))))
(check-type (id (Z)) : Nat -> (Z))
(check-type (id Z) : Nat -> Z)
(check-type (id Z) : Nat -> (Z))
;; this example will err if eval tries to tycheck again
(check-type (id (S Z)) : Nat)
(check-type (id (S Z)) : Nat -> (S Z))

(define plus
  (λ [n : Nat]
    (((nat-rec (→ Nat Nat))
      (λ [m : Nat] m)
      (λ [pm : (→ Nat Nat)]
        (λ [x : Nat]
          (S (pm x)))))
     n)))

(check-type plus : (→ Nat (→ Nat Nat)))

;; plus with less parens
(check-type
  (λ [n : Nat]
    (nat-rec (→ Nat Nat)
      (λ [m : Nat] m)
      (λ [pm : (→ Nat Nat)] [x : Nat] (S (pm x)))
      n))
  : (→ Nat Nat Nat))

;; plus, no annotations, no auto curry
(check-type
 (λ n1 n2
   ((((nat-rec (→ Nat Nat))
      (λ m m)
      (λ pm (λ x (S (pm x)))))
     n1)
    n2))
 : (→ Nat Nat Nat))

;; plus, no annotations, less parens
(check-type
 (λ n1 n2
   (nat-rec (→ Nat Nat)
            (λ m m)
            (λ pm x (S (pm x)))
            n1
            n2))
 : (→ Nat Nat Nat))

;(check-type ((plus Z) Z) : Nat -> 0)
;(check-type ((plus (S Z)) (S Z)) : Nat -> 2)
;(check-type ((plus (S Z)) Z) : Nat -> 1)
;(check-type ((plus (S Z)) Z) : Nat -> 1)
(check-type (plus (Z)) : (→ Nat Nat))
(check-type ((plus (Z)) (Z)) : Nat -> (Z))
(check-type ((plus (Z)) (S (Z))) : Nat -> (S (Z)))
(check-type ((plus (S (Z))) (Z)) : Nat -> (S (Z)))
(check-type ((plus (S (Z))) (S (Z))) : Nat -> (S (S (Z))))
(check-type ((plus (S (S (Z)))) (S (Z))) : Nat -> (S (S (S (Z)))))
(check-type ((plus (S (Z))) (S (S (Z)))) : Nat -> (S (S (S (Z)))))
;; plus examples, less parens
(check-type (plus Z) : (→ Nat Nat))
(check-type (plus Z Z) : Nat -> Z)
(check-type (plus Z (S Z)) : Nat -> (S Z))
(check-type (plus (S Z) Z) : Nat -> (S Z))
(check-type (plus (S Z) (S Z)) : Nat -> (S (S Z)))
(check-type (plus (S (S Z)) (S Z)) : Nat -> (S (S (S Z))))
(check-type (plus (S Z) (S (S Z))) : Nat -> (S (S (S Z))))

(define minus
  (λ [n : Nat]
    (λ [m : Nat]
      (elim-Nat n (λ (n : Nat) Nat)
                (elim-Nat m (λ (m : Nat) Nat)
                          Z
                          (λ (n : Nat) (ih : Nat) Z))
                (λ (n-1 : Nat)
                  (ih-n : Nat)
                  (elim-Nat m (λ (m : Nat) Nat)
                            n-1
                            (λ (m-1 : Nat)
                              (ih-m : Nat)
                              ih-n)))))))
(check-type minus : (-> Nat Nat Nat))
(check-equal? (minus (S Z) Z) Z)
(check-equal? (minus (S Z) (S Z)) Z)
(check-equal? (minus Z (S Z)) Z)

(define mult
  (λ [n : Nat]
    (λ [m : Nat]
      (elim-Nat n (λ (n : Nat) Nat)
                Z
                (λ (n-1 : Nat) (ih-n : Nat)
                  (plus m ih-n))))))

(check-type mult : (-> Nat Nat Nat))
(check-equal? (mult (S Z) Z) Z)
(check-equal? (mult (S Z) (S Z)) (S Z))
(check-equal? (mult (S (S Z)) (S (S Z))) (S (S (S (S Z)))))

;; test currying
(check-type
 (λ [A : Type] (λ [x : A] x))
 : (Π [B : Type] (Π [y : B] B)))
(check-type
 (λ [A : Type] (λ [x : A] x))
 : (Π [B : Type][y : B] B))
(check-type
 (λ [A : Type][x : A] x)
 : (Π [B : Type] (Π [y : B] B)))
(check-type
 (λ [A : Type][x : A] x)
 : (Π [B : Type][y : B] B))
(check-type ((λ [A : Type][x : A] x) Nat Z) : Nat -> Z)

(check-type
 (((λ [A : Type][x : A] x) Nat) (Z))
 : Nat -> (Z))

(check-type
 ((λ [A : Type][x : A] x) Nat (Z))
 : Nat -> (Z))

(check-type
 (plus
  (((λ [A : Type][x : A] x) Nat) (Z))
  (((λ [A : Type][x : A] x) Nat) (Z)))
 : Nat -> (Z))

;; same as previous, less parens
(check-type
 (plus
  ((λ [A : Type][x : A] x) Nat Z)
  ((λ [A : Type][x : A] x) Nat Z))
 : Nat -> Z)


;; Check define-datatype
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

;; grammar example
(define-datatype aexp : Type
  [ANum (n : Nat)]
  [APlus (a1 a2 : aexp)]
  [AMinus (a1 a2 : aexp)]
  [AMult (a1 a2 : aexp)])

(check-type aexp : Type)
(check-type ANum : (-> Nat aexp))
(check-type APlus : (-> aexp aexp aexp))
(check-type AMinus : (-> aexp aexp aexp))
(check-type AMult : (-> aexp aexp aexp))
(check-type (ANum Z) : aexp)
(check-type (APlus (ANum Z) (ANum Z)) : aexp)
(check-type (AMinus (ANum Z) (ANum Z)) : aexp)
(check-type (AMult (ANum Z) (ANum Z)) : aexp)

(define-datatype aevalR : (-> aexp Nat Type)
  [E_ANum [n : Nat] :
          (aevalR (ANum n) n)]
  [E_APlus (e1 e2 : aexp) (n1 n2 : Nat) :
           (-> (aevalR e1 n1)
               (aevalR e2 n2)
               (aevalR (APlus e1 e2) (plus n1 n2)))]
  [E_AMinus (e1 e2 : aexp) (n1 n2 : Nat) :
            (-> (aevalR e1 n1)
                (aevalR e2 n2)
                (aevalR (AMinus e1 e2) (minus n1 n2)))]
  [E_AMult (e1 e2 : aexp) (n1 n2 : Nat) :
            (-> (aevalR e1 n1)
                (aevalR e2 n2)
                (aevalR (AMult e1 e2) (mult n1 n2)))])

(check-type aevalR : (-> aexp Nat Type))
(check-type E_ANum : (∀ [n : Nat] (aevalR (ANum n) n)))
(check-type E_APlus : (∀ [e1 e2 : aexp] [n1 n2 : Nat]
                         (-> (aevalR e1 n1)
                             (aevalR e2 n2)
                             (aevalR (APlus e1 e2) (plus n1 n2)))))
(check-type E_AMinus : (∀ [e1 e2 : aexp] [n1 n2 : Nat]
                          (-> (aevalR e1 n1)
                              (aevalR e2 n2)
                              (aevalR (AMinus e1 e2) (minus n1 n2)))))
(check-type E_AMult : (∀ [e1 e2 : aexp] [n1 n2 : Nat]
                         (-> (aevalR e1 n1)
                             (aevalR e2 n2)
                             (aevalR (AMult e1 e2) (mult n1 n2)))))

;; Error message tests
(typecheck-fail/toplvl
 (define-datatype T [A : Type] : [A : Type] -> Type
   [C : (∀ [A : Type] [B : Type] (T A B))])
 #:with-msg "")

(typecheck-fail/toplvl
 (define-datatype T [A : Type] : [A : Type] -> Type
     [C : [B : Type] -> (T A B)])
 #:with-msg "")

(typecheck-fail/toplvl
 (define-datatype T [A : Type] : [B : Type] -> Type
   [C : [A : Type] -> (T A A)])
 #:with-msg "")

(typecheck-fail/toplvl
 (define-datatype T [A : A] : -> Type
   [C : (T A)])
 #:with-msg "")

(typecheck-fail/toplvl
 (define-datatype TY [A : (Π [A : Type] Type)] : -> Type
   [C : (TY A)])
 #:with-msg "")

;; Check strict positivity
(typecheck-fail/toplvl
 ; Curry's paradox
 (define-datatype Bad : (Type 0)
   [intro_B : (-> (-> Bad Bad) Bad)])
 #:with-msg "does not satisfy strict positivity")

(typecheck-fail/toplvl
 (define-datatype A : Prop
   [intro_A : (-> (-> (-> A Prop) Prop) A)])
 #:with-msg "does not satisfy strict positivity")

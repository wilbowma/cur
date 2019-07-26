#lang s-exp cur/curnel/turnstile-impl/dep-ind-cur2
(require
 cur/curnel/turnstile-impl/dep-ind-cur2+data2
 cur/curnel/turnstile-impl/dep-ind-cur2+sugar
 rackunit/turnstile)

; Π → λ ∀ ≻ ⊢ ≫ ⇒

; identical to dep-ind-fixed-tests.rkt
; but with default curry/uncurry

; should be similar to dep-ind-tests.rkt
; since dep-ind-cur does not change
; first clause of define-datatype

;; examples from Prabhakar's Proust paper

;; this file is like dep-peano-tests.rkt except it uses
;; define-datatype from #lang dep-ind-cur.rkt to define Nat,
;; instead of using the builtin Nat from #lang dep.rkt

;; the examples in this file are mostly identical to dep-peano-tests.rkt,
;; except Z is replaced with (Z)

;; check (Type n) : (Type n+1)
(check-type Type : (Type 1) -> (Type 0))
(check-type (Type 0) : (Type 1) -> (Type 0))
(check-not-type (Type 0) : (Type 0))
(check-type (Type 1) : (Type 2) -> (Type 1))
(check-type (Type 3) : (Type 4) -> (Type 3))

(typecheck-fail ((λ [x : Type] x) Type)
  #:with-msg "expected \\(Type 0\\), given \\(Type 1\\)")
(check-type ((λ [x : (Type 1)] x) Type) : (Type 1))
(check-type ((λ [x : (Type 2)] x) (Type 1)) : (Type 2))

(check-type (λ [y : (Type 0)] y) : (→ (Type 0) (Type 0)))
(check-type (λ [y : (Type 0)] (Type 0)) : (→ (Type 0) (Type 1)))
(check-type (λ [y : (Type 0)] (Type 1)) : (→ (Type 0) (Type 2)))

;; zero-arg fn is constant
;; TODO: make this err?
(check-type (λ (λ [x : Type] x)) : (→ Type Type))

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

;; TODO: define #%datum
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


;; equality -------------------------------------------------------------------

(require (only-in turnstile struct #%app- void- define-typed-syntax ⇒ ⇐ ≫ ⊢ ≻))


(struct =- (l r) #:transparent)

(define-typed-syntax (= t1 t2) ≫
  [⊢ t1 ≫ t1- ⇒ ty]
  [⊢ t2 ≫ t2- ⇐ ty]
  ---------------------
  [⊢ (#%app- =- t1- t2-) ⇒ Type])

(define-typed-syntax (eq-refl e) ≫
  [⊢ e ≫ e- ⇒ _ (⇒ ~Type)]
  ----------
  [⊢ (#%app- void-) ⇒ (= e- e-)])

;; eq-elim: t : T
;;          P : (T -> Type)
;;          pt : (P t)
;;          w : T
;;          peq : (= t w)
;;       -> (P w)
(define-typed-syntax (eq-elim t P pt w peq) ≫
  [⊢ t ≫ t- ⇒ ty]
  [⊢ P ≫ P- ⇐ (→ ty Type)]
  [⊢ pt ≫ pt- ⇐ (P- t-)]
  [⊢ w ≫ w- ⇐ ty]
  [⊢ peq ≫ peq- ⇐ (= t- w-)]
  --------------
  [⊢ pt- ⇒ (P- w-)])

;; plus zero (left)
(check-type (λ [n : Nat] (eq-refl n))
          : (Π [n : Nat] (= (plus Z n) n)))

;; plus zero (right), just the eq
;; tests that erased-wrapping is disabled
;; - if it's not, then result of eq-elim will have two (expander-merged) types,
;;   but will use the wrong one: (P- t-) instead of (P- w-)
;; current workaround:
;; - in turnstile.rkt, last-clause, dont add `erased` wrapper if current-use-stop-list? = #f
(check-type
 (λ [k : Nat]
   (λ [p : (= (plus k Z) k)]
     (eq-elim (plus k Z)
              (λ [W : Nat] (= (S (plus k Z)) (S W)))
              (eq-refl (S (plus k Z)))
              k
              p)))
 : (Π [k : Nat] [p : (= (plus k Z) k)] (= (S (plus k Z)) (S k))))
;; plus zero (right)
(check-type
 (λ [n : Nat]
   (elim-Nat n
             (λ [m : Nat] (= (plus m Z) m))
             (eq-refl Z)
             (λ [k : Nat]
               (λ [p : (= (plus k Z) k)]
                 (eq-elim (plus k Z)
                          (λ [W : Nat] (= (S (plus k Z)) (S W)))
                          (eq-refl (S (plus k Z)))
                          k
                          p)))))
 : (Π [n : Nat] (= (plus n Z) n)))

;; plus zero identity, no annotations
;; left:
(check-type (λ n (eq-refl n))
          : (Π [n : Nat] (= (plus Z n) n)))
;; right:
(check-type
 (λ n
   (elim-Nat n
             (λ m (= (plus m Z) m))
             (eq-refl Z)
             (λ k p
               (eq-elim (plus k Z)
                        (λ W (= (S (plus k Z)) (S W)))
                        (eq-refl (S (plus k Z)))
                        k
                        p))))
 : (Π [n : Nat] (= (plus n Z) n)))

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
;; this works now (broken in dep-ind-fixed bc multi-param lambdas werent let*)
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

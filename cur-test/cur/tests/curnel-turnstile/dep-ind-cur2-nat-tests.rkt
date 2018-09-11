#lang s-exp cur/curnel/turnstile-impl/dep-ind-cur2
(require cur/curnel/turnstile-impl/dep-ind-cur2+sugar
         cur/curnel/turnstile-impl/dep-ind-cur2+eq2
         cur/curnel/turnstile-impl/dep-ind-cur2+nat
         turnstile/rackunit-typechecking)

; Π → λ ∀ ≻ ⊢ ≫ ⇒

;; same as dep-ind-cur2-tests, except:
;; - uses Nat lib instead of defining it
;; - uses eq2 lib

;; check (Type n) : (Type n+1)
(check-type Type : (Type 1) -> (Type 0))
(check-type (Type 0) : (Type 1) -> (Type 0))
(check-not-type (Type 0) : (Type 0))
(check-type (Type 1) : (Type 2) -> (Type 1))
(check-type (Type 3) : (Type 4) -> (Type 3))

(typecheck-fail ((λ [x : Type] x) Type)
  #:with-msg "expected Type, given \\(Type 1\\)")
(check-type ((λ [x : (Type 1)] x) Type) : (Type 1))
(check-type ((λ [x : (Type 2)] x) (Type 1)) : (Type 2))

(check-type (λ [y : (Type 0)] y) : (→ (Type 0) (Type 0)))
(check-type (λ [y : (Type 0)] (Type 0)) : (→ (Type 0) (Type 1)))
(check-type (λ [y : (Type 0)] (Type 1)) : (→ (Type 0) (Type 2)))

;; zero-arg fn is constant
;; TODO: make this err?
(check-type (λ (λ [x : Type] x)) : (→ Type Type))


;; Peano nums -----------------------------------------------------------------

;; (define-datatype Nat : *
;;   [Z : Nat]
;;   [S : (→ Nat Nat)])

(check-type Z : Nat)
(check-type (Z) : Nat)
(check-type Z : (→ Nat)) ;; TODO: make this err?
;(check-type S : (→ Nat Nat))
(check-type Z : Nat -> Z)
(check-type (Z) : Nat -> (Z)) ;; TODO?
(check-type (S (Z)) : Nat)
(check-type (S (Z)) : Nat -> (S (Z)))
(check-type (S (S (Z))) : Nat -> (S (S (Z))))
(check-type (S Z) : Nat)
(check-type (S Z) : Nat -> (S Z))
(check-type (S (S Z)) : Nat -> (S (S Z)))

(define nat-rec
  (λ [C : *]
    (λ [zc : C][sc : (→ C C)]
      (λ [n : Nat]
        (elim-Nat n
                  (λ [x : Nat] C)
                  zc
                  (λ [x : Nat] sc))))))
;; (→ C) same as C
(check-type nat-rec : (∀ C (→ (→ C) (→ C C) (→ Nat C))))
(check-type nat-rec : (∀ C (→ C (→ C C) (→ Nat C))))

;; nat-rec with no annotations
(check-type
  (λ C
    (λ zc sc
      (λ n
        (elim-Nat n
                  (λ x C)
                  zc
                  (λ x sc)))))
  : (∀ C (→ C (→ C C) (→ Nat C))))
;; (λ zc) same as zc
(check-type
  (λ C
    (λ zc sc
      (λ n
        (elim-Nat n
                  (λ x C)
                  (λ zc)
                  (λ x sc)))))
  : (∀ C (→ C (→ C C) (→ Nat C))))

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

;; plus zero (left)
(check-type (λ [n : Nat] (eq-refl Nat n))
          : (Π [n : Nat] (= Nat (plus Z n) n)))

;; plus zero (right)
(check-type
 (λ [n : Nat]
   (elim-Nat n
             (λ [m : Nat] (= Nat (plus m Z) m))
             (eq-refl Nat Z)
             (λ [k : Nat]
               (λ [p : (= Nat (plus k Z) k)]
                 (eq-elim (plus k Z)
                          (λ [W : Nat] (= Nat (S (plus k Z)) (S W)))
                          (eq-refl Nat (S (plus k Z)))
                          k
                          p)))))
 : (Π [n : Nat] (= Nat (plus n Z) n)))

;; plus zero identity, no annotations
;; left:
(check-type (λ n (eq-refl Nat n))
          : (Π [n : Nat] (= Nat (plus Z n) n)))
;; right:
(check-type
 (λ n
   (elim-Nat n
             (λ m (= Nat (plus m Z) m))
             (eq-refl Nat Z)
             (λ k p
               (eq-elim (plus k Z)
                        (λ W (= Nat (S (plus k Z)) (S W)))
                        (eq-refl Nat (S (plus k Z)))
                        k
                        p))))
 : (Π [n : Nat] (= Nat (plus n Z) n)))

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

#lang s-exp cur/curnel/turnstile-impl/dep-ind-cur2
(require cur/curnel/turnstile-impl/dep-ind-cur2+sugar
         cur/curnel/turnstile-impl/dep-ind-cur2+eq2
         cur/curnel/turnstile-impl/dep-ind-cur2+nat+datum
         rackunit/turnstile)

; Π → λ ∀ ≻ ⊢ ≫ ⇒

;; same as dep-ind-cur2-nat tests, except uses new #%datum

;; Peano nums -----------------------------------------------------------------

(check-type 0 : Nat)
(check-type 0 : (→ Nat)) ;; TODO: make this err?
(check-type 0 : Nat -> 0)
(check-type 1 : Nat)
(check-type 1 : Nat -> 1)
(check-type 2 : Nat -> 2)

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
(check-type ((nat-rec Nat) 0 (λ [n : Nat] (S n))) : (→ Nat Nat))
(check-type (nat-rec Nat 0 (λ [n : Nat] (S n))) : (→ Nat Nat))

;; basic identity example, to test eval
(define id (nat-rec Nat 0 (λ [n : Nat] (S n))))
(check-type (id 0) : Nat -> 0)
;; this example will err if eval tries to tycheck again
(check-type (id 1) : Nat)
(check-type (id 1) : Nat -> 1)

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

(check-type (plus 0 0) : Nat -> 0)
(check-type (plus 1 1) : Nat -> 2)
(check-type (plus 1 0) : Nat -> 1)
(check-type (plus 0 1) : Nat -> 1)
(check-type (plus 0) : (→ Nat Nat))
(check-type ((plus 0) 0) : Nat -> 0)
(check-type ((plus 0) 1) : Nat -> 1)
(check-type ((plus 1) 0) : Nat -> 1)
(check-type ((plus 1) 1) : Nat -> 2)
(check-type ((plus 2) 1) : Nat -> 3)
(check-type ((plus 1) 2) : Nat -> 3)
(check-type (plus 2 1) : Nat -> 3)
(check-type (plus 1 2) : Nat -> 3)

;; plus zero (left)
(check-type (λ [n : Nat] (eq-refl Nat n))
          : (Π [n : Nat] (= Nat (plus 0 n) n)))

;; plus zero (right)
(check-type
 (λ [n : Nat]
   (elim-Nat n
             (λ [m : Nat] (= Nat (plus m 0) m))
             (eq-refl Nat 0)
             (λ [k : Nat]
               (λ [p : (= Nat (plus k 0) k)]
                 (eq-elim (plus k 0)
                          (λ [W : Nat] (= Nat (S (plus k 0)) (S W)))
                          (eq-refl Nat (S (plus k 0)))
                          k
                          p)))))
 : (Π [n : Nat] (= Nat (plus n 0) n)))

;; plus zero identity, no annotations
;; left:
(check-type (λ n (eq-refl Nat n))
          : (Π [n : Nat] (= Nat (plus 0 n) n)))
;; right:
(check-type
 (λ n
   (elim-Nat n
             (λ m (= Nat (plus m 0) m))
             (eq-refl Nat 0)
             (λ k p
               (eq-elim (plus k 0)
                        (λ W (= Nat (S (plus k 0)) (S W)))
                        (eq-refl Nat (S (plus k 0)))
                        k
                        p))))
 : (Π [n : Nat] (= Nat (plus n 0) n)))

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
(check-type ((λ [A : Type][x : A] x) Nat 0) : Nat -> 0)

(check-type
 (((λ [A : Type][x : A] x) Nat) 0)
 : Nat -> 0)

(check-type 
 ((λ [A : Type][x : A] x) Nat 0)
 : Nat -> 0)

(check-type
 (plus
  (((λ [A : Type][x : A] x) Nat) 0)
  (((λ [A : Type][x : A] x) Nat) 0))
 : Nat -> 0)

;; same as previous, less parens
(check-type
 (plus
  ((λ [A : Type][x : A] x) Nat 0)
  ((λ [A : Type][x : A] x) Nat 0))
 : Nat -> 0)

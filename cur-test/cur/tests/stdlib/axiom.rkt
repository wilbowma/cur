#lang cur
(require
 cur/stdlib/nat
 cur/stdlib/bool
 cur/stdlib/sugar
 cur/stdlib/equality
 cur/stdlib/axiom
 (only-in racket/base module)
 rackunit/turnstile+)

(module check-output racket/base
  (provide check-output)
  (require rackunit racket/port)
  (define-syntax-rule (check-output expect body ...)
    (check-equal? 'expect (with-output-to-string (λ () body ...)))))
(require 'check-output)

;; print-assumptions when no axioms used

(define fine
  (ann (λ [x : Bool]
         (elim-Bool x
                    (λ [y : Bool] (== Bool (not (not y)) y))
                    (refl true)
                    (refl false)))
       :
       (∀ [x : Bool] (== Bool (not (not x)) x))))

(check-output
 "Axioms used by \"fine\":
"
 (print-assumptions fine))

;; define an axiom

(define-axiom false=true
  (== false true))

;; print-assumptions when an axioms is used

(define not-fine
  (ann (λ [x : Bool]
         (elim-Bool x
                    (λ [y : Bool] (== Bool (not y) y))
                    false=true
                    (sym Bool false true false=true)))
       :
       (∀ [x : Bool] (== Bool (not x) x))))

(check-output
 "Axioms used by \"not-fine\":
 - false=true : (== Bool false true)
"
 (print-assumptions not-fine))

;; plus-n-0 (no J)
(check-type
 (λ [n : Nat]
   (new-elim
    n
    (λ [n : Nat] (== Nat n (plus n 0)))
    (refl Nat 0)
    (λ [n-1 : Nat]
      (λ [IH : (== Nat n-1 (plus n-1 0))]
        (new-elim
         IH
         (λ [m : Nat]
           (λ [H : (== Nat n-1 m)]
             (== Nat (s n-1) (s m))))
         (refl Nat (s n-1)))))))
 : (∀ [n : Nat] (== Nat n (plus n 0))))

(define-extension-type-rule (J t P pt w peq) ≫
  [⊢ t ≫ t- ⇒ A]
  [⊢ P ≫ P- ⇐ (→ A Type)]
  [⊢ pt ≫ pt- ⇐ (P- t-)]
  [⊢ w ≫ w- ⇐ A]
  [⊢ peq ≫ peq- ⇐ (== A t- w-)]
  --------------
  [⊢ pt- ⇒ (P- w-)])

;; plus zero (right)
(define plus0r
  (λ [n : Nat]
   (elim-Nat n
             (λ [m : Nat] (== Nat (plus m 0) m))
             (refl Nat 0)
             (λ [k : Nat]
               (λ [p : (== Nat (plus k 0) k)]
                 (J (plus k 0)
                    (λ [W : Nat] (== Nat (s (plus k 0)) (s W)))
                    (refl Nat (s (plus k 0)))
                    k
                    p))))))
(check-type plus0r : (Π [n : Nat] (== Nat (plus n 0) n)))

(print-extensions plus0r)


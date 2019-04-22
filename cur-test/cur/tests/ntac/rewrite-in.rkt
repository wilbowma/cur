#lang cur
(require cur/stdlib/equality
         cur/stdlib/sugar
         cur/stdlib/bool
         cur/ntac/base
         cur/ntac/standard
         cur/ntac/rewrite
         "rackunit-ntac.rkt"
         rackunit/turnstile)

;; test rewriting in ctx hypotheses

;; regular rewrite (no #:in)
(define-theorem trans
 (∀ [x y z : Bool]
    (-> (== x y)
        (== y z)
        (== x z)))
  (by-intros x y z H1 H2)
  (by-rewrite H1)
  by-assumption)

(:: trans
    (∀ [x y z : Bool]
       (-> (== x y)
           (== y z)
           (== x z))))

;; raw term: regular rewrite (no #:in)
(::
 (λ (x : Bool)
   (λ (y : Bool)
     (λ (z : Bool)
       (λ (H1 : (== Bool x y))
         (λ (H2 : (== Bool y z))
           (new-elim
            (sym Bool x y (H1)) ; by-rewrite H1: goal: x=z -> y=z
            (λ (g3 : Bool) (λ (g4 : (== Bool y g3)) (== Bool g3 z)))
            H2))))))
 (∀ [x y z : Bool]
    (-> (== x y)
        (== y z)
        (== x z))))

(define-theorem trans/in
  (∀ [x y z : Bool]
     (-> (== x y)
         (== y z)
         (== x z)))
  (by-intros x y z H1 H2)
  (by-rewrite H2 #:in H1)
  by-assumption)

(check-type trans/in
 : (∀ [x y z : Bool]
     (-> (== x y)
         (== y z)
         (== x z))))

;; wrong raw term (for trans/in):
#;(λ (x : Bool)
   (λ (y : Bool)
     (λ (z : Bool)
       (λ (H1 : (== Bool x y))
         (λ (H2 : (== Bool y z))
           ((λ (H1 : (== Bool x z)) H1)
            (new-elim ; by-rewrite H2 #:in H1 x=y -> x=z
             (sym Bool y z (H2))
             (λ (g21 : Bool) (λ (g22 : (== Bool z g21)) (== Bool x g21)))
             H1)))))))

;; another wrong raw term (for trans/in)
;; (bc H2 and H1 position are flipped in the elim)
;; but this one happens to typecheck
(:: 
(λ (x : Bool)
   (λ (y : Bool)
     (λ (z : Bool)
       (λ (H1 : (== Bool x y))
         (λ (H2 : (== Bool y z))
           ((λ (H1 : (== Bool x z)) H1) ; by-rewrite H2 #:in H1 x=y -> x=z
            (new-elim
             (sym Bool x y (H1))
             (λ (g21 : Bool) (λ (g22 : (== Bool y g21)) (== Bool g21 z)))
             H2)))))))
 (∀ [x y z : Bool]
    (-> (== x y)
        (== y z)
        (== x z))))

;; actual correct raw term (for trans/in):
;; - H2 is the target of elim
(:: 
(λ (x : Bool)
   (λ (y : Bool)
     (λ (z : Bool)
       (λ (H1 : (== Bool x y))
         (λ (H2 : (== Bool y z))
           ((λ (H1 : (== Bool x z)) H1) ; by-rewrite H2 #:in H1 x=y -> x=z
            (new-elim
             H2
             (λ (g21 : Bool)
               (λ (g22 : (== Bool y g21))
                 (== Bool x g21)))
             H1)))))))
 (∀ [x y z : Bool]
    (-> (== x y)
        (== y z)
        (== x z))))


(define-theorem equality_of_functions_transits
  (forall (f : (-> Bool Bool)) (x y z : Bool)
          (-> (== (f x) (f y))
              (== (f y) (f z))
              (== (f x) (f z))))
  (by-intros f x y z H H0)
  (by-rewrite H0 #:in H) ; (* or rewrite <- H0 *)
  by-assumption)

(check-type equality_of_functions_transits
  : (forall (f : (-> Bool Bool)) (x y z : Bool)
          (-> (== (f x) (f y))
              (== (f y) (f z))
              (== (f x) (f z)))))

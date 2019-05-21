#lang cur
(require cur/stdlib/nat
         cur/stdlib/prop
         cur/stdlib/sugar
         cur/stdlib/equality
         cur/ntac/base
         cur/ntac/standard
         cur/ntac/rewrite
         "rackunit-ntac.rkt")

; tests dependent induction
; (see also sf/IndProp.rkt)

(define-datatype le : (-> [n : Nat] [m : Nat] Prop)
  [le-n : (-> [n : Nat] (le n n))]
  [le-s : (-> [n : Nat] [m : Nat] (le n m) (le n (s m)))])

(define (lt [n : Nat] [m : Nat]) (le (s n) m))

(define-theorem le_minus
;(ntac/trace
  (forall (k : Nat)
          (-> (lt k 1) (== k 0)))
  (by-intros k H)
  ; TODO: should be able to use (dependent) induction? (see coq docs)
;  (by-induction H)
  (by-inversion H #:as [(n0 H1 H2)
                        (n0 m0 le0 H1 H2)])
  (by-rewrite H1 #:in H2)
  (by-inversion H2 #:as H3)
  (by-rewrite H3)
  reflexivity
  (by-rewrite H1 #:in le0)
  (by-rewrite H2 #:in le0)
  (by-inversion le0 #:as n00 H3 H4)
  (by-rewrite H3 #:in H4)
  (by-inversion H4)
)

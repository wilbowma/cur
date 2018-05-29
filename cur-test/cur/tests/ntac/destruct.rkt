#lang cur
(require cur/stdlib/prop
         cur/stdlib/sugar
         cur/stdlib/nat
         cur/stdlib/bool
         (prefix-in b: cur/stdlib/bool)
         cur/ntac/base
         cur/ntac/standard
         cur/ntac/prop
         rackunit)

;; using built-ins 
;; n+1 doesnt work, must be 1+n
(:: (λ [n : Nat]
      (match n #:return (== Bool (nat-equal? (plus 1 n) 0) false)
        [z (refl Bool false)]
        [(s n-1) (refl Bool false)]))
    (Π [n : Nat]
       (== Bool (nat-equal? (plus 1 n) 0) false)))

(define (beq-nat [n : Nat])
  (match n #:in Nat
   [z
    (λ [m : Nat]
      (match m #:in Nat #:return Bool
       [z true]
       [(s m*) false]))]
   [(s n*)
     (λ [m : Nat]
       (match m #:in Nat #:return Bool
        [z false]
        [(s m*) (beq-nat n* m*)]))]))

;; with user-defined beq-nat
;; n+1 still doesnt work
(:: (λ [n : Nat]
      (match n #:return (== Bool (beq-nat (plus 1 n) 0) false)
        [z (refl Bool false)]
        [(s n-1) (refl Bool false)]))
    (Π [n : Nat]
       (== Bool (beq-nat (plus 1 n) 0) false)))

(define-theorem plus-1-neq-0
  (∀ [n : Nat] (== Bool (beq-nat (plus 1 n) 0) false))
  (by-intro n)
  (by-destruct n #:as [() (n-1)])
  simpl
  reflexivity
  ; ---------
  simpl
  reflexivity)

(:: (refl Bool false)
    (== Bool false false))

(:: (refl Bool true)
    (== Bool true true))

;; negb-invol, with built-ins, with match
;; TODO: not working
#;(:: (λ [b : Bool]
      (match b #:in Bool #:return (== Bool (not (not b)) b)
        [true (refl Bool true)]
        [false (refl Bool false)]))
    (∀ [b : Bool] (== Bool (not (not b)) b)))
;; with elim instead of match
(:: (λ [b : Bool]
      (new-elim b
                (λ [b : Bool] (== Bool (not (not b)) b))
                (refl Bool true)
                (refl Bool false)))
    (∀ [b : Bool] (== Bool (not (not b)) b)))

(define negb
  (λ [b : Bool]
    (new-elim b (λ [b : Bool] Bool) false true)))
(:: negb (-> Bool Bool))

(check-equal? (negb true) false)
(check-equal? (negb false) true)
(check-equal? (negb (negb true)) true)
(check-equal? (negb (negb false)) false)

(:: (λ [b : Bool]
      (new-elim b
                (lambda [b : Bool] (== Bool (negb (negb b)) b))
                (refl Bool true)
                (refl Bool false)))
    (∀ [b : Bool] (== Bool (negb (negb b)) b)))

(define-theorem negb-invol
  (forall [b : Bool] (== Bool (negb (negb b)) b))
  (by-intro b)
  (by-destruct/elim b)
  simpl
  reflexivity
  ; -----------
  simpl
  reflexivity)

(:: (λ [b : Bool] [c : Bool]
       (new-elim
        b
        (λ [b : Bool] (== Bool (and b c) (and c b)))
        (new-elim
         c
         (λ [c : Bool] (== Bool (and true c) (and c true)))
         (refl Bool (and true true))
         (refl Bool (and false true)))
        (new-elim
         c
         (λ [c : Bool] (== Bool (and false c) (and c false)))
         (refl Bool (and true false))
         (refl Bool (and false false)))))
    (∀ [b : Bool] [c : Bool]
       (== Bool (and b c) (and c b))))
  
;; nested destructs
(define-theorem and-commutative
  (∀ [b : Bool] [c : Bool]
     (== Bool (and b c) (and c b)))
  (by-intro b)
  (by-intro c)
  (by-destruct/elim b)
  ; ------------
  (by-destruct/elim c)
  reflexivity
  reflexivity
  ; -----------
  (by-destruct/elim c)
  reflexivity
  reflexivity)


;; uses intro+destruct version of intro tactic
(define-theorem plus-1-neq-0*
  (∀ [n : Nat] (== Bool (beq-nat (plus 1 n) 0) false))
  (by-intro n #:as [() (n-1)])
  reflexivity
  reflexivity)


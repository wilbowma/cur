#lang cur
(require (rename-in
          (except-in
           cur/stdlib/equality
           == refl)
          [ML-= ==]
          [ML-refl refl])
         cur/stdlib/sugar
         cur/stdlib/nat
         cur/stdlib/bool
         (prefix-in b: cur/stdlib/bool)
         cur/ntac/base
         cur/ntac/standard
         cur/ntac/ML-rewrite
         rackunit)

;; separate tests for destruct tactic

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

(check-equal? (and false false) false)
(check-equal? (and true false) false)
(check-equal? (and false true) false)
(check-equal? (and true true) true)

(define-theorem and-true-elim
  (∀ [b : Bool] [c : Bool]
     (-> (== Bool (and b c) true)
         (== Bool c true)))
  (by-intro b)
  (by-intro c)
  (by-destruct/elim b)
  ; subgoal 1 ----------------
  simpl
  (by-intro H)
  (by-rewrite H)
  reflexivity
  ; subgoal 2 ----------------
  (by-destruct/elim c)
  ; subgoal 2a --------
  simpl
  (by-intro H1)
  reflexivity
  ; subgoal 2b --------
  simpl
  (by-intro H2)
  by-assumption
)

(define-theorem zero-neq-one
  (∀ [n : Nat]
     (== Bool (nat-equal? 0 (plus 1 n)) false))
  (by-intro n #:as [() (n-1)])
  simpl
  reflexivity
  simpl
  reflexivity)

;; and-eq-orb, as manually written term
(::
 (λ [b : Bool] [c : Bool]
    (new-elim
     b
     (λ [b : Bool]
       (-> (== Bool (and b c) (or b c))
           (== Bool b c)))
     (λ [H : (== Bool c true)]
       (new-elim
        H
        (λ [c* : Bool] [true : Bool]
           (λ [H : (== Bool c* true)]
             (== Bool true c*)))
        (λ [true : Bool] (refl Bool true))))
     (λ [H : (== Bool false c)]
       H)))
 (∀ [b : Bool] [c : Bool]
    (-> (== Bool (and b c) (or b c))
        (== Bool b c))))

;; and-eq-orb, but more like ntac-generated term
;; even though, `true` works here as parameter name,
;; it wont work in the ntac-generated term for some reason
(::
 (λ [b : Bool] [c : Bool]
    (new-elim
     b
     (λ [b : Bool]
       (-> (== Bool (and b c) (or b c))
           (== Bool b c)))
     ;(λ [H : (== Bool c true)]
     (λ [H : (((== Bool) c) true)]
       ((new-elim
         H
         (λ [c* : Bool] [true : Bool]
            (λ [H : (== Bool c* true)]
              ;(== Bool true c*)))
              (Π [b : Bool]
                 (((== Bool) true) c*))))
         (λ [true : Bool] (λ [b : Bool] (refl Bool true))))
        b))
     ;(λ [H : (== Bool false c)]
     ;  H)))
     (λ [anon-parameter4558 : (((== Bool) false) c)]
       anon-parameter4558)))
 (∀ [b : Bool] [c : Bool]
    (-> (== Bool (and b c) (or b c))
        (== Bool b c))))

(define-theorem andb-eq-orb
  (∀ [b : Bool] [c : Bool]
     (-> (== Bool (and b c) (or b c))
         (== Bool b c)))
  (by-intro b)
  (by-intro c)
  (by-destruct/elim b)
  ; subgoal 1 --------
  simpl
  (by-intro H)
  (by-rewrite H)
  reflexivity
  ; subgoal 2 --------
  simpl
  by-intro
  by-assumption)

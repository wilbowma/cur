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
         cur/ntac/base
         cur/ntac/standard
         cur/ntac/ML-rewrite
         rackunit/turnstile+
         "rackunit-ntac.rkt")

;; separate tests for destruct tactic

;; using built-ins
;; n+1 doesnt work, must be 1+n
(check-type (λ [n : Nat]
              (match n #:return (== Bool (nat-equal? (plus 1 n) 0) false)
                     [z (refl Bool false)]
                     [(s n-1) (refl Bool false)]))
            : (Π [n : Nat]
                 (== Bool (nat-equal? (plus 1 n) 0) false)))

(define/rec/match beq-nat : Nat Nat -> Bool
  [z z => true]
  [z (s _) => false]
  [(s _) z => false]
  [(s x) (s y) => (beq-nat x y)])

;; with user-defined beq-nat
;; n+1 still doesnt work
(check-type (λ [n : Nat]
              (match n #:return (== Bool (beq-nat (plus 1 n) 0) false)
                     [z (refl Bool false)]
                     [(s n-1) (refl Bool false)]))
            : (Π [n : Nat]
                 (== Bool (beq-nat (plus 1 n) 0) false)))

(define-theorem plus-1-neq-0/builtin
  (∀ [n : Nat] (== Bool (nat-equal? (plus 1 n) 0) false))
  (by-intro n)
  (by-destruct n #:as [() (n-1)])
  simpl
  reflexivity
  ; ---------
  simpl
  reflexivity)

(define-theorem plus-1-neq-0
  (∀ [n : Nat] (== Bool (beq-nat (plus 1 n) 0) false))
  (by-intro n)
  (by-destruct n #:as [() (n-1)])
  simpl
  reflexivity
  ; ---------
  simpl
  reflexivity)

(check-type (refl Bool false) : (== Bool false false))

(check-type (refl Bool true) : (== Bool true true))

;; negb-invol, with built-in `not`,
;; with user-defined with match:
(check-type (λ [b : Bool]
              (match b #:as b #:in Bool #:return (== Bool (not (not b)) b)
               [true (refl Bool true)]
               [false (refl Bool false)]))
            : (∀ [b : Bool] (== Bool (not (not b)) b)))

;; with elim instead of match:
(check-type (λ [b : Bool]
              (new-elim b
                        (λ [b : Bool] (== Bool (not (not b)) b))
                        (refl Bool true)
                        (refl Bool false)))
            : (∀ [b : Bool] (== Bool (not (not b)) b)))

;; negb-invol, with user-defined negb instead of `not`
#;(define negb
  (λ [b : Bool]
    (new-elim b (λ [b : Bool] Bool) false true)))
(define/rec/match negb : Bool -> Bool
  [true => false]
  [false => true])
(check-type negb : (-> Bool Bool))

(check-type (negb true) : Bool -> false)
(check-type (negb false) : Bool -> true)
(check-type (negb (negb true)) : Bool -> true)
(check-type (negb (negb false)) : Bool -> false)

;; with new-elim
(check-type (λ [b : Bool]
              (new-elim b
                        (lambda [b : Bool] (== Bool (negb (negb b)) b))
                        (refl Bool true)
                        (refl Bool false)))
            : (∀ [b : Bool] (== Bool (negb (negb b)) b)))

;; with match
(check-type (λ [b : Bool]
              (match b #:as b #:return (== Bool (negb (negb b)) b)
               [true (refl Bool true)]
               [false (refl Bool false)]))
            : (∀ [b : Bool] (== Bool (negb (negb b)) b)))

;(define-theorem negb-invol
(check-ntac-trace
 (forall [b : Bool] (== Bool (negb (negb b)) b))
 (by-intro b)
 (by-destruct b)
 reflexivity
 ; -----------
 reflexivity
 ~>
 --------------------------------
 (Π (b : Bool) (ML-= Bool (negb (negb b)) b))

 b : Bool
 --------------------------------
 (ML-= Bool (negb (negb b)) b)

 --------------------------------
 (ML-= Bool true true)

 --------------------------------
 (ML-= Bool false false))

;; and-commutative, final proof term
(check-type (λ [b : Bool] [c : Bool]
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
            : (∀ [b : Bool] [c : Bool]
                 (== Bool (and b c) (and c b))))

;; and-commutative, using match
(check-type (λ [b : Bool] [c : Bool]
               (match b
                 #:as b
                 #:return (== Bool (and b c) (and c b))
                 [true
                  (match c
                    #:as c
                    #:return (== Bool (and true c) (and c true))
                    [true (refl Bool (and true true))]
                    [false (refl Bool (and false true))])]
                 [false
                  (match c
                    #:as c
                    #:return (== Bool (and false c) (and c false))
                    [true (refl Bool (and true false))]
                    [false (refl Bool (and false false))])]))
            : (∀ [b : Bool] [c : Bool]
                 (== Bool (and b c) (and c b))))

;; and-commutative, using match, eta-expanded
;; outer match return type must have named arg (c)
(check-type (λ [b : Bool] [c : Bool]
               ((match b
                  #:as b
                  #:return (Π [c : Bool] (== Bool (and b c) (and c b)))
                  [true
                   (λ [c : Bool]
                     (match c
                       #:as c
                       #:return (== Bool (and true c) (and c true))
                       [true (refl Bool (and true true))]
                       [false (refl Bool (and false true))]))]
                  [false
                   (λ [c : Bool]
                     (match c
                       #:as c
                       #:return (== Bool (and false c) (and c false))
                       [true (refl Bool (and true false))]
                       [false (refl Bool (and false false))]))])
               c))
            : (∀ [b : Bool] [c : Bool]
                 (== Bool (and b c) (and c b))))

;; nested destructs
(define-theorem and-commutative
  (∀ [b : Bool] [c : Bool]
     (== Bool (and b c) (and c b)))
  (by-intro b)
  (by-intro c)
  (by-destruct b)
  ; ------------
  (by-destruct c)
  reflexivity
  reflexivity
  ; -----------
  (by-destruct c)
  reflexivity
  reflexivity)

;; uses intro+destruct version of intro tactic
(define-theorem plus-1-neq-0*
  (∀ [n : Nat] (== Bool (beq-nat (plus 1 n) 0) false))
  (by-intros n #:as [() (n-1)])
  reflexivity
  reflexivity)

(check-type (and false false) : Bool -> false)
(check-type (and true false) : Bool -> false)
(check-type (and false true) : Bool -> false)
(check-type (and true true) : Bool -> true)

(define-theorem and-true-elim
  (∀ [b : Bool] [c : Bool]
     (-> (== Bool (and b c) true)
         (== Bool c true)))
  (by-intro b)
  (by-intro c)
  (by-destruct b)
  ; subgoal 1 ----------------
  (by-intro H)
  (by-rewrite H)
  reflexivity
  ; subgoal 2 ----------------
  (by-destruct c)
  ; subgoal 2a --------
  (by-intro H1)
  reflexivity
  ; subgoal 2b --------
  (by-intro H2)
  by-assumption)

(define-theorem zero-neq-one
  (∀ [n : Nat]
     (== Bool (nat-equal? 0 (plus 1 n)) false))
  (by-intros n #:as [() (n-1)])
  reflexivity
  ; -------
  reflexivity)

;; and-eq-orb, as manually written term
(check-type
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
 : (∀ [b : Bool] [c : Bool]
      (-> (== Bool (and b c) (or b c))
          (== Bool b c))))

;; and-eq-orb, but more like ntac-generated term
;; even though, `true` works here as parameter name,
;; it wont work in the ntac-generated term for some reason
(check-type
 (λ [b : Bool] [c : Bool]
    (new-elim
     b
     (λ [b : Bool]
       (-> (== Bool (and b c) (or b c))
           (== Bool b c)))
     ;(λ [H : (== Bool c true)]
     (λ [H : (== Bool c true)]
       ((new-elim
         H
         (λ [c* : Bool] [true : Bool]
            (λ [H : (== Bool c* true)]
              ;(== Bool true c*)))
              (Π [b : Bool]
                 (== Bool true c*))))
         (λ [true : Bool] (λ [b : Bool] (refl Bool true))))
        b))
     ;(λ [H : (== Bool false c)]
     ;  H)))
     (λ [anon-parameter4558 : (== Bool false c)]
       anon-parameter4558)))
 : (∀ [b : Bool] [c : Bool]
      (-> (== Bool (and b c) (or b c))
          (== Bool b c))))

(define-theorem andb-eq-orb
 (∀ [b : Bool] [c : Bool]
    (-> (== Bool (and b c) (or b c))
        (== Bool b c)))
 (by-intro b)
 (by-intro c)
 (by-destruct b)
 ; subgoal 1 --------
 (by-intro H)
 (by-rewrite H)
 reflexivity
 ; subgoal 2 --------
 by-intro
 by-assumption)

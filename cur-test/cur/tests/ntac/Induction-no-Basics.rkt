#lang cur

(require
 cur/stdlib/nat
 cur/stdlib/bool
 cur/stdlib/equality
 cur/stdlib/sugar
 cur/ntac/base
 cur/ntac/standard
 cur/ntac/rewrite
 (prefix-in ML: cur/ntac/ML-rewrite)
 rackunit/turnstile+
 "rackunit-ntac.rkt") 

;; examples from SF Ch 2: Induction.v
;; - like Induction.rkt but does not import defs from Basics.rkt

;; plus-n-0
(check-type
 (λ [n : Nat]
   (new-elim
    n
    (λ [n : Nat] (ML-= Nat n (plus n 0)))
    (ML-refl Nat 0)
    (λ [n-1 : Nat]
      (λ [IH : (ML-= Nat n-1 (plus n-1 0))]
        (new-elim
         IH
         (λ [n : Nat] [m : Nat]
            (λ [H : (ML-= Nat n m)]
              (ML-= Nat (s n) (s m))))
         (λ [n : Nat]
           (ML-refl Nat (s n))))))))
 : (∀ [n : Nat] (ML-= Nat n (plus n 0))))

(define-theorem plus-n-0/ML
  (∀ [n : Nat] (ML-= Nat n (plus n z)))
  (by-intro n)
  (by-induction n #:as [() (n-1 IH)])
  ;; subgoal 1
  ML:reflexivity
  ;; subgoal 2
  (ML:by-rewriteL IH)
  ML:reflexivity)

;; check empty application = no application
(define-theorem 1=1
  (ML-= Nat (s z) (s z))
  ML:reflexivity)

(check-type 1=1 : (ML-= Nat (s z) (s z)))
(check-type (1=1) : (ML-= Nat (s z) (s z)))
(check-type ((1=1)) : (ML-= Nat (s z) (s z)))

(define/rec/match minus : Nat Nat -> Nat
  [z _ => z]
;  [z (s _) => z]
  [n z => n]
  [(s n-1) (s m-1) => (minus n-1 m-1)])

(check-type (minus z z) : Nat -> 0)
(check-type (minus 1 1) : Nat -> 0)
(check-type (minus 2 1) : Nat -> 1)
(check-type (minus 3 1) : Nat -> 2)
(check-type (minus 4 1) : Nat -> 3)
(check-type (minus 5 1) : Nat -> 4)
(check-type (minus 2 2) : Nat -> 0)
(check-type (minus 3 2) : Nat -> 1)
(check-type (minus 4 2) : Nat -> 2)
(check-type (minus 5 2) : Nat -> 3)
(check-type (minus 3 3) : Nat -> 0)
(check-type (minus 4 3) : Nat -> 1)
(check-type (minus 5 3) : Nat -> 2)

;; requires simul double-recursion
(define-theorem minus-diag
  (∀ [n : Nat] (ML-= Nat (minus n n) 0))
  (by-intro n)
  (by-induction n #:as [() (n-1 IH)])
  ;; subgoal 1
  ML:reflexivity
  ;; subgoal 2
  (ML:by-rewrite IH)
  ML:reflexivity)

;; mult_0_r manually
(check-type
 (λ [n : Nat]
   (new-elim
    n
    (λ [n : Nat] (ML-= Nat (mult n 0) 0))
    (ML-refl Nat 0)
    (λ [n-1 : Nat]
      (λ [IH : (ML-= Nat (mult n-1 0) 0)]
        (new-elim
         IH
         (λ [a : Nat] [b : Nat]
            (λ [H : (ML-= Nat a b)]
              (ML-= Nat a b)))
         (λ [a : Nat]
           (ML-refl Nat a)))))))
 : (∀ [n : Nat] (ML-= Nat (mult n 0) 0)))

; mult_0_r, expanded
(check-type
 (λ [n : Nat]
   (new-elim
    n
    (λ [n : Nat] (ML-= Nat (mult n 0) 0))
    (ML-refl Nat 0)
    (λ [n-1 : Nat]
      (λ [IH : (ML-= Nat (mult n-1 0) 0)]
        ((new-elim
          IH
          (λ [a : Nat] [b : Nat]
             (λ [H : (ML-= Nat a b)]
               (Π [n-1 : Nat]
                  (ML-= Nat a b))))
          (λ [a : Nat]
            (λ [n-1 : Nat]
              (ML-refl Nat a))))
         n-1)))))
 : (∀ [n : Nat] (ML-= Nat (mult n 0) 0)))

(define-theorem mult_0_r
  (∀ [n : Nat] (ML-= Nat (mult n 0) 0))
  (by-intro n)
  (by-induction n #:as [() (n-1 IH)])
  ;; subgoal 1 ----
  ML:reflexivity
  ;; subgoal 2 ----
  (ML:by-rewrite IH)
  ML:reflexivity)

(define-theorem plus-n-Sm/ML
  (∀ [n : Nat] [m : Nat]
     (ML-= Nat (s (plus n m)) (plus n (s m))))
  (by-intro n)
  (by-intro m)
  (by-induction n #:as [() (n-1 IH)])
  ;; subgoal 1
  ML:reflexivity
  ;; subgoal 1
  (ML:by-rewrite IH)
  ML:reflexivity)

;; plus-comm, manually, without propagation
;; (plus-comm not possible at all with ML-=?)
#;(check-type
 (λ [n : Nat] [m : Nat]
    (new-elim
     n
     (λ [n : Nat] ML-= Nat (plus n m) (plus m n)))
     ; case n = z: ----------
     ; - need to prove:
     ;   (ML-= Nat (plus z m) (plus m z)) simpl->
     ;   (ML-= Nat m (plus m z))
     #;(plus-n-0/ML m)
     (new-elim
      (plus-n-0/ML m) ; (ML-= Nat m (plus m z))
      (λ [a : Nat] [b : Nat]
         (λ [H : (ML-= Nat a b)]
           (ML-= Nat a b)))
      (λ [b : Nat] (ML-refl Nat b)))
     ; case n =  s n-1: ----------
     ; - need to prove:
     ;   (ML-= Nat (plus (s n-1) m) (plus m (s n-1))) simpl->
     ;   (ML-= Nat (s (plus n-1 m)) (plus m (s n-1)))
     (λ [n-1 : Nat]
       (λ [IH : (ML-= Nat (plus n-1 m) (plus m n-1))]
         (new-elim
          (plus-n-Sm/ML m n-1) ; (ML-= Nat (s (plus m n-1)) (plus m (s n-1)))
          (λ [a : Nat] [b : Nat]
             (λ [H : (ML-= Nat a b)]
               (ML-= Nat (s (plus n-1 m)) b)))
          ; need to prove:
          ; (P (ML-= Nat (s (plus m n-1)) (s (plus m n-1)))) =
          ;    (ML-= Nat (s (plus n-1 m)) (s (plus m n-1))) =
          ;    add 1 to each element of IH
          (λ [b1 : Nat]
            (new-elim
             IH
             (λ [a2 : Nat] [b2 : Nat]
                (λ [H : (ML-= Nat a2 b2)]
                  (ML-= Nat (s a2) (s b2))))
             (λ [b2 : Nat]
               (ML-refl Nat (s b2)))))))))
 (∀ [n : Nat] [m : Nat]
    (ML-= Nat (plus n m) (plus m n))))

;; plus-comm, manually, with propagation
;; (doesnt work with ML-=)
#;(check-type
 (λ [n : Nat] [m : Nat]
    ((new-elim
      n
      (λ [n : Nat]
        (Π [m : Nat] (ML-= Nat (plus n m) (plus m n))))
      ; case n = z: ----------
      ; - need to prove:
      ;   (ML-= Nat (plus z m) (plus m z)) simpl->
      ;   (ML-= Nat m (plus m z))
      #;(plus-n-0/ML m)
      (λ [m : Nat]
        (new-elim
         (plus-n-0/ML m) ; (ML-= Nat m (plus m z))
         (λ [a : Nat] [b : Nat]
            (λ [H : (ML-= Nat a b)]
              (ML-= Nat a b)))
         (λ [b : Nat] (ML-refl Nat b))))
      ; case n =  s n-1: ----------
      ; - need to prove:
      ;   (ML-= Nat (plus (s n-1) m) (plus m (s n-1))) simpl->
      ;   (ML-= Nat (s (plus n-1 m)) (plus m (s n-1)))
      (λ [n-1 : Nat]
        (λ [IH : (ML-= Nat (plus n-1 m) (plus m n-1))]
          (λ [m : Nat]
            ((new-elim
              (plus-n-Sm/ML m n-1) ; (ML-= Nat (s (plus m n-1)) (plus m (s n-1)))
              (λ [a : Nat] [b : Nat]
                 (λ [H : (ML-= Nat a b)]
                   (Π [m : Nat]
                      (Π [n-1 : Nat]
                         (Π [IH : (ML-= Nat (plus n-1 m) (plus m n-1))]
                            (ML-= Nat (s (plus n-1 m)) b))))))
              ; need to prove:
              ; (P (ML-= Nat (s (plus m n-1)) (s (plus m n-1)))) =
              ;    (ML-= Nat (s (plus n-1 m)) (s (plus m n-1))) =
              ;    add 1 to each element of IH
              (λ [b1 : Nat]
                (λ [m : Nat]
                  (λ [n-1 : Nat]
                    (λ [IH : (ML-= Nat (plus n-1 m) (plus m n-1))]
                      (new-elim
                       IH
                       (λ [a2 : Nat] [b2 : Nat]
                          (λ [H : (ML-= Nat a2 b2)]
                            (ML-= Nat (s a2) (s b2))))
                       (λ [b2 : Nat]
                         (ML-refl Nat (s b2)))))))))
             m n-1 IH)))))
     m))
 (∀ [n : Nat] [m : Nat]
    (ML-= Nat (plus n m) (plus m n))))

;; plus-comm not possibl with ML-=??? (see above)
;; - must use PM-= (see below)
#;(define-theorem plus-comm
  (∀ [n : Nat] [m : Nat]
     (ML-= Nat (plus n m) (plus m n)))
  (by-intro n)
  (by-intro m)
  (by-induction n #:as [() (n-1 IH)])
  ; subgoal 1
  (ML:by-rewriteL plus-n-0/ML m)
  ML:reflexivity
  ; subgoal 2
  (ML:by-rewriteL plus-n-Sm/ML m n-1)
  (ML:by-rewrite IH)
  ML:reflexivity)

;; same as above, but using PM equality
(define-theorem plus-n-0
  (∀ [n : Nat] (== Nat n (plus n z)))
  (by-intro n)
  (by-induction n #:as [() (n-1 IH)])
  ;; subgoal 1
  reflexivity
  ;; subgoal 2
  (by-rewriteL IH)
  reflexivity)
(define-theorem plus-n-Sm
  (∀ [n : Nat] [m : Nat]
     (== Nat (s (plus n m)) (plus n (s m))))
  (by-intros n m)
  (by-induction n #:as [() (n-1 IH)])
  ;; subgoal 1
  reflexivity
  ;; subgoal 2
  (by-rewrite IH)
  reflexivity)

(define-theorem plus_comm
  (∀ [n : Nat] [m : Nat]
     (== Nat (plus n m) (plus m n)))
  (by-intro n)
  (by-intro m)
  (by-induction n #:as [() (n-1 IH)])
  ; subgoal 1
  (by-rewriteL plus-n-0 m)
  reflexivity
  ; subgoal 2
  (by-rewriteL plus-n-Sm m n-1)
  (by-rewrite IH)
  reflexivity)

(define/rec/match double : Nat -> Nat
  [z => z]
  [(s n-1) => (s (s (double n-1)))])

(check-type (double 0) : Nat -> 0)
(check-type (double 1) : Nat -> 2)
(check-type (double 1) : Nat -> 2)
(check-type (double 5) : Nat -> 10)
(check-type (double 10) : Nat -> 20)

(define-theorem double-plus
  (∀ [n : Nat] (== Nat (double n) (plus n n)))
  (by-intro n)
  (by-induction n #:as [() (n-1 IH)])
  ; subgoal 1
  reflexivity
  ; subgoal 2
  (by-rewriteL plus-n-Sm n-1 n-1)
  (by-rewrite IH)
  reflexivity)

;; copied from Basics.rkt
(define/rec/match negb : Bool -> Bool
  [true => false]
  [false => true])

(define/rec/match evenb : Nat -> Bool
  [z => true]
  [(s n-1) => (negb (evenb n-1))])

(check-type (evenb 1) : Bool -> false)
(check-type (evenb 2) : Bool -> true)
(check-type (evenb 10) : Bool -> true)
(check-type (evenb 11) : Bool -> false)


(define-theorem evenb_S
 (∀ [n : Nat]
    (== Bool (evenb (s n)) (negb (evenb n))))
 (by-intro n)
 (by-induction n #:as [() (n-1 IH)])
 ; goal 1
 reflexivity
 ; goal 2
 (by-rewrite IH)
; (by-rewrite negb-invol (evenb n-1)) ; evenb doesnt need this, see evenb2 below
 reflexivity)

(define-theorem negb-invol
  (forall [b : Bool] (== Bool (negb (negb b)) b))
  (by-intro b)
  (by-destruct b)
  ; -----------
  reflexivity
  ; -----------
  reflexivity)

;; TODO: support nested patterns
;; or just use explicit match
(define/rec/match evenb2 : Nat -> Bool
  [z => true]
  [(s z) => false]
  [(s (s n-2)) => (evenb2 n-2)])

(check-type (evenb2 1) : Bool -> false)
(check-type (evenb2 2) : Bool -> true)
(check-type (evenb2 10) : Bool -> true)
(check-type (evenb2 11) : Bool -> false)

(define-theorem evenb2_S
 (∀ [n : Nat]
    (== Bool (evenb2 (s n)) (negb (evenb2 n))))
 (by-intro n)
 (by-induction n #:as [() (n-1 IH)])
 ; goal 1
 reflexivity
 ; goal 2
 (by-rewrite IH)
 (by-rewrite negb-invol (evenb2 n-1))
 reflexivity)

;; prove using assert
(define-theorem mult-0-plus*
 (∀ [n : Nat] [m : Nat]
    (ML-= Nat (mult (plus 0 n) m) (mult n m)))
 (by-intros n m)
 (by-assert H (ML-= Nat (plus 0 n) n))
 ; proving H
 ML:reflexivity
 ; proving rest
 (ML:by-rewrite H)
 ML:reflexivity)

;; plus-rearrange
(define-theorem plus-rearrange
  (∀ [n : Nat] [m : Nat] [p : Nat] [q : Nat]
     (== Nat (plus (plus n m) (plus p q))
               (plus (plus m n) (plus p q))))
  (by-intros n m p q)
  (by-assert H (== Nat (plus n m) (plus m n)))
  ; proof of H
  (by-rewrite plus_comm n m)
  reflexivity
  ; proof of rest
  (by-rewrite H)
  reflexivity)

;; plus-assoc
(define-theorem plus-assoc
  (∀ [n : Nat] [m : Nat] [p : Nat]
     (== Nat (plus n (plus m p)) (plus (plus n m) p)))
  (by-intros n m p)
  (by-induction n #:as [() (n-1 IH)])
  ; goal 1, n = 0
  reflexivity
  ; goal 2, n = (s n-1)
  (by-rewrite IH)
  reflexivity)

(define-theorem plus-swap
  (∀ [n : Nat] [m : Nat] [p : Nat]
     (== Nat (plus n (plus m p))
               (plus m (plus n p))))
  (by-intros n m p)
  (by-rewrite plus-assoc n m p)
  (by-assert H (== Nat (plus n m) (plus m n)))
  ; proof of H
  (by-rewrite plus_comm n m)
  reflexivity
  ; proof of rest
  (by-rewrite H)
  (by-rewriteL plus-assoc m n p)
  reflexivity)

;; plus-swap2 subterm1, just H proof
(check-type
 (λ [n : Nat] [m : Nat] [p : Nat]
    ((λ (H : (== Nat (plus m n) (plus n m)))
       H)
     (new-elim
      (sym Nat (plus m n) (plus n m) (plus_comm m n))
      (λ (g123214 : Nat)
        (λ (g123215 : (== Nat (plus n m) g123214))
          (== Nat g123214 (plus n m))))
      (refl Nat (plus n m)))))
 :  (∀ [n : Nat] [m : Nat] [p : Nat]
       (== Nat (plus m n) (plus n m))))

;; plus-swap2 subterm2, use of H
(check-type
 (λ [n : Nat] [m : Nat] [p : Nat]
    (λ (H : (== Nat (plus m n) (plus n m)))
      (new-elim
       H
       (λ (tgt : Nat)
         (λ (H : (== Nat (plus m n) tgt))
           (== Nat (plus tgt p) (plus m (plus n p)))))
       (new-elim
        (plus-assoc m n p)
        (λ (g122603 : Nat)
          (λ (g122604 : (== Nat (plus m (plus n p)) g122603))
            (== Nat g122603 (plus m (plus n p)))))
        (refl Nat (plus m (plus n p)))))))
 :  (∀ [n : Nat] [m : Nat] [p : Nat]
       (-> (== Nat (plus m n) (plus n m))
           (== Nat (plus (plus n m) p) (plus m (plus n p))))))

;; use replace instead of assert
(define-theorem plus-swap2
  (∀ [n : Nat] [m : Nat] [p : Nat]
     (== Nat (plus n (plus m p))
               (plus m (plus n p))))
  (by-intros n m p)
  (by-rewrite plus-assoc n m p)
  (by-replace Nat (plus n m) (plus m n)) ; H
  (by-rewriteL plus-assoc m n p)
  reflexivity
  ; proof of H
  (by-rewrite plus_comm m n)
  reflexivity)

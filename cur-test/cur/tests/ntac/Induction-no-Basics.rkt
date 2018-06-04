#lang cur

(require
 rackunit
 cur/stdlib/nat
 cur/stdlib/prop
 cur/stdlib/sugar
 cur/ntac/base
 cur/ntac/standard
 cur/ntac/prop)


;; plus-n-0
(::
 (λ [n : Nat]
   (new-elim
    n
    (λ [n : Nat] (== Nat n (plus n 0)))
    (refl Nat 0)
    (λ [n-1 : Nat]
      (λ [IH : (== Nat n-1 (plus n-1 0))]
        (new-elim
         IH
         (λ [n : Nat] [m : Nat]
            (λ [H : (== Nat n m)]
              (== Nat (s n) (s m))))
         (λ [n : Nat]
           (refl Nat (s n))))))))
 (∀ [n : Nat] (== Nat n (plus n 0))))

(define-theorem plus-n-0
  (∀ [n : Nat] (== Nat n (plus n z)))
  (by-intro n)
  simpl ;; this step doesnt do anything except get everything in expanded form
  (by-induction n #:as [() (n-1 IH)])
  ;; subgoal 1
  reflexivity
  ;; subgoal 2
  simpl
  (by-rewriteL IH)
  reflexivity)

;; check empty application = no application
(define-theorem 1=1
  (== Nat (s z) (s z))
  reflexivity)

(:: 1=1 (== Nat (s z) (s z)))
(:: (1=1) (== Nat (s z) (s z)))
(:: ((1=1)) (== Nat (s z) (s z)))

;; (define minus
;;   (λ [n : Nat] [m : Nat]
;;      (new-elim
;;       n
;;       (λ [n : Nat] Nat)
;;       0
;;       (λ [n-1 : Nat] [ih1 : Nat]
;;          (new-elim
;;           m
;;           (λ [n : Nat] Nat)
;;           n
;;           (λ [m-1 : Nat] [ih2 : Nat]
;;              (new-elim
;;               ih2
;;               (λ [n : Nat] Nat)
;;               0
;;               (λ [n* : Nat] [ih : Nat]
;;                  n*))))))))

;; (check-equal? (minus 1 1) 0)
;; (check-equal? (minus 2 1) 1)
;; (check-equal? (minus 3 1) 2)
;; (check-equal? (minus 4 1) 3)
;; (check-equal? (minus 5 1) 4)
;; (check-equal? (minus 2 2) 0)
;; (check-equal? (minus 3 2) 1)
;; (check-equal? (minus 4 2) 2)
;; (check-equal? (minus 5 2) 3)
;; (check-equal? (minus 3 3) 0)
;; (check-equal? (minus 4 3) 1)
;; (check-equal? (minus 5 3) 2)

(define minus2
  (λ [n : Nat] [m : Nat]
     (new-elim
      m
      (λ [n : Nat] Nat)
      n
      (λ [m-1 : Nat] [ih : Nat]
         (new-elim
          ih
          (λ [n : Nat] Nat)
          0
          (λ [x : Nat] [ih : Nat]
             x))))))

;; (check-equal? (minus2 1 1) 0)
;; (check-equal? (minus2 2 1) 1)
;; (check-equal? (minus2 3 1) 2)
;; (check-equal? (minus2 4 1) 3)
;; (check-equal? (minus2 5 1) 4)
;; (check-equal? (minus2 2 2) 0)
;; (check-equal? (minus2 3 2) 1)
;; (check-equal? (minus2 4 2) 2)
;; (check-equal? (minus2 5 2) 3)
;; (check-equal? (minus2 3 3) 0)
;; (check-equal? (minus2 4 3) 1)
;; (check-equal? (minus2 5 3) 2)


;; doesnt work, can't use recur outside of match
#;(: minus/recur (-> Nat Nat Nat))
#;(define (minus/recur n m)
  (new-elim
   n
   (λ [n : Nat] Nat)
   0
   (λ [n-1 : Nat] [ih1 : Nat]
      (new-elim
       m
       (λ [n : Nat] Nat)
       n
       (λ [m-1 : Nat] [ih2 : Nat]
          ((recur minus/recur) n-1 m-1))))))

;; requires simul double-recursion
#;(define-theorem minus-diag
  (∀ [n : Nat] (== Nat (minus2 n n) 0))
  (by-intro n)
;  simpl
  display-focus
  (by-induction n #:as [() (n-1 IH)])
  display-focus
  ;; subgoal 1
  simpl
  reflexivity
  display-focus
  ;; subgoal 2
  simpl ; cur doesnt simpl (n+1 - n+1 = 0) to (n - n = 0)
  display-focus
  (by-rewrite IH)
  display-focus
  reflexivity)

;; mult_0_r manually
(::
 (λ [n : Nat]
   (new-elim
    n
    (λ [n : Nat] (== Nat (mult n 0) 0))
    (refl Nat 0)
    (λ [n-1 : Nat]
      (λ [IH : (== Nat (mult n-1 0) 0)]
        (new-elim
         IH
         (λ [a : Nat] [b : Nat]
            (λ [H : (== Nat a b)]
              (== Nat a b)))
         (λ [a : Nat]
           (refl Nat a)))))))
 (∀ [n : Nat] (== Nat (mult n 0) 0)))

; mult_0_r, expanded
(::
 (λ [n : Nat]
   (new-elim
    n
    (λ [n : Nat] (== Nat (mult n 0) 0))
    (refl Nat 0)
    (λ [n-1 : Nat]
      (λ [IH : (== Nat (mult n-1 0) 0)]
        ((new-elim
          IH
          (λ [a : Nat] [b : Nat]
             (λ [H : (== Nat a b)]
               (Π [n-1 : Nat]
                  (((== Nat) a) b))))
          (λ [a : Nat]
            (λ [n-1 : Nat]
              (refl Nat a))))
         n-1)))))
 (∀ [n : Nat] (== Nat (mult n 0) 0)))

(define-theorem mult_0_r
  (∀ [n : Nat] (== Nat (mult n 0) 0))
  (by-intro n)
  simpl
  (by-induction n #:as [() (n-1 IH)])
  simpl
  reflexivity
  simpl
  (by-rewrite IH)
  reflexivity)
                
(define-theorem plus-n-Sm
  (∀ [n : Nat] [m : Nat]
     (== Nat (s (plus n m)) (plus n (s m))))
  (by-intro n)
  (by-intro m)
  simpl
  (by-induction n #:as [() (n-1 IH)])
  ;; subgoal 1
  simpl
  reflexivity
  ;; subgoal 1
  simpl
  (by-rewrite IH)
  reflexivity)
 

;; plus-comm, manually, without propagation
;; (doesnt work)
#;(::
 (λ [n : Nat] [m : Nat]
    (new-elim
     n
     (λ [n : Nat] (== Nat (plus n m) (plus m n)))
     ; case n = z: ----------
     ; - need to prove:
     ;   (== Nat (plus z m) (plus m z)) simpl-> 
     ;   (== Nat m (plus m z))
     #;(plus-n-0 m)
     (new-elim     
      (plus-n-0 m) ; (== Nat m (plus m z))
      (λ [a : Nat] [b : Nat]
         (λ [H : (== Nat a b)]
           (== Nat a b)))
      (λ [b : Nat] (refl Nat b)))
     ; case n =  s n-1: ----------
     ; - need to prove:
     ;   (== Nat (plus (s n-1) m) (plus m (s n-1))) simpl->
     ;   (== Nat (s (plus n-1 m)) (plus m (s n-1)))
     (λ [n-1 : Nat]
       (λ [IH : (== Nat (plus n-1 m) (plus m n-1))]
         (new-elim
          (plus-n-Sm m n-1) ; (== Nat (s (plus m n-1)) (plus m (s n-1)))
          (λ [a : Nat] [b : Nat]
             (λ [H : (== Nat a b)]
               (== Nat (s (plus n-1 m)) b)))
          ; need to prove:
          ; (P (== Nat (s (plus m n-1)) (s (plus m n-1)))) = 
          ;    (== Nat (s (plus n-1 m)) (s (plus m n-1))) = 
          ;    add 1 to each element of IH
          (λ [b1 : Nat]
            (new-elim
             IH
             (λ [a2 : Nat] [b2 : Nat]
                (λ [H : (== Nat a2 b2)]
                  (== Nat (s a2) (s b2))))
             (λ [b2 : Nat]
               (refl Nat (s b2))))))))))
 (∀ [n : Nat] [m : Nat]
    (== Nat (plus n m) (plus m n))))

;; plus-comm, manually, with propagation
;; (doesnt work with ==)
#;(::
 (λ [n : Nat] [m : Nat]
    ((new-elim
      n
      (λ [n : Nat]
        (Π [m : Nat] (== Nat (plus n m) (plus m n))))
      ; case n = z: ----------
      ; - need to prove:
      ;   (== Nat (plus z m) (plus m z)) simpl-> 
      ;   (== Nat m (plus m z))
      #;(plus-n-0 m)
      (λ [m : Nat]
        (new-elim
         (plus-n-0 m) ; (== Nat m (plus m z))
         (λ [a : Nat] [b : Nat]
            (λ [H : (== Nat a b)]
              (== Nat a b)))
         (λ [b : Nat] (refl Nat b))))
      ; case n =  s n-1: ----------
      ; - need to prove:
      ;   (== Nat (plus (s n-1) m) (plus m (s n-1))) simpl->
      ;   (== Nat (s (plus n-1 m)) (plus m (s n-1)))
      (λ [n-1 : Nat]
        (λ [IH : (== Nat (plus n-1 m) (plus m n-1))]
          (λ [m : Nat]
            ((new-elim
              (plus-n-Sm m n-1) ; (== Nat (s (plus m n-1)) (plus m (s n-1)))
              (λ [a : Nat] [b : Nat]
                 (λ [H : (== Nat a b)]
                   (Π [m : Nat]
                      (Π [n-1 : Nat]
                         (Π [IH : (== Nat (plus n-1 m) (plus m n-1))]
                            (== Nat (s (plus n-1 m)) b))))))
              ; need to prove:
              ; (P (== Nat (s (plus m n-1)) (s (plus m n-1)))) = 
              ;    (== Nat (s (plus n-1 m)) (s (plus m n-1))) = 
              ;    add 1 to each element of IH
              (λ [b1 : Nat]
                (λ [m : Nat]
                  (λ [n-1 : Nat]
                    (λ [IH : (== Nat (plus n-1 m) (plus m n-1))]
                      (new-elim
                       IH
                       (λ [a2 : Nat] [b2 : Nat]
                          (λ [H : (== Nat a2 b2)]
                            (== Nat (s a2) (s b2))))
                       (λ [b2 : Nat]
                         (refl Nat (s b2)))))))))
             m n-1 IH)))))
     m))
 (∀ [n : Nat] [m : Nat]
    (== Nat (plus n m) (plus m n))))

;; doesnt work with == (see above)
;; - must use coq= (see below)
#;(define-theorem plus-comm
  (∀ [n : Nat] [m : Nat]
     (== Nat (plus n m) (plus m n)))
  (by-intro n)
  (by-intro m)
  simpl
  (by-induction n #:as [() (n-1 IH)])
  ; subgoal 1
  simpl
  (by-rewriteL/thm/expand plus-n-0 m)
  reflexivity
  ; subgoal 2
  display-focus
  simpl
  display-focus
  (by-rewriteL/thm/expand plus-n-Sm m n-1)
  display-focus
  (by-rewrite IH)
  display-focus
  reflexivity)



;; same as above, but using coq=
(require cur/ntac/coqrewrite
         cur/stdlib/coqeq)
(define-theorem plus-n-0/coq
  (∀ [n : Nat] (coq= Nat n (plus n z)))
  (by-intro n)
  simpl ;; this step doesnt do anything except get everything in expanded form
  (by-induction n #:as [() (n-1 IH)])
  ;; subgoal 1
  coq-reflexivity
  ;; subgoal 2
  simpl
  (by-coq-rewriteL IH)
  coq-reflexivity)
(define-theorem plus-n-Sm/coq
  (∀ [n : Nat] [m : Nat]
     (coq= Nat (s (plus n m)) (plus n (s m))))
  (by-intro n)
  (by-intro m)
  simpl
  (by-induction n #:as [() (n-1 IH)])
  ;; subgoal 1
  simpl
  coq-reflexivity
  ;; subgoal 1
  simpl
  (by-coq-rewrite IH)
  coq-reflexivity)

(define-theorem plus_comm/coq
  (∀ [n : Nat] [m : Nat]
     (coq= Nat (plus n m) (plus m n)))
  (by-intro n)
  (by-intro m)
  simpl
  (by-induction n #:as [() (n-1 IH)])
  ; subgoal 1
  simpl
  (by-coq-rewriteL/thm/expand plus-n-0/coq m)
  coq-reflexivity
  ; subgoal 2
  simpl
  (by-coq-rewriteL/thm/expand plus-n-Sm/coq m n-1)
  (by-coq-rewrite IH)
  coq-reflexivity)


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

#;     (new-elim
      (s n-1)
      (λ [n : Nat] Nat)
      (s n-1)
      (λ [m-1 : Nat] [ih : Nat]
         (new-elim
          ih
          (λ [n : Nat] Nat)
          0
          (λ [x : Nat] [ih : Nat]
             x))))

#;(typed-elim 
 (typed-elim 
  n-1 
  (typed-λ (n : Nat) Nat) 
  (typed-app s n-1) 
  (typed-λ (m-1 : Nat) 
           (typed-λ (ih : Nat) 
                    (typed-elim 
                     ih (typed-λ (n : Nat) Nat)
                     z 
                     (typed-λ (x : Nat) 
                              (typed-λ (ih : Nat) 
                                       x))))))
 (typed-λ (n : Nat) Nat) 
 z 
 (typed-λ (x : Nat) (typed-λ (ih : Nat) x)))


;; ;; mult_0_r manually
;; (::
;;  (λ [n : Nat]
;;    (new-elim
;;     n
;;     (λ [n : Nat] (== Nat (mult n 0) 0))
;;     (refl Nat 0)
;;     (λ [n-1 : Nat]
;;       (λ [IH : (== Nat (mult n-1 0) 0)]
;;         (new-elim
;;          IH
;;          (λ [a : Nat] [b : Nat]
;;             (λ [H : (== Nat a b)]
;;               (== Nat a b)))
;;          (λ [a : Nat]
;;            (refl Nat a)))))))
;;  (∀ [n : Nat] (== Nat (mult n 0) 0)))

;; ; mult_0_r, expanded
;; (::
;;  (λ [n : Nat]
;;    (new-elim
;;     n
;;     (λ [n : Nat] (== Nat (mult n 0) 0))
;;     (refl Nat 0)
;;     (λ [n-1 : Nat]
;;       (λ [IH : (== Nat (mult n-1 0) 0)]
;;         ((new-elim
;;           IH
;;           (λ [a : Nat] [b : Nat]
;;              (λ [H : (== Nat a b)]
;;                (Π [n-1 : Nat]
;;                   (((== Nat) a) b))))
;;           (λ [a : Nat]
;;             (λ [n-1 : Nat]
;;               (refl Nat a))))
;;          n-1)))))
;;  (∀ [n : Nat] (== Nat (mult n 0) 0)))

;; (define-theorem mult_0_r
;;   (∀ [n : Nat] (== Nat (mult n 0) 0))
;;   (by-intro n)
;;   simpl
;;   (by-induction n #:as [() (n-1 IH)])
;;   display-focus
;;   simpl
;;   reflexivity
;;   display-focus
;;   simpl
;;   display-focus
;;   (by-rewrite IH)
;;   display-focus
;;   reflexivity)
                
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


(define-theorem plus_comm
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

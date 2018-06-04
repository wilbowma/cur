#lang cur

(require
 rackunit
 "Basics.rkt"
 cur/stdlib/prop
 cur/stdlib/sugar
 cur/ntac/base
 cur/ntac/standard
 cur/ntac/prop)


;; plus-n-0
(::
 (λ [n : nat]
   (new-elim
    n
    (λ [n : nat] (== nat n (plus n 0)))
    (refl nat 0)
    (λ [n-1 : nat]
      (λ [IH : (== nat n-1 (plus n-1 0))]
        (new-elim
         IH
         (λ [n : nat] [m : nat]
            (λ [H : (== nat n m)]
              (== nat (S n) (S m))))
         (λ [n : nat]
           (refl nat (S n))))))))
 (∀ [n : nat] (== nat n (plus n 0))))

(define-theorem plus-n-0
  (∀ [n : nat] (== nat n (plus n 0)))
  (by-intro n)
  simpl ;; this step doesnt do anything except get everything in expanded form
  (by-induction n #:as [() (n-1 IH)])
  ;; subgoal 1
  reflexivity
  ;; subgoal 2
  simpl
  (by-rewriteL IH)
  reflexivity)

#;(define-theorem minus-diag
  (∀ [n : nat] (== nat (minus n n) 0))
  (by-intro n)
;  simpl
  (by-induction n #:as [() (n-1 IH)])
  display-focus
  ;; subgoal 1
  simpl
  display-focus
  reflexivity
  display-focus
  ;; subgoal 2
  simpl
  display-focus
  (by-rewrite IH)
  display-focus
  reflexivity)

;IH
#;(typed-app
 (typed-app 
  (typed-app == nat) 
  (typed-elim 
   n-1 
   (typed-λ (n : nat) nat) 
   O 
   (typed-λ (m* : nat)
            (typed-λ (ih : nat) 
                     (typed-elim 
                      n-1
                      (typed-λ (n : nat) nat)
                      n-1 
                      (typed-λ (m* : nat) 
                               (typed-λ (ih* : nat) 
                                        (typed-elim
                                         ih*
                                         (typed-λ (n : nat) nat)
                                         O
                                         (typed-λ (n* : nat)
                                                  (typed-λ (ih : nat)
                                                           n*))))))))))
 O)


#;(typed-app 
 (typed-app 
  (typed-app == nat) 
  (typed-elim 
   (typed-elim 
    n-1 
    (typed-λ (n : nat) nat) 
    (typed-app S n-1) 
    (typed-λ (m* : nat)
             (typed-λ (ih* : nat) 
                      (typed-elim 
                       ih* 
                       (typed-λ (n : nat) nat) 
                       O 
                       (typed-λ (n* : nat) (typed-λ (ih : nat) n*))))))
   (typed-λ (n : nat) nat) 
   O 
   (typed-λ (n* : nat) 
            (typed-λ (ih : nat) 
                     n*)))) 
 O)

(define-theorem mult_0_r
  (∀ [n : nat] (== nat (mult n 0) 0))
  (by-intro n)
  simpl
  (by-induction n #:as [() (n-1 IH)])
  simpl
  reflexivity
  simpl
  (by-rewrite IH)
  reflexivity)

#lang cur
(require cur/stdlib/sugar
         cur/stdlib/equality
         cur/ntac/base
         cur/ntac/standard
         cur/ntac/rewrite
         "Basics.rkt"
         "Induction.rkt"
         "../rackunit-ntac.rkt")

;; examples from SF Ch 3: Lists.v
;; - only up to rev-length

(data natprod : 0 Type
      [pair : (-> nat nat natprod)])

(:: (pair 3 5) natprod)

(define/rec/match fst : natprod -> nat
  [(pair x _) => x])

(define/rec/match snd : natprod -> nat
  [(pair _ y) => y])

(check-equal? (fst (pair 3 5)) 3)

(define (swap-pair [p : natprod])
  (match p #:return natprod
   [(pair x y) (pair y x)]))

(define (swap-pair/elim [p : natprod])
  (new-elim
   p
   (λ [p : natprod] natprod)
   (λ [x : nat] [y : nat]
      (pair y x))))

(define-theorem surjective-pairing
  (∀ [n : nat] [m : nat]
     (== natprod (pair n m)
                   (pair (fst (pair n m))
                         (snd (pair n m)))))
  (by-intros n m)
  reflexivity)

(::
 (λ [p : natprod]
   (new-elim
    p
    (λ [p : natprod]
      (== natprod p (pair (fst p) (snd p))))
    (λ [n : nat] [m : nat]
       (refl natprod (pair n m)))))
 (∀ [p : natprod]
    (== natprod p (pair (fst p) (snd p)))))

(define-theorem surjective-pairing2
  (∀ [p : natprod]
     (== natprod p (pair (fst p) (snd p))))
  (by-intro p)
  (by-destruct p #:as [(n m)])
  reflexivity)

(define-theorem surjective-pairing3 ; use induction instead of destruct
  (∀ [p : natprod]
     (== natprod p (pair (fst p) (snd p))))
  (by-intro p)
  (by-induction p #:as [(n m)])
  reflexivity)

(define-theorem snd-fst-is-swap
  (∀ [p : natprod]
     (== natprod (pair (snd p) (fst p)) (swap-pair p)))
  (by-intro p)
  (by-destruct p #:as [(n m)])
  reflexivity)

(define-theorem fst-swap-is-snd
  (∀ [p : natprod]
     (== nat (fst (swap-pair p)) (snd p)))
  (by-intro p)
  (by-destruct p #:as [(n m)])
  reflexivity)

(data natlist : 0 Type
      [nil : natlist]
      [cons : (-> nat natlist natlist)])

(define-syntax lst
  (syntax-parser
    [(_) #'nil]
    [(_ h . rst) #'(cons h (lst . rst))]))

(define mylist (cons 1 (cons 2 (cons 3 nil))))

(define/rec/match repeat : nat [n : nat] -> natList
  [O => nil]
  [(S count-1) => (cons n (repeat count-1 n))])

(define/rec/match length : natlist -> nat
  [nil => 0]
  [(cons h t) => (S (length t))])

(define/rec/match app : natlist [l2 : natlist] -> natlist
  [nil => l2]
  [(cons h t) => (cons h (app t l2))])

(define/rec/match hd : [default : nat] natlist -> nat
  [nil => default]
  [(cons h _) => h])

(define/rec/match tl : natlist -> natlist
  [nil => nil]
  [(cons _ t) => t])


;; exercises

(define/rec/match nonzeros : natlist -> natlist
  [nil => nil]
  [(cons (~O) tl) => (nonzeros tl)]
  [(cons h tl) => (cons h (nonzeros tl))])

(check-equal?
 (nonzeros (cons 0 (cons 1 (cons 0 (cons 2 (cons 3 (cons 0 (cons 0 nil))))))))
 (cons 1 (cons 2 (cons 3 nil))))

;; bags

(define bag natlist)

(define/rec/match count : [v : nat] bag -> nat
  [nil => 0]
  [(cons h t) => (match (beq-nat v h) #:return nat
                   [true (S (count v t))]
                   [false (count v t)])])

(check-equal? (count 1 (lst 1 2 3 1 4 1)) 3)
(check-equal? (count 6 (lst 1 2 3 1 4 1)) 0)

(define sum app)
(check-equal? (count 1 (sum (lst 1 2 3) (lst 1 4 1))) 3)
(define add cons)
(check-equal? (count 1 (add 1 (lst 1 4 1))) 3)

#;(define/rec/match member : [v : nat] bag -> bool
    [nil => false]
    [(cons h t) => (orb (beq-nat h v) (member v t))])
(define (member [v : nat] [s : bag]) ; nonfixpoint member def
  (negb (beq-nat (count v s) 0)))
(check-equal? (member 1 (lst 1 4 1)) true)
(check-equal? (member 2 (lst 1 4 1)) false)

(define/rec/match remove-one : [v : nat] bag -> bag
  [nil => nil]
  [(cons h t) => (match (beq-nat h v) #:return bag
                  [true t]
                  [false (cons h (remove-one v t))])])

(check-equal? (count 5 (remove-one 5 (lst 2 1 5 4 1))) 0)
(check-equal? (count 5 (remove-one 5 (lst 2 1 4 1))) 0)
(check-equal? (count 4 (remove-one 5 (lst 2 1 4 5 1 4))) 2)
(check-equal? (count 5 (remove-one 5 (lst 2 1 5 4 5 1 4))) 1)

;; lists again

(define-theorem nil-app
  (forall [l : natlist] (== natlist (app nil l) l))
  (by-intro l)
  reflexivity)

; sub1
(define/rec/match pred : nat -> nat
  [O => O]
  [(S n-1) => n-1])

(define-theorem tl-length-pred
  (∀ [l : natlist] (== nat (pred (length l)) (length (tl l))))
  (by-intro l)
  (by-induction l #:as [() (h t IH)])
  ; goal 1
  reflexivity
  ; goal 2
  reflexivity)

(define-theorem app-assoc
  (∀ [l1 : natlist] [l2 : natlist] [l3 : natlist]
     (== natlist (app (app l1 l2) l3) (app l1 (app l2 l3))))
  (by-intros l1 l2 l3)
  simpl
  (by-induction l1 #:as [() (n t IH)])
  ; nil
  reflexivity
  ; cons
  simpl
  (by-rewrite IH)
  reflexivity)

(define/rec/match rev : natlist -> natlist
  [nil => nil]
  [(cons h t) => (app (rev t) (cons h nil))])

(define-theorem app-length
  (∀ [l1 : natlist] [l2 : natlist]
     (== nat (length (app l1 l2))
               (plus (length l1) (length l2))))
  (by-intros l1 l2)
  simpl
  (by-induction l1 #:as [() (h t IH)])
  ; nil
  reflexivity
  ; cons
  simpl
  (by-rewrite IH)
  reflexivity)

(define-theorem rev-length
  (∀ [l : natlist]
     (== nat (length (rev l)) (length l)))
  (by-intro l)
  (by-induction l #:as [() (h t IH)])
  ; nil
  reflexivity
  ; cons
;  (by-rewrite app-length (rev t) (cons h nil))
  (by-rewrite app-length)
  (by-rewrite plus-comm)
  (by-rewrite IH)
  reflexivity)

(define-theorem app_nil_r
  (∀ [l : natlist] (== natlist (app l nil) l))
  (by-intro l)
  (by-induction l #:as (() (h t IH)))
  reflexivity
  (by-rewrite IH)
  reflexivity)

(define-theorem rev_app_distr
  (∀ [l1 : natlist] [l2 : natlist]
     (== natlist (rev (app l1 l2)) (app (rev l2) (rev l1))))
  (by-intros l1 l2)
  (by-induction l1 #:as [() (h t IH)])
  ;---
  (by-rewrite app_nil_r)
  reflexivity
  ;----
  (by-rewrite IH)
  (by-rewrite app-assoc)
  reflexivity)

(define-theorem rev_invol
  (∀ [l : natlist] (== natlist (rev (rev l)) l))
  (by-intro l)
  (by-induction l #:as [() (h t IH)])
  reflexivity
  (by-rewrite rev_app_distr)
  (by-rewrite IH)
  reflexivity)

(define-theorem app_assoc4
  (∀ [l1 : natlist] [l2 : natlist] [l3 : natlist] [l4 : natlist]
     (== natlist
         (app l1 (app l2 (app l3 l4)))
         (app (app (app l1 l2) l3) l4)))
  (by-intros l1 l2 l3 l4)
  (by-rewrite app-assoc)
  (by-rewrite app-assoc)
  reflexivity)

(define-theorem nonzeros_app
  (forall [l1 : natlist] [l2 : natlist]
          (== natlist
              (nonzeros (app l1 l2))
              (app (nonzeros l1) (nonzeros l2))))
  (by-intros l1 l2)
  (by-induction l1 #:as [() (h t ih)])
  reflexivity
  (by-rewrite ih)
  reflexivity)

(define/rec/match beq-natlist : natlist natlist -> bool
  [nil nil => true]
  [nil (cons _ _) => false]
  [(cons _ _) nil => false]
  [(cons h1 t1) (cons h2 t2) => (andb (beq-nat h1 h2) (beq-natlist t1 t2))])

(check-equal? (beq-natlist nil nil) true)
(check-equal? (beq-natlist (lst 1 2 3) (lst 1 2 3)) true)
(check-equal? (beq-natlist (lst 1 2 3) (lst 1 2 4)) false)

(define-theorem beq_nat_refl
  (∀ [n : nat] (== bool true (beq-nat n n)))
  (by-intro n)
  (by-induction n #:as [() (n-1 ih)])
  reflexivity
  (by-rewriteL ih)
  reflexivity)

(define-theorem beq_natlist_refl
  (∀ [l : natlist] (== bool true (beq-natlist l l)))
  (by-intro l)
  (by-induction l #:as [() (h t ih)])
  reflexivity
  (by-rewriteL ih)
  (by-rewriteL beq_nat_refl)
  reflexivity)  


;; bags

(define-theorem count_member_nonzero
  (forall [s : bag] (== bool (leb 1 (count 1 (cons 1 s))) true))
  (by-intro s)
  reflexivity)

(define-theorem ble_n_Sn
  (∀ [n : nat] (== bool (leb n (S n)) true))
  (by-intro n)
  (by-induction n #:as [() (n-1 ih)])
  reflexivity
  (by-rewrite ih)
  reflexivity)

(define-theorem remove_decreases_count
  (∀ [s : bag]
     (== bool (leb (count 0 (remove-one 0 s)) (count 0 s)) true))
  (by-intro s)
  (by-induction s #:as [() (h t ih)])
  ; 1 ---
  reflexivity
  ; 2 ---
  (by-destruct h #:as [() (n-1)])
  ; 2a ---
  (by-rewrite ble_n_Sn)
  reflexivity
  ; 2b ---
  (by-rewrite ih)
  reflexivity)

(define-theorem bag-count-sum
  (∀ [s1 : bag] [s2 : bag] [n : nat]
     (== nat (count n (sum s1 s2)) (plus (count n s1) (count n s2))))
  (by-intros s1 s2 n)
  (by-induction s1 #:as [() (h t ih)])
  ; 1---
  reflexivity
  ; 2---
  (by-destruct (beq-nat n h))
  ;; 2a ---
  (by-rewrite ih)
  reflexivity
  ;; 2b ---
  (by-rewrite ih)
  reflexivity)

(define-theorem rev-injective
  (∀ [l1 : natlist] [l2 : natlist]
     (-> (== natlist (rev l1) (rev l2))
         (== natlist l1 l2)))
  (by-intros l1 l2 H)
  (by-rewriteL rev_invol l1)
  (by-rewrite H)
  (by-rewrite rev_invol)
  reflexivity)
    
(define-datatype natoption : Type
  [Some : (→ nat natoption)]
  [None : natoption])

(define/rec/match nth-error : natlist [n : nat] -> natoption
  [nil => None]
  [(cons h t) => (match (beq-nat n 0) #:return natoption
                        [true (Some h)]
                        [false (nth-error t (pred n))])])

(check-equal? (nth-error (lst 4 5 6 7) 0) (Some 4))
(check-equal? (nth-error [lst 4 5 6 7] 3) (Some 7))
(check-equal? (nth-error [lst 4 5 6 7] 9) None)

(define/rec/match option-elim : [d : nat] natoption -> nat
  [(Some n) => n]
  [None => d])

(define/rec/match hd-opt : natlist -> natoption
  [nil => None]
  [(cons h _) => (Some h)])

(define-theorem option-elim-hd
  (∀ [l : natlist] [default : nat]
     (== nat (hd default l) (option-elim default (hd-opt l))))
  (by-intros l default)
  (by-destruct l #:as [() (h t)])
  reflexivity
  reflexivity)

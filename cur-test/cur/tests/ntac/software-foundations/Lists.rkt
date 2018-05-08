#lang cur
(require cur/stdlib/sugar
         cur/stdlib/nat
         rackunit)

;; examples from SF Ch 3: Lists.v
;; - only up to rev-length

(data natprod : 0 Type
      [pair : (-> Nat Nat natprod)])

(:: (pair 3 5) natprod)

(define (fst [p : natprod])
  (match p #:return Nat
   [(pair x y) x]))

(define (snd [p : natprod])
  (match p #:return Nat
   [(pair x y) y]))

(check-equal? (fst (pair 3 5)) 3)

(define (swap-pair [p : natprod])
  (match p #:return natprod
   [(pair x y) (pair y x)]))

(define (swap-pair/elim [p : natprod])
  (new-elim
   p
   (λ [p : natprod] natprod)
   (λ [x : Nat] [y : Nat]
      (pair y x))))

(require
 cur/stdlib/equality
 cur/ntac/base
 cur/ntac/standard
 cur/ntac/rewrite)

(define-theorem surjective-pairing
  (∀ [n : Nat] [m : Nat]
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
    (λ [n : Nat] [m : Nat]
       (refl natprod (pair n m)))))
 (∀ [p : natprod]
    (== natprod p (pair (fst p) (snd p)))))

(define-theorem surjective-pairing2
  (∀ [p : natprod]
     (== natprod p (pair (fst p) (snd p))))
  (by-intro p)
  (by-destruct/elim p #:as [(n m)])
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
  (by-destruct/elim p #:as [(n m)])
  reflexivity)

(define-theorem fst-swap-is-snd
  (∀ [p : natprod]
     (== Nat (fst (swap-pair p)) (snd p)))
  (by-intro p)
  (by-destruct/elim p #:as [(n m)])
  reflexivity)

(data natlist : 0 Type
      [nil : natlist]
      [cons : (-> Nat natlist natlist)])

(define mylist (cons 1 (cons 2 (cons 3 nil))))

(define (repeat [count : Nat] [n : Nat])
  (match count #:return natlist
    [z nil]
    [(s count-1) (cons n (repeat count-1 n))]))

(define (length [l : natlist])
  (match l #:return Nat
   [nil 0]
   [(cons h t) (s (length t))]))

(define (app [l1  : natlist][l2 : natlist])
  (match l1 #:return natlist
   [nil l2]
   [(cons h t) (cons h (app t l2))]))

(define (hd [def : Nat] [l : natlist])
  (match l #:return Nat
   [nil def]
   [(cons h t) h]))

(define (tl [l : natlist])
  (match l #:return natlist
   [nil nil]
   [(cons h t) t]))

(define-theorem nil-app
  (forall [l : natlist] (== natlist (app nil l) l))
  (by-intro l)
  reflexivity)

; sub1
(define pred
  (λ [n : Nat]
    (new-elim
     n
     (λ [n : Nat] Nat)
     0
     (λ [n* : Nat] [ih : Nat]
        n*))))

(define-theorem tl-length-pred
  (∀ [l : natlist] (== Nat (pred (length l)) (length (tl l))))
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

(define (rev [l : natlist])
  (match l #:return natlist
   [nil nil]
   [(cons h t) (app (rev t) (cons h nil))]))

(define-theorem app-length
  (∀ [l1 : natlist] [l2 : natlist]
     (== Nat (length (app l1 l2))
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

#;(define-theorem rev-length
  (∀ [l : natlist]
     (== Nat (length (rev l)) (length l)))
  (by-intro l)
  simpl
  (by-induction l #:as [() (h t IH)])
  ; nil
  reflexivity
  ; cons
  simpl
  display-focus
  (by-rewrite/thm/normalized app-length (rev t) (cons h nil))
  display-focus
)

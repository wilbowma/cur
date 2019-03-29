#lang cur
(require cur/stdlib/sugar
         cur/stdlib/equality
         cur/ntac/base
         cur/ntac/standard
         cur/ntac/rewrite
         "Basics.rkt"
         rackunit/turnstile
         "../rackunit-ntac.rkt")

;; part 1 of 3 of Software Foundations Poly.v chapter

(data boollist : 0 Type
      [bool-nil : boollist]
      [bool-cons : (-> bool boollist boollist)])

;; * = "full" version; as opposed to hidden-arg version
(define-datatype list [X : Type] : Type
  [nil* : (list X)]
  [cons* : (-> X (list X) (list X))])

(:: list (-> Type Type))
(:: (nil* nat) (list nat))
(:: (cons* nat 3 (nil* nat)) (list nat))
(:: nil* (∀ [X : Type] (list X)))
(:: cons* (∀ [X : Type] (-> X (list X) (list X))))

(:: (cons* nat 2 (cons* nat 1 (nil* nat)))
    (list nat))

(define/rec/match repeat : [X : Type] [x : X] nat -> (list X)
  [O => (nil* X)]
  [(S count-1) => (cons* X x (repeat X x count-1))])

(check-equal? (repeat nat 4 2)
              (cons* nat 4 (cons* nat 4 (nil* nat))))
(check-equal? (repeat bool false 1) (cons* bool false (nil* bool)))

(define-datatype mumble : Type
  [a : mumble]
  [b : (-> mumble nat mumble)]
  [c : mumble])
(define-datatype grumble [X : Type] : Type
  [d : (-> mumble (grumble X))]
  [e : (-> X (grumble X))])

(define-implicit nil = nil* 1)
(define-implicit cons = cons* 1 _ inf)
(define-implicit repeat* = repeat 1)

;; TODO: define-implicit needs:
;; - define pattern abbreviations
;; - allow recursive references
(define/rec/match app_ : [X : Type] (list X) (list X) -> (list X)
  [(nil* _) l2 => l2]
  [(cons* _ h t) l2 => (cons h (app_ X t l2))])

(define-implicit app = app_ 1)

(define/rec/match rev_ : [X : Type] (list X) -> (list X)
  [(nil* _) => nil]
  [(cons* _ h t) => (app (rev_ X t) (cons h nil))])

(define/rec/match length_ : [X : Type] (list X) -> nat
  [(nil* _) => 0]
  [(cons* _ h t) => (S (length_ X t))])

(define-implicit rev = rev_ 1)
(define-implicit length = length_ 1)

(check-equal? (rev (cons 1 (cons 2 nil)))
              (cons 2 (cons 1 nil)))

(check-equal? (rev (cons true nil)) (cons true nil))
(check-equal? (length (cons 1 (cons 2 (cons 3 nil)))) 3)

(define-theorem app-nil-r
  (∀ [Y : Type] [l : (list Y)] (== (app l (nil* Y)) l))
  (by-intros Y l)
  (by-induction l #:as [() (x xs IH)])
  ;; 1: nil case
  reflexivity
  ;; 2: cons case
  (by-rewrite IH)
  reflexivity)

;app-nil-r raw term
(::
 (λ (Z : Type)
   (λ (l : (list Z))
     (new-elim
      l
      (λ (l : (list Z)) (== (list Z) (app_ Z l (nil* Z)) l))
      (refl (list Z) (nil* Z))
      (λ (x : Z)
        (λ (xs : (list Z))
          (λ (IH : (== (list Z) (app_ Z xs (nil* Z)) xs))
            (new-elim
             (sym (list Z) (app_ Z xs (nil* Z)) xs (IH))
             (λ (g27 : (list Z))
               (λ (g28 : (== (list Z) xs g27))
                 (== (list Z) (cons* Z x g27) (cons* Z x xs))))
             (refl (list Z) (cons* Z x xs)))))))))
 (∀ [Y : Type] [l : (list Y)] (== (list Y) (app_ Y l (nil* Y)) l)))

(define-theorem eq-remove-S
  (∀ [n : nat] [m : nat]
     (-> (== nat n m)
         (== nat (S n) (S m))))
  (by-intros n m H)
  (by-rewrite H)
  reflexivity)

;; this example tests these tactics:
;; - by-apply, elim-False, by-inversion
;; - destruct of non-innermost binding
(define-theorem length-app-sym
  (∀ [X : Type] [l1 : (list X)] [l2 : (list X)] [x : X] [n : nat]
     (-> (== nat (length_ X (app_ X l1 l2)) n)
         (== nat (length_ X (app_ X l1 (cons* X x l2))) (S n))))
  (by-intros X l1)
  (by-induction l1 #:as [() (x xs IH)])
  ; induction 1: nil -----
  (by-intros l2 x n H)
  (by-rewrite H)
  reflexivity
  ; induction 2: cons -----
  (by-intros l2 x n H)
  (by-apply eq-remove-S)
  (by-destruct n #:as [() (n-1)])
  ;; destruct 2a: z -----
  (by-inversion H)
  elim-False
  (by-assumption)
  ;; destruct 2b: (s n-1) -----
  (by-apply IH)
  (by-inversion H #:as H0)
  (by-rewrite H0)
  reflexivity)

(check-type
 length-app-sym
 : (∀ [X : Type] [l1 : (list X)] [l2 : (list X)] [x : X] [n : nat]
      (-> (== nat (length_ X (app_ X l1 l2)) n)
          (== nat (length_ X (app_ X l1 (cons* X x l2))) (S n)))))

;; for some reason, if plus from Basics is used in
;; theorem app-length twice below, it fails when a nat
;; from that plus is compared with a nat referenced here.
;; So re-define plus
(define/rec/match another-plus : nat [m : nat] -> nat
  [O => m]
  [(S n-1) => (S (another-plus n-1 m))])

(define-theorem plus-n-Sm
  (Π [n : nat] [m : nat]
     (== (S (another-plus n m)) (another-plus n (S m))))
  by-intros
  (by-induction n #:as [() (n-1 IH)])
  ; 1
  reflexivity
  ; 2
  (by-rewrite IH)
  reflexivity)

(define-theorem app-assoc
  (∀ [A : Type] [l1 : (list A)] [l2 : (list A)] [l3 : (list A)]
     (== (app l1 (app l2 l3))
         (app (app l1 l2) l3)))
  (by-intros X l1 l2 l3)
  (by-induction l1 #:as [() (x xs IH)])
  ;1
  reflexivity
  ;2
  (by-rewrite IH)
  reflexivity)

(define-theorem app-length
  (∀ [X : Type] [l1 : (list X)] [l2 : (list X)]
     (== (length (app l1 l2))
         (another-plus (length l1) (length l2))))
  (by-intros X l1 l2)
  (by-induction l1 #:as [() (x xs IH)])
  ; 1
  reflexivity
  ; 2
  (by-rewrite IH)
  reflexivity)

(define-theorem app-length-twice
  (Π [X : Type] [n : nat] [l : (list X)]
     (-> (== (length l) n)
         (== (length (app l l)) (another-plus n n))))
  (by-intros X n l)
  (by-generalize n)
  (by-induction l #:as [() (x xs IH)])
  ; induction 1
  (by-intros n H)
  (by-rewriteL H)
  reflexivity
  ; induction 2
  (by-intros n H)
  (by-destruct n #:as [() (n-1)])
  ; destruct 2a
  ; simpl
  (by-inversion H)
  elim-False
  by-assumption
  ; destruct 2b
  (by-inversion H #:as H1)
  (by-apply eq-remove-S)
  (by-rewriteL plus-n-Sm)
;  (by-rewrite H1)
  (by-apply length-app-sym)
  (by-apply IH)
  (by-apply H1))

(check-type
 app-length-twice
 : (Π [X : Type] [n : nat] [l : (list X)]
      (-> (== (length l) n)
          (== (length (app l l)) (another-plus n n)))))

(define-theorem rev-app-distr
  (∀ [X : Type] [l1 : (list X)] [l2 : (list X)]
     (== (rev (app l1 l2))
         (app (rev l2) (rev l1))))
  (by-intros X l1 l2)
  (by-induction l1 #:as [() (x xs IH)])
  ; 1
  (by-rewrite app-nil-r)
  reflexivity
  ; 2
  (by-rewrite IH)
  (by-rewrite app-assoc)
  reflexivity)

(check-type rev-app-distr
 : (∀ [X : Type] [l1 : (list X)] [l2 : (list X)]
      (== (rev (app l1 l2))
          (app (rev l2) (rev l1)))))

(define-theorem cons-rev
  (∀ [Y : Type] [l : (list Y)] [n : Y]
     (== (cons n (rev l))
         (rev (app l (cons n nil)))))
  (by-intros Y l n)
  (by-induction l #:as [() (x xs IH)])
  reflexivity      ; 1
  (by-rewriteL IH) ; 2
  reflexivity)

(check-type cons-rev
  : (∀ [X : Type] [l : (list X)] [n : X]
       (== (cons n (rev l))
           (rev (app l (cons n nil))))))

;; cons-rev raw term
(check-type
 (λ (Y : Type)
   (λ (l : (list Y))
     (λ (n : Y)
       ((new-elim
         l
         (λ (l : (list Y))
           (==
            (list Y)
            (cons* Y n (rev_ Y l))
            (rev_ Y (app_ Y l (cons* Y n (nil* Y))))))
         (refl (cons* Y n (nil* Y)))
         (λ (x : Y)
           (λ (xs : (list Y))
             (λ (IH
                 :
                 (==
                  (list Y)
                  (cons* Y n (rev_ Y xs))
                  (rev_ Y (app_ Y xs (cons* Y n (nil* Y))))))
               (new-elim
                (IH)
                (λ (g310 : (list Y))
                  (λ (g311 : (== (list Y) (cons* Y n (rev_ Y xs)) g310))
                    (==
                     (list Y)
                     (cons* Y n (app_ Y (rev_ Y xs) (cons* Y x (nil* Y))))
                     (app_ Y g310 (cons* Y x (nil* Y))))))
                (refl
                 (cons*
                  Y
                  n
                  (app_ Y (rev_ Y xs) (cons* Y x (nil* Y))))))))))))))
 : (∀ [X : Type] [l : (list X)] [n : X]
      (== (cons n (rev l))
          (rev (app l (cons n nil))))))

;; application of cons-rev
(check-type 
 (λ (X : Type) (x : X) (xs : (list X))
    (cons-rev X (rev_ X xs) x))
 : (∀ [X : Type] [x : X] [xs : (list X)]
      (== (cons x (rev (rev_ X xs)))
          (rev (app (rev_ X xs) (cons x nil))))))

;; this example tests need for unexpand in elim forms
(define-theorem rev-invol
  (∀ [X : Type] [l : (list X)]
     (== (rev (rev l)) l))
  by-intros
  (by-induction l #:as [() (x xs IH)])
  reflexivity            ; 1
  (by-rewriteL cons-rev) ; 2
  (by-rewrite IH)
  reflexivity)

(check-type rev-invol
  : (∀ [X : Type] [l : (list X)]
       (== (rev (rev l)) l)))

;; rev-invol, raw term
(check-type
 (λ (X : Type)
   (l : (list X))
   (new-elim
    l
    (λ (l : (list X)) (== (list X) (rev_ X (rev_ X l)) l))
    (refl (nil* X))
    (λ (x : X)
      (λ (xs : (list X))
        (λ (IH : (== (list X) (rev_ X (rev_ X xs)) xs))
          (new-elim
           (cons-rev X (rev_ X xs) x)
           (λ (g315 : (list X))
             (λ (g316 : (== (list X) (cons* X x (rev_ X (rev_ X xs))) g315))
               (== (list X) g315 (cons* X x xs))))
           (new-elim
            (sym (list X) (rev_ X (rev_ X xs)) xs (IH))
            (λ (g317 : (list X))
              (λ (g318 : (== (list X) xs g317))
                (== (list X) (cons* X x g317) (cons* X x xs))))
            (refl (cons* X x xs)))))))))
  : (∀ [X : Type] [l : (list X)]
       (== (rev (rev l)) l)))

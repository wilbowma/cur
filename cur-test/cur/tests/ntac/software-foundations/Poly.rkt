#lang cur
(require cur/stdlib/sugar
         cur/stdlib/equality
         cur/ntac/base
         cur/ntac/standard
         cur/ntac/rewrite
         "Basics.rkt"
         rackunit/turnstile
         "../rackunit-ntac.rkt")

(data boollist : 0 Type
      [bool-nil : boollist]
      [bool-cons : (-> bool boollist boollist)])

;; * = "full" version; as opposed to hidden-arg version
(define-datatype list [X : Type] : -> Type
  [nil* : (list X)]
  [cons* : X (list X) -> (list X)])

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
(define-datatype grumble [X : Type] -> Type
  [d : mumble -> (grumble X)]
  [e : X -> (grumble X)])

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
  (by-induction l #:as [() (x xs IH)] #:params (Y))
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
  (by-induction l1 #:as [() (x xs IH)] #:params (X))
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
  (by-inversion H #:extra-names H0)
  (by-rewrite H0)
  reflexivity)

(check-type
 length-app-sym
 : (∀ [X : Type] [l1 : (list X)] [l2 : (list X)] [x : X] [n : nat]
      (-> (== nat (length_ X (app_ X l1 l2)) n)
          (== nat (length_ X (app_ X l1 (cons* X x l2))) (S n)))))

(define-theorem length-app-sym/abbrv
  (∀ [X : Type] [l1 : (list X)] [l2 : (list X)] [x : X] [n : nat]
     (-> (== (length (app l1 l2)) n)
         (== (length (app l1 (cons x l2))) (S n))))
  (by-intros X l1)
  (by-induction l1 #:as [() (x xs IH)] #:params (X))
  ; induction 1: nil -----
  by-intros
  (by-rewrite H204)
  reflexivity
  ; induction 2: cons -----
  by-intros
  (by-apply eq-remove-S)
  (by-destruct n #:as [() (n-1)])
  ;; destruct 2a: z -----
  (by-inversion H207)
  elim-False
  (by-assumption)
  ;; destruct 2b: (s n-1) -----
  (by-apply IH)
  (by-inversion H207)
  (by-rewrite H209)
  reflexivity)

(check-type
 length-app-sym/abbrv
 : (∀ [X : Type] [l1 : (list X)] [l2 : (list X)] [x : X] [n : nat]
      (-> (== (length (app l1 l2)) n)
          (== (length (app l1 (cons x l2))) (S n)))))


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
  (by-induction l1 #:as [() (x xs IH)] #:params (X))
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
  (by-induction l1 #:as [() (x xs IH)] #:params (X))
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
  (by-induction l #:as [() (x xs IH)] #:params (X))
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
  (by-inversion H #:extra-names H1)
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
  (by-induction l1 #:as [() (x xs IH)] #:params (X))
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


#lang s-exp "redex-core.rkt"

;; Use racket libraries over your dependently typed code!?!?
;; TODO: actually, I'm not sure this should work quite as well as it
;; seems to with check-equal?
(require rackunit)

;; Look, syntax extension!
(define-syntax (-> syn)
  (syntax-case syn ()
    [(_ t1 t2)
     (with-syntax ([(x) (generate-temporaries '(1))])
       #'(forall (x : t1) t2))]))

(data nat : Type
  (z : nat)
  (s : (-> nat nat)))

(define nat-is-now-a-type
  (lambda (y : (-> nat nat))
    (lambda (x : nat) (y x))))

;; Lexical scoping! I can reuse the name nat!
(define nat-is-just-a-name (lambda (nat : Type) nat))

(data true : Type (T : true))

(data false : Type)

;; Real meta-programming! Syntax is just data.
(define-syntax (inhabit-type syn)
  (syntax-case syn (true false nat)
    [(_ true) #'T]
    [(_ nat) #'z]
    [(_ false)
     (raise-syntax-error 'inhabit
       "Actually, this type is unhabited" syn)]
    [(_ t)
     (raise-syntax-error 'inhabit
       "Sorry, this type is too much for me" syn)]))

(define hmm (inhabit-type true))
(check-equal? hmm T)

#;(define is-this-inhabited (inhabit-type false))

;; Reuse some familiar syntax
(define y (lambda (x : true) x))
(define (y1 (x : true)) x)
(define (y2 (x1 : true) (x2 : true)) x1)
(check-equal? (y2 T T) T)

;; Write functions on inductive data
(define (plus (n1 : nat) (n2 : nat))
  (case n1
    [z n2]
    ;; TODO: Add macro to enable writing this line as:
    ;; [(s x) (s (s x))]
    [s (λ (x : nat) (s (s x)))]))

(define four (plus (s (s z)) (s (s z))))
(check-equal? four (s (s (s z))))

;; It's annoying to have to write things explicitly curried
;; Macros to the rescue
(define-syntax forall*
  (syntax-rules (:)
    [(_ (a : t) (ar : tr) ... b)
     (forall (a : t)
        (forall* (ar : tr) ... b))]
    [(_ b) b]))

(define-syntax lambda*
  (syntax-rules (:)
    [(_ (a : t) (ar : tr) ... b)
     (lambda (a : t)
       (lambda* (ar : tr) ... b))]
    [(_ b) b]))

(data and : (forall* (A : Type) (B : Type) Type)
  (conj : (forall* (A : Type) (B : Type)
            (x : A) (y : B) (and A B))))

;; Prove interesting theorems!

#|
;; TODO: Well, case can't seem to type-check non-Type inductives. So I
;; guess we'll do a church encoding
(define (thm:and-is-symmetric
          (x : (forall* (P : Type) (Q : Type)
                 ;; TODO: Can't use -> for the final clause because generated
                 ;; name has to match name in proof.
                 (ab : (and P Q))
                 (and P Q))))
  T)

(define proof:and-is-symmetric
  (lambda* (P : Type) (Q : Type) (ab : (and P Q))
    (case ab
      (conj (lambda* (S : Type) (R : Type) (s : S) (r : R) (conj R S r s))))))

(check-equal? (thm:and-is-symmetric proof:and-is-symmetric) T)
|#
(define and^ (forall* (A : Type) (B : Type)
                      (forall* (C :  Type) (f : (forall* (a : A) (b : B) C))
                               C)))
(define fst (lambda* (A : Type) (B : Type) (ab : (and^ A B)) (ab A (lambda* (a : A) (b : B) a))))
(define snd (lambda* (A : Type) (B : Type) (ab : (and^ A B)) (ab B (lambda* (a : A) (b : B) b))))
(define conj^ (lambda* (A : Type) (B : Type)
                       (a : A) (b : B)
                       (lambda* (C : Type) (f : (-> A (-> B C)))
                                (f a b))))
(define (thm:and^-is-symmetric
          (x : (forall* (P : Type) (Q : Type)
                 (ab : (and^ P Q))
                 (and^ P Q))))
  T)
(define proof:and^-is-symmetric
  (lambda* (P : Type) (Q : Type) (ab : (and^ P Q))
    (conj^ Q P (snd P Q ab) (fst P Q ab))))

(check-equal? T (thm:and^-is-symmetric proof:and^-is-symmetric))

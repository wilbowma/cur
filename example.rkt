#lang s-exp "redex-core.rkt"

;; Use racket libraries over your dependently typed code!?!?
;; TODO: actually, I'm not sure this should work quite as well as it
;; seems to with check-equal?
(require rackunit)

;; -------------------
;; Define inductive data

(data true : Type (T : true))

(data false : Type)

;; -------------------
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

;; -------------------
;; Lexical scoping! I can reuse the name nat!

(define nat-is-just-a-name (lambda (nat : Type) nat))

;; -------------------
;; Reuse some familiar syntax

(define y (lambda (x : true) x))
(define (y1 (x : true)) x)
(define (y2 (x1 : true) (x2 : true)) x1)

;; -------------------
;; Unit test dependently typed code!

(check-equal? (y2 T T) T)

;; -------------------
;; Write functions on inductive data
;; TODO: This is not plus! Plus require recursion and I don't have
;; recursion!
;(define (plus (n1 : nat) (n2 : nat))
;  (case n1
;    [z n2]
;    ;; TODO: Add macro to enable writing this line as:
;    ;; [(s x) (s (s x))]
;    [s (λ (x : nat) (s (s x)))]))
;
;(define four (plus (s (s z)) (s (s z))))
;(check-equal? four (s (s (s z))))

(define (add1 (n1 : nat))
  (case n1
    [z (s z)]
    ;; TODO: Add macro to enable writing this line as:
    ;; [(s x) (s (s x))]
    [s (λ (x : nat) (s (s x)))]))

(define two (add1 (s z)))
(check-equal? two (s (s z)))

;; -------------------
;; It's annoying to have to write things explicitly curried
;; Macros to the rescue!

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

;; -------------------
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

;; -------------------
;; Gee, I wish there was a special syntax for theorems and proofs so I could think of
;; them as seperate from types and programs.

(define-syntax-rule (define-theorem name prop)
  (define (name (x : prop)) T))

(define-syntax-rule (qed thm pf)
  (check-equal? T (thm pf)))

(define-theorem thm:and^-is-symmetric^
  (forall* (P : Type) (Q : Type) (ab : (and^ P Q)) (and^ P Q)))

(qed thm:and^-is-symmetric^ proof:and^-is-symmetric)

;; -------------------
;; Gee, I wish I had special syntax for defining types like I do for
;; defining functions.

(define-syntax-rule (define-type (name (a : t) ...) body)
  (define name (forall* (a : t) ... body)))

(define-type (not (A : Type)) (-> A false))

(define-type (and^^ (A : Type) (B : Type))
  (forall* (C :  Type) (f : (forall* (a : A) (b : B) C)) C))
#|
TODO: Can't seem to pattern match on a inductive with 0 constructors...
should result in a term of any type, I think.
(define-theorem thm:absurdidty
  (forall (P : Type) (A : Type) (-> (and^ A (not A)) P)))

(define (proof:absurdidty (P : Type) (A : Type) (a*nota : (and^ A (not A)))
  ((snd A (not A) a*nota) (fst A (not A) a*nota))))
|#

;; -------------------
;; Automate theorem proving! With real meta-programming, syntax is just data.

(define-syntax (inhabit-type syn)
  (syntax-case syn (true false nat forall :)
    [(_ true) #'T]
    [(_ nat) #'z]
    [(_ false)
     (raise-syntax-error 'inhabit
       "Actually, this type is unhabited" syn)]
    ;; TODO: We want all forall*s to be expanded by this point. Should
    ;; look into Racket macro magic to expand syn before matching on it.
    [(_ (forall (x : t0) t1))
     ;; TODO: Should carry around assumptions to enable inhabhit-type to use
     ;; them
     #'(lambda (x : t0) (inhabit-type t1))]
    [(_ t)
     (raise-syntax-error 'inhabit
       "Sorry, this type is too much for me" syn)]))

(define-theorem thm:true-is-proveable true)
(qed thm:true-is-proveable (inhabit-type true))

(define-theorem thm:anything-implies-true (forall (P : Type) true))
(qed thm:true-is-proveable (inhabit-type (forall (P : Type) true)))

#;(define is-this-inhabited? (inhabit-type false))


;; -------------------
;; Unit test your theorems before proving them!

(define-syntax ->*
  (syntax-rules ()
    [(->* a) a]
    [(->* a a* ...)
     (-> a (->* a* ...))]))

;; TODO: Ought to have some syntactic sugar for doing this.
;; Or a different representation of theorems.
(define type-thm:true?
  (forall* (A : Type) (B : Type) (P : Type)
    ;; If A implies P and (and A B) then P
    (->* (-> A P) (and^ A B) P)))

(define-theorem thm:true? type-thm:true?)

(qed (lambda (x : (type-thm:true? true true true)) T)
     ;; TODO: inhabit-type ought to be able to reduce (type-thm:true? true true true)
     ;; but can't. Maybe instead there should be a reduce tactic/macro.
     (inhabit-type (forall (a : (-> true true))
                   (forall (f : (and^ true true))
                   true))))

;; TODO: Interopt with Racket at runtime via contracts?!?!

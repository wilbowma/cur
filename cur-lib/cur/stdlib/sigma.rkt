#lang s-exp "../main.rkt"

(require
 (only-in "../main.rkt" [Type typed-Type] [#%app typed-app])
 "sugar.rkt")

(provide
 Σ0
 Σ1
 Σ

 pair0
 pair1
 pair

 fst0
 fst1
 fst

 snd0
 snd1
 snd)

(data Σ0 : 2 (Π (A : (Type 0)) (P : (-> A (Type 0))) (Type 0))
      (pair0 : (Π (A : (Type 0)) (P : (-> A (Type 0))) (a : A) (b : (P a)) (Σ0 A P))))

(data Σ1 : 2 (Π (A : (Type 1)) (P : (-> A (Type 1))) (Type 1))
        (pair1 : (Π (A : (Type 1)) (P : (-> A (Type 1))) (a : A) (b : (P a)) (Σ1 A P))))

#;(define-datatype Σ0 (A : (Type 0)) (P : (-> A (Type 0))) : -> (Type 0)
  (pair0 : (a : A) (b : (P a)) -> (Σ0 A P)))

#;(define-datatype Σ1 (A : (Type 1)) (P : (-> A (Type 1))) : -> (Type 1)
  (pair1 : (a : A) (b : (P a)) -> (Σ1 A P)))

;; TODO: As demo, write macro that generates version of Σ for every universe level
(define-typed-syntax Σ
  [(_ (x:id (~datum :) A) B) ≫
   [⊢ A ≫ _ ⇒ (~Type i)]
   #:with name (format-id this-syntax "Σ~a" (syntax->datum #'i))
   -----------
   [≻ (name A (λ (x : A) B))]]
  [(_ A B) ≫
   [⊢ A ≫ _ ⇒ (~Type i)]
   #:with name (format-id this-syntax "Σ~a" (syntax->datum #'i))
   ---------
   [≻ (name A B)]])
#;(define-syntax (Σ syn)
  (syntax-parse syn
    #:datum-literals (:)
    #:literals (typed-Type)
    [(_ (x:id : A) B)
     #:with (typed-Type i) (cur-type-infer #'A)
     #:with name (format-id syn "Σ~a" (syntax->datum #'i))
     #`(name A (λ (x : A) B))]
    [(_ A B)
     #:with (typed-Type i) (cur-type-infer #'A)
     #:with name (format-id syn "Σ~a" (syntax->datum #'i))
     #`(name A B)]))

(define-typed-syntax (pair P a b) ≫
  [⊢ a ≫ a- ⇒ A (⇒ : (~Type i))]
  #:with name (format-id this-syntax "pair~a" (syntax->datum #'i))
  -----------
  [≻ (name A P a b)])
#;(define-syntax (pair syn)
  (syntax-parse syn
    #:datum-literals ()
    #:literals (typed-Type)
    [(pair P a b)
     #:with A (cur-type-infer #'a)
     #:with (typed-Type i) (cur-type-infer #'A)
     #:with name (format-id syn "pair~a" (syntax->datum #'i))
     #`(name A P a b)]))

(define (fst0 (A : (Type 0)) (P : (-> A (Type 0))) (p : (Σ A P)))
  (new-elim p (λ (x : (Σ A P)) A)
            (λ (a : A) (b : (P a)) a)))

(define (snd0 (A : (Type 0)) (P : (-> A (Type 0))) (p : (Σ A P)))
  (new-elim p (λ (x : (Σ A P)) (P (fst0 A P x)))
            (λ (a : A) (b : (P a)) b)))

(define (fst1 (A : (Type 0)) (P : (-> A (Type 0))) (p : (Σ1 A P)))
  (new-elim p (λ (x : (Σ1 A P)) A)
            (λ (a : A) (b : (P a)) a)))

(define (snd1 (A : (Type 0)) (P : (-> A (Type 0))) (p : (Σ1 A P)))
  (new-elim p (λ (x : (Σ1 A P)) (P (fst1 A P x)))
            (λ (a : A) (b : (P a)) b)))

;; TODO: Gosh there is a pattern here... but probably amounts to trying to invent universe templates
;; and I should just add universe polymorphism.
;; TODO: There is also some pattern here for implicit parameters...

(define-typed-syntax (fst p) ≫
  [⊢ p ≫ p- ⇒ t]
  #:with (~or (~Σ0 A P) (~Σ1 A P)) #'t
  #:with (~Type i) (typeof #'A)
  #:with name (format-id this-syntax "fst~a" (syntax->datum #'i))
  -----------
  [≻ (name A P p)])
#;(define-syntax (fst syn)
  (syntax-parse syn
    #:literals (typed-Type typed-app)
    [(_ p)
     #:with (typed-app (typed-app _ A)  P) (cur-type-infer #'p)
     #:with (typed-Type i) (cur-type-infer #'A)
     #:with name (format-id syn "fst~a" (syntax->datum #'i))
     #`(name A P p)]))

(define-typed-syntax (snd p) ≫
  [⊢ p ≫ p- ⇒ t]
  #:with (~or (~Σ0 A P) (~Σ1 A P)) #'t
  #:with (~Type i) (typeof #'A)
  #:with name (format-id this-syntax "snd~a" (syntax->datum #'i))
  -----------
  [≻ (name A P p)])
#;(define-syntax (snd syn)
  (syntax-parse syn
    #:literals (typed-Type typed-app)
    [(_ p)
     #:with (typed-app (typed-app _ A)  P) (cur-type-infer #'p)
     #:with (typed-Type i) (cur-type-infer #'A)
     #:with name (format-id syn "snd~a" (syntax->datum #'i))
     #`(name A P p)]))

#;(define (fst0 (A : (Type 1)) (P : (-> A (Type 1))) (p : (Σ0 A P)))
  (match p
    #:return A
    [(pair1 a _) a]))

#;(define (fst1 (A : (Type 1)) (P : (-> A (Type 1))) (p : (Σ1 A P)))
  (match p
    #:return A
    [(pair1 a _) a]))

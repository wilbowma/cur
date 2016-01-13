#lang s-exp "../cur.rkt"
(require
 "bool.rkt"
 "nat.rkt"
 "maybe.rkt"
 "sugar.rkt")

(data List : (forall (A : Type) Type)
  (nil : (forall (A : Type) (List A)))
  (cons : (forall* (A : Type) (->* A (List A) (List A)))))

(module+ test
  (require rackunit)
  (check-equal?
   nil
   nil)
  (:: (cons Bool true (nil Bool)) (List Bool))
  (:: (lambda* (A : Type) (a : A)
               (ih-a : (-> Nat (Maybe A))) 
               (n : Nat)
        (match n
          [z (some A a)]
          [(s (n-1 : Nat))
           (ih-a n-1)]))
      (forall* (A : Type) (a : A) (ih-a : (-> Nat (Maybe A)))
               (n : Nat)
               (Maybe A)))
  (:: (lambda* (A : Type) (n : Nat) (none A)) (forall (A : Type) (-> Nat (Maybe A))))
  (:: (elim List Type (lambda* (A : Type) (ls : (List A)) Nat)
            (lambda (A : Type) z)
            (lambda* (A : Type) (a : A) (ls : (List A)) (ih : Nat)
                     z)
            Bool
            (nil Bool))
      Nat)
  )

(define (list-ref (A : Type) (ls : (List A)))
  ;; TODO: case* would not type-check when used. Investigate/provide better errors for case*
  (elim
   List
   Type
   (lambda* (A : Type) (ls : (List A))
            (-> Nat (Maybe A)))
   (lambda* (A : Type) (n : Nat) (none A))
   (lambda* (A : Type) (a : A) (ls : (List A)) (ih : (-> Nat (Maybe A)))
            (lambda (n : Nat)
              (match n
                [z (some A a)]
                [(s (n-1 : Nat))
                 (ih n-1)])))
   A
   ls))

(module+ test
  (check-equal?
   ((list-ref Bool (cons Bool true (nil Bool))) z)
   (some Bool true)))

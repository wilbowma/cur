#lang s-exp "../cur.rkt"
(require
 "nat.rkt"
 "maybe.rkt"
 "sugar.rkt")

(provide
 List
 nil
 cons
 list-ref)

(data List : (-> (A : Type) Type)
  (nil : (-> (A : Type) (List A)))
  (cons : (-> (A : Type) A (List A) (List A))))

(define (list-ref (A : Type) (ls : (List A)))
  (match ls
    [nil (lambda (n : Nat) (none A))]
    [(cons (A : Type) (a : A) (rest : (List A)))
     (lambda (n : Nat)
       (match n
         [z (some A a)]
         [(s (n-1 : Nat))
          ((recur rest) n-1)]))])
  #;(elim
   List
   Type
   (lambda (A : Type) (ls : (List A))
            (-> Nat (Maybe A)))
   (lambda (A : Type) (n : Nat) (none A))
   (lambda (A : Type) (a : A) (ls : (List A)) (ih : (-> Nat (Maybe A)))
           (lambda (n : Nat)
             (match n
               [z (some A a)]
               [(s (n-1 : Nat))
                (ih n-1)])))))

#lang s-exp "../cur.rkt"
(require
 "nat.rkt"
 "maybe.rkt"
 "sugar.rkt")

(provide
 List
 nil
 cons
 list-ref
 length)

(data List : (-> (A : Type) Type)
  (nil : (-> (A : Type) (List A)))
  (cons : (-> (A : Type) A (List A) (List A))))

(define (list-ref (A : Type) (ls : (List A)))
  (match ls
    [(nil (A : Type)) (lambda (n : Nat) (none A))]
    [(cons (A : Type) (a : A) (rest : (List A)))
     (lambda (n : Nat)
       (match n
         [z (some A a)]
         [(s (n-1 : Nat))
          ((recur rest) n-1)]))]))

(define (length (A : Type) (ls : (List A)))
  (match ls
    [(nil (A : Type))
     z]
    [(cons (A : Type) (a : A) (rest : (List A)))
     (s (recur rest))]))

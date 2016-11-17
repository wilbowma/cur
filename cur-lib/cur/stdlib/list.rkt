#lang s-exp "../main.rkt"
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

(data List : 1 (-> (A : Type) Type)
  (nil : (-> (A : Type) (List A)))
  (cons : (-> (A : Type) A (List A) (List A))))

(define (list-ref (A : Type) (ls : (List A)))
  (match ls
    [nil (lambda (n : Nat) (none A))]
    [(cons a rest)
     (lambda (n : Nat)
       (match n
         #:in Nat
         [z (some A a)]
         [(s (n-1 : Nat))
          ((recur rest) n-1)]))]))

(define (length (A : Type) (ls : (List A)))
  (match ls
    [nil
     z]
    [(cons (a : A) (rest : (List A)))
     (s (recur rest))]))

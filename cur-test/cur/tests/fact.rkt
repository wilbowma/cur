#lang cur
(require cur/stdlib/sugar
         cur/stdlib/nat
         rackunit)

;; this example used to demonstrates a bug in match
(define (fact [n : Nat])
  (match n
    [z (s z)]
    [(s x) (mult (s x) (fact x))]))

(: fact^ (-> Nat Nat))
(define (fact^ n)
  (match n
    [z (s z)]
    [(s x) (mult n (fact x))]))

;; bad version is equiv to exp fn
(check-equal? (fact 2) 2) ; bad version produces 4
(check-equal? (fact 3) 6) ; bad version produces 27

(check-equal? (fact^ 2) 2) ; bad version produces 4
(check-equal? (fact^ 3) 6) ; bad version produces 27

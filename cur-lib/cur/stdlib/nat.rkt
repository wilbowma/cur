#lang s-exp "../main.rkt"
(require
 "datum.rkt"
 "sugar.rkt"
 "bool.rkt")
;; TODO: override (all-defined-out) to enable exporting all these
;; properly.
(provide #%datum Nat z s add1 sub1 plus mult exp square nat-equal? even? odd?)

(data Nat : 0 Type
  (z : Nat)
  (s : (-> Nat Nat)))

(begin-for-syntax
  (provide nat->unary)
  (define (nat->unary n)
    (if (zero? n)
        #`z
        #`(s #,(nat->unary (sub1 n))))))

(begin-for-syntax
  (provide nat-datum)
  (define (nat-datum syn f)
    (syntax-parse syn
      [x:nat
       (nat->unary (syntax->datum #'x))]
      [_ (f syn)]))
  (current-datum nat-datum))

(define (add1 (n : Nat)) (s n))

(define (sub1 (n : Nat))
  (match n
    [z z]
    [(s x) x]))

(define (plus (n1 : Nat) (n2 : Nat))
  (match n1
    [z n2]
    [(s x)
     (s (plus x n2))]))

(define (mult (m : Nat) (n : Nat))
  (match m
    [z z]
    [(s x)
     (plus n (mult x n))]))

(define (exp (m : Nat) (e : Nat))
  (match m
    [z (s z)]
    [(s x)
     (mult e (exp x e))]))

(define square (run (exp (s (s z)))))

(define (zero? (n : Nat))
  (match n
    [z true]
    [(s n)
     false]))

(define (nat-equal? (n : Nat))
  (match n
    [z zero?]
    [(s n-1)
     (lambda (m : Nat)
       (match m #:in Nat
         [z false]
         [(s m-1)
          (nat-equal? n-1 m-1)]))]))

(define (even? (n : Nat))
  (match n
    [z true]
    [(s n-1)
     (not (even? n-1))]))

(define (odd? (n : Nat))
  (not (even? n)))

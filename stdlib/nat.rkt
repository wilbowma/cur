#lang s-exp "../cur.rkt"
(require "sugar.rkt" "bool.rkt")
;; TODO: override (all-defined-out) to enable exporting all these
;; properly.
(provide Nat z s add1 sub1 plus nat-equal? even? odd?)
(module+ test
  (require rackunit))

(data Nat : Type
  (z : Nat)
  (s : (-> Nat Nat)))

(define (add1 (n : Nat)) (s n))
(module+ test
  (check-equal? (add1 (s z)) (s (s z))))

(define (sub1 (n : Nat))
  (case n
    [z z]
    [(s (x : Nat)) IH: ((ih-n : Nat)) x]))
(module+ test
  (check-equal? (sub1 (s z)) z))

(define (plus (n1 : Nat) (n2 : Nat))
  (case n1
    [z n2]
    [(s (x : Nat))
     IH: ((ih-n1 : Nat))
     (s ih-n1)]))
(module+ test
  (check-equal? (plus z z) z)
  (check-equal? (plus (s (s z)) (s (s z))) (s (s (s (s z))))))

;; Credit to this function goes to Max
(define nat-equal?
  (elim Nat Type (lambda (x : Nat) (-> Nat Bool))
    (elim Nat Type (lambda (x : Nat) Bool)
          true
          (lambda* (x : Nat) (ih-n2 : Bool) false))
    (lambda* (x : Nat) (ih : (-> Nat Bool))
      (elim Nat Type (lambda (x : Nat) Bool)
            false
            (lambda* (x : Nat) (ih-bla : Bool)
                     (ih x))))))
(module+ test
  (check-equal? (nat-equal? z z) true)
  (check-equal? (nat-equal? z (s z)) false)
  (check-equal? (nat-equal? (s z) (s z)) true))

(define (even? (n : Nat))
  (elim Nat Type (lambda (x : Nat) Bool)
        true
        (lambda* (n : Nat) (odd? : Bool)
           (not odd?))
        n))

(define (odd? (n : Nat))
  (not (even? n)))

(module+ test
  (check-equal?
    (even? z)
    true)
  (check-equal?
    (even? (s z))
    false)
  (check-equal?
    (even? (s (s z)))
    true)
  (check-equal?
    (odd? z)
    false)
  (check-equal?
    (odd? (s z))
    true)
  (check-equal?
    (odd? (s (s z)))
    false)
  (check-equal?
    (odd? (s (s (s z))))
    true))

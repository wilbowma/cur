#lang s-exp "../redex-curnel.rkt"
(require "sugar.rkt" "bool.rkt")
;; TODO: override (all-defined-out) to enable exporting all these
;; properly.
(provide nat z s add1 sub1 plus )
(module+ test
  (require rackunit))

(data nat : Type
  (z : nat)
  (s : (-> nat nat)))

(define (add1 (n : nat)) (s n))
(module+ test
  (check-equal? (add1 (s z)) (s (s z))))

(define (sub1 (n : nat))
  (case* nat Type n () (lambda (x : nat) nat)
    [z z]
    [(s (x : nat)) IH: ((ih-n : nat)) x]))
(module+ test
  (check-equal? (sub1 (s z)) z))

(define (plus (n1 : nat) (n2 : nat))
  (case* nat Type n1 () (lambda (x : nat) nat)
    [z n2]
    [(s (x : nat)) IH: ((ih-n1 : nat))
     (s ih-n1)]))
(module+ test
  (check-equal? (plus z z) z)
  (check-equal? (plus (s (s z)) (s (s z))) (s (s (s (s z))))))

;; Credit to this function goes to Max
(define nat-equal?
  (elim nat Type (lambda (x : nat) (-> nat bool))
    (elim nat Type (lambda (x : nat) bool)
          btrue
          (lambda* (x : nat) (ih-n2 : bool) bfalse))
    (lambda* (x : nat) (ih : (-> nat bool))
      (elim nat Type (lambda (x : nat) bool)
            bfalse
            (lambda* (x : nat) (ih-bla : bool)
                     (ih x))))))
(module+ test
  (check-equal? (nat-equal? z z) btrue)
  (check-equal? (nat-equal? z (s z)) bfalse)
  (check-equal? (nat-equal? (s z) (s z)) btrue))



#lang cur
(require cur/stdlib/sugar
         cur/stdlib/nat
         rackunit)

;; this example demonstrates a bug in match
(define (fact [n : Nat])
  (match n
    [z (s z)]
    ;; this must be (mult (s x) --) and cannot be (mult n --)
    [(s x) (mult (s x) (fact x))]))
#;(: fact (-> Nat Nat))
#;(define (fact n)
  (new-elim n
            (λ [n : Nat] Nat)
            1
            (λ [n* : Nat] [ih : Nat]
               ;; mult n doesnt work, must do (S n*)
               (mult (s n*) (fact n*)))))

;; bad version is equiv to exp fn
(check-equal? (fact 2) 2) ; bad version produces 4
(check-equal? (fact 3) 6) ; bad version produces 27

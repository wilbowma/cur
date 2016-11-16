#lang s-exp "lang.rkt"

(require
 (only-in racket/base define-syntax)
 (for-syntax racket/base)
 (only-in "lang.rkt"
          [#%app base-app]
          [λ base-λ]
          [define base-define])
 rackunit)

(data Nat : 0 (Type 0)
      (z : Nat)
      (s : (Π (x : Nat) Nat)))

(data Bool : 0 (Type 0)
      (true : Bool)
      (false : Bool))

(define-syntax (#%app syn)
  (syntax-case syn ()
    [(_ e)
     #'e]
    #;[(_ e e₁)
     (base-app e e₁)]
    [(_ e e₁ e_r ...)
     #'(#%app (base-app e e₁) e_r ...)]))

(require (only-in racket/trace trace-define-syntax))
(define-syntax (λ syn)
  (syntax-case syn (:)
    [(_ e)
     #'e]
    [(_ (x : t) (x_r : t_r) ... e)
     #'(base-λ (x : t) (λ (x_r : t_r) ... e))]))

(define add1 s)

(define sub1
  (λ (x : Nat)
    (elim x (λ (x : Nat) Nat)
          (z (λ (n-1 : Nat) (IH : Nat) n-1)))))

(define plus
  (λ (x : Nat) (y : Nat)
     (elim x (λ (x : Nat) Nat)
           (y (λ (n-1 : Nat) (IH : Nat) (s IH))))))

(define mult
  (λ (x : Nat) (y : Nat)
     (elim x (λ (x : Nat) Nat)
           (z (λ (n-1 : Nat) (IH : Nat) (plus IH y))))))

(define exp
  (λ (x : Nat) (y : Nat)
     (elim y (λ (x : Nat) Nat)
           ((s z) (λ (n-1 : Nat) (IH : Nat) (mult IH y))))))

(define square
  (λ (x : Nat) (mult x x)))

(define nat-equal?
  (λ (x : Nat)
    (elim x (λ (x : Nat) (Π (x : Nat) Bool))
          ((λ (y : Nat)
             (elim y (λ (x : Nat) Bool)
                   (true (λ (x : Nat) (IH : Bool) false))))
           (λ (n-1 : Nat) (IH : (Π (x : Nat) Bool))
              (λ (y : Nat)
                (elim y (λ (x : Nat) Bool)
                    (false (λ (x : Nat) (_ : Bool) (IH x))))))))))

(define not
  (λ (x : Bool)
    (elim x (λ (x : Bool) Bool) (false true))))

(define even?
  (λ (x : Nat)
    (elim x (λ (x : Nat) Bool)
          (true (λ (x : Nat) (IH : Bool) (not IH))))))

(define odd? (λ (x : Nat) (not (even? x))))

(check-equal? z z)
(check-equal? (add1 (s z)) (s (s z)))
(check-equal? (sub1 (s z)) z)

(check-equal? (plus z z) z)
(check-equal? (plus (s (s z)) (s (s z))) (s (s (s (s z)))))

(check-equal? (mult (s (s z)) z) z)
(check-equal? (mult (s (s z)) (s z)) (s (s z)))

(check-equal? (exp z z) (s z))
(check-equal? (exp (s z) z) (s z))
(check-equal? (square (s (s z))) (s (s (s (s z)))))
(check-equal? (square (s (s (s z)))) (s (s (s (s (s (s (s (s (s z))))))))))

(check-equal? (nat-equal? z z) true)
(check-equal? (nat-equal? z (s z)) false)
(check-equal? (nat-equal? (s z) (s z)) true)

(check-equal? (even? z) true)
(check-equal? (even? (s z)) false)
(check-equal? (even? (s (s z))) true)
(check-equal? (odd? z) false)
(check-equal? (odd? (s z)) true)
(check-equal? (odd? (s (s z))) false)
(check-equal? (odd? (s (s (s z)))) true)
;
;(check-equal? 0 z)
;(check-equal? 1 (s z))
;(check-equal? 2 (s (s z)))

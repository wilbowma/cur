#lang cur
(require
 cur/stdlib/sugar
 cur/stdlib/equality
 cur/stdlib/bool
 cur/stdlib/axiom
 (only-in racket/base module))

(module check-output racket/base
  (provide check-output)
  (require rackunit racket/port)
  (define-syntax-rule (check-output expect body ...)
    (check-equal? 'expect (with-output-to-string (λ () body ...)))))
(require 'check-output)

;; print-assumptions when no axioms used

(define fine
  (ann (λ [x : Bool]
         (elim-Bool x
                    (λ [y : Bool] (== Bool (not (not y)) y))
                    (refl true)
                    (refl false)))
       :
       (∀ [x : Bool] (== Bool (not (not x)) x))))

(check-output
 "Axioms used by \"fine\":
"
 (print-assumptions fine))

;; define an axiom

(define-axiom false=true
  (== false true))

;; print-assumptions when an axioms is used

(define not-fine
  (ann (λ [x : Bool]
         (elim-Bool x
                    (λ [y : Bool] (== Bool (not y) y))
                    false=true
                    (sym Bool false true false=true)))
       :
       (∀ [x : Bool] (== Bool (not x) x))))

(check-output
 "Axioms used by \"not-fine\":
 - false=true : (== Bool false true)
"
 (print-assumptions not-fine))

#lang cur
(require cur/stdlib/totality
         cur/stdlib/sugar
         (for-syntax rackunit)
         cur/stdlib/nat
         cur/stdlib/bool
         rackunit/turnstile+)

;; TOTALITY TESTS
(define n 0)
(define m 1)

(begin-for-syntax

  ; simple
  #;(check-true
   (total?
    #'((n m)
       ([z z => A]
        [z (s x) => B]
        [(s x) z => C]
        [(s x) (s x) => D]))))
  
  ; wildcards should match all cases
  #;(check-true
   (total?
    #'((n m)
       ([z _ => A]
        [(s x) z => C]
        [(s x) (s x) => D]))))

  ; syntax error in use of s, but we don't mind that here
  (check-true
   (total?
    #'((n m)
       ([z _ => A]
        [(s x) _ => B]
        [s z => C]
        [s (s x) => D]))))

  ; missing case for [z (s x)]
  (check-exn
   exn?
   (lambda ()
     (total?
      #'((n m)
         ([z z => A]
          [(s x) z => C]
          [(s x) (s x) => D])))))
  
  ; nested case: (s (s n)) is not equal to (s n)
  (check-exn
   exn?
   (lambda ()
     (total?
      #'((n m)
         ([z z => A]
          [z (s x) => B]
          [(s (s n)) z => C]
          [(s (s n)) (s x) => D]))))))

;; Using define/rec/match

(typecheck-fail/toplvl
   (define/rec/match not-bad : Bool -> Bool ; not-bad-at-all?
     [false => true])
   #:with-msg "failed totality check.*")

(typecheck-fail/toplvl
   (define/rec/match <=-bad : Nat Nat -> Bool
     [z z => true]
     [(s n*) z => false]
     [(s n*) (s m*) => (<= n* m*)])
   #:with-msg "failed totality check.*")

(typecheck-fail/toplvl
   (define/rec/match minus-bad : Nat Nat -> Nat
     [z _ => z]
     [z z => z]
     [(s n-1) (s m-1) => (minus n-1 m-1)])
   #:with-msg "failed totality check.*")

(define/rec/match minus-good : Nat Nat -> Nat
    [z _ => z]
    [n z => n]
    [(s n-1) (s m-1) => (minus n-1 m-1)])

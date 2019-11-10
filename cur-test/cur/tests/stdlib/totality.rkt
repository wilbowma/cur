#lang cur
(require cur/stdlib/totality
         cur/stdlib/sugar
         (for-syntax rackunit)
         cur/stdlib/nat
         cur/stdlib/bool
         rackunit/turnstile+)

;; TOTALITY TESTS

(begin-for-syntax
  (define (temp-assign-ty stx)
    (assign-type stx #'Nat #:wrap? #f))
  
  ; simple
  (check-true
   (total?
    #`((#,(temp-assign-ty #'n) #,(temp-assign-ty #'m))
       ([z z => A]
        [z (s x) => B]
        [(s x) z => C]
        [(s x) (s x) => D]))))

  ; wildcards should match all cases
  (check-true
   (total?
    #`((#,(temp-assign-ty #'n) #,(temp-assign-ty #'m))
       ([z _ => A]
        [(s x) z => C]
        [(s x) (s x) => D]))))

  ; missing case for [z (s x)]
  (check-exn
   exn?
   (lambda () (total?
               #`((#,(temp-assign-ty #'n) #,(temp-assign-ty #'m))
                  ([z z => A]
                   [(s x) z => C]
                   [(s x) (s x) => D])))))

  ; nested case
  (check-exn
   exn?
   (lambda () (total?
               #`((#,(temp-assign-ty #'n) #,(temp-assign-ty #'m))
                  ([z z => A]
                   [z (s x) => B]
                   [(s x) z => C]
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

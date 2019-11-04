#lang cur
(require cur/stdlib/totality
         (for-syntax rackunit))

;; TOTALITY TESTS

(begin-for-syntax
  ; simple
  (check-true
   (total?
    #'((n m)
       ([z z => A]
        [z (s x) => B]
        [(s x) z => C]
        [(s x) (s x) => D]))))

  ; wildcards should match all cases
  (check-true
   (total?
    #'((n m)
       ([z _ => A]
        [(s x) z => C]
        [(s x) (s x) => D]))))

  ; missing case for [z (s x)]
  (check-exn
   exn?
   (lambda () (total?
               #'((n m)
                  ([z z => A]
                   [(s x) z => C]
                   [(s x) (s x) => D])))))

  ; nested case
  (check-exn
   exn?
   (lambda () (total?
               #'((n m)
                  ([z z => A]
                   [z (s x) => B]
                   [(s x) z => C]
                   [(s (s n)) (s x) => D]))))))

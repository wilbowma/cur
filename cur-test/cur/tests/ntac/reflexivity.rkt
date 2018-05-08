#lang cur

(require
 rackunit
 cur/stdlib/nat
 cur/stdlib/bool
 cur/stdlib/prop
 cur/stdlib/sugar
 cur/ntac/base
 cur/ntac/standard)

;; examples from SF Ch 1: Basics

(data day : 0 (Type 0)
      (mon : day)
      (tues : day)
      (wed : day)
      (thurs : day)
      (fri : day)
      (sat : day)
      (sun : day))

(define next-weekday
  (λ [d : day] 
    (new-elim d
              (λ [x : day] day)
              tues
              wed
              thurs
              fri
              mon
              mon
              mon)))

(check-equal? (next-weekday fri) mon)
(check-equal? (next-weekday (next-weekday sat)) tues)

(:: (refl day tues)
    (== day (next-weekday (next-weekday sat)) tues))

(:: (refl day (next-weekday (next-weekday sat)))
    (== day (next-weekday (next-weekday sat)) tues))

(ntac (== day (next-weekday (next-weekday sat)) tues)
      reflexivity)

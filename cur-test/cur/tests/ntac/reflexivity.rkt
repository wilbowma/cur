#lang cur

(require
 "rackunit-ntac.rkt"
 cur/stdlib/nat
 cur/stdlib/bool
 cur/stdlib/prop
 cur/stdlib/sugar
 cur/ntac/base
 cur/ntac/standard
 cur/ntac/prop)

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

; fail, tues \neq mon
#;(:: (refl day (next-weekday (next-weekday sat)))
    (== day (next-weekday (next-weekday sat)) mon))

(ntac (== day (next-weekday (next-weekday sat)) tues)
       reflexivity)

(check-ntac-fail ; mon \new tues
 (ntac (== day (next-weekday (next-weekday sat)) mon)
       reflexivity)
 "does not have type")

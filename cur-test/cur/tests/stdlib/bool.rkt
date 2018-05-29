#lang cur
(require
 rackunit
 cur/stdlib/bool
 cur/stdlib/sugar)

(check-equal? (not true) false)
(check-equal? (not false) true)

(check-equal? (and true false) false)
(check-equal? (and false false) false)
(check-equal? (and false true) false)
(check-equal? (and true true) true)

(check-equal? (or true false) true)
(check-equal? (or false false) false)
(check-equal? (or false true) true)
(check-equal? (or true true) true)

#lang cur
(require
 cur/stdlib/sugar
 cur/stdlib/bool
 rackunit/turnstile)

(check-type (if true false true) : Bool -> false)
(check-type (if false false true) : Bool -> true)

(check-type (not true) : Bool -> false)
(check-type (not false) : Bool -> true)

(check-type (and true false) : Bool -> false)
(check-type (and false false) : Bool -> false)
(check-type (and false true) : Bool -> false)
(check-type (and true true) : Bool -> true)

(check-type (or true false) : Bool -> true)
(check-type (or false false) : Bool -> false)
(check-type (or false true) : Bool -> true)
(check-type (or true true) : Bool -> true)

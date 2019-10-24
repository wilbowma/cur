#lang cur
(require
 cur/stdlib/sugar
 cur/stdlib/prop
 rackunit/turnstile+)

(typecheck-fail/toplvl
 (define-datatype Nat : Type
       (z : Nat)
       (s : (-> (-> (-> Nat False) False) Nat)))
 #:with-msg "does not satisfy strict positivity")


#lang cur
(require
  cur/stdlib/nat
  cur/stdlib/equality
  cur/stdlib/sugar
  rackunit/turnstile)

;; examples from @florence

(typecheck-fail/toplvl
 (define/rec/match bang!1 : [n : Nat] -> (== 0 1)
   [=> (bang!1 n)])
 #:with-msg "expected at least one matching variable")

(typecheck-fail/toplvl
 (define/rec/match bang!2 : -> (== 0 1)
   [=> (bang!2)])
 #:with-msg "expected at least one matching variable")

(typecheck-fail/toplvl
 (define/rec/match bang!3 : Nat -> (== 0 1)
   [n => (bang!3 n)])
 #:with-msg "Definition bang!3 failed termination check")

#lang cur
(require
 cur/stdlib/sugar
 cur/stdlib/nat
 cur/stdlib/bool
 rackunit/turnstile)

;; tests for pattern matching in define/rec/match (from stdlib/sugar)

(typecheck-fail/toplvl
 (define/rec/match sub1-bad1 : Bool -> Nat
   [z => z]
   [(s x) => x])
 #:with-msg "expected pattern for type Bool, given pattern for.*Nat.*z")

(typecheck-fail/toplvl
 (define/rec/match sub1-bad2 : Nat -> Bool
   [z => z]
   [(s x) => x])
 #:with-msg "expected Bool, given Nat.*expression: z")

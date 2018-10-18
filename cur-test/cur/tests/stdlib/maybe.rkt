#lang cur

(require
 cur/stdlib/sugar
 cur/stdlib/bool
 cur/stdlib/maybe
 rackunit/turnstile)

(check-type (some true) : (Maybe Bool) -> (some Bool true))
(check-type
 (match (some Bool true) #:return Bool
  [none false]
  [(some (x : Bool)) (if x true false)])
 : Bool -> true)

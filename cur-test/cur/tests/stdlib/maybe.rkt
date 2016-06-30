#lang cur

(require
 rackunit
 cur/stdlib/sugar
 cur/stdlib/bool
 cur/stdlib/maybe)

(check-equal?
 (some/i true)
 (some Bool true))
(check-equal?
   (match (some Bool true)
     [none
      false]
     [(some (x : Bool))
      (if x true false)])
   true)

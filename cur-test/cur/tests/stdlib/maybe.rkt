#lang cur

(require
 rackunit
 cur/stdlib/sugar
 cur/stdlib/bool
 cur/stdlib/maybe)

(check-equal?
 (some/i true)
 (some Bool true))
;; Disabled until #22 fixed
#;(check-equal?
   (match (some Bool true)
     [(none (A : Type))
      false]
     [(some (A : Type) (x : A))
      ;; TODO: Don't know how to use dependency yet
      (if x true false)])
   true)

#lang cur

(require
 rackunit
 cur/stdlib/bool
 cur/stdlib/sugar
 cur/stdlib/tactics/base
 cur/stdlib/tactics/sartactics)

;; TODO: To much randomness for easy automated testing
(define-theorem meow (forall (x : Bool) Bool))
  #;(proof (interactive))

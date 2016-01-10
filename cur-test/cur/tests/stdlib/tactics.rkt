#lang cur

(require
 rackunit
 cur/stdlib/sugar
 cur/stdlib/bool
 cur/stdlib/tactics/base
 cur/stdlib/tactics/standard)
(define-theorem meow (forall (x : Bool) Bool))
(check-equal?
 ((proof
   (intro x)
   (by-assumption)) true)
 true)
(define-theorem meow1 (forall (x : Bool) Bool))
(check-equal?
 ((proof
   (obvious)
   ;; TODO: Add ability to check output
   #;(print)) true)
 true)
(define-theorem meow2 (forall (x : Bool) Bool))
(check-equal?
 ((proof
  (intro x)
  (restart)
  (intro x)
  (by-assumption)) true)
 true)
(define-theorem meow3 (forall (x : Bool) Bool))
(check-equal?
 ((proof (obvious)) true)
 true)
;; TODO: Fix this unit test so it doesn't require interaction
(define-theorem meow4 (forall (x : Bool) Bool))
#;(proof (interactive))

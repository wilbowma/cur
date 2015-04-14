#lang s-exp "../redex-curnel.rkt"
(require "sugar.rkt")
(provide maybe none some)

(data maybe : (forall (A : Type) Type)
  (none : (forall (A : Type) (maybe A)))
  (some : (forall* (A : Type) (a : A) (maybe A))))

(module+ test
  (require rackunit "bool.rkt")
  #;(check-equal?
    (case* maybe (some bool btrue)
      (lambda (x : (maybe bool)) bool)
      [(none (A : Type)) IH: ()
       bfalse]
      [(some (A : Type) (x : A)) IH: ()
       ;; TODO: Don't know how to use dependency yet
       (if x btrue bfalse)])
    btrue))

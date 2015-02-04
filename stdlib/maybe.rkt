#lang s-exp "../redex-curnel.rkt"
(require "sugar.rkt")
(provide maybe none some)

(data maybe : (forall (A : Type) Type)
  (none : (forall (A : Type) (maybe A)))
  (some : (forall* (A : Type) (a : A) (maybe A))))

(module+ test
  (require rackunit "bool.rkt")
  ;; TODO: Dependent pattern matching doesn't work yet
  #;(check-equal? (case* (some bool btrue)
                  [(none (A : Type)) bfalse]
                  [(some (A : Type) (x : bool))
                   (if x btrue bfalse)])
                btrue))

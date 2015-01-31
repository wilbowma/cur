#lang s-exp "redex-curnel.rkt"
(require "sugar.rkt")
(provide maybe none some)

(data maybe : (forall (A : Type) Type)
  (none : (forall (A : Type) (maybe A)))
  (some : (forall* (A : Type) (a : A) (maybe A))))

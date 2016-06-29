#lang s-exp "../main.rkt"
(require "sugar.rkt")
(provide Maybe none some some/i)

(data Maybe : 1 (forall (A : Type) Type)
  (none : (forall (A : Type) (Maybe A)))
  (some : (forall (A : Type) (a : A) (Maybe A))))

(define-syntax (some/i syn)
  (syntax-case syn ()
   [(_ a)
    (let ([a-ty (cur-type-infer #'a)])
      #`(some #,a-ty a))]))

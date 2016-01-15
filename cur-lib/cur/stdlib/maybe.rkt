#lang s-exp "../cur.rkt"
(require "sugar.rkt")
(provide Maybe none some some/i)

(data Maybe : (forall (A : Type) Type)
  (none : (forall (A : Type) (Maybe A)))
  (some : (forall (A : Type) (a : A) (Maybe A))))

(define-syntax (some/i syn)
  (syntax-case syn ()
   [(_ a)
    (let ([a-ty (type-infer/syn #'a)])
      #`(some #,a-ty a))]))

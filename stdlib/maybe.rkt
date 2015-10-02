#lang s-exp "../cur.rkt"
(require "sugar.rkt")
(provide Maybe none some some/i)

(data Maybe : (forall (A : Type) Type)
  (none : (forall (A : Type) (Maybe A)))
  (some : (forall* (A : Type) (a : A) (Maybe A))))

(define-syntax (some/i syn)
  (syntax-case syn ()
   [(_ a)
    (let ([a-ty (type-infer/syn #'a)])
      #`(some #,a-ty a))]))

(module+ test
  (require rackunit "bool.rkt")
  (check-equal?
   (some/i true)
   (some Bool true))
  ;; Disabled until #22 fixed
  #;(check-equal?
    (case* Maybe Type (some Bool true) (Bool)
      (lambda* (A : Type) (x : (Maybe A)) A)
      [(none (A : Type)) IH: ()
       false]
      [(some (A : Type) (x : A)) IH: ()
       ;; TODO: Don't know how to use dependency yet
       (if x true false)])
    true))

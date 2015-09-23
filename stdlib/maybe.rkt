#lang s-exp "../cur.rkt"
(require "sugar.rkt")
(provide Maybe none some)

(data Maybe : (forall (A : Type) Type)
  (none : (forall (A : Type) (Maybe A)))
  (some : (forall* (A : Type) (a : A) (Maybe A))))

(module+ test
  (require rackunit "bool.rkt")
  #;(check-equal?
    (case* Maybe (some Bool true)
      (lambda (x : (Maybe Bool)) Bool)
      [(none (A : Type)) IH: ()
       false]
      [(some (A : Type) (x : A)) IH: ()
       ;; TODO: Don't know how to use dependency yet
       (if x true false)])
    true))

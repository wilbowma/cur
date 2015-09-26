#lang s-exp "../cur.rkt"
(require "sugar.rkt")
(provide Maybe none some)

(data Maybe : (forall (A : Type) Type)
  (none : (forall (A : Type) (Maybe A)))
  (some : (forall* (A : Type) (a : A) (Maybe A))))

(module+ test
  (require rackunit "bool.rkt")
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

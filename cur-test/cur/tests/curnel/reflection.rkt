#lang cur

(begin-for-syntax
  (require rackunit)
  (check-true
   (cur-type-check?
    #`(lambda (A : Type) (a : A) a)
    #`(Π (A : Type) (a : A) A))))

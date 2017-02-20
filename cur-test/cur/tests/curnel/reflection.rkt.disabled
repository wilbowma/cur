#lang cur
(require cur/stdlib/nat)

(begin-for-syntax
  (require rackunit)
  (check-equal?
   (cur-constructor-telescope-length #'z)
   0)

  (check-equal?
   (length (cur-constructor-recursive-index-ls #'z))
   0)

  (check-equal?
   (cur-constructor-telescope-length #'s)
   1)

  (check-equal?
   (length (cur-constructor-recursive-index-ls #'s))
   1))

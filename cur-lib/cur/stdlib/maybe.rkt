#lang s-exp "../main.rkt"
(require "sugar.rkt")
(provide Maybe (rename-out [none/i none] [some/i some]))

(data Maybe : 1 (Π (A : Type) Type)
  (none : (Π (A : Type) (Maybe A)))
  (some : (Π (A : Type) (Π (a : A) (Maybe A)))))

;; inferring version of some and none
;; TODO: should define-datatype automatically define these?
(define-implicit some/i = some 1)
(define-implicit none/i = none 1)


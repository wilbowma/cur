#lang s-exp "cur-redex.rkt"
(require "sugar.rkt")

(data nat : Type
  (z : nat)
  (s : (-> nat nat)))

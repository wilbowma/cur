#lang s-exp "redex-curnel.rkt"
(require "sugar.rkt")

(data nat : Type
  (z : nat)
  (s : (-> nat nat)))

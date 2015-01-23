#lang s-exp "redex-core.rkt"
(require "sugar.rkt")

(data nat : Type
  (z : nat)
  (s : (-> nat nat)))

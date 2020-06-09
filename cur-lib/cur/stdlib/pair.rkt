#lang s-exp "../main.rkt"

(provide prod pair fst snd fst* snd* (for-syntax ~prod pair))

(require cur/stdlib/sugar)

(define-datatype prod [X : Type] [Y : Type] : Type
  [pair* X Y])

(define-implicit pair = pair* 2)

(define/rec/match fst* : [X : Type] [Y : Type] (prod X Y) -> X
  [(pair x _) => x]
  #:type-aliases ([pair = pair* 2]))

(define/rec/match snd* : [X : Type] [Y : Type] (prod X Y) -> Y
  [(pair _ y) => y]
  #:type-aliases ([pair = pair* 2]))

(define-implicit fst = fst* 2)
(define-implicit snd = snd* 2)

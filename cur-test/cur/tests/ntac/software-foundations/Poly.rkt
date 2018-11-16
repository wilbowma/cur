#lang cur
(require cur/stdlib/sugar
         cur/stdlib/equality
         cur/ntac/base
         cur/ntac/standard
         cur/ntac/rewrite
         "Basics.rkt"
         "../rackunit-ntac.rkt")

(data boollist : 0 Type
      [bool-nil : boollist]
      [bool-cons : (-> bool boollist boollist)])

(define-datatype list [X : Type] : -> Type
  [nil : (list X)]
  [cons : X (list X) -> (list X)])

(:: list (-> Type Type))
(:: (nil nat) (list nat))
(:: (cons nat 3 (nil nat)) (list nat))
(:: nil (∀ [X : Type] (list X)))
(:: cons (∀ [X : Type] (-> X (list X) (list X))))

(:: (cons nat 2 (cons nat 1 (nil nat)))
    (list nat))

(define/rec/match repeat : [X : Type] [x : X] nat -> (list X)
  [O => (nil X)]
  [(S count-1) => (cons X x (repeat X x count-1))])

(check-equal? (repeat nat 4 2)
              (cons nat 4 (cons nat 4 (nil nat))))
(check-equal? (repeat bool false 1) (cons bool false (nil bool)))

(define-datatype mumble : Type
  [a : mumble]
  [b : (-> mumble nat mumble)]
  [c : mumble])
(define-datatype grumble [X : Type] -> Type
  [d : mumble -> (grumble X)]
  [e : X -> (grumble X)])

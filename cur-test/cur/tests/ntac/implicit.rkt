#lang cur
(require cur/stdlib/nat
         cur/stdlib/bool
         cur/stdlib/sugar
         cur/stdlib/equality
         cur/ntac/base
         cur/ntac/standard
         cur/ntac/rewrite
         "rackunit-ntac.rkt"
         rackunit/turnstile)

;; testing implicit args
;; may be some dup from software-foundations/Poly.rkt

(define-datatype list [X : Type] : -> Type
  [nil : (list X)]
  [cons : X (list X) -> (list X)])

(:: list (-> Type Type))
(:: (nil Nat) (list Nat))
(:: (cons Nat 3 (nil Nat)) (list Nat))
(:: nil (∀ [X : Type] (list X)))
(:: cons (∀ [X : Type] (-> X (list X) (list X))))

(:: (cons Nat 2 (cons Nat 1 (nil Nat)))
    (list Nat))

(define/rec/match repeat : [X : Type] [x : X] Nat -> (list X)
  [z => (nil X)]
  [(s count-1) => (cons X x (repeat X x count-1))])

(check-equal? (repeat Nat 4 2)
              (cons Nat 4 (cons Nat 4 (nil Nat))))
(check-equal? (repeat Bool false 1) (cons Bool false (nil Bool)))

(define-implicit nil* = nil 1)
(define-implicit cons* = cons 1 _ inf)
(define-implicit repeat* = repeat 1)

(check-type (nil*) : (list Nat))
(check-type (nil*) : (list Bool))
(check-type nil* : (list Nat))
(check-type nil* : (list (list Nat)))
(check-type (cons* 2 (nil Nat)) : (list Nat) -> (cons Nat 2 (nil Nat)))
(check-type (cons* 1 nil*) : (list Nat))
(check-type (repeat* 4 2) : (list Nat) -> (repeat Nat 4 2))

(typecheck-fail (cons* 1 (nil Bool)) ; TODO: improve this msg
                #:with-msg "expected.*list.*Nat")

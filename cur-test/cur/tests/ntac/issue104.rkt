#lang cur
(require
 cur/stdlib/sugar
 cur/ntac/base
 cur/ntac/standard)

(begin-for-syntax
  (require syntax/parse/define)
  (define-simple-macro (mytac)
    (try (by-intros P p) (by-exact p))))

(define-theorem foo
  (forall (P : Type) (-> P P))
  (mytac)
  ;(by-intros P p)
  ;(by-exact p)
)

(require "rackunit-ntac.rkt")
(:: foo (forall (P : Type) (-> P P)))

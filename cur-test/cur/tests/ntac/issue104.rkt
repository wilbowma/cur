#lang cur
(require
 cur/stdlib/sugar
 cur/ntac/base
 cur/ntac/standard)

;; example from Sebastian Ullrich, see github issue#104

(begin-for-syntax
  (require syntax/parse/define)
  (define-simple-macro (mytac1)
    (try (by-intros P p) (by-exact p)))
  (define-simple-macro (mytac2)
    (seq (by-intros P p) (by-exact p))))

(require cur/ntac/metantac)
(begin-for-syntax
  (define-tactical (mytac3)
    ((compose (by-exact p) (by-intros P p)) $ptz)))

(define-theorem foo1
  (forall (P : Type) (-> P P))
  (mytac1))
(define-theorem foo2
  (forall (P : Type) (-> P P))
  (mytac2))
(define-theorem foo3
  (forall (P : Type) (-> P P))
  (mytac3))

(require "rackunit-ntac.rkt")
(:: foo1 (forall (P : Type) (-> P P)))
(:: foo2 (forall (P : Type) (-> P P)))
(:: foo3 (forall (P : Type) (-> P P)))

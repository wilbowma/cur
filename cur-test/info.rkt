#lang info
(define collection 'multi)
(define deps '())
(define build-deps '("base" "rackunit-lib" ("cur-lib" #:version "0.40") "sweet-exp-lib" "chk-lib"))
(define update-implies '("cur-lib"))
(define pkg-desc "Tests for \"cur\".")
(define pkg-authors '(wilbowma))
(define test-omit-paths
  '("cur/tests/curnel/"
    "cur/tests/issue-71.rkt"
    "cur/tests/ntac/"
    "cur/tests/ntac.rkt"
    "cur/tests/olly.rkt"
    "cur/tests/plus.rkt"
    "cur/tests/stdlib/ascii.rkt"
    "cur/tests/stdlib/list.rkt"
    "cur/tests/stdlib/maybe.rkt"
    "cur/tests/stdlib/racket-ascii.rkt"
    "cur/tests/stdlib/sigma.rkt"
    "cur/tests/stdlib/typeclass.rkt"
    "cur/tests/stlc.rkt"
    "cur/tests/sweet-exp.rkt"
    "cur/tests/vector-append.rkt"))

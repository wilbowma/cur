#lang info
(define collection 'multi)
(define deps '("base"))
(define build-deps '())
(define pkg-desc "implementation (no documentation, tests) part of \"cur\".")
(define compile-omit-paths 'all #;'("cur/curnel/snoc-env.rkt" "cur/curnel/model" "cur/curnel/racket-impl/resugar.rkt"))
(define version "0.2")
(define pkg-authors '(wilbowma))

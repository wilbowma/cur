#lang info
(define collection 'multi)
(define deps '())
(define build-deps '("base" "rackunit-lib" ("cur-lib" #:version "0.33") "sweet-exp-lib"))
(define update-implies '("cur-lib"))
(define pkg-desc "Tests for \"cur\".")
(define pkg-authors '(wilbowma))

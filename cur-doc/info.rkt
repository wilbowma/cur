#lang info
(define collection 'multi)
(define deps '("base"))
(define build-deps '("scribble-lib" "racket-doc" "sandbox-lib" ("cur-lib" #:version "0.37")))
(define pkg-desc "Documentation for \"cur\".")
(define pkg-authors '(wilbowma))

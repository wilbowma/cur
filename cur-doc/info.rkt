#lang info
(define collection 'multi)
(define deps '("base"))
(define build-deps
  '(("base" #:version "7.6")
    "scribble-lib"
    "racket-doc"
    "sandbox-lib"
    ("cur-lib" #:version "0.6")
    "data-doc"))
(define pkg-desc "Documentation for \"cur\".")
(define pkg-authors '(wilbowma))

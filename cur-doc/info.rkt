#lang info
(define collection 'multi)
(define deps '("base" "racket-doc"))
(define build-deps '("scribble-lib" ("cur-lib" #:version "0.9") "sandbox-lib"))
(define pkg-desc "Documentation for \"cur\".")
(define pkg-authors '(wilbowma))

#lang info
(define collection 'multi)
(define deps '("base"))
;; See README if you want to use in version < 7.0
(define build-deps '(("base" #:version "7.0") "scribble-lib" "racket-doc" "sandbox-lib" ("cur-lib" #:version "0.5")))
(define pkg-desc "Documentation for \"cur\".")
(define pkg-authors '(wilbowma))

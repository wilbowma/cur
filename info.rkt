#lang info
(define collection "cur")
(define deps '("base" "rackunit-lib" ("redex-lib" #:version "1.11")))
(define build-deps '("scribble-lib" "racket-doc" "sandbox-lib"))
(define scribblings '(("scribblings/cur.scrbl" (multi-page))))
(define pkg-desc "Dependent types with parenthesis and meta-programming.")
(define version "0.1")
(define pkg-authors '(wilbowma))

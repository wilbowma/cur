#lang racket
(require scribble/base
         scriblib/autobib
         scriblib/bibtex
         racket/date)
(provide (all-defined-out))

(define-cite ~cite citet generate-bibliography)
(define-bibtex-cite* "bib.bib" ~cite citet ~citea citeta)

#lang info
(define collection 'multi)
(define compile-omit-paths 'all)
(define test-timeouts
  '(("tests/ntac/software-foundations/Imp-var.rkt" 240)))
(define test-omit-paths
  '("tests/curnel/"
    "tests/olly.rkt"
    "tests/stlc-olly.rkt"))

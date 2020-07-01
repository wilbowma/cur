#lang info
(define collection 'multi)
(define compile-omit-paths 'all)
(define test-timeouts
  '(("tests/ntac/software-foundations/Imp-var.rkt" 240)))
(define test-omit-paths
  '("tests/curnel/"
    "tests/ntac/interactive.rkt"
    "tests/olly.rkt"
    "tests/stlc.rkt"
    "tests/stlc-olly.rkt"
    "tests/stdlib/ascii.rkt"
    "tests/stdlib/nat.rkt"
    "tests/stdlib/prop.rkt"
    "tests/stdlib/sigma.rkt"
    "tests/stdlib/pattern-tree.rkt"
    "tests/ntac/induction.rkt"
    "tests/ntac/inversion.rkt"
    "tests/ntac/software-foundations/Imp.rkt"
    "tests/ntac/software-foundations/Imp-var.rkt"
    "tests/ntac/software-foundations/IndProp.rkt"
    "tests/ntac/software-foundations/Maps.rkt"
    "tests/ntac/software-foundations/Poly.rkt"
    "tests/ntac/software-foundations/Poly-abbrv.rkt"
    "tests/ntac/software-foundations/Tactics.rkt"
    "tests/ntac/software-foundations/Tactics3.rkt"
    "tests/ntac/software-foundations/Tactics-destruct.rkt"
    "tests/ntac/software-foundations/Tactics-inversion.rkt"))

#lang cur

(require cur/stdlib/nat)
(require racket/trace)
(require cur/debug/syntax-trace)
(require (only-in racket/base [define r:define]))

(trace-define-syntax run
                     (lambda (stx)
                       (syntax-parse stx
                         [(_ expr)
                          (cur-normalize #'expr)])))

(r:define one (run (plus 1 0)))
one

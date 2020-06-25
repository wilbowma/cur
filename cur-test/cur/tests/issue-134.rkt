#lang cur

(require cur/stdlib/nat)
(require racket/trace)
(require cur/debug/syntax-trace)

(trace-define-syntax run
                     (lambda (stx)
                       (syntax-parse stx
                         [(_ expr)
                          (cur-normalize #'expr)])))

(define one (run (plus 1 0)))
one

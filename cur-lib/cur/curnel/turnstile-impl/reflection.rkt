#lang racket/base

(provide (for-syntax cur-expand))

(require (only-in macrotypes/typecheck-core expand1)
         (for-syntax racket/base))

(define-for-syntax (cur-expand stx env) (expand1 stx env))

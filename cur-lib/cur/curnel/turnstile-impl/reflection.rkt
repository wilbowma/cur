#lang racket/base

(provide (for-syntax cur-expand cur-type-infer))

(require (only-in macrotypes/typecheck-core expand1)
         (only-in turnstile/lang typeof)
         (for-syntax racket/base))

(define-for-syntax (cur-expand stx env) (expand1 stx env))

(define-for-syntax (cur-type-infer stx)
  (with-handlers ([values (lambda _ #f)])
    (typeof (local-expand stx 'expression null))))

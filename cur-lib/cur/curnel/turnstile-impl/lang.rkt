#lang racket/base

(provide #%module-begin
         provide require only-in for-syntax
         begin-for-syntax
         define-values begin define-syntax define #%app λ
         (for-syntax
          (all-from-out racket/base
                        syntax/parse
                        racket/syntax)))

(require (for-syntax racket/base syntax/parse racket/syntax))



(define-syntax define+provide-placeholders
  (syntax-parser
    [(_ x:id ...)
     #'(begin (define x void) ... (provide x ...))]))

(define+provide-placeholders Π Type)

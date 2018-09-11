#lang racket/base

(provide ;; #%module-begin
         provide require only-in for-syntax all-from-out
         ;; begin-for-syntax
         ;; define-values begin define-syntax define #%app λ
         (for-syntax
          (all-from-out racket/base
                        syntax/parse
                        racket/syntax)))

(require (for-syntax racket/base syntax/parse racket/syntax))

(require "dep-ind-cur2.rkt")
(provide (all-from-out "dep-ind-cur2.rkt"))

(require (only-in turnstile/base define-typed-syntax))
(provide (all-from-out turnstile/base))

;; (define-syntax define+provide-placeholders
;;   (syntax-parser
;;     [(_ x:id ...)
;;      #'(begin (define x void) ... (provide x ...))]))

;; (define+provide-placeholders Π Type)

#lang racket/base

(provide ;; #%module-begin
         provide require only-in for-syntax all-from-out
         ;; begin-for-syntax
         ;; define-values begin define #%app λ
         define-syntax define-for-syntax
         (for-syntax
          (all-from-out racket/base
                        syntax/parse
                        racket/syntax)))

(require (for-syntax racket/base syntax/parse racket/syntax))

(require "dep-ind-cur2.rkt")
(provide (all-from-out "dep-ind-cur2.rkt"))

(require (only-in turnstile/base define-typed-syntax))
(provide (all-from-out turnstile/base))

(require "dep-ind-cur2+data2.rkt")
(provide (all-from-out "dep-ind-cur2+data2.rkt"))

(require "reflection.rkt")
(provide (all-from-out "reflection.rkt"))

;; (define-syntax define+provide-placeholders
;;   (syntax-parser
;;     [(_ x:id ...)
;;      #'(begin (define x void) ... (provide x ...))]))

;; (define+provide-placeholders Π Type)

#lang racket/base
(require
 racket/syntax
 syntax/parse
 racket/function
 "type-reconstruct.rkt"
 "eval.rkt"
 "runtime-utils.rkt"
 (rename-in "equiv.rkt" [cur-equal? _cur-equal?])
 "stxutils.rkt"
 (for-template "type-check.rkt")
 (for-template "runtime.rkt")
 (for-template (only-in turnstile/lang infer typecheck?))
 (for-template  turnstile/examples/dep-ind-cur)
 )

(provide
;; with-env
;; call-with-env
; cur->datum
 ;;deprecated-cur-expand
 ;;cur-expand
 cur-type-infer
 ;cur-type-check?
 ;;cur-constructors-for
 ;;cur-data-parameters
 ;;cur-method-type
 ;;cur-constructor-recursive-index-ls
 ;;cur-constructor-telescope-length
; cur-normalize
 ;;cur-rename
 ;;cur-reflect-id
 ;;cur-step
 ;;cur-equal?
 )


(define (cur-type-infer syn)
  (car (cadddr (infer (list syn) #:ctx '()))))



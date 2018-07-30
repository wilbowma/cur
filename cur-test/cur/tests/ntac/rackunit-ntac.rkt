#lang racket
(require rackunit
         cur/ntac/standard
         (for-syntax syntax/parse rackunit))
(provide (all-from-out rackunit)
         (all-defined-out))

(define-syntax check-ntac-fail
  (syntax-parser
    [(_ e msg)
     #:when (check-exn
             (λ (exn)
               (and
                (exn:fail:ntac:goal? exn)
                (regexp-match? (syntax-e #'msg) (exn-message exn))))
             (λ () (local-expand #'e 'expression null)))
     #'(void)]))

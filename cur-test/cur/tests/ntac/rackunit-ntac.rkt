#lang racket/base

;; this file contains shim test forms for old cur test files,
;; and some new test forms, eg check-ntac-trace

(provide check-ntac-fail check-ntac-trace ntac/trace ntac/trace/raw :: check-equal?)

(require rackunit
         (only-in rackunit/turnstile check-type)
         syntax/parse/define
         (for-syntax racket/base
                     racket/port
                     racket/string
                     racket/format
                     syntax/parse
                     rackunit
                     macrotypes/stx-utils)
         (only-in cur/ntac/base ntac)
         (only-in cur/ntac/standard exn:fail:ntac:goal?))

(define-simple-macro (:: e t) (check-type e : t))

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

(define-syntax ntac/trace
  (syntax-parser
    [(_ . ts)
     #:with disp-foc (datum->syntax this-syntax 'display-focus)
     #`(ntac . #,(stx-appendmap (λ (t) (list t #'disp-foc)) #'ts))]))
(define-syntax ntac/trace/raw
  (syntax-parser
    [(_ . ts)
     #:with disp-foc (datum->syntax this-syntax 'display-focus/raw)
     #`(ntac . #,(stx-appendmap (λ (t) (list t #'disp-foc)) #'ts))]))

(define-syntax check-ntac-trace
  (syntax-parser
    [(_ t ... (~datum ~>) . expected)
     #:do[(define expected-str
            (string-join
             (append (expected-stx->strs #'expected)
                     (list "Proof complete.\n"))
             ""))
          (define actual-trace
            (with-output-to-string
              (λ ()
                (local-expand #'(ntac/trace t ...) 'expression null))))]
     #:fail-unless (equal? expected-str actual-trace)
     (format "trace not equal, expected:\n~s\ngot:\n~s\n"
             expected-str actual-trace)             
     (syntax/loc this-syntax (check-true #t))]))
  
(begin-for-syntax
  (define expected-stx->strs
    (syntax-parser
      [() null]
      [((~datum --------------------------------) . rst)
       (cons "--------------------------------\n"
             (expected-stx->strs #'rst))]
      [(X:id (~datum :) ty . rst) ; env binding
       (cons (format "~a : ~a\n" (syntax->datum #'X) (syntax->datum #'ty))
             (expected-stx->strs #'rst))]
      [(other . rst) ; goal, add extra newline
       (cons (~a (syntax->datum #'other))
             (cons "\n\n" (expected-stx->strs #'rst)))])))


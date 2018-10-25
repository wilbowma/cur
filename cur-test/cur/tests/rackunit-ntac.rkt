#lang racket/base

(provide check-ntac-trace)

(require (for-syntax racket/base
                     racket/port
                     racket/string
                     racket/format
                     syntax/parse
                     macrotypes/stx-utils)
         rackunit
         (only-in cur/ntac/base ntac)
         #;(only-in ntac/standard display-focus ntac/trace))

(define-syntax ntac/trace
  (syntax-parser
    [(_ . ts)
     #:with disp-foc (datum->syntax this-syntax 'display-focus)
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
        

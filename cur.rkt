#lang racket/base

(module extra racket
  (require
    racket/syntax
    syntax/parse
    (for-template
      (only-in "curnel/redex-lang.rkt"
       cur-expand)))

  (provide cur-match)

  (define-syntax (cur-match syn)
    (syntax-case syn ()
      [(_ syn [pattern body] ...)
       #'(syntax-parse (cur-expand syn)
           [pattern body] ...)])))

(require
  (rename-in "curnel/redex-lang.rkt" [provide real-provide])
  (for-syntax 'extra)
  'extra)
(provide
  (rename-out [real-provide provide])
  (for-syntax (all-from-out 'extra))
  (all-from-out
    'extra
    "curnel/redex-lang.rkt"))

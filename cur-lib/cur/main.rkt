#lang racket/base

(module extra racket
  (require
    racket/syntax
    syntax/parse
    (for-template
      (only-in "faithful.rkt"
       cur-expand)))

  (provide cur-match)

  (define-syntax (cur-match syn)
    (syntax-case syn ()
      [(_ syn [pattern body] ...)
       #'(syntax-parse (cur-expand syn)
           [pattern body] ...)])))

(require
  (rename-in "faithful.rkt" [provide -provide])
  (only-in racket/base eof)
  (for-syntax 'extra)
  'extra)
(provide
  (rename-out [-provide provide])
  (for-syntax (all-from-out 'extra))
  (except-out
    (all-from-out
     'extra
     "faithful.rkt")
    -provide))

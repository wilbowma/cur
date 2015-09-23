#lang racket/base

(require scribble/base scribble/manual)
(provide (all-defined-out))

(define (todo . ls)
  (apply margin-note* "TODO: " ls))

(define (gtech . x)
  (apply tech x #:doc '(lib "scribblings/guide/guide.scrbl")))

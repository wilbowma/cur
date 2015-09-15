#lang racket/base

(require (rename-in "curnel/redex-lang.rkt" [provide real-provide]))
(provide (rename-out [real-provide provide]) (all-from-out "curnel/redex-lang.rkt"))

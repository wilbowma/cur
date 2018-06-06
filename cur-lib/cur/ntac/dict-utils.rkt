#lang racket/base
(require racket/dict)
(provide (all-defined-out))

;; dict fns, with args rearranged for use with fold
(define (dict-remove/flip k h) (dict-remove h k))
(define (dict-set/flip k v dict) (dict-set dict k v))


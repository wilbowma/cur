#lang racket/base
(require racket/dict)
(provide (all-defined-out))

;; dict fns, with args rearranged for use with fold
(define (dict-remove/flip k h) (dict-remove h k))
(define (dict-set/flip k v dict) (dict-set dict k v))

;; transfer scopes from src to each stxobj in stx, except for ids in ctxt
(define (transfer-scopes src stx ctxt)
  (cond
    [(and (identifier? stx) (dict-has-key? ctxt stx)) stx]
    [(pair? (syntax-e stx))
     (datum->syntax src
       (map (λ (syn) (transfer-scopes src syn ctxt)) (syntax->list stx)))]
    [else ; literals and non-ctxt ids
     (datum->syntax src (syntax->datum stx))]))

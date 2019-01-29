#lang racket
(require cur/ntac/ctx
         rackunit)

;; tests for ntac ctx

;; use as sequence
(check-equal? (for/list ([(x ty) (mk-empty-ctx)]) x) null)

;; bindings should be returned in reverse of add
(check-true
 (free-identifier=?
  (caar
   (ctx->env
    (ctx-adds (mk-empty-ctx) #'(x y) #'(tmp1 tmp2))))
  #'y))

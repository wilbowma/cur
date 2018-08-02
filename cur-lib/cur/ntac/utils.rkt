#lang racket/base
(require
 racket/dict
 syntax/id-set
 syntax/parse
 syntax/stx
 "../curnel/racket-impl/stxutils.rkt")
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

#;(require racket/contract)
(define (stx=? e1 e2 [id=? free-identifier=?])
  #;(->* (syntax? syntax?) ((-> identifier? identifier? boolean?)) boolean?)
  (cond
    [(and (identifier? e1) (identifier? e2))
     (id=? e1 e2)]
    [(and (number? (syntax-e e1)) (number? (syntax-e e2)))
     (= (syntax-e e1) (syntax-e e2))]
    [(and (stx-pair? e1) (stx-pair? e2))
     (syntax-parse (list e1 e2) ; α equiv
       ;; XXX: Matches on underlying lambda name... this is breaking abstractions
       [(((~datum typed-λ) [x1:id (~datum :) ty1] b1)
         ((~datum typed-λ) [x2:id (~datum :) ty2] b2))
        (and (stx=? #'ty1 #'ty2 id=?)
             (stx=? #'b1 (subst #'x1 #'x2 #'b2) id=?))]
       [_
        (and
         ; short-circuit on length, for performance
         (= (length (syntax->list e1)) (length (syntax->list e2)))
         (andmap (λ (x y) (stx=? x y id=?)) (syntax->list e1) (syntax->list e2)))])]
    [else #f]))

;; returns e if e \in stx and (datum=? e0 e), else #f
;; (needed by ntac to workaround some scoping issues)
(define (find-in e0 stx [=? (λ (x y) (and (datum=? x y) y))])
  (syntax-parse stx
    [e #:do[(define res (=? e0 #'e))] #:when res res]
    [(e ...)
     (let L ([es (syntax->list #'(e ...))])
       (and (not (null? es))
            (let ([res (find-in e0 (car es) =?)])
              (or res (L (cdr es))))))]
    [_ #f]))

(define (subst-term v e0 syn [bvs (immutable-free-id-set)])
  (syntax-parse syn
    [e
     #:when (and (stx=? #'e e0)
                 (or (not (identifier? #'e))
                     (not (free-id-set-member? bvs #'e))))
     v]
    [((~and (~datum λ) lam) (z:id : ty) e)
     #`(lam (z : #,(subst-term v e0 #'ty bvs)) #,(subst-term v e0 #'e (free-id-set-add bvs #'z)))]
    [(e ...)
     (datum->syntax syn (map (λ (e1) (subst-term v e0 e1 bvs)) (attribute e)))]
    [_ syn]))

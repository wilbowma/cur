#lang racket/base
(require
 racket/dict
 syntax/stx
 syntax/parse
 syntax/id-set
 (for-template turnstile/eval)
 macrotypes/stx-utils
 cur/curnel/turnstile-impl/reflection
 "../curnel/turnstile-impl/stxutils.rkt")
(provide (all-defined-out))

;; dict fns, with args rearranged for use with fold
(define (dict-remove/flip k h) (dict-remove h k))
(define (dict-set/flip k v dict) (dict-set dict k v))

(define ctxt->env dict->list)

(define (normalize ty ctxt)
  (cur-normalize (reflect ty) #:local-env (ctxt->env ctxt)))
(define ((normalize/ctxt ctxt) ty) (normalize ty ctxt)) ; curried version

(define (transfer-type from to)
  (syntax-property
   to
   ':
   (syntax-property from ':)))

#;(require racket/contract)
(define (stx=? e1 e2 [id=? free-identifier=?])
  #;(->* (syntax? syntax?) ((-> identifier? identifier? boolean?)) boolean?)
  (cond
    [(and (identifier? e1) (identifier? e2))
     (define ref-name1 (syntax-property e1 'reflect))
     (define ref-name2 (syntax-property e2 'reflect))
     (define display-name1 (and ref-name1 (syntax-property e1 'display-as)))
     (define display-name2 (and ref-name2 (syntax-property e2 'display-as)))
     (or (and ref-name1 ref-name2 (id=? ref-name1 ref-name2))
         (and display-name1 (syntax-e display-name1) (id=? display-name1 e2))
         (and display-name2 (syntax-e display-name2) (id=? e1 display-name2))         
         (id=? e1 e2))]
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
         (stx-length=? e1 e2)
         (andmap (λ (x y) (stx=? x y id=?)) (stx->list e1) (stx->list e2)))])]
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
     (transfer-type
      syn
      #`(lam (z : #,(subst-term v e0 #'ty bvs))
         #,(subst-term v e0 #'e (free-id-set-add bvs #'z))))]
    [(e ...)
     (transfer-type
      syn
      (datum->syntax syn
        (map (λ (e1) (subst-term v e0 e1 bvs)) (attribute e))))]
    [_ syn]))

;; returns true if e0 \in syn
;; exactly like subst-term except it returns #t/#f instead of substing
(define (has-term? e0 syn [bvs (immutable-free-id-set)])
  (syntax-parse syn
    [e
     #:when (and (stx=? #'e e0)
                 (or (not (identifier? #'e))
                     (not (free-id-set-member? bvs #'e))))
     #t]
    [((~and (~datum λ) lam) (z:id : ty) e)
     (or (has-term? e0 #'ty bvs)
         (has-term? e0 #'e (free-id-set-add bvs #'z)))]
    [(e ...)
     (ormap (λ (e1) (has-term? e0 e1 bvs)) (attribute e))]
    [_ #f]))

#lang racket/base
(require
 "ctx.rkt"
 syntax/stx
 syntax/parse
 syntax/id-set
 (for-template turnstile+/eval
               (only-in macrotypes/typecheck-core substs)
               (only-in cur/curnel/lang #%plain-lambda #%plain-app))
 macrotypes/stx-utils
 cur/curnel/reflection
 "../curnel/stxutils.rkt")
(provide (all-defined-out))

(define ((freshen src) x) (datum->syntax src (stx-e x)))
(define ((freshens src) xs) (stx-map (freshen src) xs))

(define (normalize ty ctxt)
  (cur-normalize (reflect ty) #:local-env (ctx->env ctxt)))
(define ((normalize/ctxt ctxt) ty) (normalize ty ctxt)) ; curried version

(define ((mk-bind-stxf f) x ty)
  #`[#,x : #,(f ty)])

(define (mk-bind-stx x ty)
  #`[#,x : #,ty])

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
       [(((~literal #%plain-lambda) (~and (_:id ...) xs) . ts1)
         ((~literal #%plain-lambda) (~and (_:id ...) ys) . ts2))
        (and (stx-length=? #'xs #'ys) 
             (stx-length=? #'ts1 #'ts2)
             (stx-andmap
              (λ (ty1 ty2) (stx=? ty1 (substs #'xs #'ys ty2)))
              #'ts1 #'ts2))]
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

(define (subst-terms vs es syn)
  (stx-fold (λ (v e res) (subst-term v e res (immutable-free-id-set))) syn vs es))
(define ((subst-terms/es vs es) syn)
  (subst-terms vs es syn))

(define ((subst-term/e v e0) syn [bvs (immutable-free-id-set)])
  (subst-term v e0 syn bvs))

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
(define ((has-term/e? syn) e0) (has-term? e0 syn))

;; TODO: move me to separate file?
;; TODO: use turnstile+/type-constraints instead?
;; unify
;; tries to unify e1 with e2, where bvs closes over e1
;; returns list of (stx)pairs [x e], where x \in bvs, and e \in e2,
;; or #f if the args cannot be unified
(define ((unify bvs) e1 e2)
  ;; (printf "unify1: ~a\n" (stx->datum e1))
  ;; (printf "unify2: ~a\n" (stx->datum e2))
  (syntax-parse (list e1 e2)
    [(x:id e) ; found a possible binidng
     #:when (member #'x (stx->list bvs) free-identifier=?)
     ;       #:do[(printf "found: ~a = ~a\n" (stx->datum #'x) (stx->datum #'e))]
     (list #'(x e))]
#;    [(e x:id) ; found a possible binidng
     #:when (member #'x (stx->list bvs) free-identifier=?)
     ;       #:do[(printf "found: ~a = ~a\n" (stx->datum #'x) (stx->datum #'e))]
     (list #'(x e))]
    [((~and (~literal #%plain-app) x)
      (~and (~literal #%plain-app) y))
     #:do[(define da1 (syntax-property #'x 'display-as))
          (define da2 (syntax-property #'y 'display-as))]
     #:when (or (and da1 da2 (stx-e da1) (stx-e da2) (free-identifier=? da1 da2))
                (or (and (not da1) (not da2))
                    (and (not da1) da2 (not (stx-e da2))) ; why sometimes #'#f?
                    (and da1 (not (stx-e da1)) (not da2)))
                (and da1 da2 (not (stx-e da1)) (not (stx-e da2))))
     null]
    [((~and (~not (~literal #%plain-app)) x:id)
      (~and (~not (~literal #%plain-app)) y:id))
     #:when (free-identifier=? #'x #'y)
     null]
    [(((~literal #%plain-lambda) (x) e1)
      ((~literal #%plain-lambda) (y) e2))
     ((unify bvs) #'e1 (subst #'x #'y #'e2))]
    [((e1 ...) (e2 ...))
     #:do[(define e1-lst (stx->list #'(e1 ...)))
          (define e2-lst (stx->list #'(e2 ...)))]
     #:when (= (length e1-lst) (length e2-lst))
     ;; performs a fold, but stops on first fail
     (let L ([acc null] [e1s e1-lst] [e2s e2-lst])
       (cond
         [(and (null? e1s) (null? e2s)) acc]
         [else
          (define e1 (car e1s))
          (define e2 (car e2s))
          (define res ((unify bvs) e1 e2))
          ;; TODO: subst `res` into (cdr e1s) and (cdr e2s)
          (and res
               (L (append res acc) (cdr e1s) (cdr e2s)))]))]
    [((~and (~not (~literal #%plain-app)) d1) ; datums
      (~and (~not (~literal #%plain-app)) d2))
     #:when (equal? (syntax-e #'d1) (syntax-e #'d2))
     null]
    [_ #f]))

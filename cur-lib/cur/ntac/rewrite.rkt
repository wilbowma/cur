#lang s-exp "../main.rkt"
;; Rewrite, using PM equality (the "standard" one)

(provide (for-syntax reflexivity
                     replace
                     rewrite
                     by-replace
                     by-rewrite
                     by-rewriteL
                     (rename-out [by-rewrite by-rewriteR])))

(require
 "../stdlib/sugar.rkt"
 "../stdlib/equality.rkt"
 "base.rkt"
 "standard.rkt"
  (for-syntax "utils.rkt"
              (only-in macrotypes/typecheck-core subst substs)
              macrotypes/stx-utils
              racket/dict
              racket/match
              syntax/stx
              (for-syntax racket/base syntax/parse)))

(begin-for-syntax

  (define (reflexivity ptz)
    (match-define (ntt-hole _ goal) (nttz-focus ptz))
    (ntac-match goal
     [(~== ty a b) ((fill (exact #'(refl ty a))) ptz)]))

  ;; rewrite tactics ----------------------------------------------------------

  ;; surface rewrite tactics --------------------
  (define-syntax (by-rewrite syn)
    (syntax-case syn ()
      [(_ H . es)
       #`(fill (rewrite #'H #:inst-args #'es))]))

  (define-syntax (by-rewriteL syn)
    (syntax-case syn ()
      [(_ H . es)
       #`(fill (rewrite #'H #:left? #t #:inst-args #'es))]))

  ;; internal rewrite tactic --------------------
  ;; - surface tactics all defined in terms of this one

  ;; unify
  ;; tries to unify e1 with e2, where bvs closes over e1
  ;; returns list of (stx)pairs [x e], where x \in bvs, and e \in e2,
  ;; or #f if the args cannot be unified
  (define ((unify bvs) e1 e2)
    ;; (printf "unify1: ~a\n" (syntax->datum e1))
    ;; (printf "unify2: ~a\n" (syntax->datum e2))
    (syntax-parse (list e1 e2)
      [(x:id e) ; found a possible binidng
       #:when (member #'x (syntax->list bvs) free-identifier=?)
       (list #'(x e))]
      [(x:id y:id) #:when (free-identifier=? #'x #'y) null]
      [((e1 ...) (e2 ...))
       #:do[(define e1-lst (syntax->list #'(e1 ...)))
            (define e2-lst (syntax->list #'(e2 ...)))]
       #:when (= (length e1-lst) (length e2-lst))
       ;; performs a fold, but stops on first fail
       (let L ([acc null] [e1s e1-lst] [e2s e2-lst])
         (cond
           [(and (null? e1s) (null? e2s)) acc]
           [else
            (define e1 (car e1s))
            (define e2 (car e2s))
            (define res ((unify bvs) e1 e2))
            (and res
                 (L (append res acc) (cdr e1s) (cdr e2s)))]))]
      [(d1 d2) #:when (equal? (syntax-e #'d1) (syntax-e #'d2)) null] ; datums
      [_ #f]))

  ;; The theorem "H" to use for the rewrite is either:
  ;; - `thm` arg --- from previously defined define-theorem
  ;; - or (dict-ref ctxt name) --- usually an IH
  ;; H must be expanded and can have shape:
  ;; - (~== ty L R)
  ;;   - already instantiated
  ;; - (~Π [x : ty] ... (~== ty L R))
  ;;   - x ... is instantiated with `es`
  ;; L/R then marked as "source" and "target":
  ;; - [default] L = tgt, R = src, ie, replace "L" with "R" (ie coq rewrite ->)
  ;; - if left? = #t, flip and replace "R" with "L" (ie coq rewrite <-)
  (define ((rewrite name #:left? [left-src? #f] #:inst-args [inst-args_ #'()]) ctxt pt)
    (match-define (ntt-hole _ goal) pt)
    (ntac-match (or (dict-ref ctxt name #f) ; thm in ctx
                    (typeof (expand/df name))) ; prev proved tm
     [(~or
       (~and (~== TY L R) ; already-instantiated thm
             (~parse inst-args inst-args_))
       (~and (~Π [X : τX] ... (~and body (~== TY thm/L/uninst thm/R/uninst)))
             (~parse inst-args
                     (if (= (stx-length #'(X ...)) (stx-length inst-args_))
                         (stx-map
                          (λ (e)
                            (cur-normalize e #:local-env (ctxt->env ctxt)))
                          inst-args_)
                         ; else search
                         (syntax-parse goal
                           [(~== _ goal/L goal/R)
                            (let ([x+es
                                   (or
                                    (find-in (if left-src? #'thm/R/uninst #'thm/L/uninst)
                                             #'goal/L
                                             (unify #'(X ...)))
                                    (find-in (if left-src? #'thm/R/uninst #'thm/L/uninst)
                                             #'goal/R
                                             (unify #'(X ...))))])
                              (map ; extract es
                               (λ (x+es) (cadr (syntax-e (car x+es))))
                               (filter ; filter out #f
                                (λ (x) x)
                                (map ; lookup in result of unification
                                 (λ (x)
                                   (member x (or x+es null)
                                           (λ (x x+e)
                                             (free-identifier=? x (stx-car x+e)))))
                                 (syntax->list #'(X ...))))))])))
             (~parse (L R) (stx-map
                            (λ (x) (cur-normalize (reflect x) #:local-env (ctxt->env ctxt)))
                            (substs
                            #'inst-args
                            #'(X ...)
                            #'(thm/L/uninst thm/R/uninst))))))
      ;; set L and R as source/target term, depending on specified direction
      (with-syntax* ([(tgt src) (if left-src? #'(R L) #'(L R))]
                     [tgt-id (format-id #'tgt "~a" (generate-temporary))]
                     [H (format-id name "~a" (generate-temporary))]
                     [thm/inst #`(#,name . inst-args)]
                     [THM (if left-src?
                              #'thm/inst
                              #'(sym TY L R thm/inst))])
        (make-ntt-apply
         goal
         (list
          (make-ntt-hole
           (cur-normalize
            (reflect
             (subst-term #'src #'tgt goal))
             #:local-env (ctxt->env ctxt))))
         (λ (body-pf)
           (quasisyntax/loc goal
             (new-elim
              THM
              (λ [tgt-id : TY]
                (λ [H : (== TY src tgt-id)]
                  #,(subst-term #'tgt-id #'tgt goal)))
              #,body-pf)))))]))

  (define ((replace ty from to) ctxt pt)
    (match-define (ntt-hole _ goal) pt)
    ;; (define ty (transfer-scopes goal ty_ ctxt))
    ;; (define from (transfer-scopes goal from_ ctxt))
    ;; (define to (transfer-scopes goal to_ ctxt))
    (with-syntax ([tgt-id (format-id from "tgt")]
                  [H (format-id from "H")])
      (make-ntt-apply
       goal
       (list
        (make-ntt-hole
         (cur-normalize
          (reflect
           (subst-term to from goal))
          #:local-env (ctxt->env ctxt)))
        (make-ntt-hole (quasisyntax/loc goal (== #,ty #,to #,from))))
       (lambda (body-pf arg-pf)
         (quasisyntax/loc goal
           ((λ [H : (== #,ty #,to #,from)]
              (new-elim
               H
               (λ [tgt-id : #,ty]
                 (λ [H : (== #,ty #,to tgt-id)]
                   #,(subst-term #'tgt-id from goal)))
               #,body-pf))
            #,arg-pf))))))

  (define-syntax (by-replace syn)
    (syntax-case syn ()
      [(_ ty from to)
       #`(fill (replace #'ty #'from #'to))])))

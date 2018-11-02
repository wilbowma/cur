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
#;  (define ((unify bvs) e1 e2)
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
  ;; H can have shape:
  ;; - (== ty L R)
  ;; - (∀ [x : ty] ... (== ty L R))
  ;;   - x ... instantiated with `es`
  ;; - or expanded versions of the above
  ;; L/R then marked as "source" and "target":
  ;; - [default] L = tgt, R = src, ie, replace "L" with "R" (ie coq rewrite ->)
  ;; - if left? = #t, flip and replace "R" with "L" (ie coq rewrite <-)
  (define ((rewrite name #:left? [left? #f] #:inst-args [inst-args #'()]) ctxt pt)
    (match-define (ntt-hole _ goal) pt)
    (ntac-match (or (dict-ref ctxt name #f) ; thm in ctx
                  (typeof (expand/df name))) ; prev proved tm
     [(~or
       (~== TY L R) ; already-instantiated thm
       (~and (~Π [X : τX] ... body)
             (~parse (~== TY L R) (substs inst-args #'(X ...) #'body)))
       ; ∀ thm
#;       (~and
        nested-∀-thm
        (~parse ; flattened ∀-thm
         ((~datum Π)
          [x0:id _ ty0] ... ; flattened bindings
          (~and
           (~or ((~literal ==) TY L/uninst R/uninst)  ; unexpanded ==
                (~== TY L/uninst R/uninst)) ; expanded ==
           ;; compute es, by either:
           ;; - fixing hygiene in es_
           ;; - or searching goal
           (~parse
            es
            (if (= (length (syntax->list #'(x0 ...)))
                   (length (syntax->list es_)))
                ;; instantiate with given es_
                ;; TODO: why are the scopes on es_ not right? bc of eval?
                ;; - eg, they dont see the intros
                ;; - workaround for now: manually add them, creating es
                ;;   - to get the right scope, either:
                ;;     - look up e in the ctxt (if id)
                ;;     - find it in the goal
                (map
                 (λ (e) (or (and (identifier? e)
                                 (for/first ([k (dict-keys ctxt)]
                                             #:when (free-identifier=? k e))
                                   k))
                            (find-in e goal)))
                 (syntax->list es_))
                ;; find es in goal to instantiate thm with
                (let ([x+es
                       (find-in (if left? #'R/uninst #'L/uninst)
                                goal
                                (unify #'(x0 ...))
                                #;(λ (x y)
                                  (define res ((unify #'(x0 ...)) x y))
                                  (and (not (null? res)) res)))])
                  (map ; extract es
                   (λ (x+es) (cadr (syntax-e (car x+es))))
                   (filter ; filter out #f
                    (λ (x) x)
                    (map ; lookup in result of unification
                     (λ (x)
                       (member x (or x+es null)
                               (λ (x x+e)
                                 (free-identifier=? x (stx-car x+e)))))
                     (syntax->list #'(x0 ...))))))))
           ;; type check that given es match ty required by the thm
           (~fail
            #:unless (and
                      (= (length (syntax->list #'(x0 ...)))
                         (length (syntax->list #'es)))
                      (andmap
                       (λ (e ty) (cur-type-check? e ty #:local-env (ctxt->env ctxt)))
                       (syntax->list #'es)
                       (syntax->list #'(ty0 ...))))
            (format
             (string-append
             "given terms ~a have wrong arity or types ~a; "
             "or, failed to instantiate thm ~a: ~a "
             "(try supplying explicit instantiation terms?)\n")
             (syntax->datum es_)
             (map
              (λ (e)
                (define ty (dict-ref ctxt e))
                (and ty (syntax->datum ty)))
              (syntax->list #'es))
             (and real-name (syntax->datum real-name))
             (and thm (syntax->datum thm))))
           ;; prevent accidental capture (why is this needed?)
           (~parse xs* (generate-temporaries #'(x0 ...)))
           ;; instantiate the left/right components of the thm with es
           (~parse L (substs (syntax->list #'es)
                             (syntax->list #'xs*)
                             (substs (syntax->list #'xs*) (syntax->list #'(x0 ...)) #'L/uninst)))
           (~parse R (substs (syntax->list #'es)
                             (syntax->list #'xs*)
                             (substs (syntax->list #'xs*) (syntax->list #'(x0 ...)) #'R/uninst)))))
         (flatten-Π #'nested-∀-thm))))
      ;; set L and R as source/target term, depending on specified direction
      (with-syntax* ([(tgt src) (if left? #'(R L) #'(L R))]
                     [tgt-id (format-id #'tgt "~a" (generate-temporary))]
                     [H (format-id name "~a" (generate-temporary))]
                     [thm/inst #`(#,name . #,inst-args)]
                     [THM (if left?
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

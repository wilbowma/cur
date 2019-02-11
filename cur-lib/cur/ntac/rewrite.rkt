#lang s-exp "../main.rkt"
;; Rewrite, using PM equality (the "standard" one)

(provide (for-syntax reflexivity
                     replace
                     rewrite
                     symmetry
                     by-apply
                     by-replace
                     by-rewrite
                     by-rewriteL
                     by-symmetry
                     (rename-out [by-rewrite by-rewriteR])
                     elim-False
                     by-inversion))

(require
 "../stdlib/prop.rkt" ; for False, see inversion
 "../stdlib/sugar.rkt"
 "../stdlib/equality.rkt"
 "base.rkt"
 "standard.rkt"
  (for-syntax "ctx.rkt" "utils.rkt"
              (only-in macrotypes/typecheck-core subst substs)
              macrotypes/stx-utils
              racket/list
              racket/match
              racket/pretty
              syntax/stx
              (for-syntax racket/base syntax/parse)))

(begin-for-syntax

  ;; TODO: handle Π goals
  (define (reflexivity ptz)
    (match-define (ntt-hole _ goal) (nttz-focus ptz))
    (ntac-match goal
     [(~== ty a b) ((fill (exact #`(refl #,(unexpand #'ty) #,(unexpand #'a)))) ptz)]))

  (define (symmetry ctxt pt)
    (match-define (ntt-hole _ goal) pt)
    (ntac-match goal
     [(~== TY L R)
      (make-ntt-apply
       goal
       (list (make-ntt-hole (normalize #'(== TY R L) ctxt)))
       (λ (pf)
         (quasisyntax/loc goal
           (sym #,(unexpand #'TY) #,(unexpand #'R) #,(unexpand #'L) #,pf))))]))

  (define-syntax (by-symmetry syn)
    (syntax-case syn ()
      [_
       #`(fill symmetry)]))

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

  ;; MOVEME (to utils?):
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
      [((~and (~literal #%plain-app) x)
        (~and (~literal #%plain-app) y))
       #:do[(define da1 (syntax-property #'x 'display-as))
            (define da2 (syntax-property #'y 'display-as))]
       #:when (or (and da1 da2 (stx-e da1) (stx-e da2) (free-identifier=? da1 da2))
                  (and (not da1) (not da2))
                  (and da1 da2 (not (stx-e da1)) (not (stx-e da2))))
       null]
      [((~and (~not (~literal #%plain-app)) x:id)
        (~and (~not (~literal #%plain-app)) y:id))
       #:when (free-identifier=? #'x #'y)
       null]
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
      [((~and (~not (~literal #%plain-app)) d1) ; datums
        (~and (~not (~literal #%plain-app)) d2))
       #:when (equal? (syntax-e #'d1) (syntax-e #'d2))
       null]
      [_ #f]))

  ;; like unify, but with no bvs
  ;; - used in inversion
  (define (unify/open e1 e2)
    ;; (printf "unify/open1: ~a\n" (syntax->datum e1))
    ;; (printf "unify/open2: ~a\n" (syntax->datum e2))
    (syntax-parse (list e1 e2)
      [(x:id e) ; found a possible binidng
       (list #'(x e))]
      [(e x:id) ; found a possible binidng
       (list #'(e x))]
      [(((~literal #%plain-app) f1:id e1 ...)
        ((~literal #%plain-app) f2:id e2 ...))
       #:when (free-identifier=? #'f1 #'f2)
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
            (define res (unify/open e1 e2))
            (and res
                 (L (append res acc) (cdr e1s) (cdr e2s)))]))]
      [(((~literal #%plain-app) f1:id . _)
        ((~literal #%plain-app) f2:id . _))
       #:when (not (free-identifier=? #'f1 #'f2))
       (list #f)]
      [_ (list (list e1 e2))]))

  ;; The theorem "H" to use for the rewrite is either:
  ;; - `thm` arg --- from previously defined define-theorem
  ;; - or (ctx-lookup ctxt name) --- usually an IH
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
    (ntac-match (or (ctx-lookup ctxt name) ; thm in ctx
                    (typeof (expand/df name))) ; prev proved tm
     [(~or
       (~and (~== TY L R) ; already-instantiated thm
             (~parse inst-args inst-args_))
       (~and (~Π [X : τX] ... (~and body (~== TY/uninst thm/L/uninst thm/R/uninst)))
             (~parse inst-args
                     (if (= (stx-length #'(X ...)) (stx-length inst-args_))
                         (stx-map (normalize/ctxt ctxt) inst-args_)
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
             (~parse (TY L R) (stx-map
                            (normalize/ctxt ctxt)
                            (substs
                            #'inst-args
                            #'(X ...)
                            #'(TY/uninst thm/L/uninst thm/R/uninst))))))
      ;; set L and R as source/target term, depending on specified direction
      (with-syntax* ([(tgt src) (if left-src? #'(R L) #'(L R))]
                     [tgt-id (format-id #'tgt "~a" (generate-temporary))]
                     [H (format-id name "~a" (generate-temporary))]
                     [thm/inst #`(#,name #,@(stx-map unexpand #'inst-args))]
                     [THM (if left-src?
                              #'thm/inst
                              #`(sym #,(unexpand #'TY) #,(unexpand #'L) #,(unexpand #'R) thm/inst))])
        (make-ntt-apply
         goal
         (list (make-ntt-hole (normalize (subst-term #'src #'tgt goal) ctxt)))
         (λ (body-pf)
           (quasisyntax/loc goal
             (new-elim
              THM
              (λ [tgt-id : #,(unexpand #'TY)]
                (λ [H : (== #,(unexpand #'TY) #,(unexpand #'src) tgt-id)]
                  #,(unexpand (subst-term #'tgt-id #'tgt goal))))
              #,body-pf)))))]))

  ;; replace tactic
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
        (make-ntt-hole (normalize (subst-term to from goal) ctxt))
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
       #`(fill (replace #'ty #'from #'to))]))

;; apply tactic --------------------

  (define-syntax (by-apply syn)
    (syntax-case syn ()
      [(_ H . es)
       #`(fill (apply-fn #'H #:inst-args #'es))]))

  ;; The theorem "H" to apply is either:
  ;; - `thm` arg --- from previously defined define-theorem
  ;; - or (ctx-lookup ctxt name) --- usually an IH
  ;; H must be expanded and must have shape:
  ;; - (~Π [x : ty] ... [X : antecedent] ... consequent))
  ;; - where each antecedent ... is either:
  ;;   1) == type
  ;;   2) X is "tmp" tyvar (generated by ->)
  ;; - x ... is instantiated with `inst-args_` or inferred
  (define ((apply-fn name #:inst-args [inst-args_ #'()]) ctxt pt)
    (match-define (ntt-hole _ goal) pt)
    (ntac-match (or (ctx-lookup ctxt name) ; thm in ctx
                    (typeof (expand/df name))) ; prev proved tm
     [(~and (~Π [X_ : τX_] ... consequent)
            (~parse (([X τX] ...) ; only try to infer named args
                     ([_ antecedent] ...))
                    (call-with-values
                     (λ () ; antes are 1) == type, or 2) "tmp" tyvar
                       (splitf-at
                        (stx->list #'([X_ τX_] ...))
                        (syntax-parser
                          [(_ (~== _ _ _)) #f]
                          [(X:id _) (not (syntax-property #'X 'tmp))])))
                     list))
            (~parse inst-args
                    (if (= (stx-length #'(X ...)) (stx-length inst-args_))
                        (stx-map (normalize/ctxt ctxt) inst-args_)
                        ; else search
                        (let ([x+es (find-in #'consequent goal (unify #'(X ...)))])
                          (map ; extract es
                           (λ (x+es) (cadr (syntax-e (car x+es))))
                           (filter ; filter out #f
                            (λ (x) x)
                            (map ; lookup in result of unification
                             (λ (x)
                               (member x (or x+es null)
                                       (λ (x x+e)
                                         (free-identifier=? x (stx-car x+e)))))
                             (syntax->list #'(X ...))))))))
            (~fail #:unless (stx-length=? #'(X ...) #'inst-args)
                   (format "by-apply: could not infer instantiation of: ~a\n"
                           (stx->datum name))))
        (make-ntt-apply
         goal
         (stx-map ; each ante is a new subgoal; TODO: should be fold?
          (λ (ante)
            (make-ntt-hole
             (normalize (substs #'inst-args #'(X ...) ante) ctxt)))
          #'(antecedent ...))
         (λ body-pfs
           (quasisyntax/loc goal (#,name #,@#'inst-args . #,body-pfs))))]))

;; inversion tactic --------------------------------------------------

  (define-syntax (by-inversion syn)
    (syntax-case syn ()
      [(_ H) #`(fill (inversion #'H #'()))]
      [(_ H #:extra-names . names) #`(fill (inversion #'H #'names))]))

  (define-syntax (elim-False syn)
    (syntax-parse syn
      [:id #'(fill (elim-False-fn))]))
  (define ((elim-False-fn) ctxt pt)
    (match-define (ntt-hole _ goal) pt)
    (make-ntt-apply
     goal
     (list (make-ntt-hole #'False))
     (λ (body-pf) ; proof of false
       (quasisyntax/loc goal
         (new-elim #,body-pf (λ y #,goal))))))

  ;; mk-nat-elims:
  ;; - creates (nested) elim exprs for input nat
  ;; - TODO: for now, input is only iso morphic to Nat
  ;;   - TODO: use actual constructor patterns
  ;; - used by False-producing fn in inversion
  ;; - arg is rhs of equality type
  (define (mk-nat-elims r x)
    (syntax-parse r
      [((~literal #%plain-app) :id)   #`(new-elim #,x (λ x Type) False (λ x ih True))]
      [((~literal #%plain-app) :id n) #`(new-elim #,x (λ x Type) True (λ x ih #,(mk-nat-elims #'n #'x)))]))

  ;; simplified inversion tactic
  (define ((inversion name names) ctxt pt)
    (match-define (ntt-hole _ goal) pt)
    (ntac-match (or (ctx-lookup ctxt name) ; thm in ctx
                    (typeof (expand/df name))) ; prev proved tm
     [(~== TY L R)
      ;; TODO: look up constructors of TY
      ;; for now, only Nat supported
      ;; TODO: check (length names) == (length eqs)
      (let* ([eqs (unify/open #'L #'R)]
             [eq-tys (stx-map (λ (e) (if e #`(== TY . #,e) #'False)) eqs)]
             [names (if (null? (stx-e names))
                        (stx-map
                         (λ _ (datum->syntax name (stx-e (generate-temporary #'H))))
                         eq-tys)
                        names)])
        (make-ntt-apply
         goal
         (list
          (make-ntt-context
           (λ (old-ctxt)
             (foldr
              (λ (x ty ctx)
                (ctx-add ctx x (normalize ty ctx)))
              old-ctxt
              (stx->list names)
              eq-tys))
          (make-ntt-hole goal)))
         (λ (body-pf)
           (let ([n (generate-temporary)]
                 [TY- (unexpand #'TY)])
             (quasisyntax/loc goal
               ;; TODO: right now (length eq-tys) \neq the number of f-equal terms
               ((λ #,@(stx-map (λ (x ty) #`[#,x : #,ty]) names eq-tys)
                  #,body-pf)
                #,(if (andmap (λ (x) x) eqs) ; if eqs has no #f's
                      #`(f-equal
                         #,TY- #,TY-
                         (λ [#,n : #,TY-]
                           (new-elim
                            #,n
                            (λ #,n #,TY-)
                            #,n
                            (λ #,n #,(generate-temporary) #,n)))
                         #,(unexpand #'L) #,(unexpand #'R)
                         #,name)
                      #`(new-elim ; False case
                         #,name
                         (λ x h #,(mk-nat-elims #'R #'x))
                         I))
                      ))))))]))

  )

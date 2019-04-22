#lang s-exp "../main.rkt"
;; Rewrite, using PM equality (the "standard" one)

(provide (for-syntax reflexivity
                     subst
                     replace
                     rewrite
                     symmetry
                     by-apply
                     by-replace
                     by-rewrite
                     by-rewriteL
                     by-symmetry
                     (rename-out [by-rewrite by-rewriteR])))

(require
 "../stdlib/prop.rkt" ; for False (see inversion), And (rewrite)
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
     [(~Π [X : _] ... (~== ty a b))
      ((compose (fill (exact #`(refl #,(unexpand #'ty) #,(unexpand #'a))))
                (fill (intros)))
       ptz)]))

  (define-syntax subst
    (syntax-parser
      [_
       #'(λ (ptz)
           (eval-proof-steps
            ptz
            (for/list ([(H ty) (nttz-context ptz)])
              (syntax-parse ty
                [(~== _ L:id R) #`(by-rewrite #,H)]
                [(~== _ L R:id) #`(by-rewriteL #,H)]
                [_ #'nop]))))]))

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

  (define ((symmetry/in name) ctxt pt)
    (match-define (ntt-hole _ goal) pt)
    (ntac-match (ctx-lookup ctxt name)
     [(~== TY L R)
      (make-ntt-apply
       goal
       (list
        (make-ntt-context
         (λ (old-ctxt)
           (define tmp-ctx (ctx-remove old-ctxt name))
           (ctx-add tmp-ctx name (normalize #'(== TY R L) tmp-ctx)))
         (make-ntt-hole goal)))
       (λ (pf)
         (quasisyntax/loc name
           ((λ [#,name : (== #,(unexpand #'TY) #,(unexpand #'R) #,(unexpand #'L))]
              #,pf)
            (sym #,(unexpand #'TY) #,(unexpand #'L) #,(unexpand #'R) #,name)))))]))

  (define-syntax by-symmetry
    (syntax-parser
      [:id #`(fill symmetry)]
      [(_ #:in H) #`(fill (symmetry/in #'H))]))

  ;; rewrite tactics ----------------------------------------------------------

  ;; surface rewrite tactics --------------------
  (define-syntax (by-rewrite syn)
    (syntax-case syn ()
      [(_ H #:in target)
       #`(fill (rewrite #'H #:inst-args #'() #:in #'target))]
      [(_ H . es)
       #`(fill (rewrite #'H #:inst-args #'es))]))

  (define-syntax (by-rewriteL syn)
    (syntax-case syn ()
      [(_ H #:in target)
       #`(fill (rewrite #'H #:left? #t #:inst-args #'() #:in #'target))]
      [(_ H . es)
       #`(fill (rewrite #'H #:left? #t #:inst-args #'es))]))

  ;; internal rewrite tactic --------------------
  ;; - surface tactics all defined in terms of this one

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
  (define ((rewrite name #:left? [left-src? #f]
                         #:inst-args [inst-args_ #'()]
                         #:in [tgt-name #f])
           ctxt pt)
    (match-define (ntt-hole _ goal) pt)

    (define target ; target of the rewrite is either goal or some hypoth in ctxt
      (or (and tgt-name (ctx-lookup ctxt tgt-name))
          goal))

    (ntac-match (or (ctx-lookup ctxt name) ; thm in ctx
                    (typeof (expand/df name))) ; prev proved tm
     [(~or
       (~and (~or (~== TY L R) ; already-instantiated thm
                  (~and (~And (~Π [_ : L] R) (~Π [_ : R2] L2)) ; iff (only works for entire goal)
                        (~fail #:unless (and (typecheck? #'L #'L2)
                                             (typecheck? #'R #'R2)))))
             (~parse inst-args inst-args_))
       (~and (~Π [X : τX] ... (~and body (~== TY/uninst thm/L/uninst thm/R/uninst)))
             (~parse inst-args
                     (if (= (stx-length #'(X ...)) (stx-length inst-args_))
                         (stx-map (normalize/ctxt ctxt) inst-args_)
                         ; else search
                         (syntax-parse target
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
             (~fail #:unless (stx-length=? #'inst-args #'(X ...))
                    (format "could not infer instantiation of ~a; try adding explicit #:inst-args"
                            (stx->datum name)))
             (~parse (TY L R) (stx-map
                            (normalize/ctxt ctxt)
                            (substs
                            #'inst-args
                            #'(X ...)
                            #'(TY/uninst thm/L/uninst thm/R/uninst))))))
      ;; set L and R as src/tgt term, depending on specified direction
      ;; Naming Note: "tgt" here = "target of subst"; differs from "target" (of rewrite) above
      (with-syntax ([(tgt src) (if left-src? #'(R L) #'(L R))])
        (define new-target (subst-term #'src #'tgt target))
        (if tgt-name
            (let* ([new-ctx (ctx-remove ctxt tgt-name)]
                   [new-target+ (normalize new-target new-ctx)])
              (make-ntt-apply
               goal
               (list
                (make-ntt-context
                 (λ (old-ctxt) (ctx-add new-ctx tgt-name new-target+))
                 (make-ntt-hole goal)))
               (λ (pf)
                 ;; TODO: handle iff (see (not tgt-name) case below)
                 (quasisyntax/loc tgt-name
                   ((λ [#,tgt-name : #,(unexpand new-target+)] #,pf)
                    #,(with-syntax*
                        ([tgt-id (format-id #'tgt "~a" (generate-temporary))]
                         [H (format-id name "~a" (generate-temporary))]
                         [thm/inst #`(#,name #,@(stx-map unexpand #'inst-args))]
                         [THM (if left-src? ; flipped when compared to below
                                  #`(sym #,(unexpand #'TY) #,(unexpand #'L) #,(unexpand #'R) thm/inst)
                                  #'thm/inst)])
                        (quasisyntax/loc name
                          (new-elim
                           THM
                           (λ [tgt-id : #,(unexpand #'TY)]
                             (λ [H : (== #,(unexpand #'TY) #,(unexpand #'tgt) tgt-id)]
                               #,(unexpand (subst-term #'tgt-id #'tgt target))))
                           #,tgt-name))))))))
        (make-ntt-apply
         goal
         (list (make-ntt-hole (normalize new-target ctxt)))
         (λ (pf)
           (if (attribute TY) ; rewrite with == type; else rewrite with iff
               (with-syntax*
                 ([tgt-id (format-id #'tgt "~a" (generate-temporary))]
                  [H (format-id name "~a" (generate-temporary))]
                  [thm/inst #`(#,name #,@(stx-map unexpand #'inst-args))]
                  [THM (if left-src?
                           #'thm/inst
                           #`(sym #,(unexpand #'TY) #,(unexpand #'L) #,(unexpand #'R) thm/inst))])
                 (quasisyntax/loc goal
                   (new-elim
                    THM
                    (λ [tgt-id : #,(unexpand #'TY)]
                      (λ [H : (== #,(unexpand #'TY) #,(unexpand #'src) tgt-id)]
                        #,(unexpand (subst-term #'tgt-id #'tgt target))))
                    #,pf)))
               (quasisyntax/loc goal
                 (match #,name #:as #,name #:return #,goal
                  [(conj l->r r->l)
                   #,(if left-src? #`(l->r #,pf) #`(r->l #,pf))])))))))]))

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
      [(_ H)
       #`(fill (apply-fn #'H #:with #'()))]
      [(_ H #:with . es)
       #`(fill (apply-fn #'H #:with #'es))]
      [(_ H #:with-var . es)
       #`(fill (apply-fn #'H #:with-var #'es))]
      [(_ H #:in target)
       #`(fill (apply-fn #'H #:in #'target))]))

  ;; The theorem `name` to apply is either:
  ;; - from previously defined define-theorem
  ;; - or (ctx-lookup ctxt name) --- often an IH
  ;; `name` must be expanded and must have shape:
  ;; - (~Π [x : ty] ... [X : antecedent] ... consequent))
  ;; - where each antecedent ... is either:
  ;;   1) == type
  ;;   2) X is "tmp" tyvar (generated by ->)
  ;; - x ... is instantiated with `inst-args_` or inferred
  ;; - whereas inst-args is positional, and is just the term,
  ;;   `inst-var+args` includes the binder name
  ;; `name` is applied to `tgt-name` if it is not #f, o.w. the proof of goal
  (define ((apply-fn name #:with [inst-args_ #'()]
                          #:with-var [inst-var+args_ #'()]
                          #:in [tgt-name #f]) ctxt pt)
    (match-define (ntt-hole _ goal) pt)
    (define target
      (or (and tgt-name (ctx-lookup ctxt tgt-name))
          goal))
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
                          [(_ (~== _ _ _)) #f] ; TODO: split on Prop instead?
                          [(X:id _) (not (syntax-property #'X 'tmp))])))
                     list))
            (~parse inst-var-args
                    (stx-map ; convert binder X ... with correct scope
                     (syntax-parser
                       [(x:id e)
                        #`(#,(for/first ([X (in-stx-list #'(X ...))]
                                         #:when (equal? (stx-e X) (stx-e #'x)))
                               X)
                           e)])
                     inst-var+args_))
            (~parse inst-args
                    (if (= (stx-length #'(X ...)) (stx-length inst-args_))
                        (stx-map (normalize/ctxt ctxt) inst-args_)
                        ; else search
                        (let ([x+es (stx-append
                                     ;; add given constraints to unification result
                                     #'inst-var-args
                                     (syntax-parse #'inst-var-args
                                       [((x:id e) ...)
                                        (or
                                         (find-in
                                          (normalize (substs #'(e ...) #'(x ...) #'consequent) ctxt)
                                          (normalize (substs #'(e ...) #'(x ...) target) ctxt)
                                          (unify #'(X ...)))
                                         (stx-ormap
                                          (λ (a)
                                            (find-in
                                             (normalize (substs #'(e ...) #'(x ...) a) ctxt)
                                             (normalize (substs #'(e ...) #'(x ...) target) ctxt)
                                             (unify #'(X ...))))
                                          #'(antecedent ...))
                                         null)]))])
                          (map ; extract es
                           (λ (x+es) (cadr (syntax-e (car x+es))))
                           (filter ; filter out #f
                            (λ (x) x)
                            (map ; lookup in result of unification
                             (λ (x) (member x x+es
                                     (λ (x x+e) (free-identifier=? x (stx-car x+e)))))
                             (syntax->list #'(X ...))))))))
            (~fail #:unless (stx-length=? #'(X ...) #'inst-args)
                   (raise-ntac-goal-exception
                    "by-apply: could not infer instantiation of: ~a; try explicit #:with or #:with-var args?\n"
                    (stx->datum name)))
            (~parse new-thm
                    (normalize
                     (substs #'inst-args
                             #'(X ...)
                             (if tgt-name (stx-car #'(antecedent ...)) #'consequent))
                     ctxt))
            (~fail #:unless (typecheck? #'new-thm target)
                   (raise-ntac-goal-exception
                    "by-apply: applying ~a does not produce term with goal type ~a"
                   (stx->datum name) (stx->datum #`#,(resugar-type target)))))
      (if tgt-name
          (let ([new-thm (substs #'inst-args #'(X ...) #'consequent)])
            (make-ntt-apply
             goal
             (list
              (make-ntt-context
               (λ (old-ctxt)
                 (define tmp-ctx (ctx-remove old-ctxt tgt-name))
                 (ctx-add tmp-ctx tgt-name (normalize new-thm tmp-ctx)))
               (make-ntt-hole goal)))
             (λ (pf)
               (quasisyntax/loc tgt-name
                 ((λ [#,tgt-name : #,(unexpand new-thm)]
                    #,pf)
                  (#,name #,@(stx-map unexpand #'inst-args) #,tgt-name))))))
          (make-ntt-apply
           goal
           (stx-map ; each ante is a new subgoal; TODO: should be fold?
            (λ (ante)
              (make-ntt-hole
               (normalize (substs #'inst-args #'(X ...) ante) ctxt)))
            #'(antecedent ...))
           (λ body-pfs
             (quasisyntax/loc goal (#,name #,@(stx-map unexpand #'inst-args) . #,body-pfs)))))]))
  )

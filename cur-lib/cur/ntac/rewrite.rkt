#lang cur/metantac

;; Rewrite, using PM equality (the "standard" one)

(provide (for-syntax reflexivity
                     substR substL (rename-out [substL subst])
                     rewrite
                     apply-fn
                     by-apply
                     by-replace
                     by-rewrite
                     by-rewriteL
                     by-symmetry
                     (rename-out [by-rewrite by-rewriteR])))

(require cur/stdlib/prop ; for False (see inversion), And (rewrite)
         cur/stdlib/equality
         "standard.rkt")

(begin-for-syntax

  ;; TODO: handle Π goals
 (define-tactical reflexivity
   [:id #:current-goal (~Π [X : _] (... ...) (~== ty a b))
    ((compose (fill (exact #`(refl #,(unexpand #'ty) #,(unexpand #'a))))
              (fill (intros)))
     $ptz)])

  (define-syntax substR
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
  ;; when L and R are both id, rewrite L with R, ie prefer rewriteL
  (define-syntax substL
    (syntax-parser
      [_
       #'(λ (ptz)
           (define ctxt (nttz-context ptz))
           (eval-proof-steps
            ptz
            (let L ([Hs (ctx-ids ctxt)])
              (if (null? Hs)
                  null
                  (let ([H (car Hs)])
                    (append 
                     (syntax-parse (ctx-lookup ctxt H)
                       [(~== _ L R:id)
                        (cons #`(by-rewriteL #,H)
                              (for/list ([H2 (ctx-ids ctxt)]
                                         #:when (and (not (free-id=? H H2))
                                                     (has-term? #'R (ctx-lookup ctxt H2))))
                                #`(by-rewriteL #,H #:in #,H2)))]
                       [(~== _ L:id R)
                        (cons #`(by-rewrite #,H)
                              (for/list ([H2 (ctxt-ids ctxt)]
                                         #:when (and (not (free-id=? H H2))
                                                     (has-term? #'L (ctx-lookup ctxt H2))))
                                #`(by-rewrite #,H #:in #,H2)))]
                       [_ null])
                     (L (cdr Hs))))))))]))

  (define-tactic by-symmetry
    [:id #:current-goal (~== TY L R)
     ($fill (sym #,(unexpand #'TY) #,(unexpand #'R) #,(unexpand #'L) #,pf)
            #:where [⊢ pf : (normalize #'(== TY R L) $ctxt)])]
    [(_ #:in H)
     (syntax-parse (ctx-lookup $ctxt #'H)
       [(~== TY L R)
        ($fill
         ((λ [H : (== #,(unexpand #'TY) #,(unexpand #'R) #,(unexpand #'L))]
            #,pf)
          (sym #,(unexpand #'TY) #,(unexpand #'L) #,(unexpand #'R) H))
         #:where [#:update #'H : #'(== TY R L) ⊢ pf : $goal])])])

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

    (when (and tgt-name (not (ctx-has-id? ctxt tgt-name)))
      (raise-ntac-goal-exception
       "rewrite #:in: ~a id unbound in ctxt" (stx->datum tgt-name)))

    (define target ; target of the rewrite is either goal or some hypoth in ctxt
      (or (and tgt-name (ctx-lookup ctxt tgt-name))
          goal))

    (ntac-match (or (ctx-lookup ctxt name) ; thm in ctx
                    (typeof (expand/df name))) ; prev proved thm
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
            (let*-values ([(ctxt-to-change ctxt-unchanged) ; TODO: ctxt-to-change needs to be in proof term?
                           (ctx-partition/ty
                            (ctx-remove ctxt tgt-name)
                            (λ (t) (has-term? tgt-name t)))]
                          [(new-target+) (normalize new-target ctxt-unchanged)])
              (make-ntt-apply
               goal
               (list
                (make-ntt-context
                 (λ (old-ctxt)
                   (ctx-append (ctx-add ctxt-unchanged tgt-name new-target+)
                               ctxt-to-change))
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
  (define-tactic (by-replace ty from to)
    (with-syntax ([tgt-id (format-id #'from "tgt")]
                  [H (format-id #'from "H")])
      ($fill ((λ [H : (== ty to from)]
              (new-elim
               H
               (λ [tgt-id : ty]
                 (λ [H : (== ty to tgt-id)]
                   #,(subst-term #'tgt-id #'from $goal)))
               #,body-pf))
              #,arg-pf)
        #:where [⊢ body-pf : (normalize (subst-term #'to #'from $goal) $ctxt)]
                [⊢ arg-pf : #'(== ty to from)])))

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
    (define num-inst-args (stx-length inst-args_))
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
            (~parse ((X* ...) extra-antes inst-args)
                    (if (zero? num-inst-args) ; no inst-args given, try to infer
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
                          ;; produce:
                          ;; - X in (X ...) that has unify result (ie, that is in x+es)
                          ;; - new-antes are Xτ ... for X without unify result (ie, not in x+es)
                          ;; - inst args are the es in x+es, but in the order of (X ...)
                          (let L ([X+τs (stx->list #'([X τX] ...))]
                                  [Xs null] [new-antes null] [inst-args null])
                            (if (null? X+τs)
                                (list (reverse Xs) (reverse new-antes) (reverse inst-args))
                                (let* ([X+τ (car X+τs)]
                                       [maybe-unify-result
                                        (member (stx-car X+τ) x+es
                                                (λ (x x+e)
                                                  (free-identifier=? x (stx-car x+e))))])
                                  (if maybe-unify-result
                                      (L (cdr X+τs)
                                         (cons (stx-car X+τ) Xs)
                                         new-antes
                                         (cons (cadr (syntax-e (car maybe-unify-result))) inst-args))
                                      (L (cdr X+τs)
                                         Xs
                                         (cons (stx-cadr X+τ) new-antes)
                                         inst-args))))))
                        (list (stx-take #'(X ...) num-inst-args) ; X to subst
                              (stx-drop #'(τX ...) num-inst-args) ; extra antes (ie subgoals)
                              (stx-map (normalize/ctxt ctxt) inst-args_))))
            (~parse (antecedent* ...) (stx-append #'extra-antes #'(antecedent ...)))
            (~parse new-thm
                    (normalize
                     (substs #'inst-args
                             #'(X* ...)
                             (if tgt-name (stx-car #'(antecedent* ...)) #'consequent))
                     ctxt))
            (~fail #:unless (typecheck? #'new-thm target)
                   (raise-ntac-goal-exception
                    "by-apply: applying ~a does not produce term with goal type ~a"
                   (stx->datum name) (stx->datum #`#,(resugar-type target)))))
      (if tgt-name
          (let ([new-thm (substs #'inst-args #'(X* ...) #'consequent)])
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
               (normalize (substs #'inst-args #'(X* ...) ante) ctxt)))
            #'(antecedent* ...))
           (λ body-pfs
             (quasisyntax/loc goal (#,name #,@(stx-map unexpand #'inst-args) . #,body-pfs)))))]))
  )

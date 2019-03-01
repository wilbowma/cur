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
                     by-inversion
                     by-discriminate))

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
;       #:do[(printf "found: ~a = ~a\n" (stx->datum #'x) (stx->datum #'e))]
       (list #'(x e))]
      [((~and (~literal #%plain-app) x)
        (~and (~literal #%plain-app) y))
       #:do[(define da1 (syntax-property #'x 'display-as))
            (define da2 (syntax-property #'y 'display-as))]
       #:when (or (and da1 da2 (stx-e da1) (stx-e da2) (free-identifier=? da1 da2))
                  (or (and (not da1) (not da2))
                      (and (not da1) (not (stx-e da2))) ; why sometimes #'#f?
                      (and (not (stx-e da1)) (not da2)))
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
             (~fail #:unless (stx-length=? #'inst-args #'(X ...))
                    (format "could not infer instantiation of ~a; try adding explicit #:inst-args"
                            (stx->datum name)))
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
      [(_ H)
       #`(fill (apply-fn #'H #:with #'()))]
      [(_ H #:with . es)
       #`(fill (apply-fn #'H #:with #'es))]
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
  ;; `name` is applied to `tgt-name` if it is not #f, o.w. the proof of goal
  (define ((apply-fn name #:with [inst-args_ #'()] #:in [tgt-name #f]) ctxt pt)
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
                          [(_ (~== _ _ _)) #f]
                          [(X:id _) (not (syntax-property #'X 'tmp))])))
                     list))
            (~parse inst-args
                    (if (= (stx-length #'(X ...)) (stx-length inst-args_))
                        (stx-map (normalize/ctxt ctxt) inst-args_)
                        ; else search
                        (let ([x+es (or (find-in #'consequent target (unify #'(X ...)))
                                        (stx-ormap
                                         (λ (a) (find-in a target (unify #'(X ...))))
                                         #'(antecedent ...)))])
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
                   (raise-ntac-goal-exception
                    "by-apply: could not infer instantiation of: ~a; try explicit #:with args?\n"
                    (stx->datum name))))
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

;; inversion tactic --------------------------------------------------

  (define-syntax (by-inversion syn)
    (syntax-case syn ()
      [(_ H) #`(fill (inversion #'H #'()))]
      [(_ H #:as . names) #`(fill (inversion #'H #'names))]))

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
         (new-elim #,body-pf (λ y #,(unexpand goal)))))))

  (define ((inversion name names_) ctxt pt)
    (match-define (ntt-hole _ goal) pt)
    (ntac-match (or (ctx-lookup ctxt name) ; thm in ctx
                    (typeof (expand/df name))) ; prev proved tm
     [(~== TY* L* R*)
      (let ([==s null] [terms null] [xx (generate-temporary)])

        ;; FIND is imperative traversal of L and R (makes code much shorter);
        ;; the traversal populates:
        ;; - `==s`: new assumptions
        ;; - `terms`: proofs for new assumptions
        (let FIND ([expr xx] ; current node of the traversal
                   ; mk-term is a fn that produces the proof term to get to `expr`
                   ; usage: (mk-term expr TY L) creates the current proof term
                   [mk-term (λ (stx tgt-ty tgt-base-term)
                              #`(f-equal
                                 #,(unexpand #'TY*) #,(unexpand tgt-ty)
                                 (λ #,xx #,stx)
                                 #,(unexpand #'L*) #,(unexpand #'R*)
                                 #,name))]
                   [TY #'TY*] ; expr's TY
                   [L #'L*]
                   [R #'R*])
;          (printf "FIND: ~a =\n      ~a\n" (stx->datum L) (stx->datum R))
          (syntax-parse (list L R)
            [(((~literal #%plain-app) C1:id e1 ...)
              ((~literal #%plain-app) C2:id e2 ...))
             #:when (has-type-info? TY)
             #:with (_ ([A _] ...) _ (~and Cinfo/As (C _ _)) ...) (get-match-info TY)
             #:when (and (stx-member #'C1 #'(C ...) stx-datum-equal?)
                         (stx-member #'C2 #'(C ...) stx-datum-equal?))
             #:with Cinfos (substs (stx-drop TY 2) #'(A ...) #'(Cinfo/As ...))
             (if (and (free-identifier=? #'C1 #'C2)
                      (stx-length=? #'(e1 ...) #'(e2 ...)))
                 ;; Cs match, keep traversing
                 (stx-map
                  (λ (e1 e2 x+τ)
                    (FIND
                     (stx-car x+τ)
                     (λ (stx tgt-ty tgt-base-term)
                       (mk-term
                        #`(match #,expr #:return #,(unexpand tgt-ty)
                           #,@(stx-map
                               (syntax-parser
                                 [(this-C ([Cx _] ...) _)
                                  #`[(this-C Cx ...)
                                     #,(if (stx-datum-equal? #'C1 #'this-C)
                                           stx
                                           tgt-base-term)]])
                               #'Cinfos))
                        tgt-ty
                        tgt-base-term))
                     (normalize (stx-cadr x+τ) ctxt)
                     e1 e2))
                  (stx-drop #'(e1 ...) (stx-length #'(A ...)))
                  (stx-drop #'(e2 ...) (stx-length #'(A ...)))
                  (stx-cadr   ; find the matching constructor
                   (stx-findf ; returns x+τs args for matching constructor
                    (syntax-parser [(C:id . _) (stx-datum-equal? #'C #'C1)])
                    #'Cinfos)))
                 ;; found contradiction, produce False
                 (begin
                   (set! ==s (cons #'False ==s))
                   (set! terms
                     (cons #`(new-elim ; False case
                              #,name
                              ;; TODO: re-traverse R to generate False term?
                              ;; possible to re-use mk-term here?
                              (λ x h #,(mk-False-term-type #'R* #'x #'TY*))
                              I)
                           terms))))]
            [_ ; found a new assumption
;             #:do[(printf "found: ~a = ~a\n" (stx->datum L) (stx->datum R))]
             (set! ==s (cons #`(== #,(unexpand TY) #,(unexpand L) #,(unexpand R)) ==s))
             (set! terms (cons (mk-term expr TY L) terms))]))

        (define names
          (if (stx-length=? names_ ==s)
              (stx->list names_)
              (stx-map
               (λ _ (datum->syntax name (stx-e (generate-temporary #'H))))
               ==s)))
          
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
              ==s))
          (make-ntt-hole goal)))
         (λ (body-pf)
           (quasisyntax/loc goal
             ((λ #,@(stx-map (mk-bind-stxf unexpand) names ==s)
                #,body-pf)
              #,@terms)))))]))

  ;; Produces the type so that elim of name has type False
  ;; r = RHS of ==
  ;; x = parameter of elim P fn
  ;; ty = type param of == 
  (define (mk-False-term-type r x ty)
    ;; TODO: instantiate Cinfo?
    (define/syntax-parse (_ ([A _] ...) _ (~and Cinfo (C _ _)) ...)
      (get-match-info ty))
    (syntax-parse r
      [((~literal #%plain-app) this-C:id . rst)
       #:when (stx-member #'this-C #'(C ...) stx-datum-equal?)
       #`(match #,x #:return Type
          #,@(stx-map
              (syntax-parser
                [(C ([Cx _] ...) _)
                 #`[(C Cx ...)
                    #,(if (stx-datum-equal? #'this-C #'C)
                          (if (stx-length=? #'(A ...) #'rst) ; nullary constructor
                              #'False
                              ;; TODO:
                              ;; can len (Cx ...) > 1? what to do then?
                              ;; check Cτ = ty?
                              (mk-False-term-type (stx-car #'rst) (stx-car #'(Cx ...)) ty))
                          #'True)]])
              #'(Cinfo ...)))]
      ;; if not data constructor of ty, then treat as base case
      [((~literal #%plain-app) . rst) #'False]))

  (define-syntax (by-discriminate syn)
    (syntax-case syn ()
      [(_ H) #'(discriminate #'H)]))

  (define (discriminate H [H-tmp (generate-temporary #'H-false)])
    (compose (fill (apply-fn H-tmp))
             (fill (elim-False-fn))
             (fill (inversion H (list H-tmp)))))

  )

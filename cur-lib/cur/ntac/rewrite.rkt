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
      [(_ H)
       #`(fill (apply-fn #'H #:with #'()))]
      [(_ H #:with . es)
       #`(fill (apply-fn #'H #:with #'es))]))

  ;; The theorem "H" to apply is either:
  ;; - `thm` arg --- from previously defined define-theorem
  ;; - or (ctx-lookup ctxt name) --- usually an IH
  ;; H must be expanded and must have shape:
  ;; - (~Π [x : ty] ... [X : antecedent] ... consequent))
  ;; - where each antecedent ... is either:
  ;;   1) == type
  ;;   2) X is "tmp" tyvar (generated by ->)
  ;; - x ... is instantiated with `inst-args_` or inferred
  (define ((apply-fn name #:with [inst-args_ #'()]) ctxt pt)
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
        (let FIND ([expr xx]
                   ; usage: (mk-term expr TY L) creates the current proof term
                   [mk-term (λ (stx tgt-ty tgt-base-term)
                              #`(f-equal
                                 #,(unexpand #'TY*) #,tgt-ty
                                 (λ #,xx #,stx)
                                 #,(unexpand #'L*) #,(unexpand #'R*)
                                 #,name))]
                   [TY #'TY*] ; expr's TY
                   [L #'L*]
                   [R #'R*])
          (syntax-parse (list L R)
            [(e1 e2) ; found a possible binding
             #:when (or (identifier? #'e1) (identifier? #'e2))
             (set! ==s (cons #`(== #,TY e1 e2) ==s))
             (set! terms (cons (mk-term expr TY L) terms))]
            [(((~literal #%plain-app) C1:id e1 ...)
              ((~literal #%plain-app) C2:id e2 ...))
             #:when (and (free-identifier=? #'C1 #'C2)
                         (stx-length=? #'(e1 ...) #'(e2 ...)))
             #:do[(define/syntax-parse (_ ([A _] ...) Cinfo_ ...)
                    (get-match-info TY))
                  ;; instantatiate Cinfo_ with concrete params from TY
                  (define concrete-As (stx-drop TY 2))
                  (define Cinfos (substs concrete-As #'(A ...) #'(Cinfo_ ...)))
                  (define/syntax-parse (_ ([Cx* Cτ*] ...) _)
                    (stx-findf ; find the matching constructor
                     (syntax-parser [(C:id . _) (stx-datum-equal? #'C #'C1)])
                     Cinfos))]
             (stx-map
              (λ (e1 e2 x τ)
                (FIND x
                      (λ (stx tgt-ty tgt-base-term)
                        (mk-term
                         #`(match #,expr #:return #,tgt-ty
                            #,@(stx-map
                                (syntax-parser
                                  [(this-C ([Cx Cτ] ...) _)
                                   #`[(this-C Cx ...)
                                      #,(if (stx-datum-equal? #'C1 #'this-C)
                                            stx
                                            tgt-base-term)]])
                                Cinfos))
                         tgt-ty
                         tgt-base-term))
                      (normalize τ ctxt)
                      e1 e2))
              (stx-drop #'(e1 ...) (stx-length #'(A ...)))
              (stx-drop #'(e2 ...) (stx-length #'(A ...)))
              #'(Cx* ...)
              #'(Cτ* ...))]
            [(((~literal #%plain-app) f1:id . _)
              ((~literal #%plain-app) f2:id . _))
             #:when (not (free-identifier=? #'f1 #'f2)) ; False assumption
             (set! ==s (cons #'False ==s))
             (set! terms
                   (cons
                    #`(new-elim ; False case
                       #,name
                       ;; re-traverse R to generate False term,
                       ;; but it should be simpler traversal
                       (λ x h #,(mk-False-term-type #'R* #'x #'TY*))
                       I)
                    terms))]))

        (define names
          (if (null? (stx-e names_))
              (stx-map
               (λ _ (datum->syntax name (stx-e (generate-temporary #'H))))
               ==s)
              (stx->list names_)))
          
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
    (define/syntax-parse (_ ([A _] ...) Cinfo ...)
      (get-match-info ty))
    (syntax-parse r
      [((~literal #%plain-app) this-C:id . rst)
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
              #'(Cinfo ...)))]))  
  )

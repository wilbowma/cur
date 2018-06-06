#lang s-exp "../main.rkt"
(require
 "../stdlib/sugar.rkt"
 "../stdlib/coqeq.rkt"
 "base.rkt"
 "standard.rkt"
 "../curnel/racket-impl/runtime.rkt"
 "../curnel/racket-impl/type-check.rkt"
  (for-syntax "dict-utils.rkt"
              "../curnel/racket-impl/stxutils.rkt"
              "../curnel/racket-impl/runtime-utils.rkt"
              (for-syntax syntax/parse)))

(provide
 (for-syntax
  (rename-out
   [reflexivity coq-reflexivity]
   [by-replace by-coq-replace]
   [rewrite coq-rewrite]
   [rewrite coq-rewriteR]
   [by-rewrite by-coq-rewrite]
   [by-rewrite by-coq-rewriteR]
   [by-rewriteL by-coq-rewriteL]
   [by-rewrite/thm by-coq-rewrite/thm]
   [by-rewriteL/thm by-coq-rewriteL/thm]
   [by-rewrite/expand by-coq-rewrite/expand]
   [by-rewriteL/expand by-coq-rewriteL/expand]
   [by-rewrite/thm/expand by-coq-rewrite/thm/expand]
   [by-rewriteL/thm/expand by-coq-rewriteL/thm/expand])))

;; ported from (ie, started with copy of) prop.rkt
;; differences:
;; - coq= has 2 params, so elim motive and method have 1 less arg
;; - coq= rewrite does not need to propagate "unused" ids
;;   (unlike rewrite with ==) (TODO: why?)

;; require equality (coq=) from cur/stdlib/coqeq
(begin-for-syntax

  (define-syntax ~coq=
    (pattern-expander
     (syntax-parser
       [(_ ty a b)
        #'(_ (_ (_ (~literal coq=) ty) a) b)])))
  
  ;; `reflexivity` is defined here instead of standard.rkt
  ;; because it requires cur/stdlib/prop
  (define (reflexivity ptz)
    (match-define (ntt-hole _ goal) (nttz-focus ptz))
    (ntac-match goal
     [(~coq= ty a b) ((fill (exact #'(coq-refl ty a))) ptz)]))

  ;; rewrite tactics ----------------------------------------------------------
  
  ;; surface rewrite tactics --------------------
  (define-syntax (by-rewrite syn)
    (syntax-case syn ()
      [(_ H . es)
       #`(fill (rewrite #'H #:es #'es))]))

  (define-syntax (by-rewrite/expand syn)
    (syntax-case syn ()
      [(_ H . es)
       #`(fill (rewrite #'H #:es #'es #:expand? #t))]))

  (define-syntax (by-rewriteL syn)
    (syntax-case syn ()
      [(_ H . es)
       #`(fill (rewrite #'H #:left? #t #:es #'es))]))

  (define-syntax (by-rewriteL/expand syn)
    (syntax-case syn ()
      [(_ H . es)
       #`(fill (rewrite #'H #:left? #t #:es #'es #:expand? #t))]))

  (define-syntax (by-rewrite/thm syn)
    (syntax-case syn ()
      [(_ thm . es)
       #`(let ([thm-info (syntax-local-eval #'thm)])
           (fill (rewrite #'thm
                          #:real-name (theorem-info-name thm-info)
                          #:thm (theorem-info-orig thm-info)
                          #:es #'es)))]))

  (define-syntax (by-rewrite/thm/expand syn)
    (syntax-case syn ()
      [(_ thm . es)
       #`(let ([thm-info (syntax-local-eval #'thm)])
           (fill (rewrite #'thm
                          #:real-name (theorem-info-name thm-info)
                          #:thm (identifier-info-type thm-info)
                          #:es #'es)))]))

  (define-syntax (by-rewriteL/thm syn)
    (syntax-case syn ()
      [(_ thm . es)
       #`(let ([thm-info (syntax-local-eval #'thm)])
           (fill (rewrite #'thm
                          #:real-name (theorem-info-name thm-info)
                          #:thm (theorem-info-orig thm-info)
                          #:es #'es
                          #:left? #t)))]))

  (define-syntax (by-rewriteL/thm/expand syn)
    (syntax-case syn ()
      [(_ thm . es)
       #`(let ([thm-info (syntax-local-eval #'thm)])
           (fill (rewrite #'thm
                          #:real-name (theorem-info-name thm-info)
                          #:thm (cur-reflect (identifier-info-type thm-info))
                          #:es #'es
                          #:left? #t)))]))

  ;; internal rewrite tactic --------------------
  ;; - surface tactics all defined in terms of this one

  (define (flatten-Π p)
    (let loop ([p p][binds null])
      (syntax-parse p
        [(_ (~and b [_:id (~datum :) ty]) rst)
         (loop #'rst (cons #'b binds))] ; unexpanded
        #;[(plain-app Π ty (plain-lam (x:id) rst))
         (loop #'rst (cons #'[x : ty] binds))] ; expanded
        [body
         #`(Π #,@(reverse binds) body)])))

  ;; The theorem "H" to use for the rewrite is either:
  ;; - `thm` arg --- from previously defined define-theorem
  ;; - or (dict-ref ctxt name) --- usually an IH
  ;; H can have shape:
  ;; - (coq= ty L R)
  ;; - (∀ [x : ty] ... (coq= ty L R))
  ;;   - x ... instantiated with `es`
  ;; - or expanded versions of the above
  ;; L/R then marked as "source" and "target":
  ;; - [default] L = tgt, R = src, ie, replace "L" with "R" (ie coq rewrite ->)
  ;; - if left? = #t, flip and replace "R" with "L" (ie coq rewrite <-)
  (define ((rewrite name
                    #:real-name [real-name #f] ; ie, define-theorem name
                    #:thm [thm #f]
                    #:left? [left? #f]
                    #:es [es_ #'()]
                    #:expand? [expand? #f]) ; expands thm first before subst; useful for unexpanded IH
           ctxt pt)
    (match-define (ntt-hole _ goal) pt)
    (define H (or thm (dict-ref ctxt name)))
    ;(printf "thm = ~a\n" (syntax->datum H))
    (ntac-match H
     [(~or
       ; already-instantiated thm
       (~and (~coq= TY L R)
             (~parse es es_)) ; es should be #'()
       ; ∀ thm, instantiate with given es
       (~and
        nested-∀-thm
        (~parse ; flattened ∀-thm
         ((~datum Π)
          [x0:id _ ty0] ... ; flattened bindings
          (~and 
           (~or ((~literal coq=) TY L/uninst R/uninst)  ; unexpanded coq=
                (~coq= TY L/uninst R/uninst)) ; expanded coq=
           ;; TODO: why are the scopes on es_ not right? bc of eval?
           ;; - eg, they dont see the intros
           ;; - workaround for now: manually add them, creating es
           ;;   - to get the right scope, either:
           ;;     - look up e in the ctxt (if id)
           ;;     - find it in the goal
           (~parse es
                   (map
                    (λ (e) (or (and (identifier? e)
                                    (for/first ([k (dict-keys ctxt)]
                                                #:when (free-identifier=? k e))
                                      k))
                               (find-in e goal)))
                    (syntax->list es_)))
           ;; type check that given es match ty required by the thm
           (~fail
            #:unless (and
                      (= (length (syntax->list #'(x0 ...)))
                         (length (syntax->list #'es)))
                      (andmap
                       (λ (e ty) (cur-type-check? e ty #:local-env (ctxt->env ctxt)))
                       (syntax->list #'es)
                       (syntax->list #'(ty0 ...))))
            (format "given terms ~a have wrong arity, or wrong types ~a; cant be used with thm ~a: ~a\n"
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
           (~parse L (subst* (syntax->list #'es)
                             (syntax->list #'xs*)
                             (subst* (syntax->list #'xs*) (syntax->list #'(x0 ...)) #'L/uninst)))
           (~parse R (subst* (syntax->list #'es)
                             (syntax->list #'xs*)
                             (subst* (syntax->list #'xs*) (syntax->list #'(x0 ...)) #'R/uninst)))))
         (flatten-Π #'nested-∀-thm))))
      ;; set L and R as source/target term, depending on specified direction
      (with-syntax* ([(tgt src) (if left? #'(R L) #'(L R))]
                     [tgt-id (format-id #'tgt "~a" (generate-temporary))]
                     [H (format-id name "~a" (generate-temporary))]
                     [thm/inst (if thm #`(#,real-name . es) #`(#,name . es))]
                     [THM (if left?
                              #'thm/inst
                              #'(coq=-sym TY L R thm/inst))])
        ;; (printf "tgt = ~a\n" (syntax->datum #'tgt))
        ;; (printf "src = ~a\n" (syntax->datum #'src))
        (make-ntt-apply
         goal
         (list
          (make-ntt-hole (subst-term #'src #'tgt goal)))
         (λ (body-pf)
           (define res
             (quasisyntax/loc goal
               (new-elim
                THM
                (λ [tgt-id : TY]
                  (λ [H : (coq= TY src tgt-id)]
                    #,(subst-term #'tgt-id #'tgt goal)))
                #,body-pf)))
           #;(begin (cond [(and left? thm) (displayln "coq rewritethmL")]
                          [thm (displayln "coq rewritethmR")]
                          [left? (displayln "coq rewriteL")]
                          [else (displayln "coq rewriteR")])                          
                    (pretty-print (syntax->datum res)))
           res)))
      ]))

  (define ((replace ty_ from_ to_) ctxt pt)
    (match-define (ntt-hole _ goal) pt)
    (define ty (transfer-scopes goal ty_ ctxt))
    (define from (transfer-scopes goal from_ ctxt))
    (define to (transfer-scopes goal to_ ctxt))
    (with-syntax ([tgt-id (format-id from "tgt")]
                  [H (format-id from "H")])
      (make-ntt-apply
       goal
       (list
        (make-ntt-hole (subst-term to from goal))
        (make-ntt-hole (quasisyntax/loc goal (coq= #,ty #,to #,from))))
       (lambda (body-pf arg-pf)
         (define res
           (quasisyntax/loc goal
             ((λ [H : (coq= #,ty #,to #,from)]
                (new-elim
                 H
                 (λ [tgt-id : #,ty]
                   (λ [H : (coq= #,ty #,to tgt-id)]
                     #,(subst-term #'tgt-id from goal)))
                 #,body-pf))
              #,arg-pf)))
         #;(begin
           (displayln "replace")
           (pretty-print (syntax->datum res)))
         res))))

  (define-syntax (by-replace syn)
    (syntax-case syn ()
      [(_ ty from to)
       #`(fill (replace #'ty #'from #'to))]))
  )

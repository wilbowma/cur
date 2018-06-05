#lang s-exp "../main.rkt"
(require
 "../stdlib/sugar.rkt"
 "../stdlib/prop.rkt"
 "base.rkt"
 "standard.rkt"
              "../curnel/racket-impl/runtime.rkt"
              "../curnel/racket-impl/type-check.rkt"
  (for-syntax "dict-utils.rkt"
              "../curnel/racket-impl/stxutils.rkt"
              "../curnel/racket-impl/runtime-utils.rkt"
              (for-syntax syntax/parse)))

(provide (for-syntax reflexivity
                     rewrite
                     by-rewrite
                     by-rewriteL
                     by-rewrite/thm
                     by-rewriteL/thm
                     by-rewrite/expand
                     by-rewriteL/expand
                     by-rewrite/thm/expand
                     by-rewriteL/thm/expand
                     (rename-out [rewrite rewriteR]
                                 [by-rewrite by-rewriteR])))

;; require equality (==) from cur/stdlib/prop
(begin-for-syntax

  (define-syntax ~==
    (pattern-expander
     (syntax-parser
       [(_ ty a b)
        #'(_ (_ (_ (~literal ==) ty) a) b)])))
  
  ;; `reflexivity` is defined here instead of standard.rkt
  ;; because it requires cur/stdlib/prop
  (define (reflexivity ptz)
    (match-define (ntt-hole _ goal) (nttz-focus ptz))
    (ntac-match goal
     [(~== ty a b) ((fill (exact #'(refl ty a))) ptz)]))

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
       #`(fill (rewrite #'H #:es #'es #:left? #t))]))

  (define-syntax (by-rewriteL/expand syn)
    (syntax-case syn ()
      [(_ H . es)
       #`(fill (rewrite #'H #:es #'es #:left? #t #:expand? #t))]))

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
         (loop #'rst (cons #'b binds))]
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
 ;   (printf "thm = ~a\n" (syntax->datum H))
    (ntac-match H
     [(~or
       ; already-instantiated thm
       (~and (~== TY L R)
             (~parse es es_)) ; es should be #'()
       ; ∀ thm, instantiate with given es
       (~and
        nested-∀-thm
        (~parse
         ((~datum Π)
          [x0:id _ ty0] ... ; flattened bindings
          (~and 
           (~or ((~literal ==) TY L_ R_)  ; unexpanded ==
                (~== TY L_ R_)) ; expanded ==
           ;; TODO: why are the scopes on es_ not right? bc of eval?
           ;; - eg, they dont see the intros
           ;; - WORKAROUND for now: manually add them, creating es
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
                             (subst* (syntax->list #'xs*) (syntax->list #'(x0 ...)) #'L_)))
           (~parse R (subst* (syntax->list #'es)
                             (syntax->list #'xs*)
                             (subst* (syntax->list #'xs*) (syntax->list #'(x0 ...)) #'R_)))))
         (flatten-Π #'nested-∀-thm))))
      ;; set a_ and b_ as source/target term, depending on specified direction
      (with-syntax* ([(tgt src) (if left? #'(R L) #'(L R))]
                     [a* (format-id #'tgt "~a" (generate-temporary))]
                     [b* (format-id #'src "~a" (generate-temporary))]
                     [H (format-id name "~a" (generate-temporary))])
        ;; ids a* and b* are used for *two* purposes:
        ;; - in the motive: they map to L and R respectively, ie in `insert-tmps`
        ;; - in the method: b* maps to the "source"
        (define (insert-tmps stx)
          ;; middle subst-term deals with potential overlap between L and R
          (subst-term #'a* (subst-term #'b* #'R #'L) (subst-term #'b* #'R stx)))
        ;; remove tgt id from ctxt, since it's not in goal anymore
        ;; if not ∀ thm, remove name as well, since it can't be used again
        ;; TODO (cur question):
        ;  why is it necessary to manually propagate the unused ids like this?
        (let* ([used-ids (if (and (identifier? #'tgt) (dict-has-key? ctxt #'tgt))
                             (if thm (list #'tgt) (list name #'tgt))
                             (if thm null (list name)))]
               [unused-ids (foldr remove-id
                                  (dict-keys ctxt)
                                  (if (and (identifier? #'src) (dict-has-key? ctxt #'src))
                                      (cons #'src used-ids)
                                      used-ids))])
          (make-ntt-apply
           goal
           (list
            (make-ntt-context
             (lambda (old-ctxt)
               ;; TODO (cur question):
               ;; Is removing old ids like this the right thing to do?
               ;; - also, it makes display-focus output different from coq
               (foldr dict-remove/flip old-ctxt used-ids))
             (make-ntt-hole (subst-term #'src #'tgt goal))))
           (λ (body-pf)
             (define res
               (quasisyntax/loc goal 
                 ((new-elim
                   #,(if thm
                         #`(#,real-name . es)
                         #`(#,name . es))
                   (λ [a* : TY] [b* : TY]
                      (λ [H : (== TY a* b*)]
                        #,(foldl
                           (λ (x stx)
                             #`(Π [#,x : #,(insert-tmps (dict-ref ctxt x))]
                                  #,stx))
                           (insert-tmps goal)
                           unused-ids)))
                   (λ [b* : TY]
                     #,(foldl
                        (λ (x stx)
                          #`(λ [#,x : #,(subst-term #'b* #'src (dict-ref ctxt x))]
                              #,stx))
                        (subst-term #'b* #'src body-pf)
                        unused-ids)))
                  #,@(reverse unused-ids))))
             #;(begin (cond [(and left? thm) (displayln "rewritethmL")]
                          [thm (displayln "rewritethmR")]
                          [left? (displayln "rewriteL")]
                          [else (displayln "rewriteR")])                          
                    (pretty-print (syntax->datum res)))
             res))))
      ]))
  )

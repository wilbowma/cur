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
      [(_ x)
       #`(fill (rewrite #'x))]))

  (define-syntax (by-rewrite/expand syn)
    (syntax-case syn ()
      [(_ x)
       #`(fill (rewrite #'x #:expand? #t))]))

  (define-syntax (by-rewriteL syn)
    (syntax-case syn ()
      [(_ x)
       #`(fill (rewrite #'x #:left? #t))]))

  (define-syntax (by-rewriteL/expand syn)
    (syntax-case syn ()
      [(_ x)
       #`(fill (rewrite #'x #:left? #t #:expand? #t))]))

  (define-syntax (by-rewrite/thm syn)
    (syntax-case syn ()
      [(_ thm x ...)
       #`(let ([thm-info (syntax-local-eval #'thm)])
           (fill (rewrite #'thm
                          #:real-name (theorem-info-name thm-info)
                          #:thm (theorem-info-orig thm-info)
                          #:xs #'(x ...))))]))

  (define-syntax (by-rewrite/thm/expand syn)
    (syntax-case syn ()
      [(_ thm x ...)
       #`(let ([thm-info (syntax-local-eval #'thm)])
           (fill (rewrite #'thm
                          #:real-name (theorem-info-name thm-info)
                          #:thm (identifier-info-type thm-info)
                          #:xs #'(x ...))))]))

  (define-syntax (by-rewriteL/thm syn)
    (syntax-case syn ()
      [(_ thm x ...)
       #`(let ([thm-info (syntax-local-eval #'thm)])
           (fill (rewrite #'thm
                          #:real-name (theorem-info-name thm-info)
                          #:thm (theorem-info-orig thm-info)
                          #:xs #'(x ...)
                          #:left? #t)))]))

  (define-syntax (by-rewriteL/thm/expand syn)
    (syntax-case syn ()
      [(_ thm x ...)
       #`(let ([thm-info (syntax-local-eval #'thm)])
           (fill (rewrite #'thm
                          #:real-name (theorem-info-name thm-info)
                          #:thm (cur-reflect (identifier-info-type thm-info))
                          #:xs #'(x ...)
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
  ;; - thm arg --- from previously defined define-theorem
  ;; - or (dict-ref ctxt name) --- usually an IH
  ;; H can have shape:
  ;; - (== ty a_ b_)
  ;; - (∀ [x : ty] (== ty a_ b_))
  ;; - or expanded versions of the above
  ;; a_ and b_ and marked as "source" and "target":
  ;; - [default] a_ = tgt, b_ = src, ie, replace "a_" with "b_" (ie coq rewrite ->)
  ;; - if left? = #t, flip and replace "b_" with "a_" (ie coq rewrite <-)
  (define ((rewrite name
                    #:real-name [real-name #f] ; ie, define-theorem name
                    #:thm [thm #f]
                    #:left? [left? #f]
                    #:xs [xs #'()]
                    #:expand? [expand? #f]) ; expands thm first before subst; useful for unexpanded IH
           ctxt pt)
    (match-define (ntt-hole _ goal) pt)
    (define H (or thm (dict-ref ctxt name)))
 ;   (printf "thm = ~a\n" (syntax->datum H))
    (ntac-match H
     [(~or
       ; already-instantiated thm
       (~and (~== ty0 a_ b_)
             (~parse xs1 xs)) ; xs should be #'()
       ; ∀ thm, instantiate with given xs
       (~and
        nested-∀-thm
        (~parse
         ((~datum Π)
          [x0:id _ ty] ... ; flattened bindings
          (~and 
           (~or ((~literal ==) ty0 y z)  ; unexpanded ==
                (~== ty0 y z)) ; expanded ==
           ;; xs didnt get scopes of the intros, manually add them to xs1
           (~parse xs1
                   (map
                    (λ (x)
                      (for/first ([k (dict-keys ctxt)] #:when (free-identifier=? k x)) k))
                    (syntax->list xs)))
           ;; type check that given xs match ty required by the thm
           (~fail
            #:unless (and
                      (= (length (syntax->list #'(x0 ...)))
                         (length (syntax->list #'xs1)))
                      (andmap
                       (λ (x1 ty) (cur-type-check? x1 ty #:local-env (ctxt->env ctxt)))
                       (syntax->list #'xs1)
                       (syntax->list #'(ty ...))))
            (format "given ids ~a have wrong arity, or wrong types ~a; cant be used with thm ~a: ~a\n"
                    (syntax->datum xs)
                    (syntax->datum (map (λ (x) (dict-ref ctxt x)) (syntax->list #'xs1)))
                    (syntax->datum real-name)
                    (syntax->datum thm)))
           ;; instantiate the left/right components of the thm
           (~parse a_ (subst* (syntax->list #'xs1)
                              (syntax->list #'(x0 ...))
                              #'y))
           (~parse b_ (subst* (syntax->list #'xs1)
                              (syntax->list #'(x0 ...))
                              #'z))))
         (flatten-Π #'nested-∀-thm))))
      ;; set a_ and b_ as source/target term, depending on specified direction
      (with-syntax* ([(tgt src) (if left? #'(b_ a_) #'(a_ b_))]
                     [a* (format-id #'tgt "~a" (generate-temporary))]
                     [b* (format-id #'src "~a" (generate-temporary))]
                     [H (format-id name "~a" (generate-temporary))])
        ;; ids a* and b* are used for *two* purposes:
        ;; - in the motive: they map to a_ and b_ respectively, ie in `insert-tmps`
        ;; - in the method: b* maps to the "source"
        (define (insert-tmps stx)
          ;; middle subst-term deals with potential overlap between a_ and b_
          (subst-term #'a* (subst-term #'b* #'b_ #'a_) (subst-term #'b* #'b_ stx)))
        ;; TODO (cur question):
        ;  why is it necessary to manually propagate the unused ids like this?
        (let* ([used-ids (if (identifier? #'tgt)
                             (list #'tgt name)
                             (list name))]
               [unused-ids (foldr remove-id (dict-keys ctxt) (if (identifier? #'src)
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
                         #`(#,real-name . xs1)
                         #`(#,name . xs1))
                   (λ [a* : ty0] [b* : ty0]
                      (λ [H : (== ty0 a* b*)]
                        #,(foldl
                           (λ (x stx)
                             #`(Π [#,x : #,(insert-tmps (dict-ref ctxt x))]
                                  #,stx))
                           (insert-tmps goal)
                           unused-ids)))
                   (λ [b* : ty0]
                     #,(foldl
                        (λ (x stx)
                          #`(λ [#,x : #,(subst-term #'b* #'src (dict-ref ctxt x))]
                              #,stx))
                        (subst-term #'b* #'src body-pf)
                        unused-ids)))
                  #,@(reverse unused-ids))))
  #;           (begin (cond [(and left? thm) (displayln "rewritethmL")]
                          [thm (displayln "rewritethmR")]
                          [left? (displayln "rewriteL")]
                          [else (displayln "rewriteR")])                          
                      (pretty-print (syntax->datum res)))
             res))))
      ]))
  )

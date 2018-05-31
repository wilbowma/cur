#lang s-exp "../main.rkt"
(require
 "../stdlib/sugar.rkt"
 "../stdlib/prop.rkt"
 "base.rkt"
 "standard.rkt"
              "../curnel/racket-impl/runtime.rkt"
  (for-syntax "../curnel/racket-impl/stxutils.rkt"
              "../curnel/racket-impl/runtime-utils.rkt"
              (for-syntax syntax/parse)))

(provide (for-syntax reflexivity
                     rewrite
                     rewrite/thm
                     by-rewrite
                     by-rewriteL
                     by-rewrite/thm
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


  ;; TODO: currently can only do ids, and only left to right
  (define-syntax (by-rewrite syn)
    (syntax-case syn ()
      [(_ x)
       #`(fill (rewrite #'x))]))

  (define-syntax (by-rewriteL syn)
    (syntax-case syn ()
      [(_ x)
       #`(fill (rewrite #'x #:left? #t))]))

  (define (remove-id v lst) (remove v lst free-identifier=?))
  (define (dict-remove/flip k h) (dict-remove h k))
  
  ;; if (dict-ref ctxt name) = (== ty a_ b_)
  ;; - [default] replace "a_" with "b_" (ie coq rewrite ->)
  ;; - if left? = #t, replace "b_" with "a_" (ie coq rewrite <-)
  (define ((rewrite name #:left? [left? #f]) ctxt pt)
    (match-define (ntt-hole _ goal) pt)
    (ntac-match (dict-ref ctxt name)
     [(~== ty a_ b_)
      ;; a = "target", b = "source"
      (with-syntax* ([(a b) (if left? #'(b_ a_) #'(a_ b_))]
                     [a* (format-id #'a "~a" (generate-temporary))]
                     [b* (format-id #'b "~a" (generate-temporary))])
        ;; ids a* and b* are used for *two* purposes:
        ;; - in the motive: they map to a_ and b_ respectively, ie in `insert-tmps`
        ;; - in the method: b* maps to the b, ie the "source"
        (define (insert-tmps stx)
          (subst-term #'a* #'a_ (subst-term #'b* #'b_ stx)))
        ;; TODO: why is it necessary to manually propagate the unused ids like this?
        (let* ([used-ids (if (identifier? #'a)
                             (list #'a name)
                             (list name))]
               [unused-ids (foldr remove-id (dict-keys ctxt) (if (identifier? #'b)
                                                                 (cons #'b used-ids)
                                                                 used-ids))])
          (make-ntt-apply
           goal
           (list
            (make-ntt-context
             (lambda (old-ctxt)
               ;; TODO: is removing old ids like this the right thing to do?
               ;; also, it makes printing the focus look weird
               (foldr dict-remove/flip old-ctxt used-ids))
             (make-ntt-hole (subst-term #'b #'a goal))))
           (λ (body-pf)
             (define res
               (quasisyntax/loc goal 
                 ((new-elim
                   #,name
                   (λ [a* : ty] [b* : ty]
                      (λ [#,name : (== ty a* b*)]
                        #,(foldl
                           (λ (x stx)
                             #`(Π [#,x : #,(insert-tmps (dict-ref ctxt x))]
                                  #,stx))
                           (insert-tmps goal)
                           unused-ids)))
                   (λ [b* : ty]
                     #,(foldl
                        (λ (x stx)
                          #`(λ [#,x : #,(subst-term #'b* #'b (dict-ref ctxt x))]
                              #,stx))
                        (subst-term #'b* #'b body-pf)
                        unused-ids)))
                  #,@(reverse unused-ids))))
             #;(begin (if left? (displayln "rewriteL") (displayln "rewriteR"))
                      (pretty-print (syntax->datum res)))
             res))))]))

  ;; TODO: reimplement this to use rewrite, like by-coq-rewrite/thm in coqrewrite.rkt
  (define-syntax (by-rewrite/thm syn)
    (syntax-case syn ()
      [(_ thm x)
       #`(fill (rewrite/thm #'thm #'x))]))

  ;; rewrite with previously-defined theorem
  ;; `thm` must be an id
  ;; TODO: merge with rewrite
  (define ((rewrite/thm thm x) ctxt pt)
    (match-define (ntt-hole _ goal) pt)
;    (printf "goal = ~a\n" (syntax->datum goal))
    (define th (theorem-info-orig (eval thm)))
;    (printf "thm = ~a\n" (syntax->datum th))
    (ntac-match th
     [(_ #;(~literal ∀)
       [x0 _ ty]
       ((~literal ==) ; eg (plus 0 n) == n
        (~and ty0
              ;; x didnt get the scopes of the intros,
              ;; so manually add them here (on #'x1)
              (~parse x1 (for/first ([k (dict-keys ctxt)] #:when (free-identifier=? k x)) k))
              (~fail #:unless (cur-type-check? #'x1 #'ty0 #:local-env (ctxt->env ctxt))
                     (format "given id ~a has wrong type ~a; cannot be used with thm ~a: ~a\n"
                             (syntax->datum x)
                             (syntax->datum (dict-ref ctxt #'x1))
                             (syntax->datum thm)
                             (syntax->datum th))))
        (~and y (~parse a (subst #'x1 #'x0 #'y)))
        (~and z (~parse b:id (subst #'x1 #'x0 #'z)))))
      (let ([unused-ids (foldr remove-id (dict-keys ctxt) (list #'b))])
        (with-syntax ([a* (format-id #'b "~a" (generate-temporary))])
          (make-ntt-apply
           goal
           (list
            (make-ntt-context
             (lambda (old-ctxt)
               (foldr dict-remove/flip old-ctxt null))
             (make-ntt-hole (subst-term #'b #'a goal))))
           (λ (body-pf)
             (let* ([res
                     (quasisyntax/loc goal
                       ((new-elim
                         ;; thm doesnt have right scopes for some reason,
                         ;; so get them from #'x1
                         (#,(format-id #'x1 "~a" thm) x1)
                         (λ [a* : ty]
                           (λ [b : ty]
                             (λ [H : (== ty a* b)]
                               #,(foldl
                                  (λ (m stx) #`(Π [#,m : #,(dict-ref ctxt m)] #,stx))
                                  (subst-term #'b #'a goal)
                                  unused-ids))))
                         (λ [b : ty]
                           #,(foldl
                              (λ (m stx) #`(λ [#,m : #,(dict-ref ctxt m)] #,stx))
                              (subst-term #'b #'a body-pf)
                              unused-ids)))
                        #,@(reverse unused-ids)))]
                    #;[_ (pretty-print (syntax->datum res))])
               res)))))]))
  )

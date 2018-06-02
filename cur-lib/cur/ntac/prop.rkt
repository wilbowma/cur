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



  ;; TODO: currently can only do ids, and only left to right
  (define-syntax (by-rewrite syn)
    (syntax-case syn ()
      [(_ x)
       #`(fill (rewrite #'x))]))

  ;; TODO: currently can only do ids, and only left to right
  (define-syntax (by-rewrite/expand syn)
    (syntax-case syn ()
      [(_ x)
       #`(fill (rewrite #'x #:expand? #t))]))

  (define-syntax (by-rewriteL syn)
    (syntax-case syn ()
      [(_ x)
       #`(fill (rewrite #'x #:left? #t))]))

  ;; TODO: reimplement this to use rewrite, like by-coq-rewrite/thm in coqrewrite.rkt
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
#;  (define-syntax (by-rewrite/thm syn)
    (syntax-case syn ()
      [(_ thm x)
       #`(fill (rewrite/thm #'thm #'x))]))


  ;; if (dict-ref ctxt name) = (== ty a_ b_)
  ;; - [default] replace "a_" with "b_" (ie coq rewrite ->)
  ;; - if left? = #t, replace "b_" with "a_" (ie coq rewrite <-)
  (define ((rewrite name
                    #:real-name [real-name #f]
                    #:thm [thm #f]
                    #:left? [left? #f]
                    #:xs [xs #'()]
                    #:expand? [expand? #f]) ; expands thm first before subst; useful for unexpanded IH
           ctxt pt)
    (match-define (ntt-hole _ goal) pt)
    (define H (or thm (dict-ref ctxt name)))
    (printf "thm = ~a\n" (syntax->datum H))
    (ntac-match H
     [(~and
       nested-thm
       (~parse
        ((~datum Π)
         [x0:id _ ty] ...
         (~or
          ;; unexpanded ==
          ((~literal ==) ; eg (plus 0 n) == n
           (~and ty0
                 ;; xs didnt get the scopes of the intros,
                 ;; so manually add them here (on #'xs1)
                 (~parse xs1 
                         (map
                          (λ (x)
                            (for/first ([k (dict-keys ctxt)] #:when (free-identifier=? k x)) k))
                          (syntax->list xs)))
                 (~fail
                  ;; TODO: I think this isnt quite right
                  #:unless (andmap
                            (λ (x1) (cur-type-check? x1 #'ty0 #:local-env (ctxt->env ctxt)))
                            (syntax->list #'xs1))
                  (format "given ids ~a has wrong types ~a; cannot be used with thm ~a: ~a\n"
                          (syntax->datum xs)
                          (syntax->datum (map (λ (x) (dict-ref ctxt x)) (syntax->list #'xs1)))
                          (syntax->datum real-name)
                          (syntax->datum thm))))
           (~and y (~parse a_ (subst* (syntax->list #'xs1)
                                      (syntax->list #'(x0 ...))
                                      #'y)))
           (~and z (~parse b_ (subst* (syntax->list #'xs1)
                                      (syntax->list #'(x0 ...))
                                      #'z))))
          ;; expanded ==
          (~== 
           (~and ty0
                 ;; xs didnt get the scopes of the intros,
                 ;; so manually add them here (on #'xs1)
                 (~parse xs1 
                         (map
                          (λ (x)
                            (for/first ([k (dict-keys ctxt)] #:when (free-identifier=? k x)) k))
                          (syntax->list xs)))
                 (~fail
                  ;; TODO: I think this isnt quite right
                  #:unless (andmap
                            (λ (x1) (cur-type-check? x1 #'ty0 #:local-env (ctxt->env ctxt)))
                            (syntax->list #'xs1))
                  (format "given ids ~a has wrong types ~a; cannot be used with thm ~a: ~a\n"
                          (syntax->datum xs)
                          (syntax->datum (map (λ (x) (dict-ref ctxt x)) (syntax->list #'xs1)))
                          (syntax->datum real-name)
                          (syntax->datum thm))))
           (~and y (~parse a_ (subst* (syntax->list #'xs1)
                                      (syntax->list #'(x0 ...))
                                      #'y)))
           (~and z (~parse b_ (subst* (syntax->list #'xs1)
                                      (syntax->list #'(x0 ...))
                                      #'z))))
           ))
        (flatten-Π #'nested-thm)))
      (with-syntax* ([(a b) (if left? #'(b_ a_) #'(a_ b_))]
                     ;; [_ (displayln (syntax->datum #'b))]
                     ;; [_ (displayln (syntax->datum #'a))]
                     ;; [_ (displayln (syntax->datum (subst-term #'b #'a goal)))]
                     [a* (format-id #'a "~a" (generate-temporary))]
                     [b* (format-id #'b "~a" (generate-temporary))]
                     [H (format-id name "~a" (generate-temporary))])
        ;; ids a* and b* are used for *two* purposes:
        ;; - in the motive: they map to a_ and b_ respectively, ie in `insert-tmps`
        ;; - in the method: b* maps to the b, ie the "source"
        (define (insert-tmps stx)
          ;; middle subst-term deals with potential overlap between a_ and b_
          (subst-term #'a* (subst-term #'b* #'b_ #'a_) (subst-term #'b* #'b_ stx)))
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
                          #`(λ [#,x : #,(subst-term #'b* #'b (dict-ref ctxt x))]
                              #,stx))
                        (subst-term #'b* #'b body-pf)
                        unused-ids)))
                  #,@(reverse unused-ids))))
             (begin (cond [(and left? thm) (displayln "rewritethmL")]
                          [thm (displayln "rewritethmR")]
                          [left? (displayln "rewriteL")]
                          [else (displayln "rewriteR")])                          
                      (pretty-print (syntax->datum res)))
             res))))
      ]
     [(~== ty a_ b_)
      ;; a = "target", b = "source"
      (with-syntax* ([(a b) (if left? #'(b_ a_) #'(a_ b_))]
                     [a* (format-id #'a "~a" (generate-temporary))]
                     [b* (format-id #'b "~a" (generate-temporary))])
        ;; ids a* and b* are used for *two* purposes:
        ;; - in the motive: they map to a_ and b_ respectively, ie in `insert-tmps`
        ;; - in the method: b* maps to the b, ie the "source"
        (define (insert-tmps stx)
          ;; middle subst-term deals with potential overlap between a_ and b_
          (subst-term #'a* (subst-term #'b* #'b_ #'a_) (subst-term #'b* #'b_ stx)))
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

  ;; rewrite with previously-defined theorem
  ;; `thm` must be an id
  ;; TODO: merge with rewrite
  #;(define ((rewrite/thm thm x) ctxt pt)
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

  ;; TODO: reimplement this to use rewrite, like by-coq-rewrite/thm in coqrewrite.rkt
  #;(define-syntax (by-rewriteL/thm syn)
    (syntax-case syn ()
      #;[(_ thm x)
       #`(fill (rewriteL/thm #'thm #'x))]
      [(_ thm x ...)
       #`(fill (rewriteL/thm #'thm #'(x ...)))]))

  (define (flatten-Π p)
    (let loop ([p p][binds null])
      (syntax-parse p
        [(_ (~and b [_:id (~datum :) ty]) rst)
         (loop #'rst (cons #'b binds))]
        [body
         #`(Π #,@(reverse binds) body)])))
       
  ;; rewrite with previously-defined theorem
  ;; `thm` must be an id
  ;; TODO: merge with rewrite
  #;(define ((rewriteL/thm thm xs) ctxt pt)
    (match-define (ntt-hole _ goal) pt)
;    (printf "goal = ~a\n" (syntax->datum goal))
    (define th (theorem-info-orig (eval thm)))
    (printf "thm = ~a\n" (syntax->datum th))
    (ntac-match th
     [(~and
       nested-thm
       (~parse
        (Π
         [x0:id _ ty] ...
         ((~literal ==) ; eg (plus 0 n) == n
          (~and ty0
                ;; xs didnt get the scopes of the intros,
                ;; so manually add them here (on #'xs1)
                (~parse xs1 
                        (map
                         (λ (x)
                           (for/first ([k (dict-keys ctxt)] #:when (free-identifier=? k x)) k))
                         (syntax->list xs)))
                (~fail
                 ;; TODO: I think this isnt quite right
                 #:unless (andmap
                           (λ (x1) (cur-type-check? x1 #'ty0 #:local-env (ctxt->env ctxt)))
                           (syntax->list #'xs1))
                 (format "given ids ~a has wrong types ~a; cannot be used with thm ~a: ~a\n"
                         (syntax->datum xs)
                         (syntax->datum (map (λ (x) (dict-ref ctxt x)) (syntax->list #'xs1)))
                         (syntax->datum thm)
                         (syntax->datum th))))
          (~and y (~parse a (subst* (syntax->list #'xs1)
                                    (syntax->list #'(x0 ...))
                                    #'y)))
          (~and z (~parse b (subst* (syntax->list #'xs1)
                                    (syntax->list #'(x0 ...))
                                    #'z)))))
        (flatten-Π #'nested-thm)))
      (let ([unused-ids (foldr remove-id (dict-keys ctxt) (if (identifier? #'a) (list #'a) null))])
        (with-syntax ([a* (format-id #'a "~a" (generate-temporary))]
                      [b* (format-id #'b "~a" (generate-temporary))]
                      #;[H (format-id name "~a" (generate-temporary))])
          (make-ntt-apply
           goal
           (list
            (make-ntt-context
             (lambda (old-ctxt)
               (foldr dict-remove/flip old-ctxt null))
             (make-ntt-hole (subst-term #'a #'b goal))))
           (λ (body-pf)
             (let* ([res
                     (quasisyntax/loc goal
                       ((new-elim
                         ;; thm doesnt have right scopes for some reason,
                         ;; so get them from #'x1
                         (#,(format-id (car (syntax->list #'xs1)) "~a" thm) . xs1)
                         (λ [a* : ty0]
                           (λ [b* : ty0]
                             (λ [H : (== ty0 a* b*)]
                               #,(foldl
                                  (λ (m stx) #`(Π [#,m : #,(dict-ref ctxt m)] #,stx))
                                  (subst-term #'a #'b goal)
                                  unused-ids))))
                         (λ [b* : ty0]
                           #,(foldl
                              (λ (m stx) #`(λ [#,m : #,(dict-ref ctxt m)] #,stx))
                              (subst-term #'a #'b body-pf)
                              unused-ids)))
                        #,@(reverse unused-ids)))]
                    #;[_ (pretty-print (syntax->datum res))])
               res)))))]))
  )

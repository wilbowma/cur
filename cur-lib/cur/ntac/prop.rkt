#lang s-exp "../main.rkt"
(require
 "../stdlib/sugar.rkt"
 "../stdlib/prop.rkt"
 "base.rkt"
 "standard.rkt"
  (for-syntax "../curnel/racket-impl/stxutils.rkt"
              (for-syntax syntax/parse)))

(provide (for-syntax reflexivity
                     by-rewrite
                     rewrite
                     by-rewriteL
                     rewriteL
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
     ;; TODO: use pattern expanders to abstract away these #%app's?
     [(_ (_ (_ (~literal ==) ty) a) b)
      ((fill (exact #'(refl ty a))) ptz)]))


  ;; TODO: currently can only do ids, and only left to right
  (define-syntax (by-rewrite syn)
    (syntax-case syn ()
      [(_ x)
       #`(fill (rewrite #'x))]))

  (define (remove-id v lst) (remove v lst free-identifier=?))
  (define (dict-remove/flip k h) (dict-remove h k))
  
  (define ((rewrite name) ctxt pt)
    (match-define (ntt-hole _ goal) pt)
;    (printf "goal = ~a\n" (syntax->datum goal))
;    (displayln (syntax->datum (dict-ref ctxt name)))
    (ntac-match (dict-ref ctxt name)
     [(_ (_ (_ (~literal ==) ty) a:id) b) #;((~literal ==) ty a:id b)
      ;; TODO: why is it necessary to manually propagate the unused ids like this?
      (let* ([used-ids (list #'a name)]
             [unused-ids (foldr remove-id (dict-keys ctxt) used-ids)])
        (with-syntax ([b* (generate-temporary #'b)])
        (make-ntt-apply
         goal
       (list
        (make-ntt-context
         (lambda (old-ctxt)
           ;; TODO: is removing old ids like this the right thing to do?
           ;; also, it makes printing the focus look weird
           (dict-set
            (foldr dict-remove/flip old-ctxt used-ids)
            #'b*
            #'b))
         (make-ntt-hole (cur-rename #'b* #'a goal))))
         (λ (body-pf)
           (let* ([res
           (quasisyntax/loc goal 
             ((new-elim #,name
                        (λ [a : ty]
                          (λ [b* : ty]
                            (λ [#,name : (== ty a b*)]
                              #,(foldl
                                 (λ (x stx) #`(Π [#,x : #,(dict-ref ctxt x)] #,stx))
                                 (subst-term #'b* #'b goal)
                                 unused-ids))))
                        (λ [b* : ty]
                          #,(foldl
                             (λ (x stx) #`(λ [#,x : #,(dict-ref ctxt x)] #,stx))
                             (subst-term #'b* #'b body-pf)
                             unused-ids)))
              #,@(reverse unused-ids)))]
                  [_ (pretty-print (syntax->datum res))])
             res)))))]))

  ;; TODO: currently can only do ids, and only left to right
  ;; TODO: get rid of dup code with rewriteR
  (define-syntax (by-rewriteL syn)
    (syntax-case syn ()
      [(_ x)
       #`(fill (rewriteL #'x))]))

  (define ((rewriteL name) ctxt pt)
    (match-define (ntt-hole _ goal) pt)
;    (printf "goal = ~a\n" (syntax->datum goal))
;    (displayln (syntax->datum (dict-ref ctxt name)))
    (ntac-match (dict-ref ctxt name)
     [(_ (_ (_ (~literal ==) ty) a:id) b:id) #;((~literal ==) ty a:id b)
      ;; TODO: why is it necessary to manually propagate the unused ids like this?
      (let ([unused-ids (foldr remove-id (dict-keys ctxt) (list #'b #'a name))])
       (with-syntax ([a* (generate-temporary #'a)])
        (make-ntt-apply
         goal
         (list
          (make-ntt-context
           (lambda (old-ctxt)
             ;; TODO: removing old ids like this makes printing the focus look weird
             (foldr dict-remove/flip old-ctxt (list #'b name)))
           (make-ntt-hole (cur-rename #'a #'b goal))))
         (λ (body-pf)
           (quasisyntax/loc goal 
             ((new-elim #,name
                        (λ [a : ty]
                          (λ [b : ty]
                            (λ [#,name : (== ty a b)]
                              #,(foldl
                                 (λ (x stx) #`(Π [#,x : #,(dict-ref ctxt x)] #,stx))
                                 goal
                                 unused-ids))))
                        (λ [a : ty]
                          #,(foldl
                             (λ (x stx) #`(λ [#,x : #,(dict-ref ctxt x)] #,stx))
                             body-pf
                             unused-ids)))
              #,@(reverse unused-ids)))))))])))

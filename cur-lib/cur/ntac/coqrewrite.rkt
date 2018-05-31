#lang s-exp "../main.rkt"
(require
 "../stdlib/sugar.rkt"
 "../stdlib/coqeq.rkt"
 "base.rkt"
 "standard.rkt"
              "../curnel/racket-impl/runtime.rkt"
  (for-syntax "../curnel/racket-impl/stxutils.rkt"
              "../curnel/racket-impl/runtime-utils.rkt"
              syntax/parse
              syntax/stx
              (for-syntax syntax/parse)))

(provide (for-syntax by-coq-rewrite
                     by-coq-rewriteL
                     by-coq-rewrite/thm
                     coq-rewrite
                     coq-rewriteL
                     coq-reflexivity
                     (rename-out [coq-rewrite coq-rewriteR]
                                 [by-coq-rewrite by-coq-rewriteR])))

;; require equality (coq=) from cur/stdlib/coqeq
(begin-for-syntax

  (define-syntax ~coq=
    (pattern-expander
     (syntax-parser
       [(_ ty a b)
        #'(_ (_ (_ (~literal coq=) ty) a) b)])))
  
  ;; `reflexivity` is defined here instead of standard.rkt
  ;; because it requires cur/stdlib/prop
  (define (coq-reflexivity ptz)
    (match-define (ntt-hole _ goal) (nttz-focus ptz))
    (ntac-match goal
     ;; TODO: use pattern expanders to abstract away these #%app's?
     [(_ (_ (_ (~literal coq=) ty) a) b)
      ((fill (exact #'(coq-refl ty a))) ptz)]))

  (define-syntax (by-coq-rewriteL syn)
    (syntax-case syn ()
      [(_ x)
       #`(fill (coq-rewriteL #'x))]))

  (define-syntax (by-coq-rewrite syn)
    (syntax-case syn ()
      [(_ x)
       #`(fill (coq-rewrite #'x))]))

  (define-syntax (by-coq-rewrite/thm syn)
    (syntax-case syn ()
      [(_ thm)
       #`(let ([thm-info (syntax-local-eval #'thm)])
           (fill (coq-rewrite #'thm
                              (theorem-info-name thm-info)
                              (theorem-info-orig thm-info))))]))

  (define (remove-id v lst) (remove v lst free-identifier=?))
  (define (dict-remove/flip k h) (dict-remove h k))
  
  ;; unify two expressions, return list of subst, for ids in e1
  (define (unify e1 e2)
    (if (identifier? e1)
        (list (list e1 e2))
        (syntax-parse (list e1 e2)
          [((f1:id e1) (f2:id e2)) #:when (free-identifier=? #'f1 #'f2)
           (unify #'e1 #'e2)]
          [_ null])))

  ;; naively tries to unify t with all subexprs in goal, returning list of subst
  (define (search t goal)
    (append
     (unify t goal)
     (if (stx-pair? goal)
         (append-map (λ (e) (search t e)) (syntax->list goal))
         null)))

  ;; replace "a" with "b"
  ;; `real-name` arg is needed bc scopes on `name` aren't right
  (define ((coq-rewrite name [real-name #f] [thm #f]) ctxt pt)
    (match-define (ntt-hole _ goal) pt)
    ;; if not given explicit thm, then lookup in ctxt
    (ntac-match (or thm (dict-ref ctxt name))
     ;; ∀ case, elim target is application of `name`
     [(∀ [x : tyx] ((~literal coq=) ty a/x b/x))
      (with-syntax*
        ([a* (format-id #'b/x "~a" (generate-temporary))]
         ;; need this temp id, ow get err "identifier's binding is ambiguous"
         ;; when trying to use name
         [H (format-id name "~a" (generate-temporary))]
         ;; search for a/x in goal, returns substs for x
         [(x y) (car (search #'a/x goal))] ; arbitrarily use first search result
         [a/y (subst #'y #'x #'a/x)]
         [b/y (subst #'y #'x #'b/x)])
        (make-ntt-apply
         goal
         (list (make-ntt-hole (subst-term #'b/y #'a/y goal)))
         (λ (body-pf)
           (let* ([res
                   (quasisyntax/loc goal
                     (new-elim
                      (coq=-sym ty a/y b/y #,(if thm
                                                 #`(#,real-name y)
                                                 #`(#,name y)))
                      (λ [a* : ty]
                        (λ [H : (coq= ty b/y a*)]
                          #,(subst-term #'a* #'a/y goal)))
                      #,body-pf))]
                  #;[_ (pretty-print (syntax->datum res))])
             res))))]
     ;; TODO: to avoid hardcoding coq=, need to duplicate what new-elim does?
     ;;       - in order to generate proper motive and methods
     [(_ (_ (_ (~literal coq=) ty) a) b)
      ;; TODO: why is it necessary to manually propagate the unused ids like this?
      (let* ([used-ids (if (identifier? #'a) (list #'a name) (list name))]
             [unused-ids (foldr remove-id
                                (dict-keys ctxt)
                                (if (identifier? #'b) (cons #'b used-ids) used-ids))])
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
           (let* ([res
                   (quasisyntax/loc goal
                     (new-elim
                      (coq=-sym ty a b #,name)
                      (λ [a : ty]
                        (λ [#,name : (coq= ty b a)]
                          #,goal))
                      #,body-pf))]
                  #;[_ (pretty-print (syntax->datum res))])
             res))))]))

  ;; replace "b" with "a"
  (define ((coq-rewriteL name) ctxt pt)
    (match-define (ntt-hole _ goal) pt)
    (ntac-match (dict-ref ctxt name)
     ;; TODO: to avoid hardcoding coq=, need to duplicate what new-elim does?
     ;;       - in order to generate proper motive and methods
     [(_ (_ (_ (~literal coq=) ty) a) b)
      ;; TODO: why is it necessary to manually propagate the unused ids like this?
      (let* ([used-ids (if (identifier? #'b) (list #'b name) (list name))]
             [unused-ids (foldr remove-id
                                (dict-keys ctxt)
                                (if (identifier? #'a) (cons #'a used-ids) used-ids))])
        (make-ntt-apply
         goal
         (list
          (make-ntt-context
           (lambda (old-ctxt)
             ;; TODO: is removing old ids like this the right thing to do?
             ;; also, it makes printing the focus look weird
             (foldr dict-remove/flip old-ctxt used-ids))
           (make-ntt-hole (subst-term #'a #'b goal))))
         (λ (body-pf)
           (let* ([res
                   (quasisyntax/loc goal
                     (new-elim
                      #,name
                      (λ [b : ty]
                        (λ [#,name : (coq= ty a b)]
                          #,goal))
                      #,body-pf))]
                  #;[_ (pretty-print (syntax->datum res))])
             res))))]))
  )

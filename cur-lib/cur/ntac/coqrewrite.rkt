#lang s-exp "../main.rkt"
(require
 "../stdlib/sugar.rkt"
 "../stdlib/coqeq.rkt"
 "base.rkt"
 "standard.rkt"
              "../curnel/racket-impl/runtime.rkt"
  (for-syntax "../curnel/racket-impl/stxutils.rkt"
              "../curnel/racket-impl/runtime-utils.rkt"
              (for-syntax syntax/parse)))

(provide (for-syntax by-coq-rewrite
                     by-coq-rewriteL
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

  (define (remove-id v lst) (remove v lst free-identifier=?))
  (define (dict-remove/flip k h) (dict-remove h k))
  
  ;; replace "a" with "b"
  (define ((coq-rewrite name) ctxt pt)
    (match-define (ntt-hole _ goal) pt)
    (ntac-match (dict-ref ctxt name)
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

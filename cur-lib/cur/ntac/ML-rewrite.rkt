#lang cur/metantac
;; Rewrite, but using Martin-Lof equality
;; Significant code duplicate between this and rewrite.rkt;
;; someone should play the abstraction game (and abstract over *any* equivalence...?)

(provide (for-syntax reflexivity
                     rewrite
                     by-rewrite
                     by-rewriteL
                     (rename-out [by-rewrite by-rewriteR])))

(require cur/stdlib/equality
         "standard.rkt")

(begin-for-syntax

  (define (reflexivity ptz)
    (match-define (ntt-hole _ goal) (nttz-focus ptz))
    (ntac-match goal
     [(~ML-= ty a b)
      ((fill (exact #`(ML-refl #,(unexpand #'ty) #,(unexpand #'a)))) ptz)]))

  ;; rewrite tactics ----------------------------------------------------------

  ;; surface rewrite tactics --------------------
  (define-syntax (by-rewrite syn)
    (syntax-case syn ()
      [(_ H . es)
       #`(fill (rewrite #'H #:inst-args #'es))]))

  (define-syntax (by-rewriteL syn)
    (syntax-case syn ()
      [(_ H . es)
       #`(fill (rewrite #'H #:inst-args #'es #:left? #t))]))

  ;; internal rewrite tactic --------------------
  ;; - surface tactics all defined in terms of this one

  ;; TODO: This procedure is badly in need of abstraction
  ;; The theorem "H" to use for the rewrite is either:
  ;; - `thm` arg --- from previously defined define-theorem
  ;; - or (ctx-lookup ctxt name) --- usually an IH
  ;; H can have shape:
  ;; - (ML-= ty L R)
  ;; - (∀ [x : ty] ... (ML-= ty L R))
  ;;   - x ... instantiated with `es`
  ;; - or expanded versions of the above
  ;; L/R then marked as "source" and "target":
  ;; - [default] L = tgt, R = src, ie, replace "L" with "R" (ie coq rewrite ->)
  ;; - if left? = #t, flip and replace "R" with "L" (ie coq rewrite <-)
  (define ((rewrite name #:left? [left? #f] #:inst-args [inst-args #'()]) ctxt pt)
    (match-define (ntt-hole _ goal) pt)
    (define local-thm? (ctx-lookup ctxt name))
    (ntac-match (or local-thm? ; thm in ctx
                    (typeof (expand/df name))) ; prev proved thm
     [(~or
       (~ML-= TY L R) ; already-instantiated thm
       (~and (~Π [X : τX] ... body)
             (~parse (~ML-= TY L R) (substs inst-args #'(X ...) #'body))))
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
        (let* ([used-ids (if (and (identifier? #'tgt) (ctx-has-id? ctxt #'tgt)
                                  (not (find-in #'tgt #'src))) ; tgt \notin src
                             (if (not local-thm?) (list #'tgt) (list name #'tgt))
                             (if (not local-thm?) null (list name)))]
               [unused-ids (foldr remove-id
                                  (ctx-ids ctxt)
                                  (if (and (identifier? #'src) (ctx-has-id? ctxt #'src))
                                      (cons #'src used-ids)
                                      used-ids))])
          (make-ntt-apply
           goal
           (list
            (make-ntt-context
              (lambda (old-ctxt)
                ;; TODO (cur question):
                ;; this is still needed to avoid typecheck errs,
                ;; try removing this and running plus-id-exercise in ML-rewrite tests
                ;; - also, it makes display-focus output different from coq
                (ctx-removes old-ctxt used-ids))
              (make-ntt-hole (normalize (subst-term #'src #'tgt goal) ctxt))))
           (λ (body-pf)
             (quasisyntax/loc goal
               ((new-elim
                 (#,name . #,inst-args)
                 (λ [a* : TY] [b* : TY]
                    (λ [H : (ML-= TY a* b*)]
                      #,(foldr ; wrap goal with lams binding unused ids, outermost-in
                         (λ (x stx)
                           #`(Π [#,x : #,(insert-tmps (ctx-lookup ctxt x))]
                                #,stx))
                         (insert-tmps goal)
                         unused-ids)))
                 (λ [b* : TY]
                   #,(foldr
                      (λ (x stx)
                        #`(λ [#,x : #,(subst-term #'b* #'src (ctx-lookup ctxt x))]
                            #,stx))
                      (subst-term (unexpand #'b*) (unexpand #'src) body-pf)
                      unused-ids)))
                #,@unused-ids))))))])))

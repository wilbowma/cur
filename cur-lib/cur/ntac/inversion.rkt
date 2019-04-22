#lang s-exp "../main.rkt"
(provide (for-syntax inversion))

;; `by-inversion` tactic in ntac/standard

(require
 "../stdlib/prop.rkt" ; for False (see inversion)
 "../stdlib/sugar.rkt"
 "../stdlib/equality.rkt"
 "base.rkt"
 "prove-unify.rkt"
  (for-syntax "ctx.rkt" "utils.rkt"
              (only-in macrotypes/typecheck-core subst substs)
              macrotypes/stx-utils
              racket/list
              racket/match
              racket/pretty
              syntax/stx
              (for-syntax racket/base syntax/parse)))


(begin-for-syntax

  (define ((inversion name [new-xss_ #f]) ctxt pt)
    (match-define (ntt-hole _ goal) pt)
    (define name-ty (or (ctx-lookup ctxt name) ; thm in ctx
                        (typeof (expand/df name))))

    ;; get info about the datatype and its constructors
    ;; A = params
    ;; i = indices
    ;; x = non-recursive args to constructors
    ;; xrec = recrusive args to constructors
    ;; irec = indices to recursive args
    (define/syntax-parse
      (elim-TY ([A τA] ...)
               ([i τi_] ...)
               Cinfo ...)
      (get-match-info name-ty))

    (define num-params (stx-length #'(A ...)))
    (define num-idxs   (stx-length #'(i ...)))

    (define get-idxs ; extract indices from *unexpanded* (curried single-app) type
      (if (zero? num-idxs)
          (λ (t) null)
          (λ (t) (get-idxs/unexp t num-idxs))))

    (define new-xss
      (or new-xss_
          (stx-map (λ (_) null) #'(Cinfo ...))))

    ; === Extract provided params (Aval ...) and indices (ival ...)
    (define/syntax-parse ((Aval ...) (ival ...))
      (syntax-parse name-ty
        [((~literal #%plain-app) _ . name-ty-args)
         (stx-split-at #'name-ty-args num-params)]))

    (define/syntax-parse (τi ...)
      (stx-map (normalize/ctxt ctxt)
               (substs #'(Aval ...) #'(A ...) #'(τi_ ...))))

    ; === Generate subgoals for each data constructor case
    ;; subgoals : (listof ntt)
    ;; mk-elim-methods : (listof (or/c #f (-> term term)))
    (define-values [subgoals mk-elim-methods]
      (for/lists (subgoals mk-elim-methods)
                 ([Cinfo (in-stx-list #'(Cinfo ...))]
                  [new-xs (in-stx-list new-xss)])

        (define (next-id hint)
          (if (stx-null? new-xs)
            ((freshen name) (generate-temporary hint))
            (begin0 (stx-car new-xs) (set! new-xs (stx-cdr new-xs)))))

        (syntax-parse Cinfo
          [[C ([x_ τx_] ... τout_)
              ([xrec_ . _] ...)]
           #:with (x ...) (stx-map next-id #'(x_ ...))
           #:with (xrec ...) ((freshens name) #'(xrec_ ...))
           #:with (τx ... τout) (substs #'(Aval ... x ...)
                                        #'(A    ... x_ ...)
                                        #'(τx_ ... τout_))

           #:do [(define ctxt+xs (ctx-adds ctxt #'(x ...) #'(τx ...)
                                           #:do normalize))]

           #:with (iout ...) (map (normalize/ctxt ctxt+xs) (get-idxs #'τout))
           #:with (==-id ...) (stx-map (λ (_) (generate-temporary 'eq)) #'(i ...))

           #;
           #:do #;[(printf "** ~s\n** ~s\n** ~s\n------------\n"
                         (map syntax->datum (attribute ival))
                         (map syntax->datum (attribute iout))
                         (map syntax->datum (attribute ==-id)))]

           ; Unify the provided indices (ival) with the constructor's indices (iout)
           (match (prove-unifys (attribute τi)
                                (attribute iout)
                                (attribute ival)
                                (attribute ==-id)
                                #:normalize (normalize/ctxt ctxt+xs))
             ; Add derived equalities to context and make subgoal
             [(derived ==s ==-pfs)
              (define derived-==-ids   (map (λ (_) (next-id 'Heq)) ==s))
              (define derived-bindings (map mk-bind-stx derived-==-ids ==s))

              (define (update-ctxt ctxt)
                ; NOTE: xrec not added to context -- TODO do something with it?
                (for/fold ([ctxt ctxt])
                          ([x (in-list (append (attribute x)  derived-==-ids))]
                           [τ (in-list (append (attribute τx) ==s))])
                  (ctx-add ctxt x (normalize τ ctxt))))

              (values (make-ntt-context update-ctxt (make-ntt-hole goal))
                      (λ (pf)
                        #`(λ x ... xrec ... ==-id ...
                             ((λ #,@derived-bindings #,pf)
                              #,@==-pfs))))]

             ; Contradiction; generate a proof instead of creating a hole
             [(impossible false-pf)
              (values (make-ntt-exact #'False false-pf)
                      (λ (pf)
                        #`(λ x ... xrec ... ==-id ...
                             (new-elim
                              #,pf
                              (λ _ #,(unexpand goal))))))])])))

    (make-ntt-apply
     goal
     subgoals
     (λ pfs ;; constructs proof term, from each subgoals' proof terms
       (quasisyntax/loc goal
         ((new-elim
           ; target
           #,name
           ; motive
           #,(with-syntax ([(i* ...) (generate-temporaries #'(i ...))])
               (with-syntax ([(==-ty ...) (stx-map (λ (ii ty) #`(== #,ii #,(unexpand ty)))
                                                   #'(i* ...) #'(ival ...))])
                 #`(λ i* ... #,name
                      (-> ==-ty ... #,(unexpand goal)))))
           ; methods
           . #,(map (λ (mk pf) (mk pf)) mk-elim-methods pfs))
          ; arguments (refl proofs)
          #,@(stx-map unexpand #'((refl τi ival) ...))))))))

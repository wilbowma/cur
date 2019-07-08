#lang s-exp "../main.rkt"
(provide (for-syntax by-inversion))

;; `by-inversion` tactic in ntac/standard

(require
 "../stdlib/prop.rkt" ; for False (see inversion)
 "../stdlib/sugar.rkt"
 "../stdlib/equality.rkt"
 "base.rkt"
 "metantac.rkt"
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

  (define-syntax by-inversion
    (syntax-parser
      [(_ H) #'(by-inversion* H #:as ())]
      [(_ H #:as (~var name id) ...) #'(by-inversion* H #:as [(name ...)])]
      [(_ H #:as (names ...)) #'(by-inversion* H #:as (names ...))]))
  (define-tactic by-inversion*
    [(_ H #:as (names ...))
     (define pt $pt)
     (define ctxt $ctxt)
     (define name #'H)
  ;; new-xss = nested stx list of ids
  ;; Note: inversion does not check whether new-xss has correct shape or num ids;
  ;; instead it uses given ids until it runs out, and then generates fresh ids.
  ;; This enables cleaner invocations of the tactic, esp when most cases are False
     ;  (define ((inversion name [new-xss #'()]) ctxt pt)
     (define new-xss #'(names ...))
    (match-define (ntt-hole _ goal) pt)
    (define name-ty (or (ctx-lookup ctxt name) ; thm in ctx
                        (typeof (expand/df name))))

    ;; get info about the datatype and its constructors
    ;; A = params
    ;; i = indices
    ;; x = non-recursive args to constructors
    ;; xrec = recursive args to constructors
    ;; irec = indices to recursive args
    (define/syntax-parse
      (_ elim-TY ([A τA] (... ...))
         ([i τi_] (... ...))
         _
         Cinfo (... ...))
      (get-match-info name-ty))

    (define num-params (stx-length #'(A (... ...))))
    (define num-idxs   (stx-length #'(i (... ...))))

    (define get-idxs ; extract indices from *unexpanded* (curried single-app) type
      (if (zero? num-idxs)
          (λ (t) null)
          (λ (t) (get-idxs/unexp t num-idxs))))

    (define tmps? #f) ; this flag prevents re-using generated names (see push-back-ids!)
    (define (next-id! hint)
      (syntax-parse new-xss
        [() (set! tmps? #t) ((freshen name) (generate-temporary hint))]
        [(() . rst)
         (set! new-xss #'rst)
         (next-id! hint)]
        [((x . rstx) . rst)
         (set! new-xss #'(rstx . rst))
         #'x]))
    (define (push-back-ids! xs)
      (unless tmps? (set! new-xss (cons xs new-xss))))

    ; === Extract provided params (Aval (... ...)) and indices (ival (... ...))
    (define/syntax-parse ((Aval (... ...)) (ival (... ...)))
      (syntax-parse name-ty
        [((~literal #%plain-app) _ . name-ty-args)
         (stx-split-at #'name-ty-args num-params)]))

    (define/syntax-parse (τi (... ...))
      (stx-map (normalize/ctxt ctxt)
               (substs #'(Aval (... ...)) #'(A (... ...)) #'(τi_ (... ...)))))

    ; === Generate subgoals for each data constructor case
    ;; subgoals : (listof ntt)
    ;; mk-elim-methods : (listof (or/c #f (-> term term)))
    (define subgoals
      (for/list ([Cinfo (in-stx-list #'(Cinfo (... ...)))])

        (syntax-parse Cinfo
          [[C ([x_ τx_] (... ...) τout_)
              ([xrec_ . _] (... ...))]
           #:with (x (... ...)) (stx-map next-id! #'(x_ (... ...)))
           #:with (xrec (... ...)) ((freshens name) #'(xrec_ (... ...)))
           #:with (τx (... ...) τout) (substs #'(Aval (... ...) x (... ...))
                                        #'(A    (... ...) x_ (... ...))
                                        #'(τx_ (... ...) τout_))

           #:do [(define ctxt+xs (ctx-adds ctxt #'(x (... ...)) #'(τx (... ...))
                                           #:do normalize))]

           #:with (iout (... ...)) (map (normalize/ctxt ctxt+xs) (get-idxs #'τout))
           #:with (==-id (... ...)) (stx-map (λ (_) (generate-temporary 'eq)) #'(i (... ...)))

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
              (define derived-==-ids   (map (λ (_) (next-id! 'Heq)) ==s))
              (define derived-bindings (map mk-bind-stx derived-==-ids ==s))

              (define (update-ctxt ctxt)
                ; NOTE: xrec not added to context -- TODO do something with it?
                (for/fold ([ctxt ctxt])
                          ([x (in-list (append (attribute x)  derived-==-ids))]
                           [τ (in-list (append (attribute τx) ==s))])
                  (ctx-add ctxt x (normalize τ ctxt))))

              #;(make-ntt-apply
               goal
               (list (make-ntt-context update-ctxt (make-ntt-hole goal)))
               (λ (pf)
                 #`(λ x (... ...) xrec (... ...) ==-id (... ...)
                      ((λ #,@derived-bindings #,pf)
                       #,@==-pfs))))
              (define/syntax-parse (x+==ids (... ...)) (append (attribute x)  derived-==-ids))
              (define/syntax-parse (τ+==s (... ...)) (append (attribute τx) ==s))
              ($stx/holes
               goal
               (λ x (... ...) xrec (... ...) ==-id (... ...)
                  ((λ #,@derived-bindings #,?HOLE)
                   #,@==-pfs))
               #:where [x+==ids : τ+==s] (... ...) ⊢ ?HOLE : goal)]

             ; Contradiction; generate a proof instead of creating a hole
             [(impossible false-pf)
              (push-back-ids! #'(x (... ...)))
              #;(make-ntt-exact
               goal
               #`(λ x (... ...) xrec (... ...) ==-id (... ...)
                    (new-elim
                     #,false-pf
                     (λ _ #,(unexpand goal)))))
              ($stx/leaf
               goal
               (λ x (... ...) xrec (... ...) ==-id (... ...)
                  (new-elim
                   #,false-pf
                   (λ _ #,(unexpand goal)))))])])))

    ($stx/compose
     goal
     ((new-elim
       ; target
       #,name
       ; motive
       #,(with-syntax ([(i* (... ...)) (generate-temporaries #'(i (... ...)))])
           (with-syntax ([(==-ty (... ...)) (stx-map (λ (ii ty) #`(== #,ii #,(unexpand ty)))
                                                     #'(i* (... ...)) #'(ival (... ...)))])
             #`(λ i* (... ...) #,name
                  (-> ==-ty (... ...) #,(unexpand goal)))))
       ; methods
       . #,$pfs)
      ; arguments (refl proofs)
      #,@(stx-map unexpand #'((refl τi ival) (... ...))))
     #:with subgoals)
    
    #;(make-ntt-apply
     goal
     subgoals
     (λ pfs ;; constructs proof term, from each subgoals' proof terms
       (quasisyntax/loc goal
         ((new-elim
           ; target
           #,name
           ; motive
           #,(with-syntax ([(i* (... ...)) (generate-temporaries #'(i (... ...)))])
               (with-syntax ([(==-ty (... ...)) (stx-map (λ (ii ty) #`(== #,ii #,(unexpand ty)))
                                                         #'(i* (... ...)) #'(ival (... ...)))])
                 #`(λ i* (... ...) #,name
                      (-> ==-ty (... ...) #,(unexpand goal)))))
           ; methods
           . #,pfs)
          ; arguments (refl proofs)
          #,@(stx-map unexpand #'((refl τi ival) (... ...)))))))
     ]))

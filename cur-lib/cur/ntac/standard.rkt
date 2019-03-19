#lang s-exp "../main.rkt"

(provide (for-syntax (all-defined-out)))

(require
 (for-syntax "ctx.rkt" "utils.rkt"
             (except-in macrotypes/stx-utils)
             (only-in macrotypes/typecheck-core subst substs)
             racket/exn
             racket/port
             racket/list
             racket/match
             racket/format
             racket/pretty
             syntax/stx
             (for-syntax racket/base syntax/parse))
 "../stdlib/prop.rkt"
 "../stdlib/sugar.rkt"
 "base.rkt")

;; define-nttz-cmd ?
(define-for-syntax (nop ptz) ptz)

;; exceptions for tactics
(begin-for-syntax
  ;; ntac exceptions
  (struct exn:fail:ntac exn:fail ())

  ;; ntac exception for when the goal is not as expected.
  (struct exn:fail:ntac:goal exn:fail:ntac ())
  (define (raise-ntac-goal-exception msgf . rest)
    (raise (exn:fail:ntac:goal (apply format msgf rest) (current-continuation-marks))))

  (define-syntax-rule (ntac-match goal [pattern branch] ...)
    (cur-match goal
      [pattern branch]
      ...
      [_ (raise-ntac-goal-exception
          "Goal ~a did not match; you can use the `try` meta tactic to ignore this."
          goal)])))

;; display tactic
;; TODO: print number of subgoals
(begin-for-syntax
  (define (display-focus tz)
    (match (nttz-focus tz)
      [(ntt-hole _ goal)
       (when (current-tracing?)
         (let ([hole-count (num-holes (nttz-focus (to-top tz)))])
           (if (> hole-count 1)
               (printf "\n(subgoal 1 of ~a)\n\n" hole-count)
               (printf "\n"))))
       (for ([(k v) (nttz-context tz)])
         (let ([v-datum (stx->datum (cur-pretty-print v))])
           (if (> (string-length (~a v-datum)) 80)
               (printf "~a :\n ~a"
                (stx->datum k)
                (substring ; drop the leading '
                 (with-output-to-string (λ () (pretty-print v-datum))) 1))
             (printf "~a : ~a\n" (stx->datum k) v-datum))))
       (printf "--------------------------------\n")
       (let ([goal-datum (stx->datum (cur-pretty-print goal))])
         (if (> (string-length (~a goal-datum)) 80)
             (printf "~a\n" ; drop the leading '
                     (substring (with-output-to-string (λ () (pretty-print goal-datum))) 1))
             (printf "~a\n\n" goal-datum)))]
      [(ntt-done _ _ _)
       (printf "Proof complete.\n")]
      [_
       ;; XXX
       (printf "Not at hole.\n")])
    tz)
  (define (display-focus/raw tz)
    (match (nttz-focus tz)
      [(ntt-hole _ goal)
       (for ([(k v) (nttz-context tz)])
         (printf "~a : ~a\n" (syntax->datum k) (syntax->datum (cur-pretty-print v))))
       (for ([(k v) (nttz-context tz)])
         (printf "~a : ~a\n" (syntax->datum k) (syntax->datum v)))
       (printf "--------------------------------\n")
       (printf "~a\n" (syntax->datum (cur-pretty-print goal)))
       (pretty-print (syntax->datum goal))
       (printf "\n\n")]
      [(ntt-done _ _ _)
       (printf "Proof complete.\n")]
      [_
       ;; XXX
       (printf "Not at hole.\n")])
    tz))

(begin-for-syntax
  (define current-proof null)
  (define (reset-current-proof!)
    (set! current-proof null))
  (define (current-proof-add! stx)
    (set! current-proof (cons stx current-proof)))
(define (interactive ptz)
  (current-tracing? 1)
  (display-focus ptz)
  (define cmd-stx
    (let/ec esc
      (parameterize ([current-eval
                      (λ (in)
                        (syntax-case in ()
                          [(_ . cmd)
                           (esc #'cmd)]))])
        (read-eval-print-loop))))
  (current-proof-add! cmd-stx)
  (define next-ptz
    (with-handlers ([exn:fail:ntac:goal?
                     (lambda (e)
                       (displayln (exn->string e))
                       ptz)])
      (eval-proof-step ptz cmd-stx)))
  (if (nttz-done? next-ptz)
      (begin
        (printf "complete proof script:\n")
        (for-each
         (λ (stx) (printf "~a\n" (syntax->datum stx)))
         (reverse (stx->list current-proof)))
        (reset-current-proof!)
        (current-tracing? #f)
        next-ptz)
      (interactive next-ptz))))

(define-for-syntax ((fill t) ptz)
  (define new-foc (t (nttz-context ptz) (nttz-focus ptz)))
  ;; XXX Maybe new-foc could be #f for failure?
  (next
   (struct-copy nttz ptz [focus new-foc])))

;; meta tactic; not a tactic (which take tacticals); takes a tactic.
(define-for-syntax ((try t) ptz)
  (with-handlers ([exn:fail:ntac:goal? (lambda (e) ptz)])
    (t ptz)))

;; define-tactical

(begin-for-syntax

  (define ((assert H ty) ctxt pt)
    (match-define (ntt-hole _ goal) pt)

    (make-ntt-apply
     goal
     (let ([ty+ (normalize ty ctxt)])
       (list
        (make-ntt-hole ty+)
        (make-ntt-context
         (ctx-add/id H ty+)
         (make-ntt-hole goal))))
     (lambda (arg-pf body-pf)
       (quasisyntax/loc goal
         ((λ (#,H : #,ty)
            #,body-pf)
          #,arg-pf)))))

  (define-syntax (by-assert syn)
    (syntax-case syn ()
      [(_ H ty)
       #`(fill (assert #'H #'ty))]))

;; when name = #f, ie programmer does not give name
;; use scope from stx for introduced id
(define ((intro [name #f] #:stx [stx #f]) ctxt pt)
  ;; TODO: ntt-match(-define) to hide this extra argument. Maybe also add ntt- to constructors in pattern?
  (match-define (ntt-hole _ goal) pt)
  (ntac-match goal
   [(~Π (x:id : P:expr) body:expr)
    (let ()
      (define the-name (or name (datum->syntax stx (stx-e #'x))))
      (make-ntt-apply
       goal
       (list
        (make-ntt-context
         (ctx-add/id the-name #'P)
         (make-ntt-hole (cur-rename the-name #'x #'body))))
       (lambda (body-pf)
         (quasisyntax/loc goal (λ (#,the-name : #,(unexpand #'P)) #,body-pf)))))]))

;; generalize is opposite of intro
;; TODO: (generalize x) should also lift out y\in ctx where ctx[y] references x
(define ((generalize name) ctxt pt)
  (match-define (ntt-hole _ goal) pt)
    (make-ntt-apply
     goal
     (list
      (make-ntt-context
       (ctx-remove/id name)
       (make-ntt-hole
        (normalize #`(Π [#,name : #,(ctx-lookup ctxt name)] #,goal)
                   (ctx-remove ctxt name)))))
     (lambda (body-pf)
       (quasisyntax/loc goal (#,body-pf #,name)))))

;; A pattern emerges:
;; tacticals must take additional arguments as ntac-syntax
;; define-tactical should generate a phase 2 definition like the one below, and a functional version
;; of the tactical (perhaps by-tactical-name)
  (define-syntax (by-intro syn)
    (syntax-parse syn
      [(_ syn:id #:as paramss)
       #`(compose (fill (destruct #'syn #'paramss)) (fill (intro #'syn)))]
      [(_ syn:id)
       #`(fill (intro #'syn))]
      [b-i:id
       #`(fill (intro #:stx #'b-i))]))

  ;; generalize: opposite of intro
  (define-syntax (by-generalize syn)
    (syntax-case syn ()
      [(_ syn) #`(fill (generalize #'syn))]))

(define (intros names #:stx [stx #f])
  (if (null? names)
      (λ (ctxt pt)
        (match-define (ntt-hole _ goal) pt)
        (ntac-match goal
         [(~Π [x : P] ... body:expr)
          (let ()
            (define the-names
              (map
               (λ (x)
                 (if (syntax-property x 'tmp)
                     (datum->syntax stx (stx-e (generate-temporary #'H)))
                     (datum->syntax stx (stx-e x))))
               (stx->list #'(x ...))))
            (define the-Ps
              (substs the-names #'(x ...) #'(P ...)))
            (make-ntt-apply
             goal
             (list
              (make-ntt-context
               (ctx-adds/ids the-names the-Ps)
               (make-ntt-hole (substs the-names #'(x ...) #'body))))
             (lambda (body-pf)
               (quasisyntax/loc goal
                 (λ #,@(for/list ([name the-names] [P (stx->list the-Ps)])
                         #`[#,name : #,(unexpand P)])
                   #,body-pf)))))]))
      (for/fold ([t nop])
                ([n (in-list names)])
        (compose (fill (intro n)) t))))
  (define-syntax (by-intros syn)
    (syntax-parse syn
      [(_ x:id ...)
       #'(intros (list #'x ...))]
      [b-is:id
       #'(fill (intros null #:stx #'b-is))]))

;; define-tactical
(define ((exact a) ctxt pt)
  (match-define (ntt-hole _ goal) pt)
  (unless (cur-type-check? a goal #:local-env (ctx->env ctxt))
    (raise-ntac-goal-exception "~a does not have type ~a"
                               (stx->datum (resugar-type a))
                               (stx->datum (resugar-type goal))))
  (make-ntt-exact goal a))

  (define-syntax (by-exact syn)
    (syntax-case syn ()
      [(_ syn)
       #`(fill (exact #'syn))]))

;;define-tactical
(define (assumption ctxt pt)
  (match-define (ntt-hole _ goal) pt)
  ;; TODO: Actually, need to collect (k v) as we search for a matching assumption, otherwise we might
  ;; break dependency. Hopefully we have some invariants that prevent that from actually happening.
  (define ntt
    (for/or ([(k v) ctxt]
           #:when (cur-equal? v goal #:local-env (ctx->env ctxt)))
      (make-ntt-exact goal k)))
  (unless ntt
    (raise-ntac-goal-exception "could not find matching assumption for goal ~a" goal))
  ntt)

  (define-syntax (by-assumption syn)
    (syntax-case syn ()
      [_
       #`(fill assumption)]))

  (define (obvious ctxt pt)
    (match-define (ntt-hole _ goal) pt)
    (ntac-match goal
      [(~Π (a : P) body)
       ((intro #'a) ctxt pt)]
      [a:id
       (assumption ctxt pt)]))

  (define (by-obvious ptz)
    (define nptz ((fill obvious) ptz))
    (if (nttz-done? nptz)
        nptz
        (by-obvious nptz)))

  (define (simpl ptz)
    (match-define (ntt-hole _ goal) (nttz-focus ptz))
    (next
     ;; TODO: should this be a copy?
     (struct-copy nttz ptz
                  [focus
                   (make-ntt-hole (normalize goal (nttz-context ptz)))])))

  (define-syntax (by-destruct syn)
    (syntax-case syn ()
      [(_ x)
       #`(fill (destruct #'x))]
      [(_ x #:as param-namess)
       #`(fill (destruct #'x #'param-namess))]))

  ;; TODO: properly handle indexed types (copy from `induction`)
  (define ((destruct e_ [param-namess #f]) ctxt pt)
    (match-define (ntt-hole _ goal) pt)

    (define e (if (identifier? e_) e_ (normalize e_ ctxt)))
    (define e-ty (or (and (identifier? e) (ctx-lookup ctxt e))
                     ;; this is needed because the scopes of X in e
                     ;; wont match X in ctxt
                     ;; TODO: better way to fix this?
                     (ctx-introduce (typeof e) ctxt)))
    (unless e-ty
      (raise-ntac-goal-exception
       "by-destruct: could not find ~a" (stx->datum e)))
    
    (define name (if (identifier? e) e (generate-temporary)))
    (define/syntax-parse (_ ([A _] ...) ([i_ _] ...) [C ([x τ_] ... _) _] ...)
      (get-match-info e-ty))

    (define Cs #'(C ...))

    ;; infer params and indices from e-ty
    (define/syntax-parse ((X ...) (i ...))
      (syntax-parse e-ty
        [((~literal #%plain-app) _ . name-ty-args)
         (stx-split-at #'name-ty-args (stx-length #'(A ...)))]))

    (define/syntax-parse ((τ ...) ...)
      (stx-map
       (λ (ts) (stx-map (normalize/ctxt ctxt) ts))
       (substs #'(X ...) #'(A ...) #'((τ_ ...) ...))))

    (define paramss
      (or param-namess
          (stx-map (freshens e) #'((x ...) ...))))

    (unless (stx-length=? paramss Cs)
      (raise-ntac-goal-exception
       "by-destruct: given wrong number of parameter names: ~a"
       (stx->datum param-namess)))

    ;; pats and Cinstances are same except pat is used in match pattern,
    ;; which drops params (bc elim methods do not re-bind params)
    (define pats
      (stx-map
       (λ (C ps)
         (if (stx-null? ps)
             C
             #`(#,C . #,ps)))
       Cs paramss))
    (define Cinstances
      (stx-map
       (λ (C ps)
         (if (and (stx-null? ps) (stx-null? #'(X ...)))
             C
             #`(#,C X ... . #,ps)))
       Cs paramss))

    ;; split ctxt at where `name` is bound:
    ;; - innermost binding of outer-ctxt is `name`
    ;; - if e is not id, then outer-ctxt is empty
    (define-values (outer-ctxt inner-ctxt)
      (if (identifier? e_)
          (ctx-lookup/split ctxt name)
          (values (mk-empty-ctx) ctxt)))

    ;; split inner-ctxt according to whether its types contain `e`
    ;; - inner/noname: bindings have types that do not contain `e`
    ;; - inner/name: type of first binding (call it x) that has `e`
    ;;   - the rest of inner/name is the rest of inner-ctxt after `x`
    ;;     - these bindings must be re-bound because they may reference `x`
    (define-values (inner/noname inner/name)
      (ctx-splitf/ty/outerin inner-ctxt (λ (t) (not (has-term? e t)))))

    (make-ntt-apply
     goal
     (stx-map
      (λ (Cinstance C-types params)
        ;; adding params into ctx is slightly tricky:
        ;; - a param-type may refer to inner-ctxt binding
        ;;   - see plus-n-Sm, IH param, in rewrite-with-previous.rkt
        ;; - but a binding's type in inner-ctxt may also reference param
        ;;   - see destruct n in length-app-sym, in Poly.rkt
        ;; Current insertion algo:
        ;; 1. remove name from outer-ctxt
        ;; 2. add params to inner/noname
        ;; 3. update types in inner/name with destructed term instances
        ;; 4. merge together updated outer-ctxt, inner/noname, and inner/name
        (define (update-ctxt old-ctxt)
          (define tmp-ctxt
            (ctx-append
             (if (identifier? e_)
                 (ctx-remove-inner outer-ctxt) ; drop name from old-ctxt
                 (mk-empty-ctx))
             (ctx-adds
              inner/noname
              (stx->list params)
              (stx->list C-types))))
          ;(ctx-append
           ;tmp-ctxt
           (ctx-fold ; update ty in ctxt with (subst-term Cinstance name _)
            (λ (h ctxt-acc) (normalize (subst-term Cinstance e h) ctxt-acc))
            inner/name
            tmp-ctxt))
        (make-ntt-context
          update-ctxt
          (make-ntt-hole (normalize (subst-term Cinstance e goal) (update-ctxt ctxt)))))
      Cinstances
      #'((τ ...) ...)
      paramss)
     (λ pfs
       (quasisyntax/loc goal
         ;; each match body must be an eta-expansion of the pf \in pfs,
         ;; and the match term must be applied to the env bindings whose tys ref the destructed var
         ((match #,(quasisyntax/loc e_ #,(unexpand e))
            #:as #,name
            #:with-indices i ...
            #:in #,(unexpand e-ty)
            #:return (Π #,@(for/list ([(x ty) inner/name])
                             #`[#,x : #,(unexpand (subst-term name e ty))])
                         #,(unexpand (subst-term name e goal)))
                 . #,(stx-map
                      (λ (pat Cinstance pf)
                        #`[#,pat
                           (λ #,@(for/list ([(x ty) inner/name])
                                   #`[#,x : #,(unexpand (subst-term Cinstance e ty))])
                             #,pf)])
                      pats
                      Cinstances
                      pfs))
          #,@(ctx-ids inner/name))))))

  (define-syntax (by-induction syn)
    (syntax-case syn ()
      [(_ x) #'(fill (induction #'x))]
      [(_ x #:as arg-namess) #'(fill (induction #'x #:as #'arg-namess))]))

  ;; TODO: similar to destruct; merge somehow?
  ;; TODO: currently only handles induction of an identifier (`name`)
  ;; maybe-xss+IH is new data constructor arg names to use (including IH)
  (define ((induction name #:as [maybe-xss+IH #f]) ctxt pt)
    (match-define (ntt-hole _ goal) pt)

    (define name-ty (ctx-lookup ctxt name))

    (define/syntax-parse ; get define-datatype info (types are unexpanded)
      (_ ([A _] ...) #;params ([i _] ...) #;indices Cinfo ...)
      (get-match-info name-ty))

    (define num-params (stx-length #'(A ...)))
    
    (define get-idxs ; extract indices from *unexpanded* type
      (if (stx-null? #'(i ...))
          (λ (t) null)
          (λ (t) (stx-drop t (add1 num-params)))))

    (when (and maybe-xss+IH (not (stx-length=? maybe-xss+IH #'(Cinfo ...))))
      (raise-ntac-goal-exception
       "induction: not enough sets of names: given ~a, expected ~a"
       (stx-length maybe-xss+IH) (stx-length #'(Cinfo ...))))

    ;; infer from name-ty: params (Aval ...) and indices (ival ...)
    (define/syntax-parse ((Aval ...) (ival ...))
      (syntax-parse name-ty
        [((~literal #%plain-app) _ . name-ty-args)
         (stx-split-at #'name-ty-args num-params)]))

    ;; stxs-to-change: parts of the goal (and ctxt tys) to update, in each subgoal.
    ;; Consists of `name` and the index values from its type
    (define stxs-to-change (cons name #'(ival ...)))

    ;; mk-update: Stx Stxs -> (-> Ty Ty)
    ;; Consumes an instance of the destructed term its new indices.
    ;; Returns a function that updates a type by replacing any `stxs-to-change`
    ;; with the given stxs
    (define (mk-update #:inst inst #:idxs idxs)
      (unless (stx-length=? #'(ival ...) idxs)
        (raise-ntac-goal-exception
         "induction: mk-update fn: wrong number of indices, given ~a, expected ~a"
         (stx-length idxs) (stx-length #'(ival ...))))
      (subst-terms/es (cons inst idxs) stxs-to-change))

    ;; modify ctxt:
    ;; 1) remove:
    ;; - `name`
    ;; - any (ival ...), if they are id
    ;; 2) partition into:
    ;; - ctxt-to-change: extract ctx items whose type contains either
    ;;   `name` or any of the indices #'(ival ...)
    ;; These items are affected by the induction and must be updated.
    ;; - ctxt-unchanged: remaining items
    ;; Items are bound in the same relative order.
    (define-values (ctxt-to-change ctxt-unchanged)
      (ctx-partition/ty
       (ctx-removes ctxt (cons name (stx-filter id? #'(ival ...))))
       (λ (t) (or (has-term? name t)
                  (stx-ormap
                   (λ (iv) (has-term? iv t))
                   #'(ival ...))))))

    ;; generate subgoals and elim methods in one pass
    ;; subgoals: list of ntt proof tree nodes
    ;; mk-elim-methods: list of fns that turn a proof term into an elim method
    (define-values (subgoals mk-elim-methods)
      (for/lists (subgoals mk-elim-methods)
                 ([maybe-xs+IH (if maybe-xss+IH
                                   (in-stx-list maybe-xss+IH)
                                   (stx-map (λ _ #'()) #'(Cinfo ...)))] ; names not given, gen tmp for now
                  [Cinfo (in-stx-list #'(Cinfo ...))])
        (syntax-parse Cinfo
          [[C ([x τ_] ... τout_) ((xrec . _) ...)]
           #:do[(define new-xs+IH ; make sure enough names supplied
                  (if (stx-length=? maybe-xs+IH #'(x ... xrec ...))
                      maybe-xs+IH
                      (stx-append ; else generate based on extra-info names
                       ((freshens name) #'(x ...))
                       ((freshens name)
                        (stx-map (λ _ (generate-temporary 'IH)) #'(xrec ...))))))]
           #:with (new-xs _) (stx-split-at new-xs+IH (stx-length #'(x ...)))
           #:with (τ ... τout) (substs #'(Aval ... . new-xs)
                                       #'(A ... x ...)
                                       #'(τ_ ... τout_))
           #:with IHτs (for/list ([new-x (in-stx-list #'new-xs)]
                                  [τ (in-stx-list #'(τ ...))]
                                  [x (in-stx-list #'(x ...))]
                                  #:when (stx-member x #'(xrec ...)))
                         (define update-IH-ty
                           (mk-update #:inst new-x #:idxs (get-idxs τ)))
                         ;; IH must include changed ctxt bindings
                         #`(-> #,@(ctx-tys->stx ctxt-to-change #:do update-IH-ty)
                               #,(update-IH-ty goal)))
           #:do[(define update-ty
                  (mk-update #:inst #'(C Aval ... . new-xs) #:idxs (get-idxs #'τout)))
                (define (update-ctxt old-ctxt)
                  (define tmp-ctxt
                    (ctx-adds ctxt-unchanged
                              new-xs+IH
                              #'(τ ... . IHτs) #:do normalize))
                  (ctx-append tmp-ctxt
                              (ctx-map
                               (compose (normalize/ctxt tmp-ctxt) update-ty)
                               ctxt-to-change)))]
           (values
            (make-ntt-context ; subgoal
             update-ctxt
             (make-ntt-hole
              (normalize (update-ty goal) (update-ctxt ctxt))))
            (λ (pf)           ; fn to make elim method from a proof term
              #`(λ #,@new-xs+IH
                  (λ #,@(ctx->stx ctxt-to-change #:do (compose unexpand update-ty))
                    #,pf))))])))
    
    (make-ntt-apply
     goal
     subgoals
     (λ pfs ;; constructs induction proof term, from proof terms for each subgoal
       (quasisyntax/loc goal
         ((new-elim
           #,name
           #,(with-syntax ([is (generate-temporaries #'(ival ...))])
               (define update-Prop-ty
                 (compose unexpand (subst-terms/es #'is #'(ival ...))))
               #`(λ #,@#'is #,name
                    (Π #,@(ctx->stx ctxt-to-change #:do update-Prop-ty)
                       #,(update-Prop-ty goal))))
           .
           #,(map (λ (pf->meth pf) (pf->meth pf)) mk-elim-methods pfs))
          #,@(ctx-ids ctxt-to-change))))))

  (define (split-fn ctxt pt)
    (match-define (ntt-hole _ goal) pt)
    (ntac-match goal
      [(~And X Y)
       (make-ntt-apply
        goal
        (list (make-ntt-hole (normalize #'X ctxt))
              (make-ntt-hole (normalize #'Y ctxt)))
        (λ (proj1 proj2)
          #`(conj #,(unexpand #'X)
                  #,(unexpand #'Y)
                  #,proj1
                  #,proj2)))]))

  (define-syntax (by-split syn)
    (syntax-case syn ()
      [_ #'(fill split-fn)]))

  (define ((make-Or-intro-fn which constructor) ctxt pt)
    (match-define (ntt-hole _ goal) pt)
    (ntac-match goal
      [(~Or X Y)
       (make-ntt-apply
        goal
        (list (make-ntt-hole (normalize (which #'X #'Y) ctxt)))
        (λ (pf)
          #`(#,constructor
             #,(unexpand #'X)
             #,(unexpand #'Y)
             #,pf)))]))

  (define-syntax (by-left syn)
    (syntax-case syn ()
      [_ #'(fill (make-Or-intro-fn (λ (p q) p) #'left))]))
  (define-syntax (by-right syn)
    (syntax-case syn ()
      [_ #'(fill (make-Or-intro-fn (λ (p q) q) #'right))])))

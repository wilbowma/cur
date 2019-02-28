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
    (define/syntax-parse (_ ([A _] ...) ([i_ _] ...) [C ([x τ_] ...) _] ...)
      (get-match-info e-ty))

    (define Cs #'(C ...))

    ;; infer params and indices from e-ty
    (define/syntax-parse ((X ...) (i ...))
      (syntax-parse e-ty
        [((~literal #%plain-app) _ . name-ty-args)
         (stx-split-at #'name-ty-args (stx-length #'(A ...)))]))

    (define/syntax-parse ((τ ...) ...)
      (substs #'(X ...) #'(A ...) #'((τ_ ...) ...)))

    (define paramss
      (or param-namess
          (stx-map (freshens e) #'((x ...) ...))))

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
      [(_ x #:as param-namess) #'(fill (induction #'x #'param-namess))]))

  ;; TODO: similar to destruct; merge somehow?
  ;; TODO: use match or elim as proof term?
  (define ((induction name [paramss_ #f]) ctxt pt)
    (match-define (ntt-hole _ goal) pt)

    (define name-ty (ctx-lookup ctxt name))

    (define/syntax-parse (_ ([A _] ...) _ [C ([x τ_] ...) ((xrec . _) ...)] ...)
      (get-match-info name-ty))

    (define paramss
      (if (and paramss_ (stx-length=? paramss_ #'((x ...) ...)))
          (stx-map
           (λ (params xs xrecs)
             (if (stx-length=? params (stx-append xs xrecs))
                 params
                 (stx-append ((freshens name) xs)
                             ((freshens name)
                              (stx-map
                               (λ (x) (generate-temporary 'IH))
                               xrecs)))))
           paramss_
           #'((x ...) ...)
           #'((xrec ...) ...))
          (stx-map
           (λ (xs xrecs)
             (stx-append ((freshens name) xs)
                         ((freshens name)
                          (stx-map
                           (λ (x) (generate-temporary 'IH))
                           xrecs))))
           #'((x ...) ...)
           #'((xrec ...) ...))))

    (define Cs #'(C ...))

    ;; infer params from name-ty
    (define/syntax-parse (X ...)
      (syntax-parse name-ty
        [((~literal #%plain-app) _ . name-ty-args)
         (stx-take #'name-ty-args (stx-length #'(A ...)))]))

    (define/syntax-parse ((τ ...) ...)
      (substs #'(X ...) #'(A ...) #'((τ_ ...) ...)))
    (define pats ; TODO: check length of paramss against (τ...) ...?
      (stx-map
       (λ (C τs ps)
         (if (and (stx-null? ps) (stx-null? #'(X ...)))
             C
             ; dont include IHs as C arg
             #`(#,C X ... . #,(stx-take ps (stx-length τs)))))
       Cs
       #'((τ ...) ...)
       paramss))

    ;; for each param, type is either
    ;; - argument types from C-type (if arg)
    ;; - subst xrec for name in goal (if IH)
    ;;   - where xrec specified by the "match info"
    (define param-typess
      (stx-map
       (λ (params τs xs xrecs)
         ;; params = regular C args + IHs
         (match-define (list ps IHs) (stx-split-at params (stx-length τs)))
         #`(#,@τs .
            #,(for/list ([ih IHs])
                (for/fold ([g goal])
                          ([p ps] [x (in-stx-list xs)] #:when (stx-member x xrecs))
                  ;; TODO: is this right? subst xrecs (assuming only 1) for name in goal
                  (subst p name goal)))))
       paramss
       #'((τ ...) ...)
       #'((x ...) ...)
       #'((xrec ...) ...)))

    ;; split ctxt at where `name` is bound:
    ;; - innermost binding of outer-ctxt is `name`
    (define-values (outer-ctxt inner-ctxt) (ctx-lookup/split ctxt name))

    ;; split inner-ctxt according to whether its types reference `name`:
    ;; - inner/noname: bindings have types that do not reference name
    ;; - inner/name: type of first binding (call it x) references `name`
    ;;   - the rest of inner/name is the rest of inner-ctxt after `x`
    ;;     - these bindings must be rebound because they may reference `x`
    (define-values (inner/noname inner/name)
      (ctx-splitf/ty/outerin inner-ctxt (λ (t) (not (has-term? name t)))))

    (make-ntt-apply
     goal
     (stx-map
      (λ (pat params param-types)
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
             (ctx-remove-inner outer-ctxt) ; drop name from old-ctxt
             (ctx-adds
              inner/noname
              (stx->list params)
              (stx->list param-types))))
          (ctx-append
           tmp-ctxt
           (ctx-map ; update ty in ctxt with (subst-term pat name _)
            (subst-term/e (normalize pat tmp-ctxt) name)
            inner/name)))
        (make-ntt-context
         update-ctxt
         (make-ntt-hole
          (normalize (subst pat name goal) (update-ctxt ctxt)))))
      pats
      paramss
      param-typess)
     (λ pfs
       (quasisyntax/loc goal
         ((new-elim
           #,name
           (λ [#,name : #,(unexpand name-ty)]
             (Π #,@(for/list ([(x ty) inner/name])
                     #`[#,x : #,ty])
                #,(unexpand goal)))
           .
           #,(stx-map
              (λ (pat params param-types pf)
                (if (null? (stx->list params))
                    pf
                    (foldr
                     (λ (p ty e) #`(λ [#,p : #,(unexpand ty)] #,e))
                     #`(λ #,@(for/list ([(x ty) inner/name])
                               #`[#,x : #,(unexpand (subst-term pat name ty))])
                         #,pf)
                     (stx->list params)
                     (stx->list param-types))))
              pats
              paramss
              param-typess
              pfs))
          #,@(ctx-ids inner/name)))))))

#lang s-exp "../main.rkt"

(provide (for-syntax (all-defined-out) inversion))

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
             (for-syntax racket/base syntax/parse syntax/stx))
 "../stdlib/prop.rkt"
 "../stdlib/sugar.rkt"
 "base.rkt"
 "inversion.rkt")

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

(define-for-syntax ((fill t #:rest [psteps #'()]) ptz)
  (define new-foc (t (nttz-context ptz) (nttz-focus ptz)))
  ;; XXX Maybe new-foc could be #f for failure?
  (eval-proof-steps (next (struct-copy nttz ptz [focus new-foc])) psteps))

;; meta tactic; not a tactic (which take tacticals); takes a sequence of tactics
(define-for-syntax ((try . ts) ptz)
  (with-handlers ([exn:fail? #;exn:fail:ntac:goal? ; catch other fails too, eg unbound id
                             (lambda (e)
                               ;; (displayln "try failed:")
                               ;; (pretty-print e)
                               ptz)])
    ((apply compose (reverse ts)) ptz)))

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

(define ((intros #:stx [stx #f]) ctxt pt)
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
  (define-syntax (by-intros syn)
    (syntax-parse syn
      [(_ x:id ...)
       #'(for/fold ([t nop])
                   ([n (in-list (list #'x ...))])
           (compose (fill (intro n)) t))]
      [b-is:id #'(fill (intros #:stx #'b-is))]))

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

  (define ((destruct e_ [maybe-xss #f]) ctxt pt)
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

    (define/syntax-parse ; get define-datatype info (types are unexpanded)
      (_ ([A _] ...) #;params ([i _] ...) #;indices Cinfo ...)
      (get-match-info e-ty))

    (define num-params (stx-length #'(A ...)))
    (define num-idxs   (stx-length #'(i ...)))
    
    (define get-idxs ; extract indices from *unexpanded* (curried single-app) type
      (if (zero? num-idxs)
          (λ (t) null)
          (λ (t) (get-idxs/unexp t num-idxs))))

    (when (and maybe-xss (not (stx-length=? maybe-xss #'(Cinfo ...))))
      (raise-ntac-goal-exception
       "destruct: not enough sets of names: given ~a, expected ~a"
       (stx-length maybe-xss) (stx-length #'(Cinfo ...))))

    ;; infer from e-ty: params (Aval ...) and indices (ival ...)
    (define/syntax-parse ((Aval ...) (ival ...))
      (syntax-parse e-ty
        [((~literal #%plain-app) _ . e-ty-args)
         (stx-split-at #'e-ty-args num-params)]))

    ;; stxs-to-change: parts of the goal (and ctxt tys) to update, in each subgoal.
    ;; Consists of `e` and the index values from its type
    (define stxs-to-change (cons e #'(ival ...)))

    ;; mk-update: Stx Stxs -> (-> Ty Ty)
    ;; Consumes an instance of the destructed term and its new indices.
    ;; Returns a function that updates a type by replacing any `stxs-to-change`
    ;; with the given stxs
    (define (mk-update #:inst inst #:idxs idxs)
      (unless (stx-length=? #'(ival ...) idxs)
        (raise-ntac-goal-exception
         "name: mk-update: wrong number of indices, given ~a: ~a; expected ~a, eg ~a"
         (stx-length idxs) (stx->datum idxs)
         (stx-length #'(ival ...)) (stx->datum (resugar-type e-ty))))
      (subst-terms/es (cons inst idxs) stxs-to-change))

    ;; modify ctxt:
    ;; 1) remove e \in stxs-to-change, if id
    ;; 2) partition into:
    ;; - ctxt-to-change: ctx items whose type contains element of stxs-to-change
    ;;    - These items are affected by the induction and must be updated.
    ;; - ctxt-unchanged: remaining items
    ;; Items are bound in the same relative order.
    (define-values (ctxt-to-change ctxt-unchanged)
      (ctx-partition/ty
       (ctx-removes ctxt (stx-filter id? stxs-to-change))
       (λ (t) (stx-ormap (has-term/e? t) stxs-to-change))))

    ;; generate subgoals and elim methods in one pass
    ;; subgoals: list of ntt proof tree nodes
    ;; mk-match-clauses: list of fns that turn a proof term into a match clause
    (define-values (subgoals mk-match-clauses)
      (for/lists (subgoals mk-match-clauses)
                 ([maybe-xs (if maybe-xss
                                (in-stx-list maybe-xss)
                                (stx-map (λ _ #'()) #'(Cinfo ...)))] ; names not given, gen tmp for now
                  [Cinfo (in-stx-list #'(Cinfo ...))])
        (syntax-parse Cinfo
          [[C ([x τ_] ... τout_) ((xrec . _) ...)]
           #:with new-xs
                  (if (stx-length=? maybe-xs #'(x ...))
                      maybe-xs
                      ; else generate based on extra-info names
                      ((freshens e_) (generate-temporaries #'(x ...))))
           #:with (τ ... τout) (substs #'(Aval ... . new-xs)
                                       #'(A ... x ...)
                                       #'(τ_ ... τout_))
           #:with pat (if (stx-null? #'new-xs) #'C #'(C . new-xs))
           #:do[(define update-ty
                  (mk-update #:inst #'(C Aval ... . new-xs) #:idxs (get-idxs #'τout)))
                (define (update-ctxt old-ctxt)
                  (define tmp-ctxt
                    (ctx-adds ctxt-unchanged #'new-xs #'(τ ...) #:do normalize))
                  (ctx-append tmp-ctxt
                              (ctx-map
                               (compose (normalize/ctxt tmp-ctxt) update-ty)
                               ctxt-to-change)))]
           (values
            (make-ntt-context ; subgoal
             update-ctxt
             (make-ntt-hole
              (normalize (update-ty goal) (update-ctxt ctxt))))
            (λ (pf)           ; fn to make match clause from a proof term
              #`[pat
                 (λ #,@(ctx->stx ctxt-to-change #:do (compose unexpand update-ty))
                   #,pf)]))])))

    (make-ntt-apply
     goal
     subgoals
     (λ pfs
       (quasisyntax/loc goal
         ;; each match body must be an eta-expansion of the pf \in pfs,
         ;; and the match term must be applied to the env bindings whose tys ref the destructed var
         ((match #,(quasisyntax/loc e_ #,(unexpand e))
            #:as #,name
            #:with-indices i ...
            #:in #,(unexpand e-ty)
            #:return #,(let ([update-Prop-ty
                              (compose unexpand (mk-update #:inst name #:idxs #'(i ...)))])
                         #`(Π #,@(ctx->stx ctxt-to-change #:do update-Prop-ty)
                              #,(update-Prop-ty goal)))
            . #,(map (λ (pf->clause pf) (pf->clause pf)) mk-match-clauses pfs))
          #,@(ctx-ids ctxt-to-change))))))

  (define-syntax (by-induction syn)
    (syntax-case syn ()
      [(_ x) #'(fill (induction #'x))]
      [(_ x #:as arg-namess) #'(fill (induction #'x #:as #'arg-namess))]
      [(_ H [(C x ...) #:subgoal-is subg tac ...] ...)
       #'(fill (induction #'H #:as #'((x ...) ...) #:subgoals #'(subg ...))
               #:rest #'(tac ... ...))]))

  ;; TODO: similar to destruct; merge somehow?
  ;; TODO: currently only handles induction of an identifier (`name`)
  ;; maybe-xss+IH is new data constructor arg names to use (including IH)
  (define ((induction name #:as [maybe-xss+IH #f] #:subgoals [expected-subgoals #f]) ctxt pt)
    (match-define (ntt-hole _ goal) pt)

    (define name-ty (ctx-lookup ctxt name))

    (define/syntax-parse ; get define-datatype info (types are unexpanded)
      (_ ([A _] ...) #;params ([i _] ...) #;indices Cinfo ...)
      (get-match-info name-ty))

    (define num-params (stx-length #'(A ...)))
    (define num-idxs (stx-length #'(i ...)))
    
    (define get-idxs ; extract indices from *unexpanded* (curried single-app) type
      (if (stx-null? #'(i ...))
          (λ (t) null)
          (λ (t) (get-idxs/unexp t num-idxs))))

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
         "induction: mk-update: wrong number of indices, given ~a: ~a; expected ~a, eg ~a"
         (stx-length idxs) (stx->datum idxs)
         (stx-length #'(ival ...)) (stx->datum (resugar-type name-ty))))
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
                       ((freshens name) (generate-temporaries #'(x ...)))
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

    ;; check if supplied subgoals match actual
    (when (and expected-subgoals (stx-length=? expected-subgoals subgoals))
      (for ([subg subgoals]
            [exp-subg (in-stx-list expected-subgoals)])
        (match subg
          [(ntt-context _ _ update (ntt-hole _ subgoal))
           (unless (typecheck? subgoal (normalize exp-subg (update ctxt)))
             (raise-ntac-goal-exception
              "induction: encountered subgoal ~a that does not match expected: ~a"
              (stx->datum (resugar-type subgoal))
              (stx->datum exp-subg)))])))
    
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
      [_ #'(fill (make-Or-intro-fn (λ (p q) q) #'right))]))

;; find-ntt-apply : nttz -> nttz
;; Returns nttz with focus that is innermost ntt-apply node to given nttz.
;; Returns #f if there are no ntt-apply nodes in proof tree
(define (find-ntt-apply orig-ptz)
  (let L ([ptz orig-ptz])
    (define pt (nttz-focus ptz))
    (if (and (ntt-apply? pt)
             (> (length (ntt-apply-subterms pt)) 1)) ; skip nodes like rewrite
        ptz
        (if (nttz-done? ptz)
            #f
            (L (nttz-up ptz))))))

;; to-end : nttz nat -> nttz
;; Focus of ptz must be ntt-apply node.
;; Moves nth node to the end of the node list,
;; where n is the position of the first hole node.
;; Returns new nttz with the new apply node as the focus
(define (to-end ptz n) ; n is the current (hole) node
  (match-define (nttz ctxt pt prev) ptz)
  (match-define (ntt-apply _ g nodes proof-fn) pt)
  (define-values (before this+after) (split-at nodes n))
  (match-define (cons this-node after) this+after)
  (define new-pt
    (make-ntt-apply
     g
     (append before after (list this-node)) ; move first hole node to end
     (λ pfs                                 ; move last pf to nth pos
       (define-values (before-pfs this+after-pfs) (split-at pfs n))
       (match-define (cons this-pf after-pfs/rev) (reverse this+after-pfs))
       (apply proof-fn (append before-pfs (cons this-pf (reverse after-pfs/rev)))))))
  (_nttz ctxt new-pt prev))

;; applies to innermost ntt-apply node
(define-syntax (for-each-subgoal stx)
  (syntax-parse stx
    [(_ t0 #:do t_ ...)
     #:with (t ...) (reverse (stx->list #'(t_ ...)))
     #`(λ (ptz0)
         (define ptz (t0 ptz0))
         (define nttz-app (find-ntt-apply ptz)) ; innermost app node from ptz
         (if nttz-app
             (let L ([ptz ptz]
                     [current-nttz-app nttz-app]
                     [n (length (ntt-apply-subterms (nttz-focus nttz-app)))]
                     [num-solved 0]) ; the current goal is this position in the list of n
               (if (zero? n)
                   ptz
                   (let* ([next-ptz ((compose t ...) ptz)]
                          ; TODO: what if t0 introduces another apply node?
                          [next-nttz-app (find-ntt-apply next-ptz)]
                          [same-subgoal? (and next-nttz-app
                                              (> (num-holes/nttz next-nttz-app) 1)
                                              (= (num-holes/nttz current-nttz-app)
                                                 (num-holes/nttz next-nttz-app)))])
                     (when (and same-subgoal?
                                (not (eq? (nttz-prev current-nttz-app)
                                          (nttz-prev next-nttz-app))))
                       (raise-ntac-goal-exception
                        "internal err: got the wrong ntt apply node?\n~a"
                        next-nttz-app))
                     (if same-subgoal? ; put current goal to end
                         (let ([new-nttz-app (to-end next-nttz-app num-solved)])
                           (L (next new-nttz-app) new-nttz-app (sub1 n) num-solved))
                         ;; already moved to next subgoal
                         (L next-ptz next-nttz-app (sub1 n) (add1 num-solved))))))
             ((compose t ...) ptz)))]))

(define-syntax (constructor stx)
  (syntax-parse stx
    [T:id
     #'(λ (ptz)
         (for/fold ([ptz ptz])
                   ([name (namespace-mapped-symbols)]
                    #:when (with-handlers ([exn? (lambda _ #f)])
                             (typeof (expand/df (datum->syntax #'T name)))))
           (define next-ptz
             (eval-proof-step ptz #`(try (by-apply #,(datum->syntax #'T name)))))
           #:final (not (eq? ptz next-ptz))
           next-ptz))]))

  (define-syntax (by-inversion syn)
    (syntax-parse syn
      [(_ H) #'(fill (inversion #'H))]
      [(_ H #:as name:id ...) #'(fill (inversion #'H #'[(name ...)]))]
      [(_ H #:as (names ...)) #'(fill (inversion #'H #'(names ...)))]))

  (define-syntax (elim-False syn)
    (syntax-parse syn
      [:id #'(fill (elim-False-fn))]))
  (define ((elim-False-fn) ctxt pt)
    (match-define (ntt-hole _ goal) pt)
    (make-ntt-apply
     goal
     (list (make-ntt-hole (normalize #'False ctxt)))
     (λ (body-pf) ; proof of false
       (quasisyntax/loc goal
         (new-elim #,body-pf (λ y #,(unexpand goal)))))))

  (define-syntax (by-discriminate syn)
    (syntax-case syn ()
      [(_ H) #'(fill (inversion #'H))]))
)

#lang cur/metantac

(provide (for-syntax (all-defined-out) by-inversion))

(require (for-syntax racket/exn
                     racket/port
                     racket/format)
         cur/stdlib/prop
         cur/stdlib/axiom
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
(begin-for-syntax
  (define (display-focus tz)
    (match (nttz-focus tz)
      [(ntt-hole _ goal)
       (when (current-tracing?)
         (let ([hole-count (num-holes/z tz)])
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

(begin-for-syntax ; interactive
  (define current-proof null)
  (define (reset-current-proof!)
    (set! current-proof null))
  (define (current-proof-add! stx)
    (set! current-proof (cons stx current-proof)))
(define-tactical interactive
  [:id
   (let L ([curr-ptz $ptz])
  (current-tracing? 1)
  (display-focus curr-ptz)
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
                       curr-ptz)])
      (eval-proof-step curr-ptz cmd-stx)))
  (if (nttz-done? next-ptz)
      (begin
        (printf "complete proof script:\n")
        (for-each
         (λ (stx) (printf "~a\n" (syntax->datum stx)))
         (reverse (stx->list current-proof)))
        (reset-current-proof!)
        (current-tracing? #f)
        next-ptz)
      (L next-ptz)))]))


(define-for-syntax ((fill t #:rest [psteps #'()]) ptz)
  (define new-foc (t (nttz-context ptz) (nttz-focus ptz)))
  ;; XXX Maybe new-foc could be #f for failure?
  (eval-proof-steps (next (struct-copy nttz ptz [focus new-foc])) psteps))


(define-syntax assign-type/m
  (syntax-parser
    [(_ e tag τ) (syntax-property #'e (stx->datum #'tag) ((current-type-eval) #'τ))]))

;; more tactics --------------------------------------------------
(begin-for-syntax

  (define-tactic (by-assert H ty)
    (define ty+ (normalize #'ty $ctxt))
    ($fill ((λ (H : ty) #,body-pf) #,arg-pf)
           #:where [⊢ arg-pf : ty+] [#'H : ty+ ⊢ body-pf : $goal]))

(define-tactical try
  [(_ t ...)
  (with-handlers ([exn:fail? #;exn:fail:ntac:goal? ; catch other fails too, eg unbound id
                             (lambda (e)
                               ;; (displayln "try failed:")
                               ;; (pretty-print e)
                               $ptz)])
    ((apply compose (reverse (list t ...))) $ptz))])

  (define-syntax with-ctx
    (syntax-parser
      [(_ [x ty] body)
       #'(make-ntt-context (λ (ctx) (ctx-add ctx x ty)) (make-ntt-hole body))]))

(define-tactic by-intro
  [(_ name) #:current-goal (~Π (x:id : P:expr) body:expr)
   ($fill (λ (name : #,(unexpand #'P)) #,hole1)
         #:where
         [#'name : #'P ⊢ hole1 : (cur-rename #'name #'x #'body)])]
  [b-i:id (by-intro #:id-ctx b-i)]
  [(_ #:id-ctx id-ctx)
   (ntac-match $goal
    [(~Π (x:id : P:expr) body:expr)
;     (by-intro #,(datum->syntax #'b-i (stx-e #'x)))
     (let ()
       (define name (datum->syntax #'id-ctx (stx-e #'x)))
       ($fill (λ (#,name : #,(unexpand #'P)) #,pf1)
             #:where
             [name : #'P ⊢ pf1 : (cur-rename name #'x #'body)]))])])

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
  (define-tactic (by-generalize x)
    (define-values (ctxt-to-change ctxt-unchanged)
      (ctx-partition/ty
       (ctx-remove $ctxt #'x)
       (λ (t) (has-term? #'x t))))
    ($fill (#,body-pf x . #,(ctx-ids ctxt-to-change))
           #:where
           [#:ctx ctxt-unchanged ⊢
            body-pf : (normalize
                       #`(Π [x : #,(ctx-lookup $ctxt #'x)]
                            #,@(ctx-tys->stx ctxt-to-change) ; TODO: need names?
                            #,$goal)
                       ctxt-unchanged)]))

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
      [b-is:id #'(fill (intros #:stx #'b-is))]
      [(_ syn:id #:as paramss)
       #`(compose (fill (destruct #'syn #'paramss)) (fill (intro #'syn)))]))

(define ((exact a) ctxt pt)
  (match-define (ntt-hole _ goal) pt)
  (unless (cur-type-check? a goal #:local-env (ctx->env ctxt))
    (raise-ntac-goal-exception "~a does not have type ~a"
                               (stx->datum (resugar-type a))
                               (stx->datum (resugar-type goal))))
  (make-ntt-exact goal a))

  (define-tactic (by-exact e)
    (unless (cur-type-check? #'e $goal #:local-env (ctx->env $ctxt))
      (raise-ntac-goal-exception "~a does not have type ~a"
                                 (stx->datum (resugar-type #'e))
                                 (stx->datum (resugar-type $goal))))
    ($fill #'e))

(define-tactic by-assumption
  [_
   (let ([res (for/or ([(k v) $ctxt] #:when (cur-equal? v $goal #:local-env (ctx->env $ctxt)))
                ($fill k))])
     (unless res
       (raise-ntac-goal-exception "could not find matching assumption for goal ~a" $goal))
     res)])
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

  (define (obvious ctxt pt)
    (match-define (ntt-hole _ goal) pt)
    (ntac-match goal
      [(~Π (a : P) body)
       ((intro #'a) ctxt pt)]
      [a
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
      (_ _ ([A _] ...) #;params ([i _] ...) #;indices _ Cinfo ...)
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
      (_ _ ([A _] ...) #;params ([i _] ...) _ #;indices Cinfo ...)
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
    ;; Consumes an instance of the destructed term and its new indices.
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
    (define subgoals
      (for/list ([maybe-xs+IH (if maybe-xss+IH
                                  (in-stx-list maybe-xss+IH)
                                  (stx-map (λ _ #'()) #'(Cinfo ...)))] ; names not given, gen tmp for now
                 [Cinfo (in-stx-list #'(Cinfo ...))])
        (syntax-parse Cinfo
          [[C ([x τ_] ... τout_) ((xrec . _) ...)]
           #:do[(define new-xs+IH ; make sure enough names supplied
                  (if (stx-length=? maybe-xs+IH #'(x ... xrec ...))
                      maybe-xs+IH ; TODO: still check for clashes?
                      (stx-append ; else generate based on extra-info names
                       ((freshens name)
                        (stx-map
                         (λ (id)
                           (if (or (ctx-has-id? ctxt-unchanged id)
                                   (syntax-parse goal
                                     [(~Π [y : _] ... body)
                                      (stx-ormap (λ (y) (stx-datum-equal? y id)) #'(y ...))]
                                     [_ #f])
                                   (stx-ormap ; see ceval-deterministic Imp example where this check is needed
                                    (λ (y)    ; ie, due folding substs; do all substs at once instead?
                                      (and (id? y) (stx-datum-equal? y id)))
                                    stxs-to-change))
                               (generate-temporary id)
                               id))
                         #'(x ...)))
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
                ;(define (update-ctxt old-ctxt)
                  (define tmp-ctxt
                    (ctx-adds ctxt-unchanged
                              new-xs+IH
                              #'(τ ... . IHτs) #:do normalize))
                  (define new-ctxt
                    (ctx-append tmp-ctxt
                              (ctx-map
                               (compose (normalize/ctxt tmp-ctxt) update-ty)
                               ctxt-to-change)))
                (define new-goal (normalize (update-ty goal) new-ctxt))] ; new specialized subgoal
           ($stx/holes
            goal
            (λ #,@new-xs+IH
              (λ #,@(ctx->stx ctxt-to-change #:do (compose unexpand update-ty))
                #,pf))
            #:where [#:ctx new-ctxt ⊢ pf : new-goal])
#;           (values
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
          [(ntt-apply _ _ (list (ntt-context _ _ update (ntt-hole _ subgoal))) _)
           (unless (typecheck? subgoal (normalize exp-subg (update ctxt)))
             (raise-ntac-goal-exception
              "induction: encountered subgoal ~a that does not match expected: ~a"
              (stx->datum (resugar-type subgoal))
              (stx->datum exp-subg)))])))
    
#;    (make-ntt-apply
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
          #,@(ctx-ids ctxt-to-change)))))
    ($stx/compose
     goal
     ((new-elim
       #,name
       #,(with-syntax ([is (generate-temporaries #'(ival ...))])
           (define update-Prop-ty
             (compose unexpand (subst-terms/es #'is #'(ival ...))))
           #`(λ #,@#'is #,name
                (Π #,@(ctx->stx ctxt-to-change #:do update-Prop-ty)
                   #,(update-Prop-ty goal))))
       .
       #,$pfs)
;       #,(map (λ (pf->meth pf) (pf->meth pf)) mk-elim-methods $pfs))
      #,@(ctx-ids ctxt-to-change))
     #:with subgoals))

  (define-tactic by-split
    [_ #:current-goal (~And X Y)
       ($fill (conj #,(unexpand #'X)
                    #,(unexpand #'Y)
                    #,proj1
                    #,proj2)
              #:where [⊢ proj1 : #'X] [⊢ proj2 : #'Y])])

  (define-tactic by-left
    [_ #:current-goal (~Or X Y)
       ($fill (left #,(unexpand #'X) #,(unexpand #'Y) #,pf)
              #:where [⊢ pf : #'X])])
  (define-tactic by-right
    [_ #:current-goal (~Or X Y)
       ($fill (right #,(unexpand #'X) #,(unexpand #'Y) #,pf)
              #:where [⊢ pf : #'Y])])

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
(define (find-parent ptz num-goals)
  (cond
    [(nttz-done? ptz) #f]
    [(>= (num-holes/z/local ptz) num-goals) ptz]
    [else (find-parent (nttz-up ptz) num-goals)]))

;; to-end : nttz-apply-focus nat -> nttz
;; **Focus of ptz must be ntt-apply node.**
;; Moves nth node to the end of the node list,
;; where n is the position of the first hole node.
;; Returns new nttz with the new apply node as the focus
(define (to-end ptz [n (index-where ; n is the current/first (hole) node
                        (ntt-apply-subterms (nttz-focus ptz))
                        ntt-contains-hole?)])
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

;; takes a sequence of tactics
;; 1) runs the first one
;; 2) then for each subgoal produced, runs the subsequent tactics
;; equivalent to coq ";" tactical
(define-syntax (seq stx)
  (syntax-parse stx
    [(_) #'nop]
    [(_ t) #'t]
    [(_ t0 t ...)
     #`(λ (ptz0)
         (define num-goals0 (num-holes/z ptz0))
         (define ptz (t0 ptz0))
         (define num-goals (num-holes/z ptz))
         (define num-new-goals (add1 (- num-goals num-goals0)))
         (cond
           [(< num-goals num-goals0) ptz]
           [(= num-goals0 num-goals) ((seq t ...) ptz)]
           [else
            (let L ([n num-new-goals] [ptz ptz])
              (if (zero? n)
                  ptz
                  (let* ([next-ptz ((seq t ...) ptz)])
                    (cond
                      [(>= (num-holes/z next-ptz) num-new-goals) ; didnt complete any goals
                       (L (sub1 n)
                          (next (to-end (find-parent next-ptz num-new-goals))))]
                      [else next-ptz]))))]))]))

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
                                              (> (num-holes/z/local next-nttz-app) 1)
                                              (= (num-holes/z/local current-nttz-app)
                                                 (num-holes/z/local next-nttz-app)))])
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

  (define-tactic elim-False
    [:id ($fill (new-elim #,body-pf (λ y #,(unexpand $goal)))
                #:where [⊢ body-pf : (normalize #'False $ctxt)])])

  (define-syntax (by-discriminate syn)
    (syntax-case syn ()
      [(_ H) #'(by-inversion H)]));#'(fill (inversion #'H))]))

  (define-syntax admit
    (syntax-parser
      [(ad name) ; fill one hole
       #`(λ (ptz)
           (let ([goal (ntt-goal (nttz-focus ptz))])
             (next
              (struct-copy
               nttz ptz
               [focus
                (make-ntt-exact
                 goal
                 #`(assign-type/m (#%plain-app im-an-axiom 'name)
                                  : #,(unexpand goal)))]))))]
      [_ ; fill all holes
       #'(λ (ptz)
           (let L ([ptz ptz]) ; fill all holes
             (if (nttz-done? ptz)
                 ptz
                 (L ((admit #,(gensym 'admitted-thm)) ptz)))))]))
)

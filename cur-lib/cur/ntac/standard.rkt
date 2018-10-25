#lang s-exp "../main.rkt"
(require
 (for-syntax "utils.rkt"
             "../curnel/racket-impl/stxutils.rkt"
             (only-in macrotypes/stx-utils stx-appendmap)
             racket/match
             racket/dict
             racket/list
             (for-syntax racket/base))
 "../stdlib/sugar.rkt"
 "../curnel/turnstile-impl/reflection.rkt" ; simpl needs cur-normalize
 "../curnel/racket-impl/runtime.rkt" ; destruct needs constant-info
 "base.rkt")

(begin-for-syntax
  (require racket/exn)
  (provide
   (all-defined-out)))

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
(define-for-syntax (display-focus tz)
  (match (nttz-focus tz)
    [(ntt-hole _ goal)
     (for ([(k v) (in-dict (nttz-context tz))])
       (printf "~a : ~a\n" (syntax->datum k) (syntax->datum (cur-pretty-print v))))
     (printf "--------------------------------\n")
     (printf "~a\n\n" (syntax->datum (cur-pretty-print goal)))]
    [(ntt-done _ _ _)
     (printf "Proof complete.\n")]
    [_
     ;; XXX
     (printf "Not at hole.\n")])
  tz)

(define-for-syntax (interactive ptz)
  (display-focus ptz)
  (define cmd-stx
    (let/ec esc
      (parameterize ([current-eval
                      (λ (in)
                        (syntax-case in ()
                          [(_ . cmd)
                           (esc #'cmd)]))])
        (read-eval-print-loop))))
  (define next-ptz
    (with-handlers ([exn:fail:ntac:goal?
                     (lambda (e)
                       (displayln (exn->string e))
                       ptz)])
      (eval-proof-step ptz cmd-stx)))
  (if (nttz-done? next-ptz)
      next-ptz
      (interactive next-ptz)))

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
(require (for-syntax racket/trace))
(define-for-syntax (ctxt->env ctxt)
  (reverse (for/list ([(k v) (in-dict ctxt)])
             (cons k v))))

(begin-for-syntax

  (define ((assert H ty_) ctxt pt)
    (match-define (ntt-hole _ goal) pt)

    ;; ty_ has the wrong scopes (bc of eval I think)
    ;; workaround by transferring scopes from goal (except for bindings in ctx)
    (define ty (transfer-scopes goal ty_ ctxt))
    (make-ntt-apply
     goal
     (list
      (make-ntt-hole ty)
      (make-ntt-context
       (λ (old-ctxt)
         (dict-set old-ctxt H ty))
       (make-ntt-hole goal)))
     (lambda (arg-pf body-pf)
       (quasisyntax/loc goal
         ((λ (#,H : #,ty)
            #,body-pf)
          #,arg-pf)))))

  (define-syntax (by-assert syn)
    (syntax-case syn ()
      [(_ H ty)
       #`(fill (assert #'H #'ty))])))

(define-for-syntax ((intro [name #f]) ctxt pt)
  ;; TODO: ntt-match(-define) to hide this extra argument. Maybe also add ntt- to constructors in pattern?
  (match-define (ntt-hole _ goal) pt)
  (ntac-match goal
   [(~Π/1 (x:id : P:expr) body:expr)
    (let ()
      (define the-name (or name #'x))
      (make-ntt-apply
       goal
       (list
        (make-ntt-context
         (lambda (old-ctxt)
           (dict-set old-ctxt the-name #'P))
         (make-ntt-hole (cur-rename the-name #'x #'body))))
       (lambda (body-pf)
         (quasisyntax/loc goal (λ (#,the-name : P) #,body-pf)))))]))

;; A pattern emerges:
;; tacticals must take additional arguments as ntac-syntax
;; define-tactical should generate a phase 2 definition like the one below, and a functional version
;; of the tactical (perhaps by-tactical-name)
(begin-for-syntax
  (define-syntax (by-intro syn)
    (syntax-case syn ()
      [(_ syn #:as paramss)
       #`(compose (fill (destruct #'syn #'paramss)) (fill (intro #'syn)))]
      [(_ syn)
       #`(fill (intro #'syn))]
      [_
       #`(fill (intro))])))

(define-for-syntax (intros names)
  (for/fold ([t nop])
            ([n (in-list names)])
    (compose (fill (intro n)) t)))
(begin-for-syntax
  (define-syntax (by-intros syn)
    (syntax-case syn ()
      [(_ id ...)
       #`(intros (list #'id ...))])))

;; define-tactical
(define-for-syntax ((exact a) ctxt pt)
  (match-define (ntt-hole _ goal) pt)
  (unless (cur-type-check? a goal #:local-env (ctxt->env ctxt))
    (raise-ntac-goal-exception "~v does not have type ~v" a goal))
  (make-ntt-exact goal a))

(begin-for-syntax
  (define-syntax (by-exact syn)
    (syntax-case syn ()
      [(_ syn)
       #`(fill (exact #'syn))])))

;;define-tactical
(define-for-syntax (assumption ctxt pt)
  (match-define (ntt-hole _ goal) pt)
  ;; TODO: Actually, need to collect (k v) as we search for a matching assumption, otherwise we might
  ;; break dependency. Hopefully we have some invariants that prevent that from actually happening.
  (define ntt
    (for/or ([(k v) (in-dict ctxt)]
           #:when (cur-equal? v goal #:local-env (ctxt->env ctxt)))
      (make-ntt-exact goal k)))
  (unless ntt
    (raise-ntac-goal-exception "could not find matching assumption for goal ~a" goal))
  ntt)

(begin-for-syntax
  (define-syntax (by-assumption syn)
    (syntax-case syn ()
      [_
       #`(fill assumption)]))

  (define (obvious ctxt pt)
    (match-define (ntt-hole _ goal) pt)
    (ntac-match goal
      [(~Π/1 (a : P) body)
       ((intro) ctxt pt)]
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
                  [focus (make-ntt-hole
                          (cur-normalize goal
                                         #:local-env (ctxt->env (nttz-context ptz))))])))

  (define-syntax (by-destruct syn)
    (syntax-case syn ()
      [(_ x)
       #`(fill (destruct #'x))]
      [(_ x #:as param-namess)
       #`(fill (destruct #'x #'param-namess))]))

  (define (pi->anns ty)
    (syntax-parse ty
      [t:cur-runtime-pi
       (cons #'t.ann (pi->anns #'t.result))]
      [_ null]))

  (define ((destruct name [param-namess #f]) ctxt pt)
    (define name-ty (dict-ref ctxt name))
    (define c-info (syntax-local-eval name-ty))

    (define Cs
      (constant-info-constructor-ls c-info))
    (define C-types
      (map
       identifier-info-type
       (map syntax-local-eval Cs)))
    (define paramss
      (if param-namess
          (syntax->list param-namess)
          (map (λ _ #'()) Cs))
      ;; TODO: verify param-namess against result of constant-info-index-name-ls
      #;(map constant-info-index-name-ls (map syntax-local-eval Cs)))
    (define pats
      (map
       (λ (C ps)
         (if (null? (syntax->list ps))
             C
             #`(#,C . #,ps)))
       Cs paramss))

    (match-define (ntt-hole _ goal) pt)

    (make-ntt-apply
     goal
     (map
      (λ (pat C-type params)
        (make-ntt-context
         (λ (old-ctxt)
           (foldr
            dict-set/flip
            old-ctxt
            (syntax->list params)
            (pi->anns C-type)))
         (make-ntt-hole
          (subst pat name goal))))
      pats
      C-types
      paramss)
     (λ pfs
       (quasisyntax/loc goal
         (match #,name #:in #,name-ty #:return #,goal
                . #,(map
                     (λ (pat pf) #`[#,pat #,pf])
                     pats
                     pfs))))))

  ;; same as by-destruct except uses `new-elim` instead of `match`
  (define-syntax (by-destruct/elim syn)
    (syntax-case syn ()
      [(_ x)
       #`(fill (destruct/elim #'x))]
      [(_ x #:as param-namess)
       #`(fill (destruct/elim #'x #'param-namess))]))

  ;; TODO: combine this with induction (below)
  (define ((destruct/elim name [param-namess #f]) ctxt pt)
    (define name-ty (dict-ref ctxt name))
    (define c-info (syntax-local-eval name-ty))

    (define Cs
      (constant-info-constructor-ls c-info))
    (define C-infos (map syntax-local-eval Cs))
    (define C-types (map identifier-info-type C-infos))

    (define paramss
      (if param-namess
          (syntax->list param-namess)
          (map (λ _ #'()) Cs))
      ;; TODO: verify param-namess against result of constant-info-index-name-ls
      #;(map constant-info-index-name-ls (map syntax-local-eval Cs)))
    (define pats
      (map
       (λ (C ps)
         (if (null? (syntax->list ps))
             C
             #`(#,C . #,ps)))
       Cs paramss))

    (match-define (ntt-hole _ goal) pt)

    (make-ntt-apply
     goal
     (map
      (λ (pat C-type params)
        (make-ntt-context
         (lambda (old-ctxt)
           ; drop `name` from ctxt
           (dict-remove
            (foldr
             dict-set/flip
             old-ctxt
             (syntax->list params)
             (pi->anns C-type))
            name))
         (make-ntt-hole
          (subst pat name goal))))
      pats
      C-types
      paramss)
     (λ pfs
       (quasisyntax/loc goal
         (new-elim #,name
                   (λ [#,name : #,name-ty] #,goal)
                   .
                   #,(map
                      ;; TODO: add IHs?
                      (λ (params C-type pf)
                        (if (null? (syntax->list params))
                            pf
                            #`(λ #,@(map
                                     (λ (p ty) #`[#,p : #,ty])
                                     (syntax->list params)
                                     (pi->anns C-type))
                                #,pf)))
                      paramss
                      C-types
                      pfs))))))

  ;; copied from by-destruct/elim
  (define-syntax (by-induction syn)
    (syntax-case syn ()
      [(_ x #:as param-namess)
       #`(fill (induction #'x #'param-namess))]))

  ;; initially copied from destruct/elim
  (define ((induction name param-namess) ctxt pt)

    (match-define (ntt-hole _ goal) pt)

    (define name-ty (dict-ref ctxt name))
    (define c-info (syntax-local-eval name-ty))

    ;; Cs = the (data constructors) for name-ty
    (define Cs (constant-info-constructor-ls c-info))
    (define C-infos (map syntax-local-eval Cs))
    (define C-types (map identifier-info-type C-infos))

    ;; for each C, param-names consists of:
    ;; - args (index-name-ls)
    ;; - IHs (recursive-index-ls)
    (define C-IH-indexess (map constant-info-recursive-index-ls C-infos))
    (define C-arities (map (compose length constant-info-index-name-ls) C-infos))

    ;; TODO: verify param-namess against result of
    ;; - constant-info-index-name-ls
    ;; - constant-info-recursive-index-ls
    (define paramss (syntax->list param-namess))

    ;; for each param, type is either
    ;; - argument types from C-type (if arg)
    ;; - subst arg-name for name in goal (if IH)
    ;;   - where arg-name specified by recursive-index-ls
    (define param-typess
      (map
       (λ (C-type C-IH-indexes params)
         (define tys (pi->anns C-type))
         (append
          tys
          (map
           (λ (i)
             (let ([n* (list-ref (syntax->list params) i)])
               (subst n* name goal)))
           C-IH-indexes)))
       C-types
       C-IH-indexess
       paramss))

    ;; combines C with its args,
    ;; -ie drop the IHs from paramss
    (define pats
      (map
       (λ (C ps arity)
         (let ([args (take (syntax->list ps) arity)])
           (if (null? args)
               C
               #`(#,C . #,args))))
       Cs paramss C-arities))

    (make-ntt-apply
     goal
     (map
      (λ (pat params param-types)
        (make-ntt-context
         (lambda (old-ctxt)
           ; drop `name` from ctxt
           ; but add bindings for:
           ; - constructor arguments of `name`
           ; - IHs for args with type name-ty
           (dict-remove
            (foldl
             dict-set/flip
             old-ctxt
             (syntax->list params)
             param-types)
            name))
         (make-ntt-hole
          (subst pat name goal))))
      pats
      paramss
      param-typess)
     (λ pfs
       (quasisyntax/loc goal
         (new-elim
          #,name
          (λ [#,name : #,name-ty] #,goal)
          .
          #,(map
             (λ (params param-types pf)
               (if (null? (syntax->list params))
                   pf
                   (foldr
                    (λ (p ty e) #`(λ [#,p : #,ty] #,e))
                    pf
                    (syntax->list params)
                    param-types)))
             paramss
             param-typess
             pfs)))))))

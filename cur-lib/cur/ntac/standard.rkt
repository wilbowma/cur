#lang s-exp "../main.rkt"
(require
  (for-syntax "dict-utils.rkt"
              "../curnel/racket-impl/stxutils.rkt")
 "../stdlib/sugar.rkt"
 "../curnel/racket-impl/reflection.rkt" ; simpl needs cur-normalize
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
       (printf "~a : ~a\n" (syntax->datum k) (syntax->datum v)))
     (printf "--------------------------------\n")
     (printf "~a\n\n" (syntax->datum goal))]
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
  
  (define ((assert H ty_ a) ctxt pt)
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
      [(a H ty)
       #`(fill (assert #'H #'ty #'a))])))

(define-for-syntax ((intro [name #f]) ctxt pt)
  ;; TODO: ntt-match(-define) to hide this extra argument. Maybe also add ntt- to constructors in pattern?
  (match-define (ntt-hole _ goal) pt)
  (ntac-match goal
   [(forall (x:id : P:expr) body:expr)
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
      [(forall (a : P) body)
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

  ;; (struct identifier-info (type delta-def))
  ;; ;; TODO PERF: Could use vectors instead of lists; since we store the count anyway... or maybe we won't
  ;; ;; need to by storing param and index decls separately.
  ;; (struct constant-info identifier-info
  ;;   (param-count param-name-ls param-ann-ls index-name-ls index-ann-ls
  ;;                constructor-count constructor-ls constructor-index
  ;;                recursive-index-ls))

  (define (display-info c-info name [break? #f])
    (printf "constant info, for ~a -------------\n" (syntax->datum name))
    (printf "type: ~a\n" (syntax->datum (identifier-info-type c-info)))
    (printf "delta-def: ~a\n" (identifier-info-delta-def c-info))
    (printf "param-count: ~a\n" (constant-info-param-count c-info))
    (printf "param-name-ls: ~a\n" (constant-info-param-name-ls c-info))
    (printf "param-ann-ls: ~a\n" (constant-info-param-ann-ls c-info))
    (printf "index-name-ls: ~a\n" (constant-info-index-name-ls c-info))
    (printf "index-ann-ls: ~a\n" (constant-info-index-ann-ls c-info))
    (printf "constructor-count: ~a\n" (constant-info-constructor-count c-info))

    (define const-ls (constant-info-constructor-ls c-info))
    (printf "constructor-ls: ~a\n" const-ls)
    (unless break?
      (define const-c-infos (map syntax-local-eval const-ls))
      (for-each (λ (i c) (display-info i c #t)) const-c-infos const-ls))
    #;(displayln (map constant-info-index-name-ls const-c-infos))
    #;(pretty-print (map (compose syntax->datum identifier-info-type) (map syntax-local-eval const-ls)))

    (printf "constructor-index: ~a\n" (constant-info-constructor-index c-info))
    (printf "recursive-index-ls: ~a\n" (constant-info-recursive-index-ls c-info)))

  (define (pi->anns ty)
    (syntax-parse ty
      [t:cur-runtime-pi
       (cons #'t.ann (pi->anns #'t.result))]
      [_ null]))

  (define ((destruct name [param-namess #f]) ctxt pt)
    (define name-ty (dict-ref ctxt name))
    (define c-info (syntax-local-eval name-ty))

    ;; ;; (displayln (identifier-info-type c-info))
    ;; ;; (displayln (identifier-info-delta-def c-info))
    ;; ;; (displayln (constant-info-param-count c-info))
    ;; ;; (displayln (constant-info-param-name-ls c-info))
    ;; ;; (displayln (constant-info-param-ann-ls c-info))
    ;; ;; (displayln (constant-info-index-name-ls c-info))
    ;; ;; (displayln (constant-info-index-ann-ls c-info))
    ;; ;; (displayln (constant-info-constructor-count c-info))

    ;; (displayln (constant-info-constructor-ls c-info))
    ;; ;; TODO: verify param-names against result of constant-info-index-name-ls
    ;; (displayln (map constant-info-index-name-ls (map syntax-local-eval (constant-info-constructor-ls c-info))))
    ;; (pretty-print (map (compose syntax->datum identifier-info-type) (map syntax-local-eval (constant-info-constructor-ls c-info))))

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
       (let* ([res
               (quasisyntax/loc goal 
                 (match #,name #:in #,name-ty #:return #,goal
                  . #,(map 
                       (λ (pat pf) #`[#,pat #,pf])
                       pats
                       pfs)))]
              #;[_ (pretty-print (syntax->datum res))])
         res))))

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
       (let* ([res
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
                              pfs)))]
              #;[_ (begin (displayln "destruct/elim") (pretty-print (syntax->datum res)))])
         res))))

  ;; copied from by-destruct/elim
  (define-syntax (by-induction syn)
    (syntax-case syn ()
      #;[(_ x) #`(fill (destruct/elim #'x))]
      [(_ x #:as param-namess)
       #`(fill (induction #'x #'param-namess))]))
  

  ;; initially copied from destruct/elim
  (define ((induction name param-namess) ctxt pt)

    (match-define (ntt-hole _ goal) pt)

    (define name-ty (dict-ref ctxt name))
    (define c-info (syntax-local-eval name-ty))
    
    ;;(display-info c-info name-ty)

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
       (define res
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
               pfs))))
       #;(begin (displayln "induction") (pretty-print (syntax->datum res)))
       res)))
)

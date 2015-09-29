#lang racket/base
;; This module just provide module language sugar over the redex model.

(require
  "redex-core.rkt"
  redex/reduction-semantics
  racket/provide-syntax
  (for-syntax
    (except-in racket import)
    syntax/parse
    racket/syntax
    (except-in racket/provide-transform export)
    racket/require-transform
    (except-in "redex-core.rkt" remove)
    redex/reduction-semantics))
(provide
  ;; Basic syntax
  for-syntax
  only-in
  except-in
  all-defined-out
  rename-in
  rename-out
  prefix-out
  prefix-in
  submod
  #%module-begin
  (rename-out
    [dep-module+ module+]
    [dep-provide provide]
    [dep-require require]

    [dep-lambda lambda]
    [dep-lambda λ]
    [dep-app #%app]

    [dep-forall forall]
    [dep-forall ∀]

    [dep-inductive data]

    [dep-elim elim]

    [dep-top #%top]
    [dep-top-interaction #%top-interaction]

    ;      [dep-datum #%datum]
    [dep-define define]
    [dep-void void])
  begin
  Type
  ;; DYI syntax extension
  define-syntax
  begin-for-syntax
  define-for-syntax
  (for-syntax (all-from-out syntax/parse))
  syntax-case
  syntax-rules
  define-syntax-rule
  (for-syntax (all-from-out racket))
  ;; reflection
  (for-syntax
    cur->datum
    cur-expand
    type-infer/syn
    type-check/syn?
    normalize/syn
    step/syn
    cur-equal?))

(begin-for-syntax
  ;; TODO: Gamma and Sigma seem to get reset inside a module+
  (define gamma
    (make-parameter
      (term ∅)
      (lambda (x)
        (unless (Γ? x)
          (error 'core-error "We built a bad gamma ~s" x))
        x)))

  (define sigma
    (make-parameter
      (term ∅)
      (lambda (x)
        (unless (Σ? x)
          (error 'core-error "We built a bad sigma ~s" x))
        x)))

  (define (extend-Γ/term env x t)
    (term (,(env) ,x : ,t)))

  (define (extend-Γ/term! env x t) (env (extend-Γ/term env x t)))

  (define (extend-Γ/syn env x t)
    (extend-Γ/term env (syntax->datum x) (cur->datum t)))

  (define (extend-Γ/syn! env x t) (env (extend-Γ/syn env x t)))

  (define (extend-Σ/term env x t c*)
    (term (,(env) (,x : ,t (,@c*)))))

  (define (extend-Σ/term! env x t c*)
    (env (extend-Σ/term env x t c*)))

  (define (extend-Σ/syn env x t c*)
    (extend-Σ/term env (syntax->datum x) (cur->datum t)
                   (for/list ([c (syntax->list c*)])
                     (syntax-case c ()
                       [(c : ct)
                        (parameterize ([gamma (extend-Γ/syn gamma x t)])
                          (term (,(syntax->datum #'c) : ,(cur->datum #'ct))))]))))

  (define (extend-Σ/syn! env x t c*)
    (env (extend-Σ/syn env x t c*)))

  (define bind-subst (make-parameter (list null null)))

  (define (add-binding/term! x t)
    (let ([vars (first (bind-subst))]
          [exprs (second (bind-subst))])
      (bind-subst (list (cons x vars) (cons t exprs)))))

  ;; TODO: Still absurdly slow. Probably doing n^2 checks of sigma and
  ;; gamma. And lookup on sigma, gamma are linear, so probably n^2 lookup time.
  (define (type-infer/term t)
    (let ([t (judgment-holds (type-infer ,(sigma) ,(gamma) ,t t_0) t_0)])
      (and (pair? t) (car t))))

  (define (type-check/term? e t)
    (and (judgment-holds (type-check ,(sigma) ,(gamma) ,e ,t)) #t))

  ;; TODO: Blanket disarming is probably a bad idea.
  (define orig-insp (variable-reference->module-declaration-inspector (#%variable-reference)))
  (define (disarm syn) (syntax-disarm syn orig-insp))

  ;; Locally expand everything down to core forms.
  (define (core-expand syn)
    (disarm
      (local-expand
        syn
        'expression
        (append (syntax-e #'(term reduce subst-all dep-top #%app λ Π elim Unv #%datum void))))))

  ;; Only type-check at the top-level, to prevent exponential
  ;; type-checking. Redex is expensive enough.
  ;; TODO: This results in less good error messages. Add an
  ;; algorithm to find the smallest ill-typed term.
  (define inner-expand? (make-parameter #f))

  ;; Reifiy cur syntax into curnel datum
  (define (cur->datum syn)
    ;; Main loop; avoid type
    (define reified-term
      (parameterize ([inner-expand? #t])
        (let cur->datum ([syn syn])
          (syntax-parse (core-expand syn)
            #:literals (term reduce #%app subst-all)
            #:datum-literals (elim Π λ : Unv)
            [x:id (syntax->datum #'x)]
            [(subst-all e _ _) (syntax->datum #'e)]
            [(reduce Σ e) (cur->datum #'e)]
            [(term e) (cur->datum #'e)]
            [(Unv i) (term (Unv ,(syntax->datum #'i)))]
            ;; TODO: should really check that b is one of the binders
            ;; Maybe make a syntax class for the binders, core forms,
            ;; etc.
            [(b:id (x:id : t) e)
             (let* ([x (syntax->datum #'x)]
                    [t (cur->datum #'t)]
                    [e (parameterize ([gamma (extend-Γ/term gamma x t)])
                         (cur->datum #'e))])
               (term (,(syntax->datum #'b) (,x : ,t) ,e)))]
            [(elim t1 t2)
             (let* ([t1 (cur->datum #'t1)]
                    [t2 (cur->datum #'t2)])
               (term ((elim ,t1) ,t2)))]
            [(#%app e1 e2)
             (term (,(cur->datum #'e1) ,(cur->datum #'e2)))]))))
    (unless (and inner-expand? (type-infer/term reified-term))
      ;; TODO: is this really a syntax error?
      (raise-syntax-error 'cur "term is ill-typed:"
                          (begin (printf "Sigma: ~s~nGamma: ~s~n" (sigma) (gamma))
                                 reified-term)
                          syn))
    reified-term)

  (define (datum->cur syn t)
    (match t
      [(list (quote term) e)
       (quasisyntax/loc
         syn
         (datum->cur syn e))]
      [(list (quote Unv) i)
       (quasisyntax/loc
         syn
         (Type #,i))]
      [(list (quote Π) (list x (quote :) t) body)
       (quasisyntax/loc
         syn
         (dep-forall (#,(datum->syntax syn x) : #,(datum->cur syn t)) #,(datum->cur syn body)))]
      [(list (quote λ) (list x (quote :) t) body)
       (quasisyntax/loc
         syn
         (dep-lambda (#,(datum->syntax syn x) : #,(datum->cur syn t)) #,(datum->cur syn body)))]
      [(list (list (quote elim) t1) t2)
       (quasisyntax/loc
         syn
         (dep-elim #,(datum->cur syn t1) #,(datum->cur syn t2)))]
      [(list e1 e2)
       (quasisyntax/loc
         syn
         (dep-app #,(datum->cur syn e1) #,(datum->cur syn e2)))]
      [_
       (quasisyntax/loc
         syn
         #,(datum->syntax syn t))]))

  (define (eval-cur syn)
    (term (reduce ,(sigma) (subst-all ,(cur->datum syn) ,(first (bind-subst)) ,(second (bind-subst))))))

  (define (syntax->curnel-syntax syn)
    (quasisyntax/loc
      syn
      (term (reduce #,(sigma) (subst-all #,(cur->datum syn) #,(first (bind-subst)) #,(second (bind-subst)))))))

  ;; Reflection tools

  (define (normalize/syn syn)
    (datum->cur
      syn
      (eval-cur syn)))

  (define (step/syn syn)
    (datum->cur
      syn
      (term (step ,(sigma) (subst-all ,(cur->datum syn) ,(first (bind-subst)) ,(second (bind-subst)))))))

  ;; Are these two terms equivalent in type-systems internal equational reasoning?
  (define (cur-equal? e1 e2)
    (and (judgment-holds (equivalent ,(sigma) ,(eval-cur e1) ,(eval-cur e2)) #t)))

  (define (type-infer/syn syn)
    (let ([t (type-infer/term (eval-cur syn))])
      (and t (datum->cur syn t))))

  (define (type-check/syn? syn type)
    (type-check/term? (eval-cur syn) (eval-cur type)))

  ;; Takes a Cur term syn and an arbitrary number of identifiers ls. The cur term is
  ;; expanded until expansion reaches a Curnel form, or one of the
  ;; identifiers in ls.
  (define (cur-expand syn . ls)
    (disarm
      (local-expand
        syn
        'expression
        (append (syntax-e #'(Type dep-inductive dep-lambda dep-app dep-elim dep-forall dep-top))
                ls)))))

;; -----------------------------------------------------------------
;; Require/provide macros

#| TODO NB XXX
 | This is code some of the most hacky awful code I've ever written. But it works. ish
 |#
(begin-for-syntax
  (define envs (list #'(void)))

  (define (cur-identifier-bound? id)
    (let ([x (syntax->datum id)])
      (and (x? x)
        (or (term (lookup-Γ ,(gamma) ,x))
          (term (lookup-Σ ,(sigma) ,x))))))

  (define (filter-cur-exports syn modes)
    (partition (compose cur-identifier-bound? export-local-id)
               (apply append (map (lambda (e) (expand-export e modes))
                                  (syntax->list syn))))))
(define-syntax extend-env-and-provide
  (make-provide-transformer
    (lambda (syn modes)
      (syntax-case syn ()
        [(_ e ...)
         (let-values ([(cur ~cur) (filter-cur-exports #'(e ...) modes)])
           #| TODO: Ignoring the built envs for now
           (set! envs (for/list ([e cur])
           (let* ([x (syntax->datum (export-local-id e))]
                  [t (type-infer/term x)]
                  [env (if (term (lookup ,(gamma) ,x)) #'gamma #'sigma)])
             #`(extend-env/term! #,env #,(export-out-sym e) #,t))))
           |#
        ~cur)]))))

(define-syntax (export-envs syn)
  (syntax-case syn ()
    [(_ gamma-out sigma-out bind-out)
     (begin
       #`(begin-for-syntax
          (define gamma-out (term #,(gamma)))
          (define sigma-out (term #,(sigma)))
          (define bind-out '#,(bind-subst))))]))

;; TODO: This can only handle a single provide form, otherwise generates multiple *-out
(define-syntax (dep-provide syn)
  (syntax-case syn ()
    [(_ e ...)
     (begin
       #| TODO NB:
        | Ignoring the built envs above, for now.  The local-lift export seems to get executed before
        | the filtered environment is built.
        |#
       ;; TODO: rename out will need to rename variables in gamma and ; sigma.
       (syntax-local-lift-module-end-declaration
         #`(export-envs gamma-out sigma-out bind-out))
       #`(provide (extend-env-and-provide e ...)
                  (for-syntax gamma-out sigma-out bind-out)))]))
(begin-for-syntax
  (define out-gammas #`())
  (define out-sigmas #`())
  (define out-binds #`())
  (define gn 0)
  (define sn 0)
  (define bn 0)
  (define (filter-cur-imports syn)
    (for/fold ([imports '()]
               [sources '()])
              ([req-spec (syntax->list syn)])
      (let-values ([(more-imports more-sources) (expand-import req-spec)])
        (values (for/fold ([imports imports])
                          ([imp more-imports])
                  (cond
                    [(equal? (import-src-sym imp) 'gamma-out)
                     (let ([new-id (format-id (import-orig-stx imp)
                                              "gamma-out~a" gn)])
                       ;; TODO: Fewer set!s
                       ;; TODO: Do not DIY gensym
                       (set! gn (add1 gn))
                       (set! out-gammas
                             #`(#,@out-gammas (gamma (term (append-Γ
                                                             ,(gamma)
                                                             ,#,new-id)))))
                       (cons (struct-copy import imp [local-id new-id])
                             imports))]
                    ;; TODO: Many shared code between these two clauses
                    [(equal? (import-src-sym imp) 'sigma-out)
                     (let ([new-id (format-id (import-orig-stx imp)
                                              "sigma-out~a" sn)])
                       ;; TODO: Fewer set!s
                       ;; TODO: Do not DIY gensym
                       (set! sn (add1 sn))
                       (set! out-sigmas
                             #`(#,@out-sigmas (sigma (term (append-Σ
                                                             ,(sigma)
                                                             ,#,new-id)))))
                       (cons (struct-copy import imp [local-id new-id])
                             imports))]
                    ;; TODO: Many shared code between these two clauses
                    [(equal? (import-src-sym imp) 'bind-out)
                     (let ([new-id (format-id (import-orig-stx imp)
                                              "bind-out~a" bn)])
                       ;; TODO: Fewer set!s
                       ;; TODO: Do not DIY gensym
                       (set! bn (add1 bn))
                       (set! out-binds
                             #`(#,@out-binds (bind-subst (list (append
                                                                 (first #,new-id)
                                                                 (first (bind-subst)))
                                                               (append
                                                                 (second #,new-id)
                                                                 (second (bind-subst)))))))
                       (cons (struct-copy import imp [local-id new-id])
                             imports))]
                    [else (cons imp imports)]))
                (append sources more-sources))))))

(define-syntax extend-env-and-require
  (make-require-transformer
    (lambda (syn)
      (syntax-case syn ()
        [(_ e ...) (filter-cur-imports #'(e ...))]))))

;; TODO: rename in will need to rename variables in gamma and
;; sigma.
(define-syntax (import-envs syn)
  (syntax-case syn ()
    [(_) #`(begin-for-syntax #,@out-gammas #,@out-sigmas
                             #,@out-binds)]))

(define-syntax (dep-require syn)
  (syntax-case syn ()
    [(_ e ...)
     #`(begin
         (require (extend-env-and-require e ...))
         (import-envs))]))

(define-syntax (dep-module+ syn)
  (syntax-case syn ()
    [(_ name body ...)
     #`(module+ name
         (begin-for-syntax
           (gamma (term #,(gamma)))
           (sigma (term #,(sigma)))
           (bind-subst '#,(bind-subst)))
         body ...)]))

;; -----------------------------------------------------------------
;; Core wrapper macros
;;
;; TODO: Can these be simplified further?
(define-syntax (dep-lambda syn)
  (syntax-case syn (:)
    [(_ (x : t) e)
     (syntax->curnel-syntax
       (quasisyntax/loc syn (λ (x : t) e)))]))

(define-syntax (dep-app syn)
  (syntax-case syn ()
    [(_ e1 e2)
     (syntax->curnel-syntax
       (quasisyntax/loc syn (#%app e1 e2)))]))

(define-syntax (dep-forall syn)
  (syntax-case syn (:)
    [(_ (x : t) e)
     (syntax->curnel-syntax
       (quasisyntax/loc syn (Π (x : t) e)))]))

(define-syntax (Type syn)
  (syntax-case syn ()
    [(_ i)
     (syntax->curnel-syntax
       (quasisyntax/loc syn (Unv i)))]
    [_ (quasisyntax/loc syn (Type 0))]))

(define-syntax (dep-inductive syn)
  (syntax-case syn (:)
    [(_ i : ti (x1 : t1) ...)
     ;; TODO: Probably should occur only in definition context? and also, should not really produce void
     (begin
       (extend-Σ/syn! sigma #'i #'ti #'((x1 : t1) ...))
       #'(void))]))

(define-syntax (dep-elim syn)
  (syntax-case syn ()
    [(_ D T)
     (syntax->curnel-syntax
       (quasisyntax/loc syn (elim D T)))]))

(define-syntax-rule (dep-void) (void))

;; TODO: Not sure if this is the correct behavior for #%top
(define-syntax (dep-top syn)
  (syntax-case syn ()
    [(_ . id)
     ;; TODO NB FIXME: HACKS HACKS HACKS
     (let ([t (core-expand #'id)])
       (if (equal? (syntax->datum t) '(void))
           #'(void)
           (syntax->curnel-syntax t)))]))

(define-syntax (dep-top-interaction syn)
  (syntax-case syn ()
    [(_ . form)
     (begin
       ;; TODO NB FIXME: HACKS HACKS HACKS
       #`(begin
           (export-envs gamma-out sigma-out bind-out)
           (begin-for-syntax
             ;; Try to detect when we are in DrRacket, and do the right thing.
             (when (equal? 'debug-error-display-handler (object-name (error-display-handler)))
                 (cond
                   [(null? (namespace-mapped-symbols))
                    (displayln "You will need to add a (provide ...) in the definitions area for the evaluator to load Cur definitions correctly.")]
                   [(eq? 3 (length (namespace-mapped-symbols)))
                    (bind-subst (namespace-variable-value (first (namespace-mapped-symbols))))
                    (gamma (namespace-variable-value (second (namespace-mapped-symbols))))
                    (sigma (namespace-variable-value (third (namespace-mapped-symbols))))]
                   [else (void)])))
          form))]))

(define-syntax (dep-define syn)
  (syntax-parse syn
    [(_ id:id e)
     (let ([e (cur->datum #'e)]
           [id (syntax->datum #'id)])
       (extend-Γ/term! gamma id (type-infer/term e))
       (add-binding/term! id e)
       #'(void))]))

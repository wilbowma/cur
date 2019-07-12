#lang s-exp "../main.rkt"

(provide (for-syntax (all-defined-out)))

(require
 (for-syntax "ctx.rkt" "utils.rkt"
             racket/stxparam
             syntax/stx
             macrotypes/stx-utils
             (for-syntax racket/base syntax/parse racket/syntax syntax/stx macrotypes/stx-utils))
 "base.rkt")

(begin-for-syntax

  (define-syntax-parameter $ptz (λ (stx) (raise-syntax-error #f "can only be used with define-tactic" stx)))
  (define-syntax-parameter $ctxt (λ (stx) (raise-syntax-error #f "can only be used with define-tactic" stx)))
  (define-syntax-parameter $pt (λ (stx) (raise-syntax-error #f "can only be used with define-tactic" stx)))
  (define-syntax-parameter $goal (λ (stx) (raise-syntax-error #f "can only be used with define-tactic" stx)))
  (define-syntax-parameter $pfs (λ (stx) (raise-syntax-error #f "can only be used with define-tactic" stx)))
  (define-syntax-parameter $fill ; ↪
    (λ (stx) (raise-syntax-error #f "can only be used with define-tactic" stx)))

  (define-syntax $stx/holes ; mks a node
    (syntax-parser
      [(_ goal proof/holes #:where [x : τ] ooo (~datum ⊢) ?HOLE (~datum :) subgoal)
       #'(make-ntt-apply
          goal
          (list (make-ntt-context
                 (λ (ctxt)
                   (for/fold ([ctxt ctxt]) ([x (in-stx-list #'(x ooo))] [τ (in-stx-list #'(τ ooo))])
                     (ctx-add ctxt x (normalize τ ctxt))))
                 (make-ntt-hole subgoal)))
          (λ (?HOLE) (quasisyntax/loc goal proof/holes)))]))
  (define-syntax $stx/leaf
    (syntax-parser
      [(_ goal term)
       #'(make-ntt-exact goal (quasisyntax/loc goal term))]))
  (define-syntax $stx/compose
    (syntax-parser
      [(_ goal proof/holes #:with subgoals)
       #'(make-ntt-apply
          goal
          subgoals
          (λ pfs
            (syntax-parameterize
                ([$pfs (syntax-parser [_ #'pfs])])
              (quasisyntax/loc goal proof/holes))))]))
  (define-syntax $fills
    (syntax-parser
      [(_ goal pf) #'(make-ntt-exact goal pf)]
      #;[(_ go) #'(make-ntt-hole go)]
      #;[(_ go #:ctx x (~datum :) ty) #'(make-ntt-context (λ (ctx) (ctx-add ctx x ty)) (make-ntt-hole go))]
      ;[(_ proof/xholes #:where (~seq (~var x id) (~datum :) subgoal) (... (... ...)))
      [(_ goal proof/holes #:where [x (~datum :) ty (~datum ⊢) (~var ?hole id) (~datum :) subgoal] ...)
       #'(make-ntt-apply
          goal
          ;                                      (list subgoal (... (... ...)))
          (list (make-ntt-context (λ (ctx) (ctx-add ctx x ty)) (make-ntt-hole subgoal)) ...)
          (λ (?hole ...)
            (quasisyntax/loc goal proof/holes)))]
#;      [(_ goal proof/holes #:subgoals subgoals)
       #'(make-ntt-apply
          goal
          ;                                      (list subgoal (... (... ...)))
          (map realsubgoal-pt (map subgoal-goal subgoals))
          #;(list (make-ntt-context (λ (ctx) (ctx-add ctx x ty)) (make-ntt-hole subgoal)) ...)
          (λ pfs
            (syntax-parameterize
                ([$pfs (syntax-parser [_ #'(map (λ (sb pf) ((subgoal-mk-term sb) pf)) subgoals pfs)])])
              (quasisyntax/loc goal
                proof/holes))))]
      [(_ goal proof/holes #:subgoals subgoals)
       #'(make-ntt-apply
          goal
          ;                                      (list subgoal (... (... ...)))
          subgoals
          #;(list (make-ntt-context (λ (ctx) (ctx-add ctx x ty)) (make-ntt-hole subgoal)) ...)
          (λ pfs
            (syntax-parameterize
                ([$pfs (syntax-parser [_ #'pfs])])
              (quasisyntax/loc goal
                proof/holes))))]))

  ;; old version of $fill
#;  (define-syntax node
    (syntax-parser
      [(_ goal) #'(make-ntt-hole goal)]
      [(_ goal #:ctx x (~datum :) ty) #'(make-ntt-context (λ (ctx) (ctx-add ctx x ty)) (make-ntt-hole goal))]
      [(_ proof/xholes (~datum :) goal (~or (~datum ⇓) #:where) (~seq x:id (~datum :) subgoal) ...)
       #'(make-ntt-apply
          goal
          (list subgoal ...)
          (λ (x ...)
            (quasisyntax/loc goal proof/xholes))
          #;(λ (pf)
            (syntax-parameterize
                ([$pf (syntax-parser [:id #'pf])]);(unsyntax pf)])])
              (quasisyntax/loc goal proof/holes))))]))

  ;; define-tactical
  (define-syntax define-tactical
    (syntax-parser
      [(_ name [pat body ...] ...)
       #'(define-syntax name
           (syntax-parser
             [pat
              #'(λ (ptz)
                  (syntax-parameterize
                      ([$ptz (make-rename-transformer #'ptz)])
                    body ...))] ...))]))
  (define-syntax define-tactic
    (syntax-parser
      [(_ name
          [pat (~optional (~seq (~or #:current-goal #:goal) goalpat)
                          #:defaults ([goalpat (generate-temporary)]))
               body ...] ...) ; each body produces pt; each tactic must be ptz -> ptz
       #:with name-internal (generate-temporary #'name)
       #:with (dispatching-body ...) (stx-map ;  make bodies dispatch to name-internal
                                      (syntax-parser
                                        [((hd:id . rst)) #:when (free-id=? #'hd #'name) ; body is recursive call
                                          #'#'(name-internal . rst)]
                                        [_ #'(if (identifier? this-syntax)
                                                 #'name-internal
                                                 (datum->syntax this-syntax
                                                   (cons #'name-internal (stx-cdr this-syntax))))])
                                      #'((body ...) ...))
       ;; filter out unneeded internal cases (ie recursive calls)
       #:with ((internal-pat internal-gpat internal-body) ...)
              (for/list
                  ([p (in-stx-list #'(pat ...))]
                   [gp (in-stx-list #'(goalpat ...))]
                   [bs (in-stx-list #'((body ...) ...))]
                   #:when (and (stx-pair? (stx-car bs)) ; keep non-recursive call cases
                               (not (free-id=? #'name (stx-car (stx-car bs))))))
                (list p gp bs))
      #'(begin
         (define-syntax name (syntax-parser [pat dispatching-body] ...)) ; dispatching, surface macro
         (define-syntax name-internal ; the actual tactic macro
           (syntax-parser
             [internal-pat
              #'(λ (ptz)
                  (next
                   (struct-copy
                    nttz ptz
                    [focus
                     (let* ([ctxt (nttz-context ptz)]
                            [pt (nttz-focus ptz)]
                            [goal (ntt-goal pt)])
                       (syntax-parse goal
                         [internal-gpat
                          (syntax-parameterize
                              ([$ptz (make-rename-transformer #'ptz)]
                               [$ctxt (make-rename-transformer #'ctxt)]
                               [$pt  (make-rename-transformer #'pt)]
                               [$goal (make-rename-transformer #'goal)]
                               [$fill ; make this local, so it has access to and can insert $goal to make-ntt-apply
                                (syntax-parser
                                  [(_ pf) #'(make-ntt-exact goal pf)]
                                  [(_ proof/holes
                                      #:where
                                      [x (~datum :) ty (~datum ⊢) (~var ?hole id) (~datum :) subgoal]
                                      (... (... ...)))
                                   #`(make-ntt-apply
                                      goal
                                      ;(list subgoal (... (... ...)))
                                      (list
                                       (make-ntt-context (λ (ctx) (ctx-add ctx x ty)) (make-ntt-hole subgoal))
                                       (... (... ...)))
                                      (λ (?hole (... (... ...)))
                                        (quasisyntax/loc goal proof/holes)))])])
                            . internal-body)]))])))] ...)))
       ]))

)


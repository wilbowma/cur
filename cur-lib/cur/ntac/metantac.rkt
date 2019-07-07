#lang s-exp "../main.rkt"

(provide (for-syntax (all-defined-out)))

(require
 (for-syntax "ctx.rkt" "utils.rkt"
             racket/stxparam
             syntax/stx
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
      #;[(_ (name . args) . body)
       #'(define ((name . args) ctxt pt)
           (let ([goal (ntt-goal pt)])
             (syntax-parameterize
                 ([$ctxt (make-rename-transformer #'ctxt)]
                  [$pt  (make-rename-transformer #'pt)]
                  [$goal (make-rename-transformer #'goal)])
               . body)))]
      [(_ name
          [pat (~optional (~seq (~or #:current-goal #:goal) goalpat)
                          #:defaults ([goalpat (generate-temporary)]))
               body ...] ...) ; each body produces pt; each tactic must be ptz -> ptz
       #'(define-syntax name
           (syntax-parser
             [pat
              #'(λ (ptz)
                  (next
                   (struct-copy
                    nttz ptz
                    [focus
                     (let* ([ctxt (nttz-context ptz)]
                            [pt (nttz-focus ptz)]
                            [goal (ntt-goal pt)])
                       (syntax-parse goal
                         [goalpat
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
                            body ...)]))])))] ...))]))


)


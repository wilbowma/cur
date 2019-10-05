#lang cur
;; Hints for automated proof solving

(provide (for-syntax (all-defined-out)))
(provide define-theorem
         define-theorem/for-export
         ntac
         ntac/debug
         set-auto-depth!)

(require
  (for-syntax "ctx.rkt"
              racket/bool
              racket/list
              racket/set
              racket/match
              (for-syntax racket/base
                          syntax/parse))
  "base.rkt"
  "standard.rkt"
  "rewrite.rkt")

(begin-for-syntax
  (define hints (make-parameter null))
  (define hints-default '())

  ; bypass phase-level restriction in hints-add!
  (define (set-hints! . v)
    ; ignore any duplicate hints
    (begin
      (define diff-set (set-subtract (list->set (filter symbol? (map syntax->datum v)))
                                     (list->set (map syntax->datum (hints)))))
      (define diff-list
        (filter (lambda (e) (set-member? diff-set (syntax->datum e))) v))
      (hints (append diff-list (hints)))))
  
  (define-syntax (hints-add! syn)
    (syntax-case syn ()
      [(_ H ...) #'(begin
                 (set-hints! #'H ...)
                 (λ (ptz) ptz))]))

  (define (display-hints tz)
    (printf "~a" (map (compose symbol->string syntax->datum) (hints)))
    tz)

  (define (clear-hints! tz)
    (hints '())
    tz)

  ; nothing novel is introduced here, but it works better
  ; for the caller that we don't use syntax cases here
  (define (intro-hints ctxt pt)
    (match-define (ntt-hole _ goal) pt)
    (ntac-match goal
                [(~Π (a : P) body)
                 ((intro #'a) ctxt pt)]
                [_ pt]))
  
  (define (by-intros-hints ptz)
    (define nptz ((fill intro-hints) ptz))
    (if (equal? (nttz-context nptz) (nttz-context ptz))
        nptz
        (by-intros-hints nptz)))

  ; define a struct for tactic presets used in `auto`
  (struct tactic-preset (proc id no-name-arg?) #:transparent)
  ; results caching should be scoped to a single auto run
  ; in case identifiers are re-bound
  (define auto-result-hash (make-parameter null))
  ; note that tactic attempts will happen in this order
  (define auto-tactics
    (list (tactic-preset (lambda (name) (fill (apply-fn name))) "apply" #f)
          (tactic-preset (lambda (name) (fill assumption)) "assumption" #t)
          (tactic-preset (lambda (name) reflexivity) "reflexivity" #t)
          (tactic-preset (lambda (name) simpl) "simpl" #t)
          (tactic-preset (lambda (name) (fill (rewrite name #:left? #f))) "rewrite" #f)
          (tactic-preset (lambda (name) (fill (rewrite name #:left? #t))) "rewriteL" #f)
          (tactic-preset (lambda (name) (fill (destruct name))) "destruct" #f)
          (tactic-preset (lambda (name) (fill (induction name))) "induction" #f)))

  ; assumption: in general, we use auto on relatively trivial proofs; this
  ; implies that the depth of our search tree will not be very deep, and it is
  ; therefore suitable to use BFS capped at a particular depth
  (define default-max-auto-depth (make-parameter 4))

  (define (by-auto-helper ptz depth path
                          #:initial-hole-count [initial-hole-count (num-holes/z ptz)]
                          #:min-hole-ptz [min-hole-ptz ptz]
                          #:min-hole-count [min-hole-count initial-hole-count]
                          #:min-hole-path [min-hole-path '()]
                          #:worklist [worklist '()])
    ; keep track of a global solution, so we can simulate the notion of
    ; a continuation/return through mutation and breaking
    (let* ([solution #f]
           [solution-path '()]
           [thm-names-temp (append (hints) (ctx-ids (nttz-context ptz)))]
           [thm-names (if (empty? thm-names-temp)
                          (list #'dummy) ; hack for empty context
                          thm-names-temp)]
           [new-worklist (if (<= depth 0)
                             worklist
                             (append worklist (foldl append '()
                               (for/list ([tactic auto-tactics])
                                 #:break solution
                                 (filter (compose not false? car)
                                         (for/list ([thm-name thm-names])
                                           #:break solution
                                           (begin (define hash-key
                                                    (if (tactic-preset-no-name-arg? tactic)
                                                        (list tactic (nttz-focus ptz))
                                                        (list tactic thm-name (nttz-focus ptz))))
                                                  (define new-path-node
                                                    (if (tactic-preset-no-name-arg? tactic)
                                                        (cons (tactic-preset-id tactic) "")
                                                        (cons (tactic-preset-id tactic)
                                                              (symbol->string (syntax->datum thm-name)))))
                                                  (define result
                                                    (if (hash-has-key? (auto-result-hash) hash-key)
                                                        (hash-ref (auto-result-hash) hash-key)
                                                        (with-handlers ([exn:fail? (lambda (e) (begin #;(printf "~a\n" e) false))])
                                                          (begin #;(if (tactic-preset-no-name-arg? tactic)
                                                                     (printf "DEPTH: ~a Running ~a with path ~a\n"
                                                                             depth
                                                                             (tactic-preset-id tactic)
                                                                             (reverse path))
                                                                     (printf "DEPTH: ~a Running ~a with ~a with path ~a\n"
                                                                             depth
                                                                             (tactic-preset-id tactic)
                                                                             (symbol->string (syntax->datum thm-name))
                                                                             (reverse path)))
                                                                 (define nptz (((tactic-preset-proc tactic) thm-name) ptz))
                                                                 (if (nttz-done? nptz)
                                                                     (begin (set! solution nptz)
                                                                            (set! solution-path (cons new-path-node path)))
                                                                     ; keep track of nodes with the least subgoals remaining, so that we
                                                                     ; can return partial solutions if no full solution is found
                                                                     (let ([hole-count (num-holes/z nptz)])
                                                                       (when (< hole-count min-hole-count)
                                                                         (begin (set! min-hole-ptz nptz)
                                                                                (set! min-hole-count hole-count)
                                                                                (set! min-hole-path (cons new-path-node path))))))
                                                                 nptz))))
                                                  (hash-set! (auto-result-hash) hash-key false) ; subsequent hits should just be filtered out
                                                  (list result (sub1 depth) (cons new-path-node path)))))))))])
      (if ((compose not false?) solution)
          (begin (printf "auto solution: ~a\n" (reverse solution-path)) solution)
          (begin (if (empty? new-worklist)
                     (if (< min-hole-count initial-hole-count)
                         (begin (printf "auto solution with ~a subgoal(s) met: ~a\n"
                                        (- initial-hole-count min-hole-count)
                                        (reverse min-hole-path)) min-hole-ptz)
                         false)
                     (by-auto-helper (first (first new-worklist))
                                     (second (first new-worklist))
                                     (third (first new-worklist))
                                     #:initial-hole-count initial-hole-count
                                     #:min-hole-ptz min-hole-ptz
                                     #:min-hole-count min-hole-count
                                     #:min-hole-path min-hole-path
                                     #:worklist (rest new-worklist)))))))

  ; See https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.auto
  ; Description pasted below:
  ; This tactic implements a Prolog-like resolution procedure to solve the
  ; current goal. It first tries to solve the goal using the assumption
  ; tactic, then it reduces the goal to an atomic one using intros and
  ; introduces the newly generated hypotheses as hints. Then it looks at the
  ; list of tactics associated to the head symbol of the goal and tries to
  ; apply one of them (starting from the tactics with lower cost). This
  ; process is recursively applied to the generated subgoals.
  ;
  ; By default, auto only uses the hypotheses of the current goal and the
  ; hints of the database named core.
  (define ((auto^ n) ptz)
    (define asptz (with-handlers ([exn:fail? (lambda (e) ptz)]) (by-obvious ptz)))
    (if (nttz-done? asptz)
        asptz
        (let* ([inptz (by-intros-hints ptz)]
               [auto-result (parameterize ([auto-result-hash (make-hash)])
                              (by-auto-helper inptz n '()))])
          (if (false? auto-result)
              (raise-ntac-goal-exception "automatic proof failed")
              auto-result))))

  (define-syntax auto
    (syntax-parser
      [(_ n:nat)
       #`(auto^ n)]
      [_ #`(auto^ (default-max-auto-depth))]))

  (define (ntac-proc ty ps)
    (let ()
      ; hints are only active within scope of proc
      (parameterize ([hints hints-default])
        (define ctxt (mk-empty-ctx))
        (define init-pt
          (new-proof-tree (cur-expand ty)))
        (define final-pt
          (eval-proof-script
           init-pt
           ps
           ctxt
           ps))
        (define pf
          (proof-tree->complete-term
           final-pt
           ps))
        ;      (pretty-print (syntax->datum pf))
        pf))))

;; Syntax - redefinitions using modified ntac-proc
(define-syntax (define-theorem stx)
  (syntax-parse stx
    [(_ x:id ty ps ...)
     #:with e (local-expand (ntac-proc #'ty #'(ps ...)) 'expression null)
     (quasisyntax/loc stx (define x e))]))

(define-syntax (define-theorem/for-export stx)
  (syntax-parse stx
    [(_ x:id ty ps ...)
     (quasisyntax/loc stx (define x (ntac ty ps ...)))]))

;; For inline ntac
(define-syntax ntac
  (syntax-parser
    [(_ ty . pf) (ntac-proc #'ty #'pf)]))

;; For inline ntac
(define-syntax ntac/debug
  (syntax-parser
    [(_ ty . pf)
     (begin
       (current-tracing? 1)
       (begin0
         (ntac-proc #'ty #'pf)
         (current-tracing? #f)))]))

; we can short-circuit sooner if we're just looking for an intermediate solution
(define-syntax (set-auto-depth! syn)
    (syntax-case syn ()
      [(_ d) (begin (default-max-auto-depth (eval #'d))
                    #'(void))]))

#lang cur
;; Hints for automated proof solving

(provide (for-syntax (all-defined-out)))

(require
  (for-syntax "ctx.rkt"
              racket/bool
              racket/list
              racket/match
              (for-syntax racket/base))
  "base.rkt"
  "standard.rkt"
  "rewrite.rkt")

(begin-for-syntax
  (define hints (make-parameter null))

  ; bypass phase-level restriction in hints-add!
  (define (set-hints! v)
    (set! hints (make-parameter v)))
  
  (define-syntax (hints-add! syn)
    (syntax-case syn ()
      [(_ H) #'(begin
                 (set-hints! (cons #'H (hints)))
                 (λ (ptz) ptz))]))

  (define (display-hints tz)
    (printf "~a" (map (compose symbol->string syntax->datum) (hints)))
    tz)

  (define (clear-hints! tz)
    (set-hints! null)
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
  (define max-auto-depth 5)
  (define auto-result-hash (make-hash))
  (define (by-auto-helper ptz depth #:worklist [worklist '()])
    (when (<= depth 0) (raise-ntac-goal-exception "max auto depth reached"))
    ; keep track of a global solution, so we can simulate the notion of
    ; a continuation/return through mutation and breaking
    (define solution #f)
    (define thm-names-temp (append (hints) (ctx-ids (nttz-context ptz))))
    (define thm-names (if (empty? thm-names-temp)
                          (list "dummy") ; hack for empty context
                          thm-names-temp))
    (define new-worklist
      (append worklist
              (foldl append '()
                     (for/list ([tactic auto-tactics])
                       #:break (not (false? solution))
                       (filter (compose not false? car)
                               (for/list ([thm-name thm-names])
                                 #:break (not (false? solution))
                                 (begin (define hash-key (if (tactic-preset-no-name-arg? tactic)
                                                             (list tactic (nttz-focus ptz))
                                                             (list tactic thm-name (nttz-focus ptz))))
                                        (if (hash-has-key? auto-result-hash hash-key)
                                            (cons (hash-ref auto-result-hash hash-key) (sub1 depth))
                                            (let ([result
                                                   (with-handlers ([exn:fail? (lambda (e) (begin #;(printf "~a\n" e) false))])
                                                     (begin #;(if (tactic-preset-no-name-arg? tactic)
                                                                (printf "DEPTH: ~a Running ~a\n" depth (tactic-preset-id tactic))
                                                                (printf "DEPTH: ~a Running ~a with ~a\n" depth (tactic-preset-id tactic) (symbol->string (syntax->datum thm-name))))
                                                            (define nptz (((tactic-preset-proc tactic) thm-name) ptz))
                                                            (when (nttz-done? nptz) (set! solution nptz))
                                                            nptz))])
                                              (hash-set! auto-result-hash hash-key result)
                                              (cons result (sub1 depth)))))))))))
    (when (empty? new-worklist) (raise-ntac-goal-exception "automatic proof failed"))
    (if ((compose not false?) solution)
        solution
        (by-auto-helper (car (first new-worklist)) (cdr (first new-worklist)) #:worklist (rest new-worklist))))

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
  (define (auto ptz)
    (define asptz (with-handlers ([exn:fail? (lambda (e) ptz)]) (by-obvious ptz)))
    (if (nttz-done? asptz)
        asptz
        (let ([inptz (by-intros-hints ptz)])
          (begin
            (by-auto-helper inptz max-auto-depth))))))

#lang s-exp "../../main.rkt"
(require
  "base.rkt"
  "../sugar.rkt"
  (for-syntax racket/syntax))

(provide
  (for-syntax
   intro
   intros
    obvious
    restart
    forget
    print
    by-assumption
    interactive))

#| TODO:
 | Tactics should probably not error on failure. Perhaps Maybe monad, or list monad, or return proof
 | state unmodified, or raise exception, or ...
 |#
(define-tactic intro
  (case-lambda
    [(ps)
     (cur-match
      (proof-state-current-goal-ref ps)
      [(forall (x:id : P:expr) body:expr)
       (intro #'x ps)]
      [_
       (error 'intro
              "Can only intro when current goal is of the form (∀ (x : P) body)")])]
    [(name ps)
     (cur-match
      (proof-state-current-goal-ref ps)
      [(forall (x:id : P:expr) body:expr)
       (let* ([ps (proof-state-extend-env ps name #'P)]
              [ps (proof-state-current-goal-set ps #'body)]
              [ps
               (proof-state-fill-proof-hole
                ps (lambda (x)
                     (if (syntax? x)
                         #`(λ (#,name : P) #,x)
                         (error 'intro "Cannot fill hole with ~e" x))))])
         ps)]
      [_
       (error 'intro
              "Can only intro when current goal is of the form (∀ (x : P) body)")])]))

(define-tactic intros
  (case-lambda
    [(ps)
     (cur-match
      (proof-state-current-goal-ref ps)
      [(forall (x:id : P:expr) body:expr)
       (intros (intro #'x ps))]
      [_
       ps])]
    [(names ps)
     (for/fold ([ps ps]) ([n (in-list (syntax->list names))])
       (intro n ps))]))

(define-tactic (by-assumption ps)
  (cond
    [(proof-state-env-ref-by-type ps (proof-state-current-goal-ref ps))
     =>
     (lambda (x)
       (let* ([ps (proof-state-fill-proof-hole ps x)]
              [ps (proof-state-current-goal-set ps #f)])
         ps))]
    [else (error 'by-assumption "Cannot find an assumption that matches the goal")]))

;; TODO: requires more support from curnel
#;(begin-for-syntax
  (define (inductive? ps type)
    ))

;; Do the obvious thing
(define-tactic (obvious ps)
  (cur-match (proof-state-current-goal-ref ps)
    [(forall (x : P) t)
     (obvious (intro #'x ps))]
    [t:expr
     (cond
       ;; TODO: This would be cleaner if I could say "try all these
       ;; things and do whichever works".
       [(proof-state-env-ref-by-type ps #'t) (by-assumption ps)]
       ;[(inductive? ps #'t) (by-constructor ps)]
       [else (error 'obvious "This is not all that obvious to me.")])]))

(define-tactic (restart ps) (new-proof-state (proof-state-theorem ps)))

(define-tactic (print ps) (print-proof-state ps) ps)

(define-tactic (forget x ps)
  (struct-copy proof-state ps
    [env (dict-remove (syntax-e x) (proof-state-env ps))]))

;; Interactive you say? Sure whatevs, DIY
(define-tactic (interactive ps)
  (printf "Starting interactive tactic session:~n")
  (printf "Type (quit) to quit.~n")
  (let loop ([ps ps] [cmds '()])
    (print ps)
    (let ([cmd (read-syntax)])
      (syntax-case cmd (quit)
        [(quit)
         (begin
           (printf "Your tactic script:~n")
           ;; TODO: Using clever trickery, could problem write a
           ;; version of interactive that actually modifies the file.

           ;; JAY: Better to embed interactive inside of file and use
           ;; Emacs-y expr-feeding to send in the commands one by one
           (pretty-print (reverse (map syntax->datum cmds)))
           (newline)
           ps)]
        ;; TODO: Maybe use (read-eval-print-loop) and its
        ;; TODO: config parameters.
        [(tactic arg ...)
          (with-handlers (#;[exn:fail:contract?
                            (lambda (e)
                              (printf "tactic ~a expected different arguments.~n"
                                (syntax->datum #'tactic))
                              (loop ps cmds))]
                          #;[exn:fail:syntax?
                            (lambda (e)
                              (printf "~a is not a tactic.~n"
                                (syntax->datum #'tactic))
                              (loop ps cmds))])
            (loop (apply (lookup-tactic #'tactic)
                    (append (syntax->list #'(arg ...)) (list ps)))
                  (cons cmd cmds)))]))))

;; TODO:
;; Open interactive REPL for tactic DSL; exit with QED command, which
;; returns a QED script
;(define-syntax interactive-proof)

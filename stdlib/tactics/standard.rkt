#lang s-exp "../../cur.rkt"
(require
  "base.rkt"
  (for-syntax racket/syntax))

(provide
  (for-syntax
    intro
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
(define-tactic (intro name ps)
  (cur-match (proof-state-current-goal-ref ps)
    [(forall (x:id : P:expr) body:expr)
     (let* ([ps (proof-state-extend-env ps name #'P)]
            [ps (proof-state-current-goal-set ps #'body)]
            [ps (proof-state-fill-proof-hole ps (lambda (x) #`(lambda (#,name : P) #,x)))])
       ps)]
    [_ (error 'intro "Can only intro when current goal is of the form (∀ (x : P) body)")]))

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
       ;; TODO: This would be cleaner if I could say "try all these things and do whichever works".
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
           ;; TODO: Using clever trickery, could problem write a version of interactive that actually
           ;; modifies the file.
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

(module+ test
  (require
    rackunit
    "../bool.rkt")
  (define-theorem meow (forall (x : bool) bool))
  (proof
    (intro x)
    (by-assumption))
  (define-theorem meow1 (forall (x : bool) bool))
  (proof
    (obvious)
    (print))
  (define-theorem meow2 (forall (x : bool) bool))
  (proof
    (intro x)
    (restart)
    (intro x)
    (by-assumption))
  (define-theorem meow3 (forall (x : bool) bool))
  (proof (obvious))
  ;; TODO: Fix this unit test so it doesn't require interaction
  (define-theorem meow4 (forall (x : bool) bool))
  (proof
    (interactive))
  ;; TODO: Add check-cur-equal? for unit testing?
  #;(check-pred (curry cur-equal? '(lambda (x : bool) x)))
  )

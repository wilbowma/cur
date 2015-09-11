#lang s-exp "../../redex-curnel.rkt"
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

;;; TACTICS
;;; A tactic is a function from proof state to proof state

;; TODO: Tactics probably should not error for failure. Perhaps return
;; TODO: proof state unmodified, or raise an exception.
(define-tactic (intro name ps)
  ;; TODO: Maybe cur-expand current-goal by default
  (syntax-parse (cur-expand (proof-state-current-goal ps))
    [(forall (x:id : P:expr) body:expr)
     (update-current-goal
       (update-current-proof
        ;; TODO: Should hide syntax-e in push-env
        (push-env ps (syntax-e name) #'P)
        (lambda (x) #`(λ (#,x : P) #,x)))
       #'body)]
    [_ (error 'intro "Can only intro when current goal is of the form (∀ (x : P) body)")]))

(begin-for-syntax
  (define (assumption ps type)
    (for/first ([(k v) (in-dict (proof-state-env ps))]
                #:when (cur-equal? v type))
      k)))

(define-tactic (by-assumption ps)
  (cond
    [(assumption ps (cur-expand (proof-state-current-goal ps)))
     => (curry update-current-proof (update-current-goal ps #f))]
    [else (error 'by-assumption "Cannot find an assumption that matches the goal")]))

;; TODO: requires more support from curnel
#;(begin-for-syntax
  (define (inductive? ps type)
    ))

;; Do the obvious thing
(define-tactic (obvious ps)
  (syntax-parse (cur-expand (proof-state-current-goal ps))
    [(forall (x : P) t)
     (obvious (intro #'x ps))]
    [t:expr
     (cond
       [(assumption ps #'t) (by-assumption ps)]
       ;[(inductive? ps #'t) (by-constructor ps)]
       [else (error 'obvious "This is not all that obvious to me.")])]))

(define-tactic (restart ps)
  (struct-copy proof-state ps
    [current-goal (proof-state-original-goal ps)]
    [current-proof empty-proof]))

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
           (pretty-print (map syntax->datum cmds))
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
  #;(proof
    (interactive))
  ;; TODO: Add check-cur-equal? for unit testing?
  #;(check-pred (curry cur-equal? '(lambda (x : bool) x)))
  )

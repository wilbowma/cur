#lang s-exp "../redex-curnel.rkt"
(require
  racket/stxparam
  racket/trace
  racket/syntax
  (for-syntax racket/trace racket/syntax))

;; NB: The design of Cur currently seems to prevent intermediate type-checking
;; NB: during a tactic-based proof, unless I were to either reimplement the
;; NB: type-checker or extend it with a notion of holes.
;; TODO: A notion of holes my be useful in general...

;; NB: Per below, note that Cur already has contexts. The issue with
;; NB: type-checking intermediate results has to do with the fact that Cur
;; NB: contexts are not exposed properly, nor is type-checking defined on
;; NB: them.

;;; ======================================================================
;;; Tactic support

;;; A Goal is a syntax object representing a Cur proposition (type).

;;; A Expr is a syntax object representing Cur expression (term).

;;; A Hole is a procedure of type

;;; A Ctxt is a procedure (Either Ctxt Expr) -> (Either Ctxt Expr)
;;; representing a Cur expression with a hole.

;;; A Environment is a map from Symbol to Goal.

;;; The compile-time proof-state interface.
;;; TODO: I'm partially implementing lens here.
;;; TODO: Interface is mildly inconsistent.
(begin-for-syntax
  ;; How to display a hole, for pretty printing.
  (define hole 'hole)

  ;; A Proof-State is a struct containing:
  ;;   env: An Environment, the assumptions introduced during a tactic
  ;;        script.
  ;;   goals: A map from Natural to Goal, the goals necessary to finish
  ;;          this proof
  ;;   current-goal: A Natural, the index into goals of the current Goal
  ;;                 to be proved.
  ;;   current-proof: A (Either Ctxt Expr), representing the proof so far.
  ;;                  current-proof is an Expr, the proof is complete.
  (define-struct proof-state (env goals current-goal current-proof
                              original-goal))

  (define (print-proof-state ps)
    (for ([(k v) (in-dict (proof-state-env ps))])
      (printf "~n~a : ~a~n" k (syntax->datum v)))
    (printf "--------------------------------~n")
    (cond
      [(proof-state-current-goal ps) =>
       (lambda (x) (printf "~a~n~n" (syntax->datum x)))]
      [else (printf "Goal complete!~n~n")]))

  (define current-proof-state (make-parameter #f))

  ;; The current theorem; used internally to achieve a Coq-like notation
  ;; for defining theorems and tactic-based proofs.
  (define current-theorem (make-parameter #f))

  (define empty-proof values)

  (define (new-proof-state prop)
    (proof-state (make-immutable-hash) (make-immutable-hash) prop
                 empty-proof prop))

  ;; push-env adds a mapping from name to P in (proof-state-env ps).
  ;; Proof-State -> Symbol -> Goal -> Proof-State
  (define (push-env ps name P)
    (struct-copy proof-state ps
      [env (hash-set (proof-state-env ps) name P)]))

  ;; TODO: Cur already has contexts; perhaps they should be exposed?
  ;; Ctxt -> (Either Ctxt Expr) -> (Either Ctxt Expr)
  ;; C1[C2]
  (define (plug-ctxt C1 C2) (C1 C2))

  (define ctxt? procedure?)

  (define (proof-complete? ps) (not (ctxt? (proof-state-current-proof ps))))

  (define (update-current-proof ps pf)
    ;; TODO: Check for proof completion?
    (struct-copy proof-state ps
      [current-proof (plug-ctxt (proof-state-current-proof ps) pf)]))

  (define (update-current-goal ps goal)
    (struct-copy proof-state ps
      [current-goal goal]))

  (define-namespace-anchor tactics)

  (define (lookup-tactic sym)
    (namespace-variable-value sym #f #f (namespace-anchor->namespace tactics)))

  (define (lookup-tactic-syn syn)
    (namespace-variable-value (syntax->datum syn)
      #f #f (namespace-anchor->namespace tactics))))

;;; ======================================================================

;; A tactic is a Racket function that manipulates the current proof state.
;; Tactic : Args ... Proof-State -> Proof-State

;;; Syntax for defining tactics.
;; (define-tactic command-name function)
;; (define-tactic (command-name args ... Proof-State) body)
(define-syntax (define-tactic syn)
  (syntax-case syn ()
    [(_ (name args ... ps) body ...)
     (quasisyntax/loc syn
       (define-for-syntax (name args ... ps) body ...))]
    [(_ name function)
     (raise-syntax-error "Syntax not yet defined")]))

;; (define-goal-tactic command-name function)
;; (define-goal-tactic (command-name args ... ctx goal-list current-goal) body)

;; Define a theorem, with similar semantics to Coq theorems in that you
;; can define the theorem then define the proof next.
(define-syntax (define-theorem syn)
  (syntax-case syn ()
    [(_ name prop)
     (current-theorem (cur-expand #'prop))
     #'(define name prop)]))

;; Aliases for theorems.
;; TODO: I think there's some define-syntax-rename thing that would
;; TODO: prevent eta expanding these.
(define-syntax-rule (define-lemma s ...) (define-theorem s ...))

;; The proof macro starts a proof environment. Every proof should begin
;; with it.
;; TODO: uh should probably save the proof. Perhaps theorem should
;; TODO: define something else, then proof should be bound to theorem name.
(define-syntax (proof syn)
  (syntax-parse syn
    [(_ (f args* ...) ... (~optional (~literal qed)))
     (unless (current-theorem)
       (raise-syntax-error 'proof
         "You can't use proof without a first using define-theorem"))
     (let* ([t (current-theorem)]
            [pf (proof-state-current-proof
                  ;; Thread proof state through tactic calls, and eval
                  ;; at compile-time.
                  (for/fold ([ps (new-proof-state t)])
                            ([f (map lookup-tactic-syn (syntax->list #'(f ...)))]
                             [args (map syntax->list
                                        (syntax->list #'((args* ...) ...)))])
                    (apply f (append args (list ps)))))])
          (when (ctxt? pf)
            (raise-syntax-error 'qed "Proof contains holes" (pf hole)))
          (unless (type-check/syn? pf t)
            (raise-syntax-error 'qed "Invalid proof" pf t))
          pf)]))

;;; TODO: Everything below here should probably be in a separate module
;;; ======================================================================

;;; TACTICS

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
                          [exn:fail:syntax?
                            (lambda (e)
                              (printf "~a is not a tactic.~n"
                                (syntax->datum #'tactic))
                              (loop ps cmds))])
            (loop (apply (lookup-tactic-syn #'tactic)
                    (append (syntax->list #'(arg ...)) (list ps)))
                  (cons cmd cmds)))]))))

;; TODO:
;; Open interactive REPL for tactic DSL; exit with QED command, which
;; returns a QED script
;(define-syntax interactive-proof)

(module+ test
  (require rackunit "bool.rkt")
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
  (proof
    (interactive))
  ;; TODO: Add check-cur-equal? for unit testing?
  #;(check-pred (curry cur-equal? '(lambda (x : bool) x)))
  )

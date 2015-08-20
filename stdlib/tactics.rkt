#lang s-exp "../redex-curnel.rkt"

;; NB: The design of Cur currently seems to prevent intermediate type-checking
;; NB: during a tactic-based proof, unless I were to either reimplement the
;; NB: type-checker or extend it with a notion of holes.

(begin-for-syntax
  ;; current-goal is a Goal, a Cur proposition to be shown
  (define-parameter current-goal none)

  ;; goals is a map of Naturals to Goals
  (define-parameter goals (make-hash))

  ;; current-expr is an Expr, a Cur expression that may include Holes.
  (define-parameter current-expr hole)

  ;; env is an Environment, a map of Symbols to Cur propositions, 
  ;; i.e., a map of of names to assumptions introduced during the
  ;; tactic script
  (define-parameter env (make-hash))

  ;; A tactic is a function that manipulates the current goal state.
  ;; Tactic : Context -> Goals -> Goal -> (list Environment Goals Goal Expr)

  ;; tactics: map of tactic names to interpretation functions.
  ;; i.e. tactics is a map Symbols => Tactics
  (define-parameter tactics (make-hash))
  )

;; (define-tactic command-name function)
;; (define-tactic (command-name ctx goal-list current-goal args ...) body)
(define-syntax (define-tactic syn)
  (syntax-case syn ()
    [(_ (name ctx goal-list current-goal args ...) body ...)
     (register-tactic! (syntax->datum #'name) 
       (syntax->datum #'(lambda (ctx goal-list current-goal args ...) body ...)))]
    [(_ name function)
     (register-tactic! (syntax->datum #'name) 
       (syntax->datum #'function))]))

;; NB: Assumes Cur terms are represented as lists
(define-tactic (intro env goals current-goal name)
  ;; TODO: Probably need to cur-expand current-goal
  ;; TODO: Goals should probably be Curnel terms
  (match current-goal
    [(∀ (x : P) body)
     (list (push-env env name P) goals body 
           `(λ (,name : ,P) ,hole))]
    [_ (error 'intro "Can only intro when current goal is of the form (∀
    (x : P) body)")]))

(define-tactic (obvious env goals current-goal)
  (match current-goal
    [(∀ (x : P) body)
     ;; TODO: These patterns seem to indicate env, goals, current-goal
     ;; TODO: should just be parameters, manipulated in a stateful manner.
     (match-let ([(list env goals current-goal body)
                  (obvious (push-env env name P) goals body)])
       (list env goals current-goal `(λ (,x : ,P) ,body)))]
    [(? assumption?) (by-assumption env goals current-goal)]
    [(? inductive?) (by-constructor env goals current-goal)]
    [_ (error 'obvious "This isn't all that obvious to me.")]))

(define-tactic (by-assumption env goals current-goal)
  (match current-goal
    [(? assumption P)
     ;; TODO: How should "completing" a goal work? should the tactic
     ;; TODO: handle this, or the systen? Probably the system... detect when an
     ;; TODO: expr with 0 holes has been returned, and type-check against
     ;; TODO: current goal.
     (list env goals current-goal (env-search-by-prop env P))]
    ;; TODO: Check uses of error vs errorf, or whatever
    [_ (error 'by-assumption "You have not assumed this.")]))

;; Tactic DSL grammar:
;;   tactic-script ::= (qed (tactic-name args ...))
;;   tactic-name ::= dom(tactics)
;;   args ::= dom(env)

;; Open interactive REPL for tactic DSL; exit with QED command, which
;; returns a QED script
(define-syntax interactive-qed)

;; Drop into tactic DSL, ends either explicitly or implicitly with the
;; QED command.
;; Example:
;;   (define-theorem name prop
;;     (qed
;;       (intro x)
;;       (elim)
;;       (apply f x)))
(define-syntax qed)

#lang s-exp "../redex-curnel.rkt"
(require racket/stxparam
         racket/trace
         racket/syntax
         (for-syntax racket/trace racket/syntax))

;; NB: The design of Cur currently seems to prevent intermediate type-checking
;; NB: during a tactic-based proof, unless I were to either reimplement the
;; NB: type-checker or extend it with a notion of holes.

;; NB: Per below, note that Cur already has contexts. The issue with
;; NB: type-checking intermediate results has to do with the fact that Cur
;; NB: contexts are not exposed properly, nor is type-checking defined on
;; NB: them.

;;; A Goal is a syntax object representing a Cur proposition (type).

;;; A Expr is a syntax object representing Cur expression (term).

;;; A Hole is a procedure of type

;;; A Ctxt is a procedure (Either Ctxt Expr) -> (Either Ctxt Expr)
;;; representing a Cur expression with a hole.

;;; A Environment is a map from Symbol to Goal.

;; A Proof-State is a struct containing:
;;   env: An Environment, the assumptions introduced during a tactic
;;        script.
;;   goals: A map from Natural to Goal, the goals necessary to finish
;;          this proof
;;   current-goal: A Natural, the index into goals of the current Goal
;;                 to be proved.
;;   current-proof: A (Either Ctxt Expr), representing the proof so far.
;;                  current-proof is an Expr, the proof is complete.

(begin-for-syntax
  (define hole 'hole)
  (define-struct proof-state (env goals current-goal current-proof))

  (define current-proof-state (make-parameter #f))

  ;; The current theorem; used internally to achieve a Coq-like notation
  ;; for defining theorems and tactic-based proofs.
  (define current-theorem (make-parameter #f))

  (define (new-proof-state prop)
    (unless prop
      (raise-syntax-error 'qed "You can't use qed without a first using define-theorem"))
    (proof-state (make-immutable-hash) (make-immutable-hash) prop values))

  ;; push-env adds a mapping from name to P in (proof-state-env ps).
  ;; Proof-State -> Symbol -> Goal -> Proof-State
  (define (push-env ps name P)
    (struct-copy proof-state ps
      [env (hash-set (proof-state-env ps) name P)]))

  ;; TODO: Cur already has contexts; perhaps they should be exposed?
  ;; Ctxt -> (Either Ctxt Expr) -> (Either Ctxt Expr)
  ;; C1[C2]
  (define (plug-ctxt C1 C2) (C1 C2))

  (define Ctxt? procedure?)

  (define (proof-complete? ps) (not (Ctxt? (proof-state-current-proof ps))))

  (define (update-current-proof ps pf)
    ;; TODO: Check for proof completion?
    (struct-copy proof-state ps
      [current-proof (plug-ctxt (proof-state-current-proof ps) pf)]))

  (define (update-current-goal ps goal)
    (struct-copy proof-state ps
      [current-goal goal])))

;; A tactic is a Racket function that manipulates the current proof state.
;; Tactic : Args ... Proof-State -> Proof-State

;;; Syntax for defining tactics.
;; (define-tactic command-name function)
;; (define-tactic (command-name args ... Proof-State) body)
(define-syntax (define-tactic syn)
  (syntax-case syn ()
    [(_ (name args ... ps) body ...)
     ;; TODO: quasisyntax/loc
     #'(begin-for-syntax
         (define (name args ... ps)
           body ...))]
    [(_ name function)
     (raise-syntax-error "Syntax not yet defined")]))

;; (define-goal-tactic command-name function)
;; (define-goal-tactic (command-name args ... ctx goal-list current-goal) body)

(define-tactic (intro name ps)
  ;; TODO: Maybe cur-expand current-goal by default
  ;; TODO: Goals should probably be Curnel terms
  (syntax-parse (cur-expand (proof-state-current-goal ps))
    [(forall (x:id : P:expr) body:expr)
     (update-current-goal
       (update-current-proof
        (push-env ps (syntax-e name) #'P)
        (lambda (x) #`(λ (x : P) #,x)))
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
     => (curry update-current-proof ps)]
    [else (error 'by-assumption "Cannot find an assumption that matches the goal")]))

;; TODO: requires more support from curnel
#;(begin-for-syntax
  (define (inductive? ps type)
    ))
(define-tactic (obvious ps)
  (syntax-parse (cur-expand (proof-state-current-goal ps))
    [(forall (x : P) t)
     (obvious (intro #'x ps))]
    [t:expr
     (cond
       [(assumption ps #'t) (by-assumption ps)]
       ;[(inductive? ps #'t) (by-constructor ps)]
       [else (error 'obvious "This is not all that obvious to me.")])]))

;; Tactic DSL grammar:
;;   tactic-script ::= (qed (tactic-name args ...))
;;   tactic-name ::= dom(tactics)
;;   args ::= dom(env)

;; TODO:
;; Open interactive REPL for tactic DSL; exit with QED command, which
;; returns a QED script
;(define-syntax interactive-qed)

;; Drop into tactic DSL, ends either explicitly or implicitly with the
;; QED command.
;; Example:
;;   (define-theorem name prop)
;;   (qed
;;     (intro x)
;;     (elim)
;;     (apply f x)))
(define-syntax (define-theorem syn)
  (syntax-case syn ()
    [(_ name prop)
     (begin
       (current-theorem (cur-expand #'prop))
       #'(define name prop))]))
(define-syntax (qed syn)
  (syntax-case syn ()
    [(_ (f args* ...) ...)
     (let* ([t (current-theorem)]
            [pf (proof-state-current-proof
                  (syntax-local-eval #`(let* ([ps (new-proof-state #'#,t)]
                                              [ps (f #'args* ... ps)] ...)
                                             ps)))])
          (when (procedure? pf)
             (raise-syntax-error 'qed "Proof contains holes" (pf hole)))
          (unless (type-check/syn? pf t)
             (raise-syntax-error 'qed "Invalid proof" pf t))
          pf)]))
(module+ test
  (require "bool.rkt")
  (define-theorem meow (forall (x : bool) bool))
  (qed
    (intro x)
    (by-assumption))
  (define-theorem meow1 (forall (x : bool) bool))
  (qed (obvious))
  )

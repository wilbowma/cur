#lang s-exp "../../redex-curnel.rkt"
(require
  (for-syntax racket/syntax))
(provide
  proof
  define-theorem
  define-lemma
  define-tactic

  (for-syntax
    hole
    proof-state
    proof-state-env
    proof-state-goals
    proof-state-current-goal
    proof-state-current-proof
    proof-state-original-goal
    print-proof-state
    current-theorem
    empty-proof
    new-proof-state
    push-env
    ctxt?
    proof-complete?
    update-current-proof
    update-current-goal
    lookup-tactic))

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

  ;; Given a Proof-State, return #t if the current-proof is complete
  ;; (i.e. is a Expr and not a Ctxt), #f otherwise.
  (define (proof-complete? ps) (not (ctxt? (proof-state-current-proof ps))))

  ;; Given a Proof-State ps and Ctxt pf, plug pf into the current Ctxt
  ;; and return the modified Proof-State.
  (define (update-current-proof ps pf)
    ;; TODO: Check for proof completion?
    (struct-copy proof-state ps
      [current-proof (plug-ctxt (proof-state-current-proof ps) pf)]))

  ;; Given a Proof-State ps and a Goal, update the current goal and
  ;; return the modified Proof-State.
  (define (update-current-goal ps goal)
    (struct-copy proof-state ps
      [current-goal goal]))

  ;; Takes a symbol or syntax object naming a tactic, and returns the
  ;; procedure for that tactic.
  (define (lookup-tactic syn)
    (eval
      (if (syntax? syn)
          ;; Ensure eval gets the right environment
          (datum->syntax (current-theorem) (syntax->datum syn))
          syn))))

;;; ======================================================================

;; A tactic is a Racket function that manipulates the current proof state.
;; Tactic : Args ... Proof-State -> Proof-State

;;; Syntax for defining tactics.
;; (define-tactic command-name function)
;; (define-tactic (command-name args ... Proof-State) body)
;; TODO: Srsly?
(define-syntax (define-tactic syn)
  (syntax-case syn ()
    [(_ (name args ... ps) body ...)
     (quasisyntax/loc syn
       (define-for-syntax (name args ... ps) body ...))]
    [(_ name function)
     (quasisyntax/loc syn
       (define-for-syntax name function))]))

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

(begin-for-syntax
  ;; Given a list of tactics and their arguments, run the tactic script
  ;; on the current theorem, returning the proof if the proof is valid.
  (define (run-tactic-script f* args*)
    (unless (current-theorem)
      (raise-syntax-error 'proof
        "You can't use proof without a first using define-theorem"))
    (let* ([t (current-theorem)]
           [pf (proof-state-current-proof
                 ;; Thread proof state through tactic calls, and eval
                 ;; at compile-time.
                 (for/fold ([ps (new-proof-state t)])
                           ([f f*] [args args*])
                    (apply (lookup-tactic f) (append args (list ps)))))])
          (when (ctxt? pf)
            (raise-syntax-error 'qed "Proof contains holes" (pf hole)))
          (unless (type-check/syn? pf t)
            (raise-syntax-error 'qed "Invalid proof" pf t))
          pf)))

;; The proof macro starts a proof environment. Every proof should begin
;; with it.
;; TODO: uh should probably save the proof. Perhaps theorem should
;; TODO: define something else, then proof should be bound to theorem name.
(define-syntax (proof syn)
  (syntax-parse syn
    [(_ (f args* ...) ... (~optional (~literal qed)))
     (run-tactic-script
       (syntax->list #'(f ...))
       (map syntax->list (syntax->list #'((args* ...) ...))))]))

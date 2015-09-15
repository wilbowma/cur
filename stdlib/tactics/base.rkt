#lang s-exp "../../cur.rkt"
(require
  (for-syntax racket/syntax))
(provide
  proof
  define-theorem
  define-tactic

  (for-syntax
    proof-state
    proof-state-env
    proof-state-goals
    proof-state-proof
    proof-state-theorem
    new-proof
    new-proof-state
    proof-state-proof-complete?
    proof-state-goal-ref
    proof-state-current-goal-ref
    proof-state-current-goal-set
    proof-state-env-ref
    proof-state-env-ref-by-type
    proof-state-extend-env
    proof-state-fill-proof-hole
    proof-state-extend-proof-context
    current-hole-pretty-symbol
    print-proof-state
    lookup-tactic))

#| NB:
 | The design of Cur currently seems to prevent intermediate type-checking
 | during a tactic-based proof, unless I were to either reimplement the
 | type-checker or extend it with a notion of holes.
 | TODO: A noation of holes may be useful in general.
 |#

#| NB:
 | Per below, note that Cur already has contexts. The issue with
 | type-checking intermediate results has to do with the fact that Cur
 | contexts are not exposed properly, nor is type-checking defined on
 | them.
 |#

;; ------------------------------------------------------------------------
;;; Proof state interface

#|
 | A Goal, aka, Theorem is a syntax object representing a Cur proposition (type).
 |
 | A Expr is a syntax object representing Cur expression (term).
 |
 | A Hole is a procedure of type
 |
 | A Proof is (Either Ctxt Expr)
 |
 | A Ctxt is a procedure Proof -> Proof representing a Cur expression
 | with a hole.
 |
 | A Environment is a map from Symbol to Theorems.
 |
 | A Proof-State is a struct containing:
 |   env: An Environment, the assumptions introduced during a tactic
 |        script.
 |   goals: A map from Natural to Goal, the goals necessary to finish
 |          this proof
 |   current-goal: A Natural, the index into goals of the current Goal
 |                 to be proved.
 |   proof: A Proof, representing the proof so far. when the proof is
 |          an Expr, the proof is complete.
 |   theorem: A Theorem, the original statement of the theorem this proof is
 |            attempting to prove.
 |#
;;; TODO: I'm partially implementing lens here.
;;; TODO: Interface is mildly inconsistent.
(begin-for-syntax
  (define-struct proof-state (env goals current-goal proof theorem))

  (define new-proof values)

  (define (new-proof-state prop)
    (proof-state
      (make-immutable-hash)
      (dict-set (make-immutable-hash) 0 prop)
      0
      new-proof
      prop))

  ;; Given a Proof-State, return #t if the current-proof is complete
  ;; (i.e. is a Expr and not a Ctxt), #f otherwise.
  (define (proof-state-proof-complete? ps) (not (procedure? (proof-state-proof ps))))

  ;;; Extra accessors

  ;; Return the goal with index i in proof-state-goals
  (define (proof-state-goal-ref ps i)
    (dict-ref (proof-state-goals ps) i))

  ;; Return the current-goal from proof-state-goals
  (define (proof-state-current-goal-ref ps)
    (proof-state-goal-ref ps (proof-state-current-goal ps)))

  ;; Return the theorem named by name in the local environment
  (define (proof-state-env-ref ps name)
    (dict-ref (proof-state-env ps) name))

  ;; Return the name of an assumption with type thm, or #f.
  (define (proof-state-env-ref-by-type ps thm)
    (for/first ([(k v) (in-dict (proof-state-env ps))]
                #:when (cur-equal? v thm))
      k))

  ;;; Functional updators

  (define (maybe-syntax->symbol name)
    (if (syntax? name)
        (syntax->datum name)
        name))

  ;; Extend the local environment with a new assumption, name, of type thm. Name can be a syntax
  ;; object or a symbol.
  (define (proof-state-extend-env ps name thm)
    (struct-copy proof-state ps
      [env (dict-set (proof-state-env ps) (maybe-syntax->symbol name) thm)]))

  ;; Updates the current-goal to pf
  (define (proof-state-current-goal-set ps pf)
    (struct-copy proof-state ps
      [goals (dict-set (proof-state-goals ps) (proof-state-current-goal ps) pf)]))

  ;; Fill the current proof hole with pf
  (define (proof-state-fill-proof-hole ps pf)
    ;; TODO: Check for proof completion?
    ;; TODO: What about multiple holes?
    (struct-copy proof-state ps
      [proof ((proof-state-proof ps) pf)]))

  ;; Place the current proof in the context ctxt.
  (define (proof-state-extend-proof-context ps ctxt)
    (struct-copy proof-state ps
      [proof (ctxt (proof-state-proof ps))]))

  ;; How to display a hole, for pretty printing.
  (define current-hole-pretty-symbol (make-parameter 'hole))

  ;; A pretty printer for proof-state
  (define (print-proof-state ps)
    (for ([(k v) (in-dict (proof-state-env ps))])
      (printf "~n~a : ~a~n" k (syntax->datum v)))
    (printf "--------------------------------~n")
    (cond
      [(proof-state-current-goal-ref ps)
       =>
       (lambda (x) (printf "~a~n~n" (syntax->datum x)))]
      [else (printf "Goal complete!~n~n")])))

;; -----------------------------------------------------------------------
;;; Syntax for tactic-based proofs similar to Coq.

#|
 | A tactic is a phase 1 Racket function that manipulates the current proof state.
 | Tactic : Any ... Proof-State -> Proof-State
 |
 | Examples:
 |
 | (define-tactic command-name function)
 | (define-tactic (command-name args ... ps) body)
 |#
(define-syntax define-tactic (make-rename-transformer #'define-for-syntax))

(begin-for-syntax
  ;; Takes a symbol or syntax object naming a tactic, and returns the
  ;; procedure for that tactic.
  (define (lookup-tactic syn)
    (eval
      (if (syntax? syn)
          ;; NB: Ensure eval gets the right environment
          (datum->syntax (current-theorem) (syntax->datum syn))
          syn))))

(begin-for-syntax
  ;; The current theorem; used internally to achieve a Coq-like notation
  ;; for defining theorems and tactic-based proofs.
  (define current-theorem (make-parameter #f)))

;; Define a theorem, with similar semantics to Coq theorems in that you
;; can define the theorem then define the proof next.
(define-syntax (define-theorem syn)
  (syntax-case syn ()
    [(_ name prop)
     (current-theorem (cur-expand #'prop))
     #'(define name prop)]))

;; Aliases for theorems.
;; (define-syntax define-lemma (make-rename-transformer #'define-theorem))

(begin-for-syntax
  ;; Given a list of tactics and their arguments, run the tactic script
  ;; on the current theorem, returning the proof if the proof is valid.
  (define (run-tactic-script f* args*)
    (unless (current-theorem)
      (raise-syntax-error
        'proof
        "You can't use proof without a first using define-theorem"))
    (let* ([t (current-theorem)]
           [ps ;; Thread proof state through tactic calls, and eval
               ;; at compile-time.
               (for/fold ([ps (new-proof-state t)])
                         ([f f*] [args args*])
                 (apply (lookup-tactic f) (append args (list ps))))]
           [pf (proof-state-proof ps)])
      (unless (proof-state-proof-complete? ps)
        (raise-syntax-error 'qed "Proof contains holes" (pf (current-hole-pretty-symbol))))
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

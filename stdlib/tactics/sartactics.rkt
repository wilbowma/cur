#lang s-exp "../../cur.rkt"
(require
  "base.rkt"
  (prefix-in basic: "standard.rkt")
  (for-syntax racket/syntax))

(provide
  (for-syntax
    intro
    interactive))

;;; SARCASTIC INTERACTIVE TACTICS

(begin-for-syntax
  (define jabs
    (list
      "I don't think you know what you're doing."
      "Does this look right to *you*?"
      "Prove it."))

  (define (random-ref ls)
    (list-ref ls (random (length ls))))

  (define (random-jab) (random-ref jabs))
  )

(define-tactic (print ps)
  (basic:print ps)
  (displayln (random-jab))
  ps)

(begin-for-syntax
  (define intro-jabs
    (list
      "What a clever name."
      "How original."
      "I'm sure that seems like a good idea to *you*."
      "Why don't you just assume false while you're at it?")))

(define-tactic (intro name ps)
  (displayln (random-ref intro-jabs))
  (newline)
  (basic:intro name ps))

(define-tactic (forget ps)
  (displayln "Like hell.")
  ps)
(define-tactic by-assumption basic:by-assumption)

(begin-for-syntax
  (define restart-jabs
    (list
      "Hahahahahahahaha."
      "Lawl."
      "Why don't you just do it right the first time?"
      "Stupid human."
      "I've been waiting for this.")))
(define-tactic (restart ps)
  (displayln (random-ref restart-jabs))
  (basic:restart ps))

(begin-for-syntax
  (define denied-obvious-jabs
    (list
      "It's not obvious to me."
      "You expect me to know this?"
      "If it's so obvious then just finish the proof already."
      "Maybe you should hire a grad student."))
  (define accept-obvious-jabs
    (list
      "I wasn't going to say anything, but this was taking you forever."
      "Finally."
      "Let me show you how it's done."
      "You're right, I am better at proving things than you are."
      "Aw that was *sooo* tough...")))
(define-tactic (obvious ps)
  (if (< (random 10) 3)
      (begin
        (displayln (random-ref accept-obvious-jabs))
        (newline)
        (basic:obvious ps))
      (begin
        (displayln (random-ref denied-obvious-jabs))
        (newline)
        ps)))

(begin-for-syntax
  (define no-quit-jabs
    (list
      "Na."
      "How about instead I just delete all your work?"
      "I don't think you're ready yet.")))
(define-tactic (interactive ps)
  (printf "Starting interactive tactic session. Prepared to be sassed:~n")
  (printf "Type (quit) to quit.~n")
  (let loop ([ps ps] [cmds '()])
    (if (proof-state-proof-complete? ps)
        (basic:print ps)
        (print ps))
    (let ([cmd (read-syntax)])
      (newline)
      (syntax-case cmd (quit)
        [(quit)
         (if (< (random 10) 4)
             (begin
               (printf "Don't forget this. It took you long enough:~n")
               (pretty-print (reverse (map syntax->datum cmds)))
               (newline)
               ps)
             (begin
               (displayln (random-ref no-quit-jabs))
               (loop ps cmds)))]
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

(module+ test
  (require
    rackunit
    "../bool.rkt")
  (define-theorem meow (forall (x : bool) bool))
  #;(proof
    (interactive))
  )

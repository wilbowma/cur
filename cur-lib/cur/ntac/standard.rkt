#lang s-exp "../main.rkt"
(require
 "../stdlib/sugar.rkt"
 "../curnel/racket-impl/reflection.rkt" ; simpl needs cur-normalize
 "base.rkt")

(begin-for-syntax
  (require racket/exn)
  (provide
   (all-defined-out)))

;; define-nttz-cmd ?
(define-for-syntax (nop ptz) ptz)

;; exceptions for tactics
(begin-for-syntax
  ;; ntac exceptions
  (struct exn:fail:ntac exn:fail ())

  ;; ntac exception for when the goal is not as expected.
  (struct exn:fail:ntac:goal exn:fail:ntac ())
  (define (raise-ntac-goal-exception msgf . rest)
    (raise (exn:fail:ntac:goal (apply format msgf rest) (current-continuation-marks))))

  (define-syntax-rule (ntac-match goal [pattern branch] ...)
    (cur-match goal
      [pattern branch]
      ...
      [_ (raise-ntac-goal-exception
          "Goal ~a did not match; you can use the `try` meta tactic to ignore this."
          goal)])))

;; display tactic
(define-for-syntax (display-focus tz)
  (match (nttz-focus tz)
    [(ntt-hole _ goal)
     (for ([(k v) (in-dict (nttz-context tz))])
       (printf "~a : ~a\n" (syntax->datum k) (syntax->datum v)))
     (printf "--------------------------------\n")
     (printf "~a\n\n" (syntax->datum goal))]
    [(ntt-done _ _ _)
     (printf "Proof complete.\n")]
    [_
     ;; XXX
     (printf "Not at hole.\n")])
  tz)

(define-for-syntax (interactive ptz)
  (display-focus ptz)
  (define cmd-stx
    (let/ec esc
      (parameterize ([current-eval
                      (λ (in)
                        (syntax-case in ()
                          [(_ . cmd)
                           (esc #'cmd)]))])
        (read-eval-print-loop))))
  (define next-ptz
    (with-handlers ([exn:fail:ntac:goal?
                     (lambda (e)
                       (displayln (exn->string e))
                       ptz)])
      (eval-proof-step ptz cmd-stx)))
  (if (nttz-done? next-ptz)
      next-ptz
      (interactive next-ptz)))

(define-for-syntax ((fill t) ptz)
  (define new-foc (t (nttz-context ptz) (nttz-focus ptz)))
  ;; XXX Maybe new-foc could be #f for failure?
  (next
   (struct-copy nttz ptz [focus new-foc])))

;; meta tactic; not a tactic (which take tacticals); takes a tactic.
(define-for-syntax ((try t) ptz)
  (with-handlers ([exn:fail:ntac:goal? (lambda (e) ptz)])
    (t ptz)))

;; define-tactical
(require (for-syntax racket/trace))
(define-for-syntax (ctxt->env ctxt)
  (reverse (for/list ([(k v) (in-dict ctxt)])
             (cons k v))))

(define-for-syntax ((intro [name #f]) ctxt pt)
  ;; TODO: ntt-match(-define) to hide this extra argument. Maybe also add ntt- to constructors in pattern?
  (match-define (ntt-hole _ goal) pt)
  (ntac-match goal
   [(forall (x:id : P:expr) body:expr)
    (let ()
      (define the-name (or name #'x))
      (make-ntt-apply
       goal
       (list
        (make-ntt-context
         (lambda (old-ctxt)
           (dict-set old-ctxt the-name #'P))
         (make-ntt-hole (cur-rename the-name #'x #'body))))
       (lambda (body-pf)
         (quasisyntax/loc goal (λ (#,the-name : P) #,body-pf)))))]))

;; A pattern emerges:
;; tacticals must take additional arguments as ntac-syntax
;; define-tactical should generate a phase 2 definition like the one below, and a functional version
;; of the tactical (perhaps by-tactical-name)
(begin-for-syntax
  (define-syntax (by-intro syn)
    (syntax-case syn ()
      [(_ syn)
       #`(fill (intro #'syn))]
      [_
       #`(fill (intro))])))

(define-for-syntax (intros names)
  (for/fold ([t nop])
            ([n (in-list names)])
    (compose (fill (intro n)) t)))
(begin-for-syntax
  (define-syntax (by-intros syn)
    (syntax-case syn ()
      [(_ id ...)
       #`(intros (list #'id ...))])))

;; define-tactical
(define-for-syntax ((exact a) ctxt pt)
  (match-define (ntt-hole _ goal) pt)
  (unless (cur-type-check? a goal #:local-env (ctxt->env ctxt))
    (raise-ntac-goal-exception "~v does not have type ~v" a goal))
  (make-ntt-exact goal a))

(begin-for-syntax
  (define-syntax (by-exact syn)
    (syntax-case syn ()
      [(_ syn)
       #`(fill (exact #'syn))])))

;;define-tactical
(define-for-syntax (assumption ctxt pt)
  (match-define (ntt-hole _ goal) pt)
  ;; TODO: Actually, need to collect (k v) as we search for a matching assumption, otherwise we might
  ;; break dependency. Hopefully we have some invariants that prevent that from actually happening.
  (define ntt
    (for/or ([(k v) (in-dict ctxt)]
           #:when (cur-equal? v goal #:local-env (ctxt->env ctxt)))
      (make-ntt-exact goal k)))
  (unless ntt
    (raise-ntac-goal-exception "could not find matching assumption for goal ~a" goal))
  ntt)

(begin-for-syntax
  (define-syntax (by-assumption syn)
    (syntax-case syn ()
      [_
       #`(fill assumption)])))

(define-for-syntax (obvious ctxt pt)
 (match-define (ntt-hole _ goal) pt)
  (ntac-match goal
    [(forall (a : P) body)
     ((intro) ctxt pt)]
    [a:id
     (assumption ctxt pt)]))

(define-for-syntax (by-obvious ptz)
  (define nptz ((fill obvious) ptz))
  (if (nttz-done? nptz)
      nptz
      (by-obvious nptz)))

(define-for-syntax (simpl ptz)
  (match-define (ntt-hole _ goal) (nttz-focus ptz))
  (next
   ;; TODO: should this be a copy?
   (struct-copy nttz ptz
     [focus (make-ntt-hole (cur-normalize goal))])))


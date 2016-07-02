#lang s-exp "../../main.rkt"
(require
 "../sugar.rkt"
 "base.rkt")

;; define-nttz-cmd ?
(define-for-syntax (nop ptz) ptz)

(define-for-syntax (interactive ptz)
  (define cmd-stx
    (let/ec esc
      (parameterize ([current-eval
                      (λ (in)
                        (syntax-case in ()
                          [(_ . cmd)
                           (esc (ntac-syntax #'cmd))]))])
        (read-eval-print-loop))))
  (define next-ptz
    (eval-proof-step ptz cmd-stx))
  (if (nttz-done? next-ptz)
      next-ptz
      (interactive next-ptz)))

(define-for-syntax ((fill t) ptz)
  (define new-foc (t (nttz-context ptz) (nttz-focus ptz)))
  ;; XXX Maybe new-foc could be #f for failure?
  (next
   (struct-copy nttz ptz [focus new-foc])))

;; define-tactical
(define-for-syntax ((_intro [name #f]) ctxt pt)
  (match-define (ntt-hole _ goal) pt)
  (cur-match goal
   [(forall (x:id : P:expr) body:expr)
    (let ()
      ;; NB: syntax is not hashable.
      (define the-name (syntax->datum (or name #'x)))
      (make-ntt-apply
       goal
       (list
        (make-ntt-context
         (λ (old-ctxt) (hash-set old-ctxt the-name #'P))
         (make-ntt-hole #'body)))
       (λ (body-pf)
         #`(λ (#,the-name : P) #,body-pf))))]))

;; A pattern emerges:
;; tacticals must take additional arguments as ntac-syntax
;; define-tactical should generate a phase 2 definition like the one below, and a functional version
;; of the tactical (perhaps tactical-name-f)
(begin-for-syntax
  (define-syntax (intro syn)
    (syntax-case syn ()
      [(_)
       #`(fill (_intro))]
      [(_ syn)
       #`(fill (_intro (ntac-syntax #'syn)))])))

(define-for-syntax (_intros names)
  (for/fold ([t nop])
            ([n (in-list names)])
    (compose (fill (_intro n)) t)))
(begin-for-syntax
  (define-syntax (intros syn)
    (syntax-case syn ()
      [(_ (id ...))
       #`(_intros (list (ntac-syntax #'id) ...))])))

;; define-tactical
(define-for-syntax ((_exact a) ctxt pt)
  (match-define (ntt-hole _ goal) pt)
  (define env
    (for/list ([(k v) (in-hash ctxt)])
      (cons (datum->syntax #f k) v)))
  (unless (cur-type-check? a goal #:local-env env)
    (error 'exact "~v does not have type ~v" a goal))
  (make-ntt-exact goal a))

(begin-for-syntax
  (define-syntax (exact syn)
    (syntax-case syn ()
      [(_ syn)
       #`(fill (_exact (ntac-syntax #'syn)))])))

;;define-tactical 
(define-for-syntax (by-assumption ctxt pt)
  (match-define (ntt-hole _ goal) pt)
  (define env
    (for/list ([(k v) (in-hash ctxt)])
      (cons (datum->syntax #f k) v)))
  ;; TODO: Actually, need to collect (k v) as we search for a matching assumption, otherwise we might
  ;; break dependency. Hopefully we have some invariants that prevent that from actually happening.
  (for/or ([(k v) (in-hash ctxt)]
           ;; TODO: Probably need to add local-env to cur-equal?
           #:when (cur-equal? v goal #:local-env env))
    (make-ntt-exact goal k)))

(module+ test
  (require
   "../prop.rkt"
   "../sugar.rkt")

  ;; Not quite and-proj1; need elim for that.
  (define-theorem and-proj1
    (forall (A : Type) (B : Type) (c : (And A B)) Type)
    nop
    ;; XXX The use of fill is ugly. Perhaps could be infered
    (intro A)
    (intro)
    (intros (c))
    nop
    ;interactive ; try (fill (exact 'A))
    ;; This works too
    (exact A)
    ;; And this
    #;(fill by-assumption))

  and-proj1

  (ntac-prove
   (forall (A : Type) (a : A) A)
   (intros (A a))
   (fill by-assumption)))

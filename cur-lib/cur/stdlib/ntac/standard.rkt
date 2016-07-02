#lang s-exp "../../main.rkt"
(require
 "../sugar.rkt"
 "base.rkt")

(begin-for-syntax
  (provide
   (all-defined-out)))

;; define-nttz-cmd ?
(define-for-syntax (nop ptz) ptz)

(define-for-syntax (interactive ptz)
  (display-nttz ptz)
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
(define-for-syntax ((intro [name #f]) ctxt pt)
  ;; TODO: ntt-match(-define) to hide this extra argument. Maybe also add ntt- to constructors in pattern?
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
;; of the tactical (perhaps by-tactical-name)
(begin-for-syntax
  (define-syntax (by-intro syn)
    (syntax-case syn ()
      [_
       #`(fill (intro))]
      [(_ syn)
       #`(fill (intro (ntac-syntax #'syn)))])))

(define-for-syntax (intros names)
  (for/fold ([t nop])
            ([n (in-list names)])
    (compose (fill (intro n)) t)))
(begin-for-syntax
  (define-syntax (by-intros syn)
    (syntax-case syn ()
      [(_ id ...)
       #`(intros (list (ntac-syntax #'id) ...))])))

;; define-tactical
(define-for-syntax ((exact a) ctxt pt)
  (match-define (ntt-hole _ goal) pt)
  (define env
    (for/list ([(k v) (in-hash ctxt)])
      (cons (datum->syntax #f k) v)))
  (unless (cur-type-check? a goal #:local-env env)
    (error 'exact "~v does not have type ~v" a goal))
  (make-ntt-exact goal a))

(begin-for-syntax
  (define-syntax (by-exact syn)
    (syntax-case syn ()
      [(_ syn)
       #`(fill (exact (ntac-syntax #'syn)))])))

;;define-tactical 
(define-for-syntax (assumption ctxt pt)
  (match-define (ntt-hole _ goal) pt)
  (define env
    (for/list ([(k v) (in-hash ctxt)])
      (cons (datum->syntax #f k) v)))
  ;; TODO: Actually, need to collect (k v) as we search for a matching assumption, otherwise we might
  ;; break dependency. Hopefully we have some invariants that prevent that from actually happening.
  (for/or ([(k v) (in-hash ctxt)]
           #:when (cur-equal? v goal #:local-env env))
    (make-ntt-exact goal k)))

(begin-for-syntax
  (define-syntax (by-assumption syn)
    (syntax-case syn ()
      [_
       #`(fill assumption)])))

(define-for-syntax (obvious ctxt pt)
 (match-define (ntt-hole _ goal) pt)
  (cur-match goal
    [(forall (a : P) body)
     ((intro) ctxt pt)]
    [a:id
     (assumption ctxt pt)]))

(define-for-syntax (by-obvious ptz)
  (define nptz ((fill obvious) ptz))
  (if (nttz-done? nptz)
      nptz
      (by-obvious nptz)))

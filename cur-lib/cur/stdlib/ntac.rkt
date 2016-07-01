#lang cur
(require "sugar.rkt")
(provide
 define-theorem
 (for-syntax
  qed interactive))

(define-syntax (define-theorem stx)
  (syntax-parse stx
    [(_ x:id ty . ps)
     (quasisyntax/loc stx
       (begin (define x #,(expand-proof-during-stxtime #'ty #'ps))
              (:: x ty)))]))

(begin-for-syntax
  (struct PT (contains-hole? A) #:transparent)
  (struct *PT:Hole PT () #:transparent)
  (define (PT:Hole A)
    (*PT:Hole #t A))
  (struct *PT:Exact PT (a) #:transparent)
  (define (PT:Exact A a)
    (*PT:Exact #f A a))
  (struct *PT:Ctxt PT (gf k) #:transparent)
  (define (PT:Ctxt gf k)
    (*PT:Ctxt (PT-contains-hole? k) (PT-A k) gf k))
  (struct *PT:App PT (children f) #:transparent)
  (define (PT:App A cs f)
    (*PT:App (ormap PT-contains-hole? cs) A cs f))
  (struct *PT:Done PT (k) #:transparent)
  (define (PT:Done k)
    (when (PT-contains-hole? k)
      (error 'PT:Done "Cannot construct done if hole present: ~v" k))
    (*PT:Done #f (PT-A k) k))

  (define (new-proof-tree #:of A)
    (PT:Hole A))

  (define (proof-tree->complete-term #:err-stx [err-stx #f] pt)
    (match pt
      [(*PT:Hole _ _)
       (raise-syntax-error 'define-theorem "attempt to save incomplete proof" err-stx)]
      [(*PT:Exact _ _ a) a]
      [(*PT:Ctxt _ _ gf k)
       (proof-tree->complete-term #:err-stx err-stx k)]
      [(*PT:App _ _ cs f)
       (apply f (map (λ (c) (proof-tree->complete-term #:err-stx err-stx c)) cs))]
      [(*PT:Done _ _ k)
       (proof-tree->complete-term #:err-stx err-stx k)]))

  (struct PTZ (ctxt focus up))
  (define (PTZ-New pt)
    (PTZ (hasheq) pt
         (λ (last-pt)
           (PTZ-New (PT:Done last-pt)))))
  (define (PTZ-Up ptz)
    ((PTZ-up ptz) (PTZ-focus ptz)))
  (define (PTZ-Down-Ctxt ptz)
    (match-define (PTZ ctxt foc up) ptz)
    (match-define (*PT:Ctxt _ _ gf k) foc)
    (PTZ (gf ctxt) k (λ (new-k) (PTZ ctxt (PT:Ctxt gf new-k) up))))
  (define (PTZ-Down-App ptz i)
    (match-define (PTZ ctxt foc up) ptz)
    (match-define (*PT:App _ A cs f) foc)
    (define-values (before i+after) (split-at cs i))
    (match-define (cons c_i after) i+after)
    (PTZ ctxt c_i
         (λ (new-i) (PTZ ctxt (PT:App A (append before (cons new-i after)) f) up))))

  (define (display-ptz ptz)
    (match (PTZ-focus ptz)
      [(*PT:Hole _ A)
       (for ([(k v) (in-hash (PTZ-ctxt ptz))])
         (printf "~a : ~a\n" k (syntax->datum v)))
       (printf "--------------------------------\n")
       (printf "~a\n" (syntax->datum A))]
      [(*PT:Done _ _ _)
       (printf "Proof complete.\n")]
      [_
       ;; XXX
       (printf "Not at hole.\n")]))

  (define (eval-proof-script #:err-stx [err-stx #f] pt psteps)
    (define last-ptz
      (for/fold ([ptz (PTZ-New pt)])
                ([pstep-stx (in-list psteps)])
        (display-ptz ptz)
        (eval-proof-step ptz pstep-stx)))
    (display-ptz last-ptz)
    (qed last-ptz))

  (define (eval-proof-step ptz pstep-stx)
    (printf "\nProof Step: ~a\n" (syntax->datum pstep-stx))
    ;; XXX Error handling on eval
    ;; XXX Namespace is wrong
    (define pstep (eval pstep-stx))
    ;; XXX Error handling on what pstep is and what it returns
    (pstep ptz))

  (define (PTZ-Done? ptz)
    (*PT:Done? (PTZ-focus ptz)))

  (define (qed ptz)
    (define up-ptz (next ptz))
    (unless (PTZ-Done? up-ptz)
      (error 'qed "Proof incomplete.\n"))
    (PTZ-focus up-ptz))

  (define (next ptz)
    (match (PTZ-focus ptz)
      [(*PT:Hole _ _) ptz]
      [(*PT:Exact _ _ _) (next (PTZ-Up ptz))]
      [(*PT:Ctxt hole? _ _ k)
       (next (if hole? (PTZ-Down-Ctxt ptz) (PTZ-Up ptz)))]
      [(*PT:App _ _ cs _)
       (next
        (or
         (for/or ([i (in-naturals)]
                  [c (in-list cs)])
           (if (PT-contains-hole? c)
               (PTZ-Down-App ptz i)
               #f))
         (PTZ-Up ptz)))]
      [(*PT:Done _ _ _)
       ptz]))

  (define (interactive ptz)
    (define cmd-stx
      (let/ec esc
        (parameterize ([current-eval
                        (λ (in)
                          (syntax-case in ()
                            [(_ . cmd)
                             (esc (datum->syntax anchor (syntax->datum #'cmd)))]))])
          (read-eval-print-loop))))
    (define next-ptz
      (eval-proof-step ptz cmd-stx))
    (if (PTZ-Done? next-ptz)
        next-ptz
        (interactive next-ptz)))

  (define ((fill t) ptz)
    (define new-foc (t (PTZ-ctxt ptz) (PTZ-focus ptz)))
    ;; XXX Maybe new-foc could be #f for failure?
    (next
     (struct-copy PTZ ptz [focus new-foc])))

  (define (intros names)
    (for/fold ([t nop])
              ([n (in-list names)])
      (compose (fill (intro n)) t)))

  (define ((intro [name #f]) ctxt pt)
    (match-define (*PT:Hole _ A) pt)
    (cur-match
     A
     [(forall (x:id : P:expr) body:expr)
      (let ()
        (define the-name (or name (syntax->datum #'x)))
        (PT:App A
                (list
                 (PT:Ctxt
                  (λ (old-ctxt)
                    (hash-set old-ctxt the-name #'P))
                  (PT:Hole #'body)))
                (λ (body-pf)
                  #`(λ (#,the-name : P) #,body-pf))))]))

  #;(define-syntax-rule (exact* a)
    (exact #'a))
  (define anchor #'a)
  (define (exact qa)
    (λ (ctxt pt)
      ;; NB: In principle, maybe exact should take syntax. But then the eval used to run the proof
      ;; script doesn't know that the syntax should be Cur syntax; by delaying datum->syntax here, we
      ;; can make it Cur syntax.
      (define a (datum->syntax anchor qa))
      (match-define (*PT:Hole _ A) pt)
      (define env
        (for/list ([(k v) (in-hash ctxt)])
          (cons (datum->syntax #f k) v)))
      (unless (cur-type-check? a A #:local-env env)
        (printf "~a ~a ~a~n" a A env)
        (error 'exact "~v does not have type ~v" a A))
      (PT:Exact A a)))

  (define (by-assumption ctxt pt)
    (match-define (*PT:Hole _ A) pt)
    (for/or ([(k v) (in-hash ctxt)]
             ;; TODO: Probably need to add local-env to cur-equal?
             #:when (cur-equal? v A))
      (PT:Exact A k)))

  (define (nop ptz) ptz))

(define-for-syntax (expand-proof-during-stxtime ty ps)
  (let ()
    (define init-pt
      (new-proof-tree #:of (cur-expand ty)))
    (define final-pt
      (eval-proof-script
       #:err-stx ps
       init-pt
       (syntax->list ps)))
    (define pf
      (proof-tree->complete-term
       #:err-stx ps
       final-pt))
    (printf "Term is: ~v\n" (syntax->datum pf))
    pf))

(module+ test
  (require
   "prop.rkt"
   "sugar.rkt")

  (define-theorem and-proj1
    (forall (A : Type) (B : Type) (c : (And A B)) Type)
    nop
    ;; XXX The use of fill is ugly. Perhaps could be infered
    (fill (intro 'A))
    (fill (intro))
    (intros '(c))
    nop
    ;interactive ; try (fill (exact 'A))
    ;; This works too
    #;(fill
     (exact 'A))
    ;; And this
    (fill by-assumption)))

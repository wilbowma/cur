#lang s-exp "../main.rkt"
;; Proof tree representation and top-level syntax

(require
 "../stdlib/sugar.rkt"
 "../easy-extension.rkt")

(provide
 (for-syntax
  #%app)
 define-theorem
 ntac)

(begin-for-syntax
  (provide
   ntac-syntax

   qed next

   (struct-out ntt)
   (struct-out ntt-hole)
   make-ntt-hole
   (struct-out ntt-exact)
   make-ntt-exact
   (struct-out ntt-context)
   make-ntt-context
   (struct-out ntt-apply)
   make-ntt-apply
   (struct-out ntt-done)
   make-ntt-done

   ;; proof tree zipper
   (struct-out nttz)
   make-nttz nttz-up nttz-down-context nttz-down-apply nttz-done?

   ;; In case someone wants to redefine define-theorem
   new-proof-tree
   proof-tree->complete-term
   eval-proof-script
   eval-proof-step
   ntac-proc)

  ;; NTac proof Tree
  (struct ntt (contains-hole? goal) #:transparent)

  ;; This is gross boilerplate to obtain default fields.
  (struct ntt-hole ntt () #:transparent #:constructor-name _ntt-hole)
  (define (make-ntt-hole goal)
    (_ntt-hole #t goal))

  (struct ntt-exact ntt (term) #:transparent #:constructor-name _ntt-exact)
  (define (make-ntt-exact goal term)
    (_ntt-exact #f goal term))

  (struct ntt-context ntt (env-transformer subtree) #:transparent #:constructor-name _ntt-context)
  (define (make-ntt-context f k)
    (_ntt-context (ntt-contains-hole? k) (ntt-goal k) f k))

  (struct ntt-apply ntt (subterms tactic) #:transparent #:constructor-name _ntt-apply)
  (define (make-ntt-apply goal subterms tactic)
    (_ntt-apply (ormap ntt-contains-hole? subterms) goal subterms tactic))

  (struct ntt-done ntt (subtree) #:transparent #:constructor-name _ntt-done)
  (define (make-ntt-done subtree)
    (when (ntt-contains-hole? subtree)
      (error 'ntt-done "Cannot construct done if hole present: ~v" subtree))
    (_ntt-done #f (ntt-goal subtree) subtree))

  (define (new-proof-tree goal)
    (make-ntt-hole goal))

  (require racket/trace)
  (define (proof-tree->complete-term pt [err-stx #f])
    (let loop ([pt pt])
      (match pt
        [(ntt-hole _ _)
         (raise-syntax-error 'define-theorem "attempt to save incomplete proof" err-stx)]
        [(ntt-exact _ _ a) a]
        [(ntt-context _ _ gf k)
         (loop k)]
        [(ntt-apply _ _ cs f)
         (apply f (map (λ (c) (loop c)) cs))]
        [(ntt-done _ _ k)
         (loop k)])))

    ;; NTac proof Tree Zipper
  (struct nttz (context focus prev) #:constructor-name _nttz)

  (require racket/dict)
  (define (identifier-hash) (make-immutable-custom-hash free-identifier=?))
  (define (make-nttz pt)
    (_nttz (identifier-hash) pt
         (λ (last-pt)
           (make-nttz (make-ntt-done last-pt)))))

  (define (nttz-up nttz)
    ((nttz-prev nttz) (nttz-focus nttz)))

  (define (nttz-down-context tz)
    (match-define (nttz context foc up) tz)
    (match-define (ntt-context _ _ gf k) foc)
    (_nttz (gf context) k (λ (new-k) (_nttz context (make-ntt-context gf new-k) up))))

  (define (nttz-down-apply tz i)
    (match-define (nttz context foc up) tz)
    (match-define (ntt-apply _ a cs f) foc)
    (define-values (before i+after) (split-at cs i))
    (match-define (cons c_i after) i+after)
    (_nttz context c_i
         (λ (new-i) (_nttz context (make-ntt-apply a (append before (cons new-i after)) f) up))))

  (define (nttz-done? tz)
    (ntt-done? (nttz-focus tz)))

  (define (ntac-proc ty ps)
    (let ()
      (define init-pt
        (new-proof-tree (cur-expand ty)))
      (define final-pt
        (eval-proof-script
         init-pt
         (syntax->list ps)
         ps))
      (define pf
        (proof-tree->complete-term
         final-pt
         ps))
      pf))

  (define (eval-proof-script pt psteps [err-stx #f])
    (define last-nttz
      (for/fold ([nttz (make-nttz pt)])
                ([pstep-stx (in-list psteps)])
        (eval-proof-step nttz pstep-stx)))
    (qed last-nttz err-stx))

  (define (eval-proof-step nttz pstep-stx)
    ;; XXX Error handling on eval
    ;; XXX Namespace is wrong
    (define pstep (eval pstep-stx))
    ;; XXX Error handling on what pstep is and what it returns
    (pstep nttz))

  (define (next tz)
    (match (nttz-focus tz)
      [(ntt-hole _ _) tz]
      [(ntt-exact _ _ _) (next (nttz-up tz))]
      [(ntt-context hole? _ _ k)
       (next (if hole? (nttz-down-context tz) (nttz-up tz)))]
      [(ntt-apply _ _ cs _)
       (next
        (or
         (for/or ([i (in-naturals)]
                  [c (in-list cs)])
           (if (ntt-contains-hole? c)
               (nttz-down-apply tz i)
               #f))
         (nttz-up tz)))]
      [(ntt-done _ _ _)
       tz]))

  (define (qed nttz [err-stx #f])
    (define up-nttz (next nttz))
    (unless (nttz-done? up-nttz)
      (raise-syntax-error 'qed "Proof incomplete.\n" err-stx))
    (nttz-focus up-nttz))

  (define anchor #'a)
  (define (ntac-syntax syn)
    (datum->syntax anchor (syntax->datum syn))))

;; Syntax
(define-syntax (define-theorem stx)
  (syntax-parse stx
    [(_ x:id ty ps ...)
     (quasisyntax/loc stx
       (begin (define x (ntac ty ps ...))
              (:: x ty)))]))

;; For inline ntac
(define-syntax (ntac stx)
  (syntax-case stx ()
    [(_ ty . pf) (ntac-proc #'ty #'pf)]))

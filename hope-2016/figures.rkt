define-language stlc
  τ ::= 1  | (τ * τ) | (τ -> τ)
  e ::= () | (cons e e) | (prj i e) |  (λ (x : τ) e) | (e e)


define-language-sugar (let x = e₁ in e₂) ((λ (x : τ) e₂) e₁)
  where τ = infer-type e₁

define-theorem Type-Soundness
  if Γ ⊢ e : τ then e →* v


(begin-for-syntax
  ;; A function in the meta language
  (define (transform-lambda obj)
    (syntax-case obj (:)
      [(lambda (x : t) e)
       #'(λ (x : t) e)])))

;; A syntactic hook in the object language
(define-syntax lambda transform-lambda)

(lambda (x : Nat) z)
;; causes the computation, at compile-time:
(transform-lambda #'(lambda (x : Nat) z))

cur-expand : SyntaxObject -> SyntaxObject

(begin-for-syntax
  (define (solver type)
    (syntax-case (cur-expand type) ()
      [(Unv i) ....]
      [(Π (x : t) e) ....]
      [(e₁ e₂) ....]
      [x ....])))

cur-type-infer : SyntaxObject -> SyntaxObject

(define-syntax (let obj)
  (syntax-case obj (= in)
    [(let (x = e₁) in e₂)
     #`((λ (x : #,(cur-type-infer #'e₁)) e₂) e₁)]))

cur-type-check? : SyntaxObject -> SyntaxObject -> boolean?

(define-syntax (:: obj)
  (syntax-case obj ()
    [(:: e t)
     (if (not (cur-type-check #'e #'t))
         (raise-type-error
          "~a does not have type expected type ~a"
          #'e #'t))]))

cur-normalize : SyntaxObject -> SyntaxObject

(define-syntax run cur-normalize)
(define (add2 (n : Nat)) (run (+ (s (s z)) n)))


(define (+ (n1 : Nat) (n2 : Nat))
  (elim Nat (lambda (x : Nat) Nat)
    (n2
     (lambda (x : Nat) (ih : Nat) (s ih)))
    n1))

(define (+ (n1 : Nat) (n2 : Nat))
  (match n1
    [z n2]
    [(s x) (s (+ x n2))]))

(define-syntax (match obj)
  (syntax-case obj ()
    [(_ e clause* ...)
     (let* ([clauses (parse-clauses #'(clause* ...))]
            [R (infer-result clauses)]
            [D (cur-type-infer #'e)]
            [motive #`(lambda (x : #,D) #,R)])
       #`(elim #,D #,motive
               #,(map (clause->method D motive) clauses)
               e))]))

(define (+ (n1 : Nat) (n2 : Nat))
  (match n1
    [z n2]
    [(s x) (s (+ x n2))]))

(require
 (rename-in cur [define base-define]))

(define-syntax (define obj)
  (syntax-case obj ()
    [(_ (name args ...) body)
     #`(base-define (name args ...)
         #,(parameterize ([current-function-name #'name]
                          [current-function-args #'(args ...)])
            #'body))]))

(ntac (forall (A : Type) (a : A) A)
  (by-intro A)
  (by-intro b)
  by-assumption)

;; generates:
(lambda (A : Type) (b : A) b)

(define-syntax (ntac obj)
  (syntax-case obj ()
    [(_ goal . script)
;;  ↓ note the lack of #'
     (ntac-interp #'goal #'script)]))

(begin-for-syntax
  (define (ntac-interp goal script)
    (define pt (new-proof-tree (cur-expand goal)))
    (define last-nttz
      (for/fold ([nttz (make-nttz pt)])
                ([tactic-stx (syntax->list script)])
        (run-tactic nttz tactic-stx)))
    (proof-tree->term (finish-nttz last-nttz))))

(begin-for-syntax
  (define (run-tactic nttz tactic-stx)
    (define tactic (eval tactic-stx))
    (tactic nttz)))

(define-tactical ((intro [name #f]) env pt)
  (define goal (ntt-goal pt))
  (ntac-match goal
   [(forall (x : P) body)
    (define the-name (syntax->datum (or name #'x)))
    (make-ntt-apply
     goal
     (λ (body-pf)
       #`(λ (#,the-name : P) #,body-pf))
     (list
      (make-ntt-env
       (λ (old-env)
         (hash-set old-env the-name #'P))
       (make-ntt-hole #'body))))]))

define-language stlc
  #:vars (x)
  #:output-coq "stlc.v"
  #:output-latex "stlc.tex"
  type (A B) ::= unitty (* A A) (-> A B)
  term (e)   ::= x unit (cons e e) (fst e) (snd e)
                 (lambda (#:bind x : A) e) (app e e)

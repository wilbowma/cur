#lang s-exp "../cur.rkt"
(provide
  ->
  ->*
  forall*
  lambda*
  (rename-out
    [-> →]
    [->* →*]
    [lambda* λ*]
    [forall* ∀*])
  #%app
  define
  elim
  define-type
  case
  case*
  let

  ;; type-check
  ::

  ;; reflection in syntax
  run
  step
  step-n
  query-type
  )

(require
  (only-in "../cur.rkt"
    [elim real-elim]
    [#%app real-app]
    [define real-define]))


(define-syntax (-> syn)
  (syntax-case syn ()
    [(_ t1 t2) #`(forall (#,(gensym) : t1) t2)]))

(define-syntax ->*
  (syntax-rules ()
    [(->* a) a]
    [(->* a a* ...)
     (-> a (->* a* ...))]))

(define-syntax forall*
  (syntax-rules (:)
    [(_ (a : t) (ar : tr) ... b)
     (forall (a : t)
        (forall* (ar : tr) ... b))]
    [(_ b) b]))

(define-syntax lambda*
  (syntax-rules (:)
    [(_ (a : t) (ar : tr) ... b)
     (lambda (a : t)
       (lambda* (ar : tr) ... b))]
    [(_ b) b]))

(define-syntax (#%app syn)
  (syntax-case syn ()
    [(_ e) #'e]
    [(_ e1 e2)
     #'(real-app e1 e2)]
    [(_ e1 e2 e3 ...)
     #'(#%app (#%app e1 e2) e3 ...)]))

(define-syntax define-type
  (syntax-rules ()
    [(_ (name (a : t) ...) body)
     (define name (forall* (a : t) ... body))]
    [(_ name type)
     (define name type)]))

(define-syntax (define syn)
  (syntax-case syn ()
    [(define (name (x : t) ...) body)
     #'(real-define name (lambda* (x : t) ... body))]
    [(define id body)
     #'(real-define id body)]))

(define-syntax-rule (elim t1 t2 e ...)
  ((real-elim t1 t2) e ...))

(begin-for-syntax
  (define (rewrite-clause clause)
    (syntax-case clause (: IH:)
      [((con (a : A) ...) IH: ((x : t) ...) body)
       #'(lambda* (a : A) ... (x : t) ... body)]
      [(e body) #'body])))

;; TODO: Expects clauses in same order as constructors as specified when
;; TODO: inductive D is defined.
;; TODO: Assumes D has no parameters
(define-syntax (case syn)
  ;; duplicated code
  (define (clause-body syn)
    (syntax-case (car (syntax->list syn)) (: IH:)
      [((con (a : A) ...) IH: ((x : t) ...) body) #'body]
      [(e body) #'body]))
  (syntax-case syn (=>)
    [(_ e clause* ...)
     (let* ([D (type-infer/syn #'e)]
            [M (type-infer/syn (clause-body #'(clause* ...)))]
            [U (type-infer/syn M)])
       #`(elim #,D #,U (lambda (x : #,D) #,M) #,@(map rewrite-clause (syntax->list #'(clause* ...)))
               e))]))

(define-syntax (case* syn)
  (syntax-case syn ()
    [(_ D U e (p ...) P clause* ...)
     #`(elim D U P #,@(map rewrite-clause (syntax->list #'(clause* ...))) p ... e)]))

(begin-for-syntax
  (define-syntax-class (gamma/cur-expr env)
    (pattern e:expr
             #:fail-unless (parameterize ([gamma env])
                             (type-infer/syn #'e))
             (format "Could not infer a type for Cur term ~a"
                     (syntax->datum #'e))
             #:attr type (parameterize ([gamma env])
                           (type-infer/syn #'e))))
  (define-syntax-class cur-expr
    (pattern e
             #:declare e (gamma/cur-expr (gamma))
             #:attr type #'e.type))
  (define-syntax-class let-clause
    (pattern
     (~or ((x:id (~commit (~datum :)) t:cur-expr) e) (x:id e:cur-expr))
     #:fail-unless
     (or (not (attribute t))
         (type-check/syn? #'e #'t))
     (format "Term ~a does not have expected type ~a. Inferred type was ~a"
             (cur->datum #'e) (cur->datum #'t) (cur->datum (type-infer/syn #'e)))
     #:attr id #'x
     #:attr expr #'e
     #:attr type (if (attribute t) #'t #'e.type))))
(define-syntax (let syn)
  (syntax-parse syn
    [(let (c:let-clause ...) body)
     #'((lambda* (c.id : c.type) ... body) c.expr ...)]))

#;(define-syntax (let syn)
  (syntax-parse syn
    [(let ([x:id e:cur-expr]) body)
     #:declare body (gamma/cur-expr (extend-Γ/syn gamma #'x #'e.type))
     #'((lambda (x : e.type) body) e)]))

;; Normally type checking will only happen if a term is actually used. This forces a term to be
;; checked against a particular type.
(define-syntax (:: syn)
  (syntax-case syn ()
    [(_ pf t)
     (begin
       ;; TODO: Code duplication in let-clause pattern
       (unless (type-check/syn? #'pf #'t)
         (raise-syntax-error
           '::
           (format "Term ~a does not have expected type ~a. Inferred type was ~a"
                   (cur->datum #'pf) (cur->datum #'t) (cur->datum (type-infer/syn #'pf)))
           syn))
       #'(void))]))

(define-syntax (run syn)
  (syntax-case syn ()
    [(_ expr) (normalize/syn #'expr)]))

(define-syntax (step syn)
  (syntax-case syn ()
    [(_ expr)
     (let ([t (step/syn #'expr)])
       (displayln (cur->datum t))
       t)]))

(define-syntax (step-n syn)
  (syntax-case syn ()
    [(_ n expr)
     (for/fold
       ([expr #'expr])
       ([i (in-range (syntax->datum #'n))])
       #`(step #,expr))]))

(define-syntax (query-type syn)
  (syntax-case syn ()
    [(_ term)
     (begin
       (printf "\"~a\" has type \"~a\"~n" (syntax->datum #'term) (syntax->datum (type-infer/syn #'term)))
       ;; Void is undocumented and a hack, but sort of works
       #'(void))]))

(module+ test
  (require rackunit (submod ".."))

  (check-equal?
    ((λ* (x : (Type 1)) (y : (∀* (x : (Type 1)) (Type 1))) (y x))
     Type
     (λ (x : (Type 1)) x))
    Type)

  (check-equal?
    ((λ* (x : (Type 1)) (y : (→* (Type 1) (Type 1))) (y x))
     Type
     (λ (x : (Type 1)) x))
    Type)

  (check-equal?
    ((λ* (x : (Type 1)) (y : (→ (Type 1) (Type 1))) (y x))
     Type
     (λ (x : (Type 1)) x))
    Type)

  (check-equal?
    (let ([x Type])
      x)
    Type)

  (check-equal?
    (let ([(x : (Type 1)) Type]
          [y (λ (x : (Type 1)) x)])
      (y x))
    Type)

  ;; check that raises decent syntax error
  ;; Can't use this because (lambda () ...) and thunk are not things in Cur at runtime
  (let ([x : (Type 1) Type]
        [y (λ (x : (Type 1)) x)])
    (y x))
  #;(check-exn
    ;exn:fail:syntax?
    )

  ;; check that raises type error
  #;(check-exn
    exn:fail:syntax?
    (let ([x uninferrable-expr]
          [y (λ (x : (Type 1)) x)])
      (y x)))

  )

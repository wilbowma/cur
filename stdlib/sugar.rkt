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

  ;; reflection in syntax
  run
  step
  step-n
  query-type

  ;; don't use these
  define-theorem
  qed
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
  (define-syntax-class let-clause
    (pattern
      (~or (x:id e) ((x:id (~datum :) t) e))
      #:attr id #'x
      #:attr expr #'e
      #:attr type (cond
                    [(attribute t) #'t]
                    [(type-infer/syn #'e)]
                    [else
                      (raise-syntax-error
                        'let
                        "Could not infer type of let bound expression"
                        #'e (quasisyntax/loc #'x (x e)))]))))
(define-syntax (let syn)
  (syntax-parse syn
    [(let (c:let-clause ...) body)
     #'((lambda* (c.id : c.type) ... body) c.e ...)]))

(define-syntax-rule (define-theorem name prop)
  (define name prop))

(define-syntax (qed stx)
  (syntax-case stx ()
    [(_ t pf)
     (begin
       (unless (type-check/syn? #'pf #'t)
         (raise-syntax-error 'qed "Invalid proof"
           #'pf #'t))
       #'pf)]))

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
    (let ([x Type]
          [y (λ (x : (Type 1)) x)])
      (y x))
    Type)

  (check-equal?
    (let ([(x : (Type 1)) Type]
          [y (λ (x : (Type 1)) x)])
      (y x))
    Type)

  ;; check that raises decent syntax error
  ;; Can't use this because (lambda () ...) and thunk are not things in Cur at runtime
  #;(check-exn
    exn:fail:syntax?
    (let ([x : (Type 1) Type]
          [y (λ (x : (Type 1)) x)])
      (y x)))

  ;; check that raises type error
  #;(check-exn
    exn:fail:syntax?
    (let ([x uninferrable-expr]
          [y (λ (x : (Type 1)) x)])
      (y x)))

  )

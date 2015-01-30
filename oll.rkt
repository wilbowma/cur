#lang s-exp "redex-curnel.rkt"
;; OLL: The OTT-Like Library
(require "sugar.rkt" "nat.rkt")

;; TODO: Can't export var, avar because technically these aren't
;; defined....
;; REALLY NEED TO FIX THAT
(provide define-relation define-language)

(begin-for-syntax
  (define-syntax-class dash
    (pattern x:id
           #:fail-unless (regexp-match #rx"-+" (symbol->string (syntax-e #'x)))
           "Invalid dash"))

  (define-syntax-class decl (pattern (x:id (~datum :) t:id)))

  ;; TODO: Automatically infer decl ... by binding all free identifiers?
  (define-syntax-class inferrence-rule
    (pattern (d:decl ...
              x*:expr ...
              line:dash lab:id
              (name:id y* ...))
              #:with rule #'(lab : (forall* d ...
                                     (->* x* ... (name y* ...)))))))
(define-syntax (define-relation syn)
  (syntax-parse syn
    [(_ (n:id types* ...) rules:inferrence-rule ...)
     #:fail-unless (andmap (curry equal? (length (syntax->datum #'(types* ...))))
                           (map length (syntax->datum #'((rules.y* ...)
                                                          ...))))
     "Mismatch between relation declared and relation definition"
     #:fail-unless (andmap (curry equal? (syntax->datum #'n))
                           (syntax->datum #'(rules.name ...)))
     "Mismatch between relation declared name and result of inference rule"
      #`(data n : (->* types* ... Type)
          rules.rule ...)]))

(begin-for-syntax
  (require racket/syntax)
  (define (new-name name . id*)
    (apply format-id name (for/fold ([str "~a"])
                                  ([_ id*])
                          (string-append str "-~a")) name (map syntax->datum id*)))

  (define (fresh-name id)
    (datum->syntax id (gensym (syntax->datum id)))))

(module+ test
  (begin-for-syntax
    (require rackunit)
    (define (check-id-equal? v1 v2)
      (check-equal?
        (syntax->datum v1)
        (syntax->datum v2)))
    (define (check-id-match? v1 v2)
       (check-regexp-match
         v1
         (symbol->string (syntax->datum v2))))
    (check-id-match?
      #px"term\\d+"
      (fresh-name #'term))
    (check-id-equal?
      #'stlc-lambda
      (new-name #'stlc #'lambda))
    (check-id-match?
      #px"stlc-term\\d+"
      (new-name #'stlc (fresh-name #'term)))))

(begin-for-syntax
  (define lang-name (make-parameter #'name))
  (define nts (make-parameter (make-immutable-hash)))

  (define-syntax-class nt
    (pattern e:id #:fail-unless (hash-has-key? (nts) (syntax->datum #'e)) #f
             #:attr name (hash-ref (nts) (syntax->datum #'e))
             #:attr type (hash-ref (nts) (syntax->datum #'e))))

  (define (flatten-args arg arg*)
    (for/fold ([ls (syntax->list arg)])
              ([e (syntax->list arg*)])
      (append ls (syntax->list e))))

  (define-syntax-class (right-clause type)
    #;(pattern (~datum var)
             #:attr clause-context #`(#,(new-name (lang-name) #'var) :
                                      (-> #,(hash-ref (nts) 'var) #,(hash-ref (nts) type)))
             #:attr name #'var
             #:attr arg-context #'(var))
    (pattern e:nt
             #:attr clause-context #`(#,(new-name #'e.name #'->
                                                  (hash-ref (nts) type)) :
                                      (-> e.type #,(hash-ref (nts) type)))
             #:attr name (fresh-name #'e.name)
             #:attr arg-context #'(e.type))
    (pattern x:id
             #:attr clause-context #`(#,(new-name (lang-name) #'x) :
                                      #,(hash-ref (nts) type))
             #:attr name (new-name (lang-name) #'x)
             #:attr arg-context #'())
    (pattern ((~var e (right-clause type)) (~var e* (right-clause type)) ...)
             #:attr name (fresh-name #'e.name)
             #:attr clause-context #`(e.name : (->* #,@(flatten-args #'e.arg-context #'(e*.arg-context ...))
                                                    #,(hash-ref (nts) type)))
             #:attr arg-context #`(#,@(flatten-args #'e.arg-context #'(e*.arg-context ...)))))

  (define-syntax-class (right type)
    (pattern ((~var r (right-clause type)) ...)
             #:attr clause #'(r.clause-context ...)))

  #;(define-syntax-class left
    (pattern (type:id (nt*:id ...+))
             #:do ))

  (define-syntax-class nt-clauses
    (pattern ((type:id (nt*:id ...+)
              (~do (nts (for/fold ([ht (nts)])
                                  ([nt (syntax->datum #'(type nt* ...))])
                          (hash-set ht nt (new-name (lang-name) #'type)))))
              (~datum ::=)
              . (~var rhs* (right (syntax->datum #'type)))) ...)
             #:with defs (with-syntax ([(name* ...)
                                        (map (λ (x) (hash-ref (nts) x))
                                             (syntax->datum #'(type ...)))])
                           #`((data name* : Type . rhs*.clause)
                              ...)))))

;; TODO: For better error messages, add context, rename some of these patterns. e.g.
;;    (type (meta-vars) ::= ?? )
(define-syntax (define-language syn)
  (syntax-parse syn
    [(_ name:id (~do (lang-name #'name))
        (~do (nts (hash-set (make-immutable-hash) 'var #'var)))
        (~optional (~seq #:vars (x*:id ...)
           (~do (nts (for/fold ([ht (nts)])
                               ([v (syntax->datum #'(x* ...))])
                       (hash-set ht v (hash-ref ht 'var)))))))
        . clause*:nt-clauses)
     #`(begin . clause*.defs)]))

(data var : Type (avar : (-> nat var)))

;;Type this:

(define-language stlc
  #:vars (x)
  (val  (v)   ::= true false)
  (type (A B) ::= bool (-> A B))
  (term (e)   ::= x v (e e) (lambda (x : A) e)))

;;This gets generated:

#;
(begin
  (data stlc-val : Type
    (stlc-true : stlc-val)
    (stlc-false : stlc-val))

  (data stlc-type : Type
    (stlc-bool : stlc-type)
    (stlc--> : (->* stlc-type stlc-type stlc-type)))

  (data stlc-term : Type
    (var-->-stlc-term : (-> var stlc-term))
    (stlc-val-->-stlc-term : (-> stlc-val stlc-term))
    (stlc-term2151 : (->* stlc-term stlc-term stlc-term))
    (stlc-lambda : (->* var stlc-type stlc-term stlc-term))))

(begin-for-syntax
  (define orig-insp (variable-reference->module-declaration-inspector
    (#%variable-reference)))

  (define (disarm syn) (syntax-disarm syn orig-insp))

  ;; TODO: Pull expand, perhaps list of literals, into a library.
  (define (expand syn)
    (disarm (local-expand syn 'expression (syntax-e #'(lambda forall data case fix Type #%app #%top)))))

  (define (output-coq syn)
    (syntax-parse (expand syn)
       [((~literal lambda) ~! (x:id (~datum :) t) body:expr)
        (format "(fun ~a : ~a => ~a)" (syntax-e #'x) (output-coq #'t)
                (output-coq #'body))]
       [((~literal forall) ~! (x:id (~datum :) t) body:expr)
        (format "(forall ~a : ~a, ~a)" (syntax-e #'x) (output-coq #'t)
                (output-coq #'body))]
       [((~literal data) ~! n:id (~datum :) t (x*:id (~datum :) t*) ...)
        (format "Inductive ~a : ~a :=~n~a."
                (syntax-e #'n)
                (output-coq #'t)
                (string-trim
                  (for/fold ([strs ""])
                            ([clause (syntax->list #'((x* : t*) ...))])
                    (syntax-parse clause
                      [(x (~datum :) t)
                       (format "~a~a : ~a~n| " strs (syntax-e #'x)
                               (output-coq #'t))]))
                  #px"\\s\\| $"
                  #:left? #f))]
       ;; TODO: Add "case". Will be slightly tricky since the syntax is
       ;; quite different from Coq.
       [(e1 e* ...)
        (format "(~a~a)" (output-coq #'e1)
          (for/fold ([strs ""])
                    ([arg (syntax->list #'(e* ...))])
            (format "~a ~a" strs (output-coq arg))))]
       [e:id (format "~a" (syntax->datum #'e))])))

(define-syntax (generate-coq syn)
  (syntax-parse syn
    [(_ (~optional (~seq #:file file)) body:expr)
     (parameterize ([current-output-port (if (attribute file)
                                             (syntax->datum #'file)
                                             (current-output-port))])
       (displayln (output-coq #'body))
       #'Type)]))

(module+ test
  (require "sugar.rkt")
  (begin-for-syntax
    (require rackunit)
    (check-equal?
      (format "Inductive nat : Type :=~nz : nat.")
      (output-coq #'(data nat : Type (z : nat))))
    (check-regexp-match
      "(forall .+ : Type, Type)"
      (output-coq #'(-> Type Type)))
    ;; TODO: Not sure why these tests are failing.
    (let ([t (output-coq #'(define-relation (meow gamma term type)
                             [(g : gamma) (e : term) (t : type)
                              --------------- T-Bla
                              (meow g e t)]))])
      (check-regexp-match
        "Inductive meow : (forall temp. : gamma, (forall temp. : term, (forall temp. : type, Type))) :="
        (first (string-split t "\n")))
      (check-regexp-match
        "T-Bla : (forall g : gamma, (forall e : term, (forall t : type, (meow g e t))))\\."
        (second (string-split t "\n"))))))

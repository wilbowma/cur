#lang s-exp "redex-core.rkt"
(require "sugar.rkt")
(provide define-relation)

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

;; TODO: Add BNF syntax, with binders?
;; (define-language name
;     #:literal (-> lambda)
;     #:var (x)
;     (v : val  ::= true false)
;     (t : type ::= bool (-> t t))
;     (e : term ::= var (e e) (lambda (x : t) e)))
;  =>
;  (data var : Type (avar : (-> nat var)))
;  (also generate gamma, function, etc.)
;  (data name-val : Type
;     (name-true : val)
;     (name-false : val))
;  (data name-term : Type
;     (name-term-var : (-> var name-term))
;     (name-term1 : (->* name-term name-term name-term))
;     (name-lambda : (->* var name-type name-term name-term)))
;  (data name-type : Type
;     (name-bool : type)
;     (name--> : (-> name-type name-type)))

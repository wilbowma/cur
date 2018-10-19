#lang cur

(require
 (only-in cur/stdlib/sugar -> #%app)
 (for-syntax
  racket/function
  syntax/stx
  syntax/free-vars
  syntax/parse))

#|
Syntax for BNF grammars in Cur.
|#

;; Test 1
;;
;; (define-data/bnf Nat (N) ::= z (s N))

;; Should produce:
;;
;; (data Nat : (Type 0)
;;   (z : Nat)
;;   (s : (Π (x : Nat) Nat)))
;;
;; Should also reserve N as a BNF identifier, forbidding later re-definition of
;; N, and reserving N for using in the BNF macro.

(begin-for-syntax
  (define-syntax-rule (observe stx)
    (begin
      (displayln #'stx)
      (let ([x stx])
        (displayln x)
        x)))

  (define-syntax-class bnf-nt
    (pattern x:id
             #:when (bnf-nonterminal? (syntax-local-value #'x (lambda () #f)))))

  (define-syntax-class free-id
    (pattern x:id
             #:when (with-handlers ([exn:fail:syntax:unbound? (lambda (_) #t)])
                      (local-expand #'x 'expression null)
                      #f)))

  (define-syntax-class cur-term
    (pattern e:expr #:when (with-handlers ([exn:fail:syntax:unbound? (lambda (_) #f)])
                             (cur-type-infer #'e))))

  (define-syntax-class cur-type
    (pattern e:expr #:when (with-handlers ([exn:fail:syntax:unbound? (lambda (_) #f)])
                             (cur-type-infer #'e))))

  (require (for-syntax racket/base))

  (define-syntax ~of-cur-type
    (pattern-expander
     (lambda (stx)
       (syntax-case stx ()
         [(_ e type)
          #'(~var e (of-cur-type #'type))]))))

  (define-syntax-class (of-cur-type t)
    (pattern e:expr #:when (cur-type-check? #'e t)))

  ;; TODO: Enrich with
  ;; - binding annotations
  ;; - constructor name annotations

  ;; A BNF-Expr is a syntax object representing one of:
  ;; - A BNF nonterminal
  ;; - Free-Id
  ;; - A Cur Type
  ;; TODO: No recursive structure? Couldn't figure out how to interpret it.

  ;; A BNF-Arg-Expr is a BNF-Expr excluding Free-Id
  ;; - A BNF nonterminal
  ;; - A Cur Type

  ;; Parse a BNF-Arg-Expr as into the right constructor when parsing a BNF-Sexpr-Production
  (define (parse-bnf-arg-expr nt stx)
    (syntax-parse stx
      [N:bnf-nt (bnf-nonterminal-name (syntax-local-value #'N))]
      [x:free-id
       (bnf-nonterminal-name nt)]
      [e:cur-type stx]))

  ;; A BNF-Production is (a syntax object representing a) one of:
  ;;   - BNF-Expr
  ;;   - A list of BNF-Arg-Exprs with a Free-Id at some position in the list
  ;;     (BNF-Arg-Expr ... Free-Id BNF-Arg-Expr ...)
  (define (bnf-production-sexprize nt stx)
    (if (stx-pair? stx)
        (let-values ([(ctor args)
                      (for/fold ([a #f]
                                 [ls '()])
                                ([arg (syntax->list stx)])
                        (syntax-parse arg
                          ;; NB: Order of these clauses matters
                          [(~or e:bnf-nt e:cur-type)
                           (values a (cons #'e ls))]
                          [x:free-id
                           #:when (ormap (curry free-identifier=? #'x) (syntax->list (bnf-nonterminal-ids nt)))
                           (values a (cons #'x ls))]
                          [x:free-id
                           (values arg ls)]))])
          #`(#,ctor #,@(reverse args)))
        stx))

  ;; A BNF-Sexpr-Production is a BNF-Production but the Free-Id must always
  ;; appear in head position.
  ;;   - BNF-Expr
  ;;   - A list of BNF-Exprs preceeded by a Free-Id
  ;;     (Free-Id BNF-Arg-Expr ...)

  ;; A BNF-SexprProduction is parsed into the bnf-production structure, which records
  ;; a unique constructor name for the Cur representation of the BNF production
  ;; and the Cur type.
  ;; The Constructor ctor is a canonical identifier for this production.
  (struct bnf-production (ctor type))

  ;; Every production belongs to a nonterminal, which also represents the type of the production.
  ;; parse-bnf-production takes this bnf-nonterminal, and a BNF-Production, and
  ;; produces a bnf-production structure.
  (define (parse-bnf-production nt stx)
    (syntax-parse (bnf-production-sexprize nt stx)
      [(x:free-id e ...)
       (let ([ctor (syntax/loc stx x)])
         (bnf-production
          ctor
          #`(-> #,@(map (curry parse-bnf-arg-expr nt) (attribute e))
                #,(bnf-nonterminal-name nt))))]
      [_
       (parse-bnf-expr nt stx)]))

    ;; Parse a BNF-Expr as a BNF-Production
  (define (parse-bnf-expr nt stx)
    (syntax-parse stx
      [N:bnf-nt
       (let* ([N-type (bnf-nonterminal-name (syntax-local-value #'N))]
              [nt-type (bnf-nonterminal-name nt)]
              [ctor (format-id stx "~a->~a" N-type nt-type)])
         (bnf-production
          ctor
          (quasisyntax/loc stx
            (-> N-type #,nt-type))))]
      [x:free-id
       (bnf-production
        (syntax/loc stx x)
        (bnf-nonterminal-name nt))]
      [A:cur-type
       (let* ([nt-type (bnf-nonterminal-name nt)]
              [ctor (format-id stx "~a->~a" #'A nt-type)])
         (bnf-production
          ctor
          (quasisyntax/loc stx
            (-> e #,nt-type))))]))

  (struct bnf-nonterminal (name ids)
    #:property prop:procedure
    (lambda (stx)
      (raise-syntax-error
       (format "~a is a reserved name and can only be used in a BNF literal."
               (stx-car stx)))))

  ;; TODO: These are not goign to be free-ids anymore, but bound ids, i.e., constructors for nt.
  ;; define the bnf literal data and rewrite
  (define (parse-bnf-literal nt stx)
    (syntax-parse (bnf-production-sexprize nt stx)
      ;; TODO: Duplicate between this and earlier parsing to constructor ctors
      [(x:free-id e ...)
       (quasisyntax/loc stx
         (x
          #,@(map parse-bnf-literal (attribute e))))]
      [x:free-id
       this-syntax]
      [e:cur-term
       (displayln (bnf-nonterminal-name nt))
       (displayln (cur-type-infer #'e))
       (let* ([nt-type (bnf-nonterminal-name nt)]
              [ctor (format-id stx "~a->~a" (cur-type-infer #'e) nt-type)])
         (quasisyntax/loc stx
           (#,ctor e)))])))

(define-syntax (bnf stx)
  (syntax-parse stx
    [(_ name:id literal)
     (parse-bnf-literal (syntax-local-value #'name) #'literal)]))
;;; Here's how bnf should work.
;;; First, is s-exprizes the literal.
;;; Next, it walks the tree.
;;;   Any sexpr whose head is a bnf constructor is left alone at the top-level.
;;;   Any sexpr whose head is not a bnf constructor must be a cur-type, and is
;;;   replaced by the appropriate constructor

(define-syntax (define-data/bnf stx)
  (syntax-parse stx
    [(_ name:id (nt:id nts:id ...)
        (~optional (~datum ::=))
        e
        ...
        ;; TODO: Check that f has the right type?
        #;(~optional (~seq #:parser f)))
     #:do [(define bnf-nt (bnf-nonterminal #'name #'(nt nts ...)))
           (define bnf-prods (map (curry parse-bnf-production bnf-nt) (attribute e)))]
     #:with (c ...) (map bnf-production-ctor bnf-prods)
     #:with (t ...) (map bnf-production-type bnf-prods)
     (quasisyntax/loc this-syntax
       (begin
         (define-syntax nt #,bnf-nt)
         (define-syntax nts (make-variable-like-transformer #'nt)) ...

         #,(quasisyntax/loc this-syntax
             (define-datatype name : #,(syntax/loc this-syntax (Type 0)) (c : t) ...))))]))

(require (only-in racket/base module+))

(module+ test
  (require (for-syntax (only-in racket/list first)))
  (define-data/bnf Nat (N) ::= z (s N)
   ; #:parser (lambda (stx ctors) stx)
    )
  z
  (bnf N z)
  (s z)
  #;(bnf N (s z))

  (define-data/bnf List (L) ::= nil (cons N L)
    ; #:parser (lambda (stx ctors) stx)
    )
  nil
  (cons z nil)
  ;(cons nil nil) -> type error

;  (require (for-syntax racket/dict racket/list syntax/id-table))
;  (define-data/bnf Arith-Term (e) ::= Nat (e + e) (e - e) (e * e) error
;    #:parser (lambda (stx ctors)
;               (define d
;                 (make-immutable-free-id-table
;                  (list
;                   (cons #'+ (second ctors))
;                   (cons #'- (third ctors))
;                   (cons #'* (fourth ctors)))))
;               (let loop ([stx stx])
;                 (syntax-parse stx
;                   #:literals (+ - * error)
;                   [(~of-cur-type e Nat)
;                    (quasisyntax/loc stx
;                      (#,(first ctors)
;                       e))]
;                   ;; TODO: Inline operators
;                   [((~and x (~or + - *)) e1 e2)
;                    (quasisyntax/loc stx
;                      (#,(dict-ref d #'x)
;                       #,(loop #'e1)
;                       #,(loop #'e2)))]
;                   [error stx])))
;    )
;
;  (Nat->Arith-Term z)
;  (+ (Nat->Arith-Term z) (Nat->Arith-Term z))
;  (bnf e z)
;  (bnf e (+ z z))
;  (bnf e (+ (* z (s z)) (s z)))
  )

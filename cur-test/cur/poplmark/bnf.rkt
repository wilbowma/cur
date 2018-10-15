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

  (define-syntax-class cur-type
    (pattern e:expr #:when (cur-type-infer #'e)))

  ;; TODO: Enrich with
  ;; - binding annotations
  ;; - constructor name annotations

  ;; A BNF-Expr is a syntax object representing one of:
  ;; - A BNF nonterminal
  ;; - Free-Id
  ;; - A Cur Type
  ;; TODO: No recursive structure? Couldn't figure out how to interpret it.

  ;; A BNF-Production is (a syntax object representing a) one of:
  ;;   - BNF-Expr
  ;;   - A list starting with a Free-Id followed by BNF-Exprs, i.e.,
  ;;     (Free-Id BNF-Expr ...)
  ;;   TODO: Loosen final clause to allow mix fix BNF-Productions?
  ;;
  ;; A BNF-Production is parsed into the bnf-production structure, which records
  ;; a unique constructor name for the Cur representation of the BNF production
  ;; and the Cur type.
  (struct bnf-production (ctor type))

  ;; Every production belongs to a nonterminal, which also represents the type of the production.
  ;; parse-bnf-production takes this bnf-nonterminal, and a BNF-Production, and
  ;; produces a bnf-production structure.
  (define (parse-bnf-production nt stx)
    (syntax-parse stx
      [(x:free-id e ...)
       (let ([ctor (syntax/loc stx x)])
         (bnf-production
          ctor
          #`(-> #,@(map (curry parse-bnf-expr-arg nt) (attribute e))
                #,(bnf-nonterminal-name nt))))]
      [_
       (parse-bnf-expr nt stx)]))

  ;; Parse a BNF-Expr as an argument in a BNF-Production
  (define (parse-bnf-expr-arg nt stx)
    (syntax-parse stx
      [N:bnf-nt (bnf-nonterminal-name (syntax-local-value #'N))]
      [x:free-id
       (bnf-nonterminal-name nt)]
      [e:cur-type stx]))

  ;; Parse a BNF-Expr as a BNF-Production
  (define (parse-bnf-expr nt stx)
    (syntax-parse stx
      [N:bnf-nt
       (let ([N-type (bnf-nonterminal-name (syntax-local-value #'N))]
             [nt-type (bnf-nonterminal-name nt)])
         (bnf-production
          (format-id stx "~a->~a" N-type nt-type)
          (quasisyntax/loc stx
            (-> N-type #,nt-type))))]
      [x:free-id
       (bnf-production (syntax/loc stx x) (bnf-nonterminal-name nt))]
      [e:cur-type
       (let ([nt-type (bnf-nonterminal-name nt)])
         (bnf-production
          (format-id stx "~a->~a" #'e nt-type)
          (quasisyntax/loc stx
            (-> e #,nt-type))))]
      ))

  (struct bnf-nonterminal (name parser)
    #:property prop:procedure
    (lambda (stx)
      (raise-syntax-error
       (format "~a is a reserved name and can only be used in a BNF literal."
               (stx-car stx)))))
  )

;; TODO: Support unquote
(define-syntax (bnf stx)
  (syntax-parse stx
    [(_ name:id literal)
     ((bnf-nonterminal-parser (syntax-local-value #'name)) #'literal)]))

(define-syntax (define-data/bnf stx)
  (syntax-parse stx
    [(_ name:id (nt:id nts:id ...)
        (~optional (~datum ::=))
        e
        ...
        ;; TODO: Optional;
        ;; TODO: Check that f has the right type?
        (~seq #:parser f))
     #:do [(define bnf-nt (bnf-nonterminal #'name #f))
           (define bnf-prods (map (curry parse-bnf-production bnf-nt) (attribute e)))]
     #:with (c ...) (map bnf-production-ctor bnf-prods)
     #:with (t ...) (map bnf-production-type bnf-prods)
     (quasisyntax/loc this-syntax
       (begin
         (define-for-syntax (parser stx) (f stx (list #'c ...)))
         (define-syntax nt (bnf-nonterminal #'name parser))
         (define-syntax nts (make-variable-like-transformer #'nt)) ...

         #,(quasisyntax/loc this-syntax
             (define-datatype name : #,(syntax/loc this-syntax (Type 0)) (c : t) ...))))]))

(require (only-in racket/base module+))

(module+ test
  (require (for-syntax (only-in racket/list first)))
  (define-data/bnf Nat (N) ::= z (s N)
    #:parser (lambda (stx ctors)
               stx))
  z
  (bnf N z)
  (s z)
  (bnf N (s z))

  (define-data/bnf List (L) ::= nil (cons N L)
    #:parser (lambda (stx ctors)
               stx))
  nil
  (cons z nil)
  ;(cons nil nil) -> type error

  #;(define-syntax ~of-cur-type
    (pattern-expander
     (lambda (stx)
       (syntax-case stx ()
         [(type e)
          #'(~var e (of-cur-type #'type))]))))

  (begin-for-syntax
    (define-syntax-class (of-cur-type t)
      (pattern e:expr #:when (cur-type-check? #'e t))))

  (define-data/bnf Arith-Term (e) ::= Nat (+ e e) (- e e) (* e e) error
    #:parser (lambda (stx ctors)
               (syntax-parse stx
                 [(~var e (of-cur-type #'Nat))
                  (quasisyntax/loc stx
                    (#,(first ctors)
                     e))]
                 ;; TODO: Work recursively
                 ;; TODO: Inline operators
                 [_ stx])))

  (Nat->Arith-Term z)
  (+ (Nat->Arith-Term z) (Nat->Arith-Term z))
  (bnf e z)
  (bnf e (+ z z))
  )

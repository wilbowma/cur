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

  ;; A BNF-Production is (a syntax object representing a) one of:
  ;;   - BNF-Expr
  ;;   - A list starting with a Free-Id followed by BNF-Exprs, i.e.,
  ;;     (Free-Id BNF-Expr ...)
  ;;   TODO: Loosen final clause to allow mix fix BNF-Productions?
  ;;
  ;; A BNF-Production is parsed into the bnf-production structure, which records
  ;; a unique constructor name for the Cur representation of the BNF production
  ;; and the Cur type.
  (struct bnf-production (ctor type parse))

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
                #,(bnf-nonterminal-name nt))

          (lambda (f stx)
            (syntax-parse stx
              [(y e ...)
               #:when (free-identifier=? #'y #'x)
               (quasisyntax/loc stx
                 (#,ctor
                  ;; TODO: This is wrong for recursion
                  #,@(map f (attribute e))))]
              [_ (f stx)]))))]
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
       (let* ([N-type (bnf-nonterminal-name (syntax-local-value #'N))]
              [nt-type (bnf-nonterminal-name nt)]
              [ctor (format-id stx "~a->~a" N-type nt-type)])
         (when (free-identifier=? N-type nt-type)
           (raise-syntax-error "Cannot have unguarded recursive BNF" stx))
         (bnf-production
          ctor
          (quasisyntax/loc stx
            (-> N-type #,nt-type))
          (lambda (f stx)
            (syntax-parse stx
              [N1:bnf-nt
               #:when (free-identifier=? #'N #'N1)
               (quasisyntax/loc stx
                 (#,ctor N1))]
              [_ (f stx)]))))]
      [x:free-id
       (bnf-production
        (syntax/loc stx x)
        (bnf-nonterminal-name nt)
        (lambda (f stx)
          (syntax-parse stx
            [y:free-id
             (syntax/loc stx y)]
            [_ (f stx)])))]
      [A:cur-type
       (let* ([nt-type (bnf-nonterminal-name nt)]
              [ctor (format-id stx "~a->~a" #'A nt-type)])
         (bnf-production
          ctor
          (quasisyntax/loc stx
            (-> e #,nt-type))
          (lambda (f stx)
            (syntax-parse stx
              [(~of-cur-type e A)
               (quasisyntax/loc stx
                 (#,ctor e))]
              [_ (f stx)]))))]))

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

(define-for-syntax (make-bnf-production-parser prods)
  (lambda (stx ctors)
    ((for/fold ([f
                (lambda (f stx)
                  (f (lambda (stx)
                       (syntax-parse stx
                         [_ (raise-syntax-error
                             (format
                              "Could not parse BNF expression as ~a"
                              (syntax->datum #'name))
                             stx)]))
                     stx))])
              ([prod prods])
       ;; TODO: This is too complicated and doesn't generate a recursive parser.
      (lambda (f stx)
        (f (lambda (stx)
             (bnf-production-parse prod) f stx) stx)))
     (lambda (f stx) (f stx))
     stx)))

(define-syntax (define-data/bnf stx)
  (syntax-parse stx
    [(_ name:id (nt:id nts:id ...)
        (~optional (~datum ::=))
        e
        ...
        ;; TODO: Check that f has the right type?
        (~optional (~seq #:parser f)))
     #:do [(define bnf-nt (bnf-nonterminal #'name #f))
           (define bnf-prods (map (curry parse-bnf-production bnf-nt) (attribute e)))]
     #:with (c ...) (map bnf-production-ctor bnf-prods)
     #:with (t ...) (map bnf-production-type bnf-prods)
     (quasisyntax/loc this-syntax
       (begin
         (define-for-syntax (parser stx)
           (#,(if (attribute f) #'f #`(make-bnf-production-parser (list #,@bnf-prods)))
            stx (list #'c ...)))
         (define-syntax nt (bnf-nonterminal #'name parser))
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
  (bnf N (s z))

  (define-data/bnf List (L) ::= nil (cons N L)
   ; #:parser (lambda (stx ctors) stx)
    )
  nil
  (cons z nil)
  ;(cons nil nil) -> type error

;  (require (for-syntax racket/dict racket/list syntax/id-table))
;  (define-data/bnf Arith-Term (e) ::= Nat (+ e e) (- e e) (* e e) error
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

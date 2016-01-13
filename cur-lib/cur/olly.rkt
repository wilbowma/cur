#lang s-exp "cur.rkt"
;; Olly: The OTT-Like LibrarY
;; TODO: Automagically create a parser from bnf grammar
(require
  "stdlib/sugar.rkt"
  "stdlib/nat.rkt"
  ;; TODO: "real-"? More like "curnel-"
  (only-in "cur.rkt" [#%app real-app] [elim real-elim] [forall real-forall] [lambda real-lambda]))

(provide
  define-relation
  define-language
  Var
  avar
  var-equal?
  generate-coq

  ;; private; exported for testing only
  (for-syntax
   coq-defns
   output-latex-bnf
   output-coq))

(begin-for-syntax
  (define-syntax-class dash
    (pattern
     x:id
     #:fail-unless (regexp-match #rx"-+" (symbol->string (syntax-e #'x))) "Invalid dash"))

  (define-syntax-class decl (pattern (x:id (~datum :) t:id)))

  ;; TODO: Automatically infer decl ... by binding all free identifiers?
  ;; TODO: Automatically infer decl ... for meta-variables that are the
  ;; same as bnf grammar.
  (define-syntax-class inferrence-rule
    (pattern (d:decl ...
              x*:expr ...
              line:dash lab:id
              (name:id y* ...))
              #:with rule #'(lab : (-> d ... x* ... (name y* ...)))
              ;; TODO: convert meta-vars such as e1 to e_1
              #:attr latex (format "\\inferrule~n{~a}~n{~a}"
                             (string-trim
                               (for/fold ([str ""])
                                        ([hyp (syntax->datum #'(x* ...))])
                                 (format "~a~a \\+" str hyp))
                               " \\+"
                               #:left? #f)
                             (format "~a" (syntax->datum #'(name y* ...)))))))
(define-syntax (define-relation syn)
  (syntax-parse syn
    [(_ (n:id types* ...)
        (~optional (~seq #:output-coq coq-file:str))
        (~optional (~seq #:output-latex latex-file:str))
        rules:inferrence-rule ...)
     #:fail-unless (andmap (curry equal? (length (syntax->datum #'(types* ...))))
                           (map length (syntax->datum #'((rules.y* ...)
                                                          ...))))
     "Mismatch between relation declared and relation definition"
     #:fail-unless (andmap (curry equal? (syntax->datum #'n))
                           (syntax->datum #'(rules.name ...)))
     "Mismatch between relation declared name and result of inference rule"
      (let ([output #`(data n : (-> types* ... Type) rules.rule ...)])
        ;; TODO: Pull this out into a separate function and test. Except
        ;; that might make using attritbutes more difficult.
        (when (attribute latex-file)
          (with-output-to-file (syntax->datum #'latex-file)
            (thunk
              (printf (format "\\fbox{$~a$}$~n$\\begin{mathpar}~n~a~n\\end{mathpar}$$"
                       (syntax->datum #'(n types* ...))
                       (string-trim
                         (for/fold ([str ""])
                                   ([rule (attribute rules.latex)])
                           (format "~a~a\\and~n" str rule))
                         "\\and"
                         #:left? #f))))
            #:exists 'append))
        #`(begin
            #,@(if (attribute coq-file)
                   #`((generate-coq #:file coq-file #:exists
                                    'append #,output))
                   #'())
               #,output))]))

;; ------------------------------------
;; define-language

(begin-for-syntax
  ;; TODO: More clever use of syntax-parse would enable something akin to what
  ;; define-relation is doing---having attributes that contain the latex
  ;; code for each clause.
  ;; TODO: convert meta-vars such as e1 to e_1
  (define (output-latex-bnf clauses)
    (format "$$\\begin{array}{lrrl}~n~a~n\\end{array}$$"
      (for/fold ([str ""])
                ([clause (syntax->list clauses)])
        (syntax-parse clause
          #:datum-literals (::=)
          [(type:id (nonterminal:id ...) ::= exprs ...)
           (format "\\mbox{\\textit{~a}} & ~a & \\bnfdef & ~a\\\\~n"
                   (symbol->string (syntax->datum #'type))
                   (string-trim
                     (for/fold ([str ""])
                               ([nt (syntax->datum #'(nonterminal ...))])
                       (format "~a~a," str nt))
                     ","
                     #:left? #f)
                   (string-trim
                     (for/fold ([str ""])
                               ([expr (syntax->datum #'(exprs ...))])
                       (format "~a~a \\bnfalt " str expr))
                     " \\bnfalt "
                     #:left? #f))]))))
  (define (generate-latex-bnf file-name clauses)
    (with-output-to-file file-name
      (thunk (printf (output-latex-bnf clauses)))
      #:exists 'append)))

(begin-for-syntax
  ;; A mutable map from non-terminal meta-variables names to their types
  (define mv-map (make-parameter #f))

  ;; A meta-variable is any identifiers that belongs to the mv-map
  (define-syntax-class meta-variable
    (pattern
     e:id
     #:attr sym (syntax->datum #'e)
     #:fail-unless (dict-has-key? (mv-map) (attribute sym)) #f
     #:attr type (dict-ref (mv-map) (attribute sym))))

  ;; A expression is parameterized by the name of the non-terminal to
  ;; which is belongs, the language name, and the map of meta-varibles to
  ;; their types.
  ;; Each expression exports a decl-context and arg-context attribute.
  ;; In decl-context, a expression generates a constructor
  ;; declaration for an inductive type.
  ;; In arg-context, a expression generates the list of types
  ;; indicated by the expression; e.g., in the definition of
  ;; stlc-term, the expression v, representing a meta-variable for
  ;; stlc-val, generates
  ;;   (stlc-val->stlc-term : (-> stlc-val stlc-term))
  ;; in decl-context, and
  ;;   (stlc-val)
  ;; in arg-context
  (define-syntax-class (expression non-terminal-type lang-name)
    ;; A meta-variable is a valid expression.
    ;; Generates a conversion constructor in decl-context, and the type of
    (pattern
     e:meta-variable
     #:attr constructor-name
     (format-id #'e "~a->~a" #'e.type non-terminal-type)
     #:attr arg-context
     (list #'e.type)
     #:attr decl-context
     #`(constructor-name : (-> #,@(attribute arg-context) #,non-terminal-type)))

    ;; An identifier is a valid expression, generating a base constructor.
    (pattern
     x:id
     #:attr constructor-name
     (format-id #'x "~a-~a" lang-name #'x)
     ;; Cannot appear in arg-context
     #:attr arg-context
     '()
     #:attr decl-context
     #`(constructor-name : #,non-terminal-type))

    (pattern
     ((~var x (expression non-terminal-type lang-name)) (~var c (expression non-terminal-type lang-name)) ...)
     ;; TODO: Should be pattern below, but this simplifies defs as expression-args is mostly a expression. Related to arg-context vs decl-context
     ;; (x:id (~var c (expression-args non-terminal-type lang-name)) ...)
     #:attr constructor-name
     (attribute x.constructor-name)
     #:attr arg-context
     ;; Flatten nested arg-contexts
     (for/fold ([ls (attribute x.arg-context)])
               ([e (attribute c.arg-context)])
       (append ls e))
     #:attr decl-context
     #`(constructor-name : (-> #,@(attribute arg-context) #,non-terminal-type))))

  ;; Syntax class non-terminal-def is parameterized by a language name
  ;; to the inductive types representing their non-terminal.
  (define-syntax-class (non-terminal-def lang-name)
    (pattern
     (name:id
      (meta-var:id ...+)
      (~optional (~datum ::=))
      ;; Create a name for the type of this non-terminal, from the
      ;; language name and the non-terminal name.
      (~bind [nt-type (format-id #'name "~a-~a" lang-name #'name)])
      ;; Imperatively update the map from meta-variables to the
      ;; nt-type, to be used when generating the types of the constructors
      ;; for this and later non-terminal.
      (~do (for ([mv (syntax->datum #'(meta-var ...))])
             (dict-set! (mv-map) mv (attribute nt-type))))
      (~var c (expression (attribute nt-type) lang-name)) ...)
     ;; Generates the inductive data type for this non-terminal definition.
     #:attr def
     #`(data nt-type : Type c.decl-context ...))))

;; TODO: For better error messages, add context
;; TODO: Extend define-language with syntax such as ....
;;   (term (e) ::= (e1 e2) ((lambda (x) e)
(define-syntax (define-language syn)
  (parameterize ([mv-map (make-hash)])
    (syntax-parse syn
      [(_ lang-name:id
          (~optional (~seq #:vars (x:id ...)))
          ;; Update the mv-map to include x -> Var for each x
          (~do (cond
                 [(attribute x) =>
                  (lambda (xls)
                    (for ([x xls])
                      (dict-set! (mv-map) (syntax-e x) #'Var)))]))
          (~optional (~seq #:output-coq coq-file:str))
          (~optional (~seq #:output-latex latex-file:str))
          (~var defs (non-terminal-def #'lang-name)) ...)
       (let ([output #`(begin defs.def ...)])
         ;; TODO: Should do this via attributes
         (when (attribute latex-file)
           (generate-latex-bnf (syntax->datum #'latex-file) #'(defs ...)))
         #`(begin
             ;; TODO: generate-coq should also export a compile-time function.
             #,@(if (attribute coq-file)
                    #`((generate-coq #:file coq-file #:exists 'append #,output))
                    #'())
             #,output))])))

(data Var : Type (avar : (-> Nat Var)))

(define (var-equal? (v1 : Var) (v2 : Var))
  (match v1
    [(avar (n1 : Nat))
     (match v2
       [(avar (n2 : Nat))
        (nat-equal? n1 n2)])]))

;; See stlc.rkt for examples

;; Generate Coq from Cur:

(begin-for-syntax
  (define coq-defns (make-parameter ""))
  (define (coq-lift-top-level str)
    (coq-defns (format "~a~a~n" (coq-defns) str)))
  ;; TODO: OOps, type-infer doesn't return a cur term but a redex syntax bla
  ;; TODO: Think the above TODO was fixed; consult git log
  (define (constructor-args syn)
    (syntax-parse (type-infer/syn syn)
      #:datum-literals (Π :)
      [(Π (x:id : t) body)
       (cons #'x (constructor-args #'body))]
      [_ null]))
  (define (sanitize-id str)
    (let ([replace-by `((: _) (- _))])
      (for/fold ([str str])
                ([p replace-by])
        (string-replace str (symbol->string (first p))
                        (symbol->string (second p))))))
  (define (output-coq syn)
    (syntax-parse (cur-expand syn #'define #'begin)
       ;; TODO: Need to add these to a literal set and export it
       ;; Or, maybe overwrite syntax-parse
       #:literals (real-lambda real-forall data real-app real-elim define begin Type)
       [(begin e ...)
        (for/fold ([str ""])
                  ([e (syntax->list #'(e ...))])
          (format "~a~n" (output-coq e)))]
       [(define name:id body)
        (begin
          (coq-lift-top-level
            (format "Definition ~a := ~a.~n"
                    (output-coq #'name)
                    (output-coq #'body)))
          "")]
       [(define (name:id (x:id : t) ...) body)
        (begin
          (coq-lift-top-level
            (format "Function ~a ~a := ~a.~n"
                    (output-coq #'name)
                    (for/fold ([str ""])
                              ([n (syntax->list #'(x ...))]
                               [t (syntax->list #'(t ...))])
                      (format "~a(~a : ~a) " str (output-coq n) (output-coq t)))
                    (output-coq #'body)))
          "")]
       [(real-lambda ~! (x:id (~datum :) t) body:expr)
        (format "(fun ~a : ~a => ~a)" (output-coq #'x) (output-coq #'t)
                (output-coq #'body))]
       [(real-forall ~! (x:id (~datum :) t) body:expr)
        (format "(forall ~a : ~a, ~a)" (syntax-e #'x) (output-coq #'t)
                (output-coq #'body))]
       [(data ~! n:id (~datum :) t (x*:id (~datum :) t*) ...)
        (begin
          (coq-lift-top-level
            (format "Inductive ~a : ~a :=~a."
                   (sanitize-id (format "~a" (syntax-e #'n)))
                   (output-coq #'t)
                   (for/fold ([strs ""])
                             ([clause (syntax->list #'((x* : t*) ...))])
                     (syntax-parse clause
                       [(x (~datum :) t)
                        (format "~a~n| ~a : ~a" strs (syntax-e #'x)
                          (output-coq #'t))]))))
          "")]
       [(Type i) "Type"]
       [(real-elim var t)
        (format "~a_rect" (output-coq #'var))]
       [(real-app e1 e2)
        (format "(~a ~a)" (output-coq #'e1) (output-coq #'e2))]
       [e:id (sanitize-id (format "~a" (syntax->datum #'e)))])))

(define-syntax (generate-coq syn)
  (syntax-parse syn
    [(_ (~optional (~seq #:file file))
        (~optional (~seq #:exists flag)) body:expr)
     (parameterize ([current-output-port (if (attribute file)
                                             (open-output-file (syntax->datum #'file)
                                                               #:exists
                                                               (if (attribute flag)
                                                                   ;; TODO: AHH WHAT?
                                                                   (eval (syntax->datum #'flag))
                                                                   'error))
                                             (current-output-port))]
                    [coq-defns ""])
       (define output
         (let ([body (output-coq #'body)])
           (if (regexp-match "^\\s*$" body)
               ""
               (format "Eval compute in ~a." body))))
       (displayln (format "~a~a" (coq-defns) output))
       #'(begin))]))

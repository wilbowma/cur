#lang s-exp "redex-curnel.rkt"
;; OLL: The OTT-Like Library
;; TODO: Add latex extraction
;; TODO: Automagically create a parser from bnf grammar
(require "stdlib/sugar.rkt" "stdlib/nat.rkt" racket/trace)

(provide define-relation define-language var avar var-equal?
         generate-coq #;(rename-out [oll-define-theorem define-theorem]))

(begin-for-syntax
  (define-syntax-class dash
    (pattern x:id
           #:fail-unless (regexp-match #rx"-+" (symbol->string (syntax-e #'x)))
           "Invalid dash"))

  (define-syntax-class decl (pattern (x:id (~datum :) t:id)))

  ;; TODO: Automatically infer decl ... by binding all free identifiers?
  ;; TODO: Automatically infer decl ... for meta-variables that are the
  ;; same as bnf grammar.
  (define-syntax-class inferrence-rule
    (pattern (d:decl ...
              x*:expr ...
              line:dash lab:id
              (name:id y* ...))
              #:with rule #'(lab : (forall* d ...
                                     (->* x* ... (name y* ...))))
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
      (let ([output #`(data n : (->* types* ... Type) rules.rule ...)])
        ;; TODO: Pull this out into a separate function and test. Except
        ;; that might make using attritbutes more difficult.
        (when (attribute latex-file)
          (with-output-to-file (syntax->datum #'latex-file)
            (thunk
              (format "\\fbox{$~a$}$~n$\\begin{mathpar}~n~a~n\end{mathpar}$$"
                      (syntax->datum #'(n types* ...))
                      (string-trim
                        (for/fold ([str ""])
                                  ([rule (attribute rules.latex)])
                          (format "~a~a\\and~n" str rule))
                        "\\and"
                        #:left? #f)))
            #:exists 'append))
        #`(begin
            #,@(if (attribute coq-file)
                   #`((generate-coq #:file coq-file #:exists
                                    'append #,output))
                   #'())
               #,output))]))

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

;; TODO: Oh, this is a mess. Rewrite it.
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

(begin-for-syntax
  ;; TODO: More clever use of syntax-parse would enable something akin to what
  ;; define-relation is doing---having attributes that contain the latex
  ;; code for each clause.
  ;; TODO: convert meta-vars such as e1 to e_1
  (define (output-latex-bnf vars clauses)
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
  (define (generate-latex-bnf file-name vars clauses)
    (with-output-to-file file-name
      (thunk (output-latex-bnf vars clauses))
      #:exists 'append)))
(module+ test
  (require "stdlib/sugar.rkt")
  (begin-for-syntax
    (require rackunit)
    (check-equal?
      (format "$$\\begin{array}{lrrl}~n~a~n\\end{array}$$"
        (format "\\mbox{\\textit{term}} & e & \\bnfdef & (e1 e2) \\bnfalt (lambda (x) e)\\\\~n"))
      (output-latex-bnf #'(x)
                    #'((term (e) ::= (e1 e2) (lambda (x) e)))))
    (check-equal?
      (format "$$\\begin{array}{lrrl}~n~a~n\\end{array}$$"
        (format "\\mbox{\\textit{type}} & A,B,C & \\bnfdef & unit \\bnfalt (* A B) \\bnfalt (+ A C)\\\\~n"))
      (output-latex-bnf #'(x)
                    #'((type (A B C) ::= unit (* A B) (+ A C)))))))
;; TODO: For better error messages, add context, rename some of these patterns. e.g.
;;    (type (meta-vars) ::= ?? )
;; TODO: Extend define-language with syntax such as ....
;;   (term (e) ::= (e1 e2) ((lambda (x) e)
;                           #:latex "(\\lambda ,x. ,e)"))
(define-syntax (define-language syn)
  (syntax-parse syn
    [(_ name:id (~do (lang-name #'name))
        (~do (nts (hash-set (make-immutable-hash) 'var #'var)))
        (~optional (~seq #:vars (x*:id ...)
           (~do (nts (for/fold ([ht (nts)])
                               ([v (syntax->datum #'(x* ...))])
                       (hash-set ht v (hash-ref ht 'var)))))))
        (~optional (~seq #:output-coq coq-file:str))
        (~optional (~seq #:output-latex latex-file:str))
        . clause*:nt-clauses)
     (let ([output #`(begin . clause*.defs)])
       (when (attribute latex-file)
         (generate-latex-bnf (syntax->datum #'latex-file) #'vars #'clause*))
       #`(begin
           #,@(if (attribute coq-file)
                 #`((generate-coq #:file coq-file #:exists 'append #,output))
                 #'())
           #,output))]))

(data var : Type (avar : (-> nat var)))

(define (var-equal? (v1 : var) (v2 : var))
  (case* var v1 (lambda* (v : var) bool)
    [(avar (n1 : nat)) IH: ()
     (case* var v2 (lambda* (v : var) bool)
       [(avar (n2 : nat)) IH: ()
        (nat-equal? n1 n2)])]))
(module+ test
  (require rackunit)
  (check-equal?
    (var-equal? (avar z) (avar z))
    btrue)
  (check-equal?
    (var-equal? (avar z) (avar (s z)))
    bfalse))

;; See stlc.rkt for examples

;; Generate Coq from Cur:

(begin-for-syntax
  (define coq-defns (make-parameter ""))
  (define (coq-lift-top-level str)
    (coq-defns (format "~a~a~n" (coq-defns) str)))
  ;; TODO: OOps, type-infer doesn't return a cur term but a redex syntax bla
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
    (syntax-parse (cur-expand syn #'define #'define-theorem #'qed
                              #'begin)
       ;; TODO: Need to add these to a literal set and export it
       ;; Or, maybe overwrite syntax-parse
       #:literals (lambda forall data real-app elim define-theorem
                          define qed begin Type)
       [(begin e ...)
        (for/fold ([str ""])
                  ([e (syntax->list #'(e ...))])
          (format "~a~n" (output-coq e)))]
       [(define-theorem name prop)
        (begin
          (fprintf (current-error-port) "Warning: If theorem ~a is not followed by a proof using (qed ...), the resulting Coq code may be malformed.~n" (output-coq #'name))
          (coq-lift-top-level
            (format "Theorem ~a : ~a.~n"
                    (output-coq #'name)
                    (output-coq #'prop)))
          "")]
       [(qed thm proof)
        ;; TODO: Have some sort of coq-lift-to-theorem, to auto match
        ;; proofs and theorems.
        (begin
          (coq-lift-top-level
            (format "Proof. exact ~a. Qed.~n" (output-coq #'proof)))
          "")]
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
       [(lambda ~! (x:id (~datum :) t) body:expr)
        (format "(fun ~a : ~a => ~a)" (syntax-e #'x) (output-coq #'t)
                (output-coq #'body))]
       [(forall ~! (x:id (~datum :) t) body:expr)
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
       [(elim var e P m ...)
        (format "(~a_rect ~a~a ~a)"
          (output-coq #'var)
          (output-coq #'P)
          (for/fold ([x ""])
                    ([m (syntax->list #'(m ...))])
            (format "~a ~a" (output-coq m)))
          (output-coq #'e))]
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

(module+ test
  (begin-for-syntax
    (check-equal?
      (parameterize ([coq-defns ""]) (output-coq #'(data nat : Type (z : nat))) (coq-defns))
      (format "Inductive nat : Type :=~n| z : nat.~n"))
    (check-regexp-match
      "(forall .+ : Type, Type)"
      (output-coq #'(-> Type Type)))
    (let ([t (parameterize ([coq-defns ""])
               (output-coq #'(define-relation (meow gamma term type)
                               [(g : gamma) (e : term) (t : type)
                                --------------- T-Bla
                                (meow g e t)]))
               (coq-defns))])
      (check-regexp-match
        "Inductive meow : \\(forall temp. : gamma, \\(forall temp. : term, \\(forall temp. : type, Type\\)\\)\\) :="
        (first (string-split t "\n")))
      (check-regexp-match
        "\\| T-Bla : \\(forall g : gamma, \\(forall e : term, \\(forall t : type, \\(\\(\\(meow g\\) e\\) t\\)\\)\\)\\)\\."
        (second (string-split t "\n"))))
    (let ([t (output-coq #'(case z (z z) (s (lambda (n : nat) (s n)))))])
      (check-regexp-match
        "\\(match z with\n\\| \\(z\\) => z\n\\| \\(s .+\\) => \\(\\(fun n : nat => \\(s n\\)\\) .+\\)\nend\\)"
        t))
    (check-regexp-match
      "Theorem thm_plus_commutes : \\(forall n : nat, \\(forall m : nat, \\(\\(\\(== nat\\) \\(\\(plus n\\) m\\)\\) \\(\\(plus m\\) n\\)\\)\\)\\).\n"
      (parameterize ([coq-defns ""])
        (output-coq #'(define-theorem thm:plus-commutes
                                     (forall* (n : nat) (m : nat)
                                              (== nat (plus n m) (plus m n)))))
        (coq-defns)))
    (check-regexp-match
      "Function add1 \\(n : nat\\)  := \\(s n\\).\n"
      (parameterize ([coq-defns ""])
        (output-coq #'(define (add1 (n : nat)) (s n)))
        (coq-defns)))))

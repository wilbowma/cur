#lang s-exp "../cur.rkt"
(provide
  ->
  lambda
  (rename-out
    [-> →]
    [-> forall]
    [-> ∀]
    [lambda λ])
  #%app
  define
  elim
  define-type
  match
  recur
  let

  ;; type-check
  ::

  ;; reflection in syntax
  run
  step
  step-n
  query-type)

(require
  (only-in "../cur.rkt"
    [elim real-elim]
    [#%app real-app]
    ;; Somehow, using real-lambda instead of _lambda causes weird import error
    [lambda real-lambda]
    #;[forall real-forall]
    [define real-define]))

(begin-for-syntax
  (define-syntax-class result-type
    (pattern type:expr))

  (define-syntax-class parameter-declaration
    (pattern (name:id (~datum :) type:expr))

    (pattern
     type:expr
     #:attr name (format-id #'type "~a" (gensym 'anon-parameter)))))

;; A multi-arity function type; takes parameter declaration of either
;; a binding (name : type), or type whose name is generated.
;; E.g.
;; (-> (A : Type) A A)
(define-syntax (-> syn)
  (syntax-parse syn
    [(_ d:parameter-declaration ...+ result:result-type)
     (foldr (lambda (src name type r)
              (quasisyntax/loc src
                (forall (#,name : #,type) #,r)))
            #'result
            (attribute d)
            (attribute d.name)
            (attribute d.type))]))

;; TODO: Add forall macro that allows specifying *names*, with types
;; inferred. unlike -> which require types but not names
;; E.g.
;; (forall x (y : Nat) (== Nat x y))

;; TODO: Allows argument-declarations to have types inferred, similar
;; to above TODO forall
(begin-for-syntax
  ;; eta-expand syntax-class for error messages
  (define-syntax-class argument-declaration
    (pattern
     e:parameter-declaration
     #:attr name #'e.name
     #:attr type #'e.type)))
(define-syntax (lambda syn)
  (syntax-parse syn
    [(_ d:argument-declaration ...+ body:expr)
     (foldr (lambda (src name type r)
              (quasisyntax/loc src
                (real-lambda (#,name : #,type) #,r)))
            #'body
            (attribute d)
            (attribute d.name)
            (attribute d.type))]))

;; TODO: This makes for really bad error messages when an identifier is undefined.
(define-syntax (#%app syn)
  (syntax-case syn ()
    [(_ e)
     (quasisyntax/loc syn e)]
    [(_ e1 e2)
     (quasisyntax/loc syn
       (real-app e1 e2))]
    [(_ e1 e2 e3 ...)
     (quasisyntax/loc syn
       (#%app (#%app e1 e2) e3 ...))]))
(module+ test
  ((lambda (A : (Type 1)) (B : (Type 1)) A)
   Type
   Type))

(define-syntax define-type
  (syntax-rules ()
    [(_ (name (a : t) ...) body)
     (define name (forall (a : t) ... body))]
    [(_ name type)
     (define name type)]))

;; TODO: Allow inferring types as in above TODOs for lambda, forall
(define-syntax (define syn)
  (syntax-case syn ()
    [(define (name (x : t) ...) body)
     (quasisyntax/loc syn
       (real-define name (lambda (x : t) ... body)))]
    [(define id body)
     (quasisyntax/loc syn
       (real-define id body))]))

(define-syntax-rule (elim t1 t2 e ...)
  ((real-elim t1 t2) e ...))

;; Quite fragie to give a syntactic treatment of pattern matching -> eliminator. Replace with "Elimination with a Motive"
(begin-for-syntax
  (define ih-dict (make-hash))

  (define-syntax-class curried-application
    (pattern
     ((~literal real-app) name:id e:expr)
     #:attr args
     (list #'e))

    (pattern
     ((~literal real-app) a:curried-application e:expr)
     #:attr name #'a.name
     #:attr args
     ;; TODO BUG: repeated appends are not performant; cons then reverse in inductive-type-declaration
     (append
      (attribute a.args)
      (list #'e))))

  (define-syntax-class inductive-type-declaration
    (pattern
     x:id
     #:attr inductive-name
     #'x
     #:attr indices
     '()
     #:attr decls
     (list #`(#,(gensym 'anon-discriminant) : x))
     #:attr abstract-indices
     values)

    (pattern
     ;; BUG TODO NB: Because the inductive type may have been inferred, it may appear in Curnel syntax, i.e., nested applications starting with dep-app
     ;; Best to ensure it *always* is in Curnel form, and pattern match on that.
     a:curried-application
     #:attr inductive-name
     (attribute a.name)
     #:attr indices
     (attribute a.args)
     #:attr names
     (for/list ([e (attribute indices)])
       (format-id e "~a" (gensym 'anon-index)))
     #:attr types
     ;; TODO: Detect failure, report error/suggestions
     (for/list ([e (attribute indices)])
       (or (type-infer/syn e)
           (raise-syntax-error
            'match
            (format
             "Could not infer type of index ~a"
             e)
            e)))
     #:attr decls
     (append
      (for/list ([name (attribute names)]
                 [type (attribute types)]
                 [src (attribute indices)])
        (quasisyntax/loc src
          (#,name : #,type)))
      (list
       (quasisyntax/loc #'a
         (#,(gensym 'anon-discriminant) : (inductive-name #,@(attribute names))))))
     #:attr abstract-indices
     (lambda (return)
       ;; NB: unhygenic
       ;; Normalize at compile-time, for efficiency at run-time
       (normalize/syn
        #`((lambda
              ;; TODO: utteraly fragile; relines on the indices being referred to by name, not computed
              ;; works only for simple type familes and simply matches on them
             #,@(for/list ([name (attribute indices)]
                           [type (attribute types)])
                 #`(#,name : #,type))
            #,return)
          #,@(attribute names))))))

  ;; todo: Support just names, inferring types
  (define-syntax-class match-declaration
    (pattern
     ;; TODO: Use parameter-declaration defined earlier
     (name:id (~datum :) type:expr)
     #:attr decl
     #'(name : type)))

  (define-syntax-class match-prepattern
    ;; TODO: Check that x is a valid constructor for the inductive type
    (pattern
     x:id
     #:attr local-env
     '()
     #:attr decls
     '()
     #:attr types
     '()
     #:attr names
     '())

    (pattern
     (x:id d:match-declaration ...+)
     #:attr local-env
     (for/fold ([d (make-immutable-hash)])
               ([name (attribute d.name)]
                [type (attribute d.type)])
       (dict-set d name type))
     #:attr decls
     (attribute d.decl)
     #:attr names
     (attribute d.name)
     #:attr types
     (attribute d.type)))

  (define-syntax-class (match-pattern D motive)
    (pattern
     d:match-prepattern
     #:attr decls
     ;; Infer the inductive hypotheses, add them to the pattern decls
     ;; and update the dictionarty for the recur form
     (for/fold ([decls (attribute d.decls)])
               ([type-syn (attribute d.types)]
                [name-syn (attribute d.names)]
                [src (attribute d.decls)]
                ;; NB: Non-hygenic
                ;; BUG TODO: This fails when D is an inductive applied to arguments...
                #:when (cur-equal? type-syn D))
       (define/syntax-parse type:inductive-type-declaration (cur-expand type-syn))
       (let ([ih-name (quasisyntax/loc src #,(format-id name-syn "ih-~a" name-syn))]
             ;; Normalize at compile-time, for efficiency at run-time
             [ih-type (normalize/syn #`(#,motive #,@(attribute type.indices) #,name-syn))])
         (dict-set! ih-dict (syntax->datum name-syn) ih-name)
         (append decls (list #`(#,ih-name : #,ih-type)))))))

  (define-syntax-class (match-preclause maybe-return-type)
    (pattern
     (p:match-prepattern b:expr)
     #:attr return-type
     ;; TODO: Check that the infered type matches maybe-return-type, if it is provied
     (or maybe-return-type
         ;; Ignore errors when trying to infer this type; other attempt might succeed
         (with-handlers ([values (lambda _ #f)])
           (type-infer/syn #:local-env (attribute p.local-env) #'b)))))

  (define-syntax-class (match-clause D motive)
    (pattern
     ((~var p (match-pattern D motive))
      ;; TODO: nothing more advanced?
      b:expr)
     #:attr method
     (quasisyntax/loc #'p
       #,(if (null? (attribute p.decls))
         #'b
         #`(lambda #,@(attribute p.decls) b))))))

(define-syntax (recur syn)
  (syntax-case syn ()
    [(_ id)
     (dict-ref
      ih-dict
      (syntax->datum #'id)
      (lambda ()
        (raise-syntax-error
         'match
         ;; TODO: Detect when inside a match to provide better error
         (format
          "Cannot recur on ~a. Ether not inside a match or ~a is not an inductive argument."
          (syntax->datum #'id)
          (syntax->datum #'id))
         syn)))]))

(define-syntax (match syn)
  (syntax-parse syn
    [(_ d
        ~!
        (~optional
         (~seq #:in ~! t)
         #:defaults
         ([t (or (type-infer/syn #'d)
                 (raise-syntax-error
                  'match
                  "Could not infer discrimnant's type. Try using #:in to declare it."
                  syn))]))
        (~optional (~seq #:return ~! maybe-return-type))
        (~peek (~seq (~var prec (match-preclause (attribute maybe-return-type))) ...))
        ~!
        (~parse D:inductive-type-declaration (cur-expand (attribute t)))
        (~bind (return-type (ormap values (attribute prec.return-type))))
        (~do (unless (attribute return-type)
               (raise-syntax-error
                'match
                "Could not infer return type. Try using #:return to declare it."
                syn)))
        ;; BUG TODO: return-type is inferred with the indexes of the branches, but those must be abstracted in the motive...
        ;; Replace each of the D.indicies with the equivalent name from D.decls
        (~bind (motive (quasisyntax/loc syn
                         (lambda #,@(attribute D.decls)
                           #,((attribute D.abstract-indices) (attribute return-type))))))
        (~var c (match-clause (attribute D) (attribute motive))) ...)
     ;; TODO: Make all syntax extensions type check, report good error, rather than fail at Curnel
     (quasisyntax/loc syn
       (elim
        D.inductive-name
        #,(or
           (type-infer/syn (attribute return-type))
           (raise-syntax-error
            'match
            "Could not infer type of motive. Sorry, you'll have to use elim."
            syn))
        motive
        c.method ...
        #,@(attribute D.indices)
        d))]))

(begin-for-syntax
  (define-syntax-class let-clause
    (pattern
      (~or (x:id e) ((x:id (~datum :) t) e))
      #:attr id #'x
      #:attr expr #'e
      #:attr type (cond
                    [(attribute t)
                     ;; TODO: Code duplication in ::
                     (unless (type-check/syn? #'e #'t)
                       (raise-syntax-error
                         'let
                         (format "Term ~a does not have expected type ~a. Inferred type was ~a"
                                 (cur->datum #'e) (cur->datum #'t) (cur->datum (type-infer/syn #'e)))
                         #'e (quasisyntax/loc #'x (x e))))
                     #'t]
                    [(type-infer/syn #'e)]
                    [else
                      (raise-syntax-error
                        'let
                        "Could not infer type of let bound expression"
                        #'e (quasisyntax/loc #'x (x e)))]))))
(define-syntax (let syn)
  (syntax-parse syn
    [(let (c:let-clause ...) body)
     #'((lambda (c.id : c.type) ... body) c.e ...)]))

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

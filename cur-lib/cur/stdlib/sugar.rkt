#lang s-exp "../main.rkt"
(provide
  ->
  lambda
  (rename-out
    [-> →]
    [-> forall]
    [-> ∀]
    [-> Π]
    [-> Pi]
    [lambda λ])
  #%app
  define
  :
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
  query-type

  ;; extension abstractions
  (for-syntax
   cur-match))

(require
  (only-in "../main.rkt"
    [#%app real-app]
    [λ real-lambda]
    [Π real-Π]
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
                (real-Π (#,name : #,type) #,r)))
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
     #:attr type #'e.type))

  (define current-function-arg-ids
    (make-parameter #f #;(raise-syntax-error "Not currently in a function definition")))
  (define current-function-arg-types
    (make-parameter #f #;(raise-syntax-error "Not currently in a function definition"))))

(define-syntax (lambda syn)
  (syntax-parse syn
    [(_ d:argument-declaration ...+ body:expr)
     (foldr (lambda (src name type r)
              (quasisyntax/loc src
                (real-lambda (#,name : #,type) #,r)))
            #'body
            (attribute d)
            (attribute d.name)
            (attribute d.type))]
    ;; Support for non-zero number of arguments is handy for meta-programming
    [(_ body:expr) #'body]))

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

(define-syntax define-type
  (syntax-rules ()
    [(_ (name (a : t) ...) body)
     (define name (-> (a : t) ... body))]
    [(_ name type)
     (define name type)]))

;; Cooperates with define to allow Haskell-esque type annotations
#| TODO NB:
 | This method of cooperating macros is sort of a terrible
 | hack. Instead, need principled way of adding/retrieving information
 | to/from current module. E.g. perhaps provide extensions an interface to
 | module's term environment and inductive signature. Then, :: could add
 | new "id : type" to environment, and define could extract type and use.
 |#
(begin-for-syntax
  (define annotation-dict (make-hash))
  (define (annotation->types type-syn)
    (let loop ([ls '()]
               [syn type-syn])
      (syntax-parse (cur-expand syn)
        #:datum-literals (:)
        [(real-Π (x:id : type) body)
         (loop (cons #'type ls) #'body)]
        [_ (reverse ls)]))))

(define-syntax (: syn)
  (syntax-parse syn
    [(_ name:id type:expr)
     ;; NB: Unhygenic; need to reuse Racket's identifiers, and make this type annotation a syntax property
     (syntax-parse (cur-expand #'type)
      #:datum-literals (:)
      [(real-Π (x:id : type) body) (void)]
      [_
       (raise-syntax-error
        ':
        "Can only declare annotations for functions, but not a function type"
        syn)])
     (dict-set! annotation-dict (syntax->datum #'name) (annotation->types #'type))
     #'(void)]))

;; TODO: These parameters should be syntax-parameters, but trying to use them resulted in
;; strange error
(begin-for-syntax
  (define current-definition-id (make-parameter #f))
  (define current-definition-param-decl (make-parameter #f))

  )
;(define-syntax-parameter current-definition-id #f)

;; TODO: Allow inferring types as in above TODOs for lambda, forall
(define-syntax (define syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(define (name:id x:id ...) body)
     (cond
       [(dict-ref annotation-dict (syntax->datum #'name)) =>
        (lambda (anns)
          (quasisyntax/loc syn
            (define (name #,@(for/list ([x (syntax->list #'(x ...))]
                                        [type anns])
                               #`(#,x : #,type)))
              body)))]
       [else
        (raise-syntax-error
         'define
         "Cannot omit type annotations unless you have declared them with (: name type) form first."
         syn)])]
    [(define (name (x : t) ...) body)
     (current-definition-param-decl (syntax->list #`((x : t) ...)))
     (quasisyntax/loc syn
       (define name (lambda (x : t) ... body)))]
    [(define id body)
     ;; TODO: without syntax-parameterize, or similar, this information will become stale and may
     ;; result in incorrect expansion
     (current-definition-id #'id)
     (quasisyntax/loc syn
       (real-define id body))]))


#|
(begin-for-syntax
  (define (type->telescope syn)
    (syntax-parse (cur-expand syn)
      #:literals (real-Π)
      #:datum-literals (:)
      [(real-Π (x:id : t) body)
       (cons #'(x : t) (type->telescope #'body))]
      [_ '()]))

  (define (type->body syn)
    (syntax-parse syn
      #:literals (real-Π)
      #:datum-literals (:)
      [(real-Π (x:id : t) body)
       (type->body #'body)]
      [e #'e]))

  (define (constructor-indices D syn)
    (let loop ([syn syn]
               [args '()])
      (syntax-parse (cur-expand syn)
        #:literals (real-app)
        [D:id args]
        [(real-app e1 e2)
         (loop #'e1 (cons #'e2 args))])))

  (define (inductive-index-telescope D)
    (type->telescope (cur-type-infer D)))

  (define (inductive-method-telescope D motive)
    (for/list ([syn (cur-constructor-map D)])
      (with-syntax ([(c : t) syn]
                    [name (gensym (format-symbol "~a-~a" #'c 'method))]
                    [((arg : arg-type) ...) (type->telescope #'t)]
                    [((rarg : rarg-type) ...) (constructor-recursive-args D #'((arg : arg-type) ...))]
                    [((ih : ih-type) ...) (constructor-inductive-hypotheses #'((rarg : rarg-type) ...) motive)]
                    [(iarg ...) (constructor-indices D (type->body #'t))]
                    )
        #`(name : (forall (arg : arg-type) ...
                          (ih : ih-type) ...
                          (motive iarg ...)))))))

(define-syntax (elim syn)
  (syntax-parse syn
    [(elim D:id U e ...)
     (with-syntax ([((x : t) ...) (inductive-index-telescope #'D)]
                   [motive (gensym 'motive)]
                   [y (gensym 'y)]
                   [disc (gensym 'disc)]
                   [((method : method-type) ...) (inductive-method-telescope #'D #'motive)])
       #`((lambda
            (motive : (forall (x : t) ... (y : (D x ...)) U))
            (method : ) ...
            (x : t) ...
            (disc : (D x ...)) ...
            (real-elim D motive (x ...) (method ...) disc))
          e ...)
       )
     ]))
|#

;; Quite fragie to give a syntactic treatment of pattern matching -> eliminator. Replace with "Elimination with a Motive"
(begin-for-syntax
  (define ih-dict (make-hash))

  (define-syntax-class curried-application
    (pattern
     ((~literal real-app) name:id e:expr)
     #:attr args
     (list #'e))

    ;; TODO BUG: will not match when a is not expanded yet
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
     #:attr params
     (take (attribute a.args) (cur-data-parameters (attribute a.name)))
     #:attr indices
     (drop (attribute a.args) (cur-data-parameters (attribute a.name)))
     #:attr names
     (for/list ([e (attribute indices)])
       (format-id e "~a" (gensym 'anon-index)))
     #:attr types
     ;; TODO: Detect failure, report error/suggestions
     (for/list ([e (attribute indices)])
       (or (cur-type-infer e)
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
         (#,(gensym 'anon-discriminant) : (inductive-name #,@(attribute params) #,@(attribute names))))))
     #:attr abstract-indices
     (lambda (return)
       ;; NB: unhygenic
       ;; Normalize at compile-time, for efficiency at run-time
       (cur-normalize
        #`((lambda
              ;; TODO: utterly fragile; relies on the indices being referred to by name, not computed
              ;; works only for simple type families and simple matches on them
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
             [ih-type (cur-normalize #`(#,motive #,@(attribute type.indices) #,name-syn))])
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
           (cur-type-infer #:local-env (attribute p.local-env) #'b)))))

  (define (replace-recursive-call body)
    (syntax-parse (cur-expand body)
      #:literals (real-lambda real-Π real-app elim)
      [(real-lambda (x : t) e)
       #`(real-lambda (x : #,(replace-recursive-call #'t)) #,(replace-recursive-call #'e))]
      [(real-Π (x : t) e)
       #`(real-Π (x : #,(replace-recursive-call #'t)) #,(replace-recursive-call #'e))]
      [(real-app e:id a:expr)
       ;; TODO: Need proper identifiers to do the right thing
       #:when (and (current-definition-id) (eq? (syntax-e #'e) (syntax-e (current-definition-id))))
;       #:when (bound-identifier=? #'e (syntax-parameter-value #'current-definition-id))
       #`(lambda #,@(cdr (current-definition-param-decl)) (recur #,(replace-recursive-call #'a)))]
      [(real-app e:expr e2:expr)
       #`(#,(replace-recursive-call #'e) #,(replace-recursive-call #'e2))]
      [(elim e:expr ...)
       #`(elim #,@(map replace-recursive-call (attribute e)))]
      [x:id #'x]))

  (define-syntax-class (match-clause D motive)
    (pattern
     ((~var p (match-pattern D motive))
      ;; TODO: nothing more advanced?
      b:expr)
     #:attr method
     (let ([b (replace-recursive-call #'b)])
       (quasisyntax/loc #'p
         #,(if (null? (attribute p.decls))
               b
               #`(lambda #,@(attribute p.decls) #,b)))))))

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
         ([t (or (cur-type-infer #'d)
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
        ;; Replace each of the D.indices with the equivalent name from D.decls
        (~bind (motive (quasisyntax/loc syn
                         (lambda #,@(attribute D.decls)
                           #,((attribute D.abstract-indices) (attribute return-type))))))
        (~var c (match-clause (attribute D) (attribute motive))) ...)
     ;; TODO: Make all syntax extensions type check, report good error, rather than fail at Curnel
     (quasisyntax/loc syn
       (elim
        D.inductive-name
        motive
        (c.method ...)
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
                     (unless (cur-type-check? #'e #'t)
                       (raise-syntax-error
                         'let
                         (format "Term ~a does not have expected type ~a. Inferred type was ~a"
                                 (cur->datum #'e) (cur->datum #'t) (cur->datum (cur-type-infer #'e)))
                         #'e (quasisyntax/loc #'x (x e))))
                     #'t]
                    [(cur-type-infer #'e)]
                    [else
                      (raise-syntax-error
                        'let
                        "Could not infer type of let bound expression"
                        #'e (quasisyntax/loc #'x (x e)))]))))
(define-syntax (let syn)
  (syntax-parse syn
    [(let (c:let-clause ...) body)
     #'((lambda (c.id : c.type) ... body) c.e ...)]))

;; Normally type checking will only happen if a term is actually used/appears at top-level.
;; This forces a term to be checked against a particular type.
(define-syntax (:: syn)
  (syntax-case syn ()
    [(_ pf t)
     (begin
       ;; TODO: Code duplication in let-clause pattern
       (unless (cur-type-check? #'pf #'t)
         (raise-syntax-error
           '::
           (format "Term ~a does not have expected type ~a. Inferred type was ~a"
                   (cur->datum #'pf) (cur->datum #'t) (cur->datum (cur-type-infer #'pf)))
           syn))
       #'(void))]))

(define-syntax (run syn)
  (syntax-case syn ()
    [(_ expr) (cur-normalize #'expr)]))

(define-syntax (step syn)
  (syntax-case syn ()
    [(_ expr)
     (let ([t (cur-step #'expr)])
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
       (printf "\"~a\" has type \"~a\"~n" (syntax->datum #'term) (syntax->datum (cur-type-infer #'term)))
       ;; Void is undocumented and a hack, but sort of works
       #'(void))]))

(begin-for-syntax
  (define-syntax (cur-match syn)
    (syntax-case syn ()
      [(_ syn [pattern body] ...)
       #'(syntax-parse (cur-expand syn)
           [pattern body] ...)])))

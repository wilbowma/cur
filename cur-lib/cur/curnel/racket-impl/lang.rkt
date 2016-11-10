#lang racket/base
#| TODO NB XXX Before merging:
 | 1. Handle all TODOs
 | 2. ensure all error messages are reported with surface expression and source information
 | 3. be consistent about using #' vs attribute. (I seem to think attribute do more than #' even when
 |    referring to pattern variables, but I'm not sure that's true)
 | 4. Test
 |    - a. things that should work
 |    - b. things that shouldn't
 | 5. Ensure backwards compatibility
 | ~6. Have Stephen review code/maybe rewrite using his library.~--Library requires term/type/kind
 |     distinction, and has a lot of dependenices. Would complicate core too much.
 | 7. Get rid of boilerplatey stuff; superseded by using library.
 | 8. Abstract errors/make consistent
 |#
(require
 (only-in racket/struct struct->list)
 (only-in racket/function curryr)
 (for-syntax
  racket/base
  (only-in racket/syntax format-id)
  syntax/parse))
(provide
 (rename-out
  [cur-type Type]
  [cur-define define]
  [cur-λ λ]
  [cur-Π Π]
  [cur-app #%app]
  [cur-axiom axiom]
  [cur-data data]
  [cur-elim elim]
  #;[cur-var #%variable-reference])
 require
 provide
 #%top
 #%datum
 ;(struct-out Type)
 #%module-begin
 (for-syntax
  #%datum))

;;; Reflected (compile-time) and reified (run-time) representations of Curnel terms
;;; ------------------------------------------------------------------------

;; The run-time representation of univeres. (Type i), where i is a Nat.
(struct Type (level) #:transparent)

;; The run-time representation of Π types. (Π t f), where is a type and f is a procedure that computes
;; the body type given an argument.
(struct Π (t f))

;; The run-time representation of an application is a Racket plain application: (#%plain-app e1 e2),
;; where e1 is a procedure and e2 is its argument.

;; The run-time representation of a function is a Racket plain procedure: (#%plain-lambda (f) e)
(begin-for-syntax
  ;; A syntax class for detecting the constructor of a struct
  (define-syntax-class (constructor constr-syn)
    (pattern x:id
             #:attr constr (syntax-property #'x 'constructor-for)
             #:when (and (attribute constr) (free-identifier=? constr-syn #'constr))))

  (define-syntax-class reified-universe
    #:literals (#%plain-app quote Type)
    (pattern (#%plain-app (~var constr (constructor #'Type)) ~! (quote i:nat))
             #:attr level (eval #'i)))

  ;; TODO: Maybe "arg" should be "ann", as in annotation
  (define-syntax-class reified-pi
    #:literals (#%plain-app #%plain-lambda Π)
    (pattern (#%plain-app (~var constr (constructor #'Π)) ~! arg (#%plain-lambda (name) body))))

  (define-syntax-class reified-app
    #:literals (#%plain-app)
    (pattern (#%plain-app operator operand)))

  (define-syntax-class reified-lambda
    #:literals (#%plain-lambda)
    (pattern (#%plain-lambda (name) body)
             #:with (_ _ (_ : arg)) (get-type #'name)))

  (define (cur-reflect e)
    (syntax-parse e
      #:literals (#%plain-app #%plain-lambda)
      [x:id e]
      [e:reified-universe
       #`(cur-Type e.level)]
      [e:reified-pi
       #`(cur-Π (e.name : #,(cur-reflect #'e.arg)) #,(cur-reflect #'e.body))]
      [e:reified-app
       #`(cur-app #,(cur-reflect #'e.operator) #,(cur-reflect #'e.operand))]
      [e:reified-lambda
       #`(cur-λ (e.name : #,(cur-reflect #'e.arg)) #,(cur-reflect #'e.body))])))

(begin-for-syntax
  (module+ test
    (require chk))
  (define (maybe-syntax->datum x)
    (if (syntax? x)
        (syntax->datum x)
        x))

  (require racket/trace)

  (current-trace-print-args
   (let ([ctpa (current-trace-print-args)])
     (lambda (s l kw l2 n)
       (ctpa s (map maybe-syntax->datum l) kw l2 n))))
  (current-trace-print-results
   (let ([ctpr (current-trace-print-results)])
     (lambda (s l n)
       (ctpr s (map maybe-syntax->datum l) n)))))

(begin-for-syntax
  (define (fresh [x #f])
    (datum->syntax x (gensym (if x (syntax->datum x) 'x))))

  (define (cur-local-expand e)
    (local-expand e 'expression null))

  ;; Helpers; based on Types as Macros
  (trace-define (set-type e t)
    (syntax-property e 'type (syntax-local-introduce t)))

  (define (erase-type e)
    (cur-local-expand e))

  (require racket/list)
  (define (and-print . e)
    (map (compose displayln maybe-syntax->datum) e)
    (last e))

  (define (merge-type-props syn t)
    ;; TODO: Check that list is consistent and report error if not
    (if (pair? t) (car t) t))

  (define (get-type e #:ctx [ctx #'()])
    (displayln e)
    (syntax-parse ctx
      #:datum-literals (:)
      #:literals (#%plain-lambda let-values)
      [([x:id t] ...)
       #:with (yv ...) (map fresh (attribute x))
       #:with (#%plain-lambda (zv ...) (let-values () (let-values () e2)))
       (cur-local-expand
        #`(lambda (yv ...)
            (let-syntax ([x (make-rename-transformer (set-type #'yv #'t))] ...)
              #,e)))
       ;; TODO: Not sure if this is sensible; testing seemed to indicate "no"
       ;#:with (yt ...) (map fresh (attribute x))
       ;#:with (#%plain-lambda (zt ...) (let-values () (let-values () t2)))
       #;(cur-local-expand
        #`(lambda (yt ...)
            (let-syntax ([x (make-rename-transformer (set-type #'yt #'t))] ...)
              #,(merge-type-props e (syntax-property (attribute e2) 'type)))))
       ;; TODO: if t2 is ever #f, an error should be raised. However, this error should be a last resort;
       ;; typed macros should be able to provide their own error message.
       ;; 1. could use exceptions
       ;;    + always get a type error
       ;;    + simplified interface
       ;;    - exceptions feel weird to me
       ;;    - have to remember to handle them in macros
       ;; 2. could pass in an error message
       ;;    + statically enforced that you give a more specific error message
       ;;    + always get a type error
       ;;    - adds some burden to use
       ;;    - may not cover all use cases
       ;; 3. could put in error monad
       ;;    + flexible
       ;;    - may get random, unrelated error if you forget to handle
       ;; look into how types as macros does this
       #:attr maybe-t2 (syntax-property (attribute e2) 'type)
       #:fail-unless (attribute maybe-t2)
       (raise-syntax-error
        'core-type-error
        "Expected a well-typed Curnel term, but found something else"
        (attribute e2))
       #:with t2 (syntax-local-introduce (merge-type-props e (attribute maybe-t2)))
       (and-print #`((zv ...) (zv ...) (e2 : t2)))]))

  (define (subst v x e)
    (syntax-parse e
      [y:id
       #:when (bound-identifier=? e x)
       v]
      [(e ...)
       #`(#,@(map (lambda (e) (subst v x e)) (attribute e)))]
      [_ e]))
  (module+ test
    (define syn-eq? (lambda (x y) (equal? (syntax->datum x) (syntax->datum y))))
    (chk
     #:eq bound-identifier=? (subst #'z #'x #'x) #'z
     #:eq bound-identifier=? (subst #'z #'x #'y) #'y
; TODO Not sure how to capture this test; x isn't getting the "right" binding...
;     #:eq syn-eq? (subst #'z #'x (expand-syntax-once #'(#%plain-lambda (y) x))) #'(#%plain-lambda (y) z)
     #:eq syn-eq? (subst #'z #'x (expand-syntax-once #'(#%plain-lambda (x) x))) #'(#%plain-lambda (x) x)))

  (define (cur-eval-cbv e)
    (syntax-parse e
      #:literals (#%plain-app #%plain-lambda)
      [A:reified-universe e]
      [x:id e]
      [_:reified-pi e]
      [(#%plain-app e1 e2)
       #:with a (cur-eval-cbv #'e2)
       (syntax-parse (cur-eval-cbv #'e1)
         [(#%plain-lambda (x) body)
          (cur-eval-cbv (subst #'a #'x #'body))]
         [e1-
          #`(#%plain-app e1- a)])]
      [(#%plain-lambda (x) body) e]))

  (define (cur-normalize e)
    ;; TODO:
    ;; Beta reduce until no more betas
    ;; Eta expand while non-lambda term that is of function type.
    ;; Reify the runtime syntax into the surface syntax.
    (cur-eval-cbv (cur-local-expand e))
    #;(reify (eta-expand (beta-reduce (cur-local-expand e)))))

  ;; TODO: This is more like "types compatible" or something. Look at implementation of subtyping to
  ;; see how to do conversion probably.
  (define (type-equal? t1 t2)
    (syntax-parse #`(#,(cur-normalize t1) #,(cur-normalize t2))
      #:literals (#%plain-app #%plain-lambda)
      #:datum-literals (:)
      [(x:id y:id)
       (free-identifier=? t1 t2)]
      [(A:reified-universe B:reified-universe)
       (<= (attribute A.level) (attribute B.level))]
      ;; TODO: Can we compile surface patterns into the expanded representation? Do we need to? Maybe
      ;; reify does that work
      #;[((cur-Π (x:id : A₁) B₁)
        (cur-Π (y:id : A₂) B₂))]
      [(e1:reified-pi e2:reified-pi)
       (and (type-equal? #'e1.arg #'e2.arg)
            (type-equal? #'e1.body (subst #'e1.name #'e2.name #'e2.body)))]
      [((#%plain-app e1 e2) (#%plain-app e1^ e2^))
       (and (type-equal? #'e1 #'e1^) (type-equal? #'e2 #'e2^))]
      [((#%plain-lambda (x1) e1) (#%plain-lambda (x2) e2))
       (type-equal? #'e1 (subst #'x1 #'x2 #'e2))]
      ;; TODO: Is this complete?
      [_ #f #;(error 'type-equal? (format "not implemented for ~a ~a" t1 t2))]))

  (define-syntax-class telescope
    (pattern (cur-Π (x : t1) t2:telescope)
             #:attr hole #'t2.hole
             #:attr xs (cons #'x (attribute t2.xs)))

    (pattern hole:expr
             #:attr xs '())))

(define-syntax (cur-define syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_ name:id body:expr)
     #:with y (fresh)
     #:with (_ _ (e : t)) (get-type (attribute body))
     #`(begin
         (define-syntax name (make-rename-transformer (set-type #'y #'t)))
         (define y e))]))

#;(define-syntax cur-module-begin)


;; Returns the definitions for the axiom, the constructor (as an identifier) and the predicate (as an identifier).
(define-for-syntax (make-axiom n t)
  (syntax-parse (list n t)
    [(name:id type:telescope)
     #:with axiom (fresh n)
     #:do (printf "Props: ~a~n" (syntax-property-symbol-keys n))
     #:with make-axiom (format-id n "make-~a" (syntax->datum #'axiom) #:props n)
     (values
      #`(begin
          (struct axiom (#,@(attribute type.xs)) #:transparent #:reflection-name 'name)
          (define-syntax name (make-rename-transformer (set-type #'make-axiom (cur-local-expand #'type))))
          (define make-axiom ((curryr axiom))))
      #'make-axiom
      (format-id n "~a?" (syntax->datum #'axiom)))]
    [_ (error 'make-axiom "Something terrible has happened")]))

(define-syntax (cur-axiom syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_ name:id : type:telescope)
     #:with (_ _ (_ : U)) (get-type #'type)
     #:fail-unless (attribute U)
     (error 'core-type-error (format "Axiom ~a has declared type ~a, which is not valid" #'name #'type))
     (let-values ([(defs _1 _2) (make-axiom #'name #'type)])
       defs)]))

;; TODO: Strict positivity checking
;; TODO: Recursion
;; TODO: Rewrite and abstract this code omg
(define-syntax (cur-data syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(data name:id : params:nat type
           (c:id : c-type)
           ...)
     #:with (cs ...) (map (λ (x) (syntax-property (syntax-property x 'constant #t) 'params (eval #'params)))
                          (syntax->list #'(c ...)))
     #:with (m ...) (map fresh (syntax->list #'(c ...)))
     #:attr ls (for/list ([c (syntax->list #'(cs ...))]
                          [t (syntax->list #'(c-type ...))])
                 (let-values ([(defs _ pred?) (make-axiom c t)])
                   (cons defs (λ (e m)
                                #`[(#,pred? #,e)
                                   (if (null? (struct->list #,e))
                                       #,m
                                       (apply #,m (struct->list #,e)))]))))
     #:attr c-defs (map car (attribute ls))
     #:attr branch-templates (map cdr (attribute ls))
     #:attr elim-name (format-id syn "~a-elim" (syntax->datum #'name))
     #`(begin
         (cur-axiom #,(syntax-property (syntax-property (syntax-property (syntax-property #'name 'inductive #t)
                                                        'constructors (length (syntax->list #'(c
                                                                                               ...))))
                                                        'params (eval #'params)) 'elim-name (attribute
                                                                                             elim-name)) : type)
         #,@(attribute c-defs)
         (define #,(attribute elim-name)
           (lambda (e m ...)
             (cond
               #,@(map (λ (f m) (f #'e m)) (attribute branch-templates) (syntax->list #'(m ...)))))))]))

(begin-for-syntax
  (trace-define (check-motive mt D)
    (syntax-parse (get-type D)
      [(_ _ (_ : t))
       #'t]
      [_ (error "meow")])))

;; TODO: Type check motive, methods.
;; TODO: Return type
(define-syntax (cur-elim syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_ e motive methods)
     #:with (_ _ (e^ : t)) (get-type #'e)
     #:with (_ _ (t^ : U)) (get-type #'t)
     #:fail-unless (syntax-parse #'U
                     [_:reified-universe #t]
                     [_ #f])
     (raise-syntax-error 'core-type-error
                         (format "Can only eliminate a fully applied inductive type. The type of the
discriminant ~a is ~a, which accepts more arguments"
                         (attribute e)
                         (attribute t))
                         syn)
     #:fail-unless (syntax-parse #'t^
                     #:literals (#%plain-app)
                     [(#%plain-app x:id . r)
                      (syntax-property #'x 'inductive)]
                     [x:id
                      (syntax-property #'x 'inductive)]
                     [_ #f])
     (raise-syntax-error 'core-type-error
                         (format "Can only eliminate an inductive type, but ~a is of type ~a, which is not an inductive."
                         (attribute e)
                         (syntax-property (attribute t) 'origin))
                         syn)
     #:with (_ _ (motive^ : mt)) (get-type #'motive)
     #:fail-unless (syntax-parse #'mt [e:reified-pi #t] [_ #f])
     (raise-syntax-error
      'core-type-error
      (format "Expected motive to be a function, but found ~a of type ~a"
              #'motive
              (last (syntax-property #'mt 'origin)))
      syn
      #'motive)
     #:with name
     (syntax-parse #'t^
       #:literals (#%plain-app)
       [(#%plain-app x:id . r)
        #'x]
       [x:id
        #'x])
     #:with elim-name
     (syntax-property #'name 'elim-name)
;     #:do [(check-motive #'mt #'name)]
     #:attr constructors (syntax-parse #'t^
                          #:literals (#%plain-app)
                          [(#%plain-app x:id . r)
                           (syntax-property #'x 'constructors)]
                          [x:id
                           (syntax-property #'x 'constructors)])
     #:fail-unless (= (attribute constructors) (length (syntax->list #'methods)))
     (raise-syntax-error 'core-type-error
                         "Need one method for each constructor; found ~a constructors and ~a branches"
                         (syntax-property #'D 'constructors)
                         (length (syntax->list #'methods))
                         syn)
     #:with ((_ _ (methods^ : _)) ...) (map get-type (syntax->list #'methods))
     #`(elim-name e^ methods^ ...)]))


(define-syntax (cur-type syn)
  (syntax-parse syn
    [(_ i:nat)
     (set-type (quasisyntax/loc syn (Type i)) #`(cur-type #,(add1 (eval #'i))))]))

#;(define-syntax (cur-var syn)
  (syntax-parse syn
    [(_ . x:id)
     #:with (e : t) (get-type #'x)
     #`(#%variable-reference . e)]))


(require racket/trace)
(define-syntax (cur-Π syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_ (x:id : t1:expr) ~! e:expr)
     #:with (_ _ (t1^ : _)) (get-type #'t1)
     #:with ((zv) (zt) (e2 : U)) (get-type (attribute e) #:ctx #`([#,(attribute x) t1^]))
     #:fail-unless (attribute U)
     (raise-syntax-error 'core-type-error
                         "Could not infer type of Π"
                         (attribute e))
     (set-type
      (quasisyntax/loc syn (Π t1^ (lambda (zv) #,(erase-type (attribute e2)))))
      (quasisyntax/loc syn U))]))

(define-syntax (cur-λ syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_ (x:id : t1:expr) e:expr #;cur-syntax )
     #:with (_ _ (t1^ : _)) (get-type #'t1)
     #:with ((zv) (zt) (e2 : t2)) (get-type #'e #:ctx #`([#,(attribute x) t1^]))
     #:fail-unless (attribute t2)
     (raise-syntax-error 'core-type-error
                         "Could not infer type of body of function"
                         (attribute e))
     (set-type
      (quasisyntax/loc syn (lambda (zv) #,(erase-type #'e2)))
      (quasisyntax/loc syn #,(cur-local-expand #'(cur-Π (zt : t1^) t2))))]))

(define-syntax (cur-app syn)
  (syntax-parse syn
    #:datum-literals (:)
    #:literals (#%plain-app)
    [(_ e1:expr e2:expr)
     #:with (_ _ (e1^ : f-type)) (get-type #'e1)
     ;; TODO: More error checking. Maybe hide error checkings and stuff in syntax-classes? Maybe mimic turnstyle.
     #:fail-unless (syntax-parse #'f-type [e:reified-pi #t] [_ #f])
     (raise-syntax-error
      'core-type-error
      (format "Expected function but found something ~a of type ~a"
              ;; TODO Should probably be using 'origin  in more error messages. Maybe need principled
              ;; way to do that.
              (syntax-property (attribute e1) 'origin)
              (syntax-property (attribute f-type) 'origin))
      syn)
;     #:with (cur-Π (x : t1) e) #'f-type
     #:with f-type-again:reified-pi #'f-type
     #:attr t1 (attribute f-type-again.arg)
     #:with (_ _ (e2^ : maybe-t1)) (get-type #'e2)
     #:fail-unless (attribute maybe-t1)
     (raise-syntax-error
      'core-type-error
      (format "Could not infer the type of argument ~a to function ~a; expected argument of type ~a"
              (attribute e2)
              (attribute e1)
              (attribute t1))
      syn)
     #:fail-unless (type-equal? #'t1 #'maybe-t1)
     (raise-syntax-error
      'core-type-error
      (format "Function ~a expected argument of type ~a but received argument ~a of type ~a"
              (attribute e1)
              (attribute t1)
              (attribute e2)
              (attribute maybe-t1))
      syn)
     #:with x (attribute f-type-again.name)
     #:with e (attribute f-type-again.body)
     ;; TODO: This computation seems to be over erased terms, hence t2^ has no type.
     ;; Need to reify t2^ back into the core macros, so it's type will be computed if necessary.
     ;; This may be part of a large problem/solution: need to reify terms after evaluation, so we can
     ;; pattern match on the core syntax and not the runtime representation.
     #:with t2^ (subst #'e2 #'x #'e)
     (set-type
      (quasisyntax/loc syn (#%app e1^ e2^))
      (quasisyntax/loc syn t2^))]))

#;(define-syntax cur-elim)

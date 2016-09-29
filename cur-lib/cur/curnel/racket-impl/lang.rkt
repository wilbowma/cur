#lang racket/base
#| TODO NB XXX Before merging:
 | 1. Handle all TODOs
 | 2. ensure all error messages are reported with surface expression and source information
 | 3. be consistent about using #' vs attribute. (I seem to think attribute do more than #' even when
 |    referring to pattern variables, but I'm not sure that's true)
 | 4. Test
 | 5. Ensure backwards compatibility
 | 6. Have Stephen review code/maybe rewrite using his library.
 | 7. Get rid of boilerplatey stuff; superseded by using library.
 | 8. Abstract errors/make consistent
 |#
(require
 (for-syntax
  racket/base
  syntax/parse))

(provide
 (rename-out
  [cur-type Type]
  [cur-define define]
  [cur-λ λ]
  [cur-Π Π]
  [cur-app #%app]
  [cur-axiom axiom]
  #;[cur-var #%variable-reference])
 #%top
 #%datum
 ;(struct-out Type)
 #%module-begin
 (for-syntax
  #%datum))

(begin-for-syntax
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
  (define (set-type e t)
    (syntax-property e 'type t))

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
       ;#:with (yt ...) (map fresh (attribute x))
       ;#:with (#%plain-lambda (zt ...) (let-values () (let-values () t2)))
       #;(cur-local-expand
        #`(lambda (yt ...)
            (let-syntax ([x (make-rename-transformer (set-type #'yt #'t))] ...)
              #,(merge-type-props e (syntax-property (attribute e2) 'type)))))
       #:with t2 (merge-type-props e (syntax-property (attribute e2) 'type))
       #`((zv ...) (zv ...) (e2 : t2))]))

  (define (free-maybe-identifier=? x1 x2)
    (and (identifier? x1) (identifier? x2) (free-identifier=? x1 x2)))

  ;; TODO: Remove dead code
  (define (lift-id-equal? s1 s2)
    (map free-maybe-identifier=? (syntax-e s1) (syntax-e s2)))

  (define-syntax-class Type-constr
    (pattern x:id #:when (free-identifier=? #'Type (syntax-property #'x 'constructor-for))))

  (define (type-equal? t1 t2)
    (syntax-parse #`(#,(cur-local-expand t1) #,(cur-local-expand t2))
      #:literals (Type #%plain-app quote)
      [(x:id y:id)
       (free-identifier=? t1 t2)]
      [((#%plain-app _:Type-constr (quote i:nat)) (#%plain-app _:Type-constr (quote j:nat)))
       (<= (eval #'i) (eval #'j))]
      ;; TODO: implement the rest of it.
      [_ (error 'type-equal? (format "not implemented for ~a ~a" t1 t2))]))

  ;; TODO: Substitution doesn't seem to work. Maybe need to use lambda to bind
  ;; Takes a type that binds (must expand to something with a Racket lambda as it's final form) and a
  ;; thing to substitute
  (define (subst v x e);(subst binds v)
    (define (_subst v x e)
      (syntax-parse e
        [y:id
         ;; TODO: Stephen's code says this should be bound-identifier=?, but that doesn't work. While this does.
         ;; And this makes more sense... x and y *are* free; they've been taken out of the scope of
         ;; their lambda... unless e is supposed to be a lambda expression, and x is it's argument?
         ;; That could make sense.
         #:when (free-identifier=? e x)
         v]
        [(e ...)
         #`(#,@(map (lambda (e) (_subst v x e)) (attribute e)))]
        [_ e]))
    (_subst v x e)
    #;(syntax-parse binds
      #:literals (#%plain-lambda)
      [(cur-Π (x : t1) e2)
       (_subst v #'x #'e2)]))

  ;; syntax classes
  #;(define-syntax-class cur-syntax
    )
  (define-syntax-class cur-type-level-annotation
    (pattern i:nat))

  (define-syntax-class cur-expr
    (pattern e:expr #;cur-syntax
             #:fail-unless (get-type (attribute e))
             (raise-syntax-error 'core-type-error "Could not infer any type for term"
                                 (attribute e))))

  (define-syntax-class telescope
    (pattern (cur-Π (x : t1) t2:telescope)
             #:attr xs (cons #'x (attribute t2.xs)))

    (pattern e:expr
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

(require racket/function)
(define-syntax (cur-axiom syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_ name:id : type:telescope)
     #:with (_ _ (_ : U)) (get-type #'type)
     #:fail-unless (attribute U)
     (error 'core-type-error (format "Axiom ~a has declared type ~a, which is not valid" #'name #'type))
     #:with axiom (fresh #'axiom)
     #:with make-axiom (fresh #'make-axiom)
     #`(begin
         (struct axiom (#,@(attribute type.xs)) #:transparent #:reflection-name 'name #:constructor-name make-axiom)
         (define-syntax name (make-rename-transformer (set-type #'y #'type)))
         (define y ((curryr make-axiom))))]))

#;(define-syntax (cur-data syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(data name:id : params:nat type:cur-expr
           (c:id : c-type:cur-expr)
           ...)
     ]))

(struct Type (level) #:transparent)

(define-syntax (cur-type syn)
  (syntax-parse syn
    [(_ i:cur-type-level-annotation)
     ;; NB: This #%app is necessary; otherwise, the syntax-property 'type seems to get duplicated
     (set-type (quasisyntax/loc syn (Type i)) #`(cur-type #,(add1 (eval #'i))))]))

#;(define-syntax (cur-var syn)
  (syntax-parse syn
    [(_ . x:id)
     #:with (e : t) (get-type #'x)
     #`(#%variable-reference . e)]))

(struct Π (t f))

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
      (quasisyntax/loc syn (cur-Π (zt : t1^) t2)))]))

(define-syntax (cur-app syn)
  (syntax-parse syn
    #:datum-literals (:)
    #:literals (#%plain-app)
    [(_ e1:expr e2:expr)
     #:with (_ _ (e1^ : f-type)) (get-type #'e1)
     ;; TODO: Wish this could be (cur-Π (x : t1) e)
     ;#:with (#%plain-app Π t1 f) #'f-type
     #:with (cur-Π (x : t1) e) #'f-type
     #:with (_ _ (e2^ : maybe-t1)) (get-type #'e2)
     #:fail-unless (type-equal? #'t1 #'maybe-t1)
     (raise-syntax-error
      'core-type-error
      (format "Function ~a expected argument of type ~a but received argument ~a of type ~a"
              (attribute e1)
              (attribute t1)
              (attribute e2)
              (attribute maybe-t1))
      syn)
;     #:with t2^ (subst #'f-type #'e2)
     #:with t2^ (subst #'e2 #'x #'e)
     ;; TODO: See thoughts about this on definition of subst
;     #:with (#%plain-lambda _ t2^)(subst #'e2 #'x #'(#%plain-lambda (x) e))
     (set-type
      (quasisyntax/loc syn (#%app e1^ e2^))
      (quasisyntax/loc syn t2^))]))

#;(define-syntax cur-elim)


#lang racket/base
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

  (define (and-print e)
    (displayln (maybe-syntax->datum e))
    e)

  (define (get-type e #:ctx [ctx #'()])
    (syntax-parse ctx
      #:datum-literals (:)
      ;; Including lambda in this literals list prevents the #:with clause from matching, causing
      ;; terrible terrible error messages.
      ;; TODO: File bug report
      #:literals (let-values)
      [(y:id ... [x:id t] ...)
       #:with (st ...) (map set-type (attribute y) (attribute t))
       #:with (_ (z ...) (let-values () (let-values () e2)))
       ;; If cur-local-expand uses #f instead of '() for the stop list, then this @:with
       ;; pattern won't match, and a an absolutely terrible error message results.
       ;; TODO: File bug report
       (cur-local-expand
        #`(lambda (y ...)
            (let-syntax ([x (syntax-id-rules () [_ st])] ...)
              #,e)))
       #`(z ... e2 : #,(syntax-property (attribute e2) 'type))]))

  (define (free-maybe-identifier=? x1 x2)
    (and (identifier? x1) (identifier? x2) (free-identifier=? x1 x2)))

  (define (lift-id-equal? s1 s2)
    (map free-maybe-identifier=? (syntax-e s1) (syntax-e s2)))

  (define (type-equal? t1 t2)
    (or (free-maybe-identifier=? t1 t2)
        (lift-id-equal? t1 t2)
        (error "type equality not yet implemented")))

  ;; TODO: Substitution doesn't seem to work. Maybe need to use lambda to bind
  (trace-define (subst v x e)
    (syntax-parse e
      [y:id
       #:when (bound-identifier=? e x)
       v]
      [(e ...)
       #`(#,@(map (lambda (e) (subst v x e)) (attribute e)))]
      [_ e]))

  (trace-define (substs vs xs e)
    (foldr subst e vs xs))

  ;; syntax classes
  #;(define-syntax-class cur-syntax
    )
  (define-syntax-class cur-type-level-annotation
    (pattern i:nat))

  (define-syntax-class cur-expr
    (pattern e:expr #;cur-syntax
             #:fail-unless (get-type (attribute e))
             (raise-syntax-error 'core-type-error "Could not infer any type for term"
                                 (attribute e)))))

(define-syntax (cur-define syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_ name:id body:expr)
     #:with (e : t) (get-type (attribute body))
     #`(define #,(set-type #'name #'t) e)]))

#;(define-syntax cur-module-begin)

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
     (set-type (quasisyntax/loc syn (#%app Type i)) #`(cur-type #,(add1 (eval #'i))))]))

#;(define-syntax (cur-var syn)
  (syntax-parse syn
    [(_ . x:id)
     #:with (e : t) (get-type #'x)
     #`(#%variable-reference . e)]))

(struct Π (t f))
(define-syntax (cur-Π syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_ (x:id : t1:expr) ~! e:expr)
     #:with y (fresh)
     #:with (z e2 : t2) (get-type #'e #:ctx #`(y [x t1]))
     #:fail-unless (attribute t2)
     (raise-syntax-error 'core-type-error
                         "Could not infer type of body of Π"
                         (attribute e))
     (set-type
      (quasisyntax/loc syn (Π t1 (lambda (z) e2)))
      (quasisyntax/loc syn (attribute t2)))]))

(define-syntax (cur-λ syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_ (x:id : t1:expr) e:expr #;cur-syntax )
     #:with y (fresh #'x)
     #:with (z e2 : t2) (get-type #'e #:ctx #`(y [#,(attribute x) t1]))
     #:fail-unless (attribute t2)
     (raise-syntax-error 'core-type-error
                         "Could not infer type of body of function"
                         (attribute e))
     (set-type
      (quasisyntax/loc syn (lambda (z) #,(erase-type #'e2)))
      (quasisyntax/loc syn (cur-Π (x : t1) t2)))]))

(define-syntax (cur-app syn)
  (syntax-parse syn
    #:datum-literals (:)
    #:literals (let-values)
    [(_ e1:cur-expr e2:expr)
     #:with (_  : (cur-Π (x : t1) t2)) (get-type #'e1)
     #:with (_ : maybe-t1) (get-type #'e2)
     #:fail-unless (type-equal? #'t1 #'maybe-t1)
     (raise-syntax-error
      'core-type-error
      (format "Function ~a expected argument of type ~a but received argument ~a of type ~a"
              (attribute e1)
              (attribute t1)
              (attribute e2)
              (attribute maybe-t1))
      syn)
     #:with t2^ (subst #'e2 #'x #'t2)
     (set-type
      (quasisyntax/loc syn (#%app #,(erase-type #'e1) #,(erase-type #'e2)))
      (quasisyntax/loc syn t2^))]))

#;(define-syntax cur-elim)

#lang racket/base

(require
 (for-syntax
  "equiv.rkt"
  "elab.rkt"
  "type-reconstructor.rkt"
  racket/base
  syntax/parse)
 "runtime.rkt")

(begin-for-syntax
  (define (cur-reflect syn)
    (syntax-parse syn
      [x:cur-runtime-identifier
       syn
       ;; TODO: I'd love to reflect the names, but I don't think we can.
       #;(or (syntax-property syn 'reflected-name) syn)]
      [e:cur-runtime-universe
       (quasisyntax/loc syn (surface-Type e.level-syn))]
      [e:cur-runtime-pi
       (quasisyntax/loc syn
         (surface-Π (#,(cur-reflect #'e.name) : #,(cur-reflect #'e.ann))
                #,(cur-reflect #'e.result)))]
      [e:cur-runtime-app
       (quasisyntax/loc syn
         (surface-app #,(cur-reflect #'e.rator) #,(cur-reflect #'e.rand)))]
      [e:cur-runtime-lambda
       (quasisyntax/loc syn
         (surface-λ (#,(cur-reflect #'e.name) : #,(cur-reflect #'e.ann)) #,(cur-reflect #'e.body)))]
      [e:cur-runtime-elim
       (quasisyntax/loc syn
         (surface-elim #,(cur-reflect #'e.target) #,(cur-reflect #'e.motive)
                       #,@(map cur-reflect (attribute e.method-ls))))]))

  (define-syntax-class cur-expr #:attributes (reified type)
    (pattern e:expr
             #:attr t (cur-elab #'e)
             #:attr type (get-type #'reified)))

  (define-syntax-class (cur-expr/ctx ctx) #:attributes (reified type)
    (pattern e:expr
             #:with reified (cur-elab/ctx #'e ctx)
             #:with term (get-type #'reified)))

  (define-syntax-class (cur-expr-of-type type) #:attributes (reified)
    (pattern e:cur-expr
             #:fail-unless (cur-subtype? #'e.type type)
             (cur-type-error
              this-syntax
              "term of type ~a"
              (syntax->datum #'e)
              (syntax->datum (cur-reflect #'e.type))
              (syntax->datum (cur-reflect type)))
             #:attr reified #'e.reified))

  (define-syntax-class cur-kind #:attributes (reified type)
    (pattern e:cur-expr
             ;; TODO: A pattern
             #:with (~or type:cur-runtime-universe) #'e.type
             #:fail-unless (attribute type)
             (cur-type-error
              #'e
              "a kind (a type whose type is a universe)"
              (syntax->datum #'e)
              (syntax->datum (last (syntax-property #'e.type 'origin))))
             #:attr reified #'e.reified))

  (define-syntax-class cur-procedure #:attributes (reified type ann name result)
    (pattern e:cur-expr
             #:with (~or type:cur-runtime-pi) #'e.type
             #:fail-unless (attribute type)
             (raise-syntax-error
              'core-type-error
              (format "Expected function, but found ~a of type ~a"
                      ;; TODO Should probably be using 'origin  in more error messages. Maybe need principled
                      ;; way to do that.
                      (syntax->datum #'e)
                      ;; TODO: Not always clear how to resugar; probably need some function for this:
                      ;; 1. Sometimes, origin is the best resugaring.
                      ;; 2. Sometimes, just syntax->datum is.
                      ;; 3. Sometimes, it seems none are, because the type was generated in the macro
                      ;; (e.g. the types of univeres) and origin gives a very very bad
                      ;; resugaring.. Maybe a Racket bug? Bug seems likely, happens only with Type and
                      ;; Pi, which go through struct. Other types seem fine.
                      ;(syntax->datum (last (syntax-property (attribute e) 'origin)))
                      ;(syntax->datum #'e.type)
                      #;(third (syntax-property #'f-type 'origin))
                      (syntax->datum (last (syntax-property #'e.type 'origin))))
              #'e)
             #:attr ann #'type.ann
             #:attr name #'type.name
             #:attr result #'type.result
             #:attr reified #'e.reified))
  )


;; TODO: Make all these for-syntax functions, for testing.
;; Only make the macros in lang.rkt
(define-syntax (surface-Type syn)
  (syntax-parse syn
    [(_ i:nat)
     (quasisyntax/loc syn (#%plain-app cur-Type 'i))]))

(define-syntax (surface-Π syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_ (x:id : t1:cur-kind) (~var e (cur-expr/ctx (list (cons #'x #'t1.reified)))))
     #:declare e.type cur-kind
     (quasisyntax/loc syn
       (#%plain-app cur-Π t1.reified (#%plain-lambda (x) e.reified)))]))

(define-syntax (surface-λ syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_ (x:id : t1:cur-kind) (~var e (cur-expr/ctx (list (cons #'x #'t1.reified)))))
     (quasisyntax/loc syn
       (#%plain-app cur-λ t1.reified (#%plain-lambda (x) e.reified)))]))

(define-syntax (surface-app syn)
  (syntax-parse syn
    [(_ e1:cur-procedure (~var e2 (cur-expr-of-type #'e1.ann)))
     (quasisyntax/loc syn
       (#%plain-app cur-apply e1.reified e2.reified))]))

(define-syntax (surface-define syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_:top-level-id name:id body:cur-expr)
     #:with delta (format-id #'name "delta:~a" #'name)
     #`(begin
         (define-syntax delta (make-variable-like-transformer body.reified))
         (define name delta)
         (define-for-syntax name (identifier-info #'body.type #'delta)))]))

(define-syntax (surface-axiom syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_:top-level-id name:id : type:cur-axiom-telescope)
     #:with c (format-id #'name "constant:~a" #'name)
     #`(begin
         (struct c constant (type.name-ls ...) #:transparent
           #:extra-constructor-name name
           #:reflection name 'name)
         (define-for-syntax name
           (constant-info (lambda (type.name-ls ...) #'type.reified)))))))

;; New syntax:
;; (data (Nat) : 0 (Type 0)
;;   ((z) : (Nat))
;;   ((s (x : (Nat))) : (Nat)))
;; No more pretending these things are functions.
(define-syntax (surface-data syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_:top-level-id (name:id (i:id : itype:cur-expr) ...) : p:nat type:cur-kind
                     ((c-name:id (a:id : (~var atype (cur-expr/ctx (list (cons #'name #'type.reified)))))
                                 ...)
                      :
                      (name (~var r (cur-expr/ctx (list (map cons (attribute a) (attribute atype.reified))))) ...))
                     ...)
     #:do [(define constructor-count (length (attribute c-name)))]
     #:with dispatch (format-id #'name "~a-dispatch" #'name)
     #:with structD (format-id #'name "constant:~a" #'name)
     #:with (structC ...) (map (lambda (x) (format-id x "constant:~a" x)))
     #:with (c-index ...) (build-list constructor-count values)
     #:with (c-recursive-index-ls ...)
     (for/list ([type-ls (attribute atype.reified)])
       (for/list ([type type-ls]
                  [i (in-naturals)]
                  #:when (syntax-parse type
                           [e:cur-runtime-constant
                            (free-identifier=? #'e.name #'name)]))
         i))
     #`(begin
         (define dispatch (box #f))
         (struct structD constant (i ...) #:transparent
           #:extra-constructor-name name
           #:reflection-name 'name
           #:property prop:parameter-count 'p)

         (define-for-syntax name
           (constant-info
            (lambda (i ...)
              #'type.reified)
            'p
            #f
            #f))

         (struct structC constant (a ...) #:transparent
           #:extra-constructor-name c-name
           #:reflection-name 'c-name
           #:property prop:parameter-count 'p
           #:property prop:dispatch dispatch
           #:property prop:recursive-index-ls c-recursive-index-ls)
         ...

         (define-for-syntax c-name
           (constant-info
            (lambda (a ...)
              #'(#%plain-app name r.reified ...))
            'p
            c-index
            c-recursive-index-ls)) ...)]))

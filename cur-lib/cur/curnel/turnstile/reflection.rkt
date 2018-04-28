#lang racket/base
(require
 racket/syntax
 syntax/parse
 racket/function
 syntax/to-string
 syntax/stx
 ;"type-reconstruct.rkt"
 "eval.rkt"
; "runtime-utils.rkt"
 (rename-in "equiv.rkt" [cur-equal? _cur-equal?])
 ;"stxutils.rkt"
; (for-template "type-check.rkt")
 ;(for-template "runtime.rkt")
 (for-template (only-in turnstile/lang infer typecheck? current-type-eval ~and ~parse expand/df ~literal ~fail type=? subst))
 (for-template turnstile/examples/dep-ind-cur)
 (for-template macrotypes/stx-utils)
 (for-template "cur-to-turnstile.rkt")
 (for-template (only-in racket/base quote #%expression void #%plain-lambda #%plain-app list))
 )

(provide
;; with-env
;; call-with-env
 cur->datum
 ;;deprecated-cur-expand
 cur-expand
 cur-type-infer
 cur-type-check?
 cur-constructors-for
 cur-data-parameters
 ;;cur-method-type
 ;;cur-constructor-recursive-index-ls
 ;;cur-constructor-telescope-length
 cur-normalize
 cur-rename
 cur-reflect-id
 ;;cur-step
 cur-equal?
 cur-eval)



(define (cur-type-infer syn)
  (let ([t   (car (cadddr (infer (list syn) )))])
    ;(displayln (format "inferred stx: ~a\n inferred type: ~a\n\n" (syntax->datum syn) (syntax->datum t)))
    (cur-reflect t)))

(define (cur-type-check? term expected-type)
  (let ([inferred-type (car (cadddr (infer (list term))))])
    ;(displayln (format "inferred: ~a\nexpected: ~a" (syntax->datum inferred-type) (syntax->datum expected-type)))
    (typecheck? inferred-type (cur-expand expected-type))))

(define (cur->datum syn) 
  (let ([expanded (cur-expand syn)])
    ;(displayln (format "expanded: ~a" expanded))
    (let ([reflected (cur-reflect expanded)])
      ;(displayln (format "reflected: ~a" reflected))
      (syntax->datum reflected))))

(define (cur-normalize syn)
  (let ([evaled (cur-eval syn)])
    ;(displayln (format "evaled: ~a" evaled))
    (cur-reflect evaled)))

(define (cur-equal? term1 term2)
  (let ([term1-evaled (cur-eval term1)] ;fails on inferred types of constructors with params, param isn't bound in body
        [term2-evaled (cur-eval term2)])
    (type=? term1-evaled term2-evaled)))

(define (cur-constructors-for syn)
  (let ([constructor-ls (syntax-property (cur-expand syn) 'constructors)])
    (if (pair? constructor-ls)
        (syntax->list (car constructor-ls))
        (syntax->list constructor-ls))))

(define (cur-rename new old term) ;bound variables?
  (subst new old term))

(define (cur-data-parameters syn)
  (let ([num-params (syntax-property (cur-expand syn) 'num-parameters)])
    (if (pair? num-params)
        (car num-params)
        num-params)))
  

(define (cur-reflect-id syn)
  (syntax-parse syn
    [c:constructor-id 
     #'c.name]
    [x:defined-id 
     #'x.name]
    [x:axiom-id 
     #'x.name]
    [x:id 
     #'x]))

(define (cur-eval syn)
  ((current-type-eval) syn))

;; TODO: ~Π and ~Type should just be imported from dep-ind-cur, but they aren't exported yet.
(require (for-syntax racket/base syntax/parse))
(define-syntax ~Π
  (pattern-expander
   (lambda (stx)
     (syntax-parse stx
       #:datum-literals (: list)
       ;#:literals (quote #%expression void #%plain-lambda #%plain-app list)
       [(_ ([x : τ_arg]) τ_res)
        #'(_
           _
           (_
            (x)
            _
            (_ _
               (_ _
                  (_ ()
                     _
                     (_ list τ_arg τ_res))))))
        #;#'(#%plain-app
           _
           (#%plain-lambda
            (x)
            (#%expression void)
            (#%plain-app list
                         (#%plain-app _
                                      (#%plain-lambda ()
                                                      (#%expression void)
                                                      (#%plain-app list τ_arg τ_res))))))]))))
(define-syntax ~Type
  (pattern-expander
   (lambda (stx)
     (syntax-parse stx
       ;#:literals (quote #%expression void #%plain-lambda #%plain-app list)
       #:literals (quote)
       [(_ i)
        #'(_
           _
           (_ () _ (_ _ (quote i))))
        #;#'(#%plain-app
           _
           (#%plain-lambda () (#%expression void) (#%plain-app list (quote i))))]))))
   


(define-syntax ~Cons
  (pattern-expander
   (lambda (stx)
     (syntax-parse stx
       [(_ (C x ...))
        #'(_ _
              (_ (_ _ x ...) (_ _))
              (_ (_ _ . _) (expand/df #'(C)))
              (_ (_ _ _)))
        #;#'(~and TMP
                (~parse (~plain-app/c C-:id x ...) (expand/df #'TMP))
                (~parse (_ C+ . _) (expand/df #'(C)))
                (~fail #:unless (free-id=? #'C- #'C+)))]))))

  
(define (cur-reflect syn)
  ;; NB: must be called on fully expanded code;
  ;; TODO: Would be better to enforce that to avoid quadratic expansion cost... 
  (syntax-parse (cur-expand syn)
    #:literals (quote #%expression void #%plain-lambda #%plain-app list )
    #:datum-literals (:)
    [x:id 
     (cur-reflect-id syn)] 
    [(~Type i:exact-nonnegative-integer)
     #'(turn-Type i)]
    [(#%plain-lambda (x:id) body)
     #:with (~Π ([y : t]) _) (syntax-property syn ':)
     #`(turn-λ (x : #,(cur-reflect #'t)) #,(cur-reflect #'body))]
    [(~Π ([x : arg-type]) body-type)
     #`(turn-Π (x : #,(cur-reflect #'arg-type)) #,(cur-reflect #'body-type))]
    [d:expanded-datatype 
     #'d.unexpanded]
    [(#%plain-app fn arg) ;actual application
      #`(turn-app #,(cur-reflect #'fn) #,(cur-reflect #'arg))]))

(define-syntax-class constructor-id #:attributes (name)
  #:commit
  (pattern c:id 
           #:fail-unless (syntax-property #'c 'c-ref-name) (format "error: ~a has no property 'c-ref-name" #'c)
           #:attr name (syntax-property #'c 'c-ref-name)))

(define-syntax-class expanded-datatype #:attributes (unexpanded) #:literals (#%plain-app)
  #:commit
  (pattern (#%plain-app type arg)
           #:fail-unless (syntax-property this-syntax 'data-ref-name) (format "error: ~a has no property 'data-ref-name" this-syntax)
           #:attr unexpanded (syntax-property this-syntax 'data-ref-name))
  (pattern (#%plain-app type)
           #:fail-unless (syntax-property this-syntax 'data-ref-name) (format "error: ~a has no property 'data-ref-name" this-syntax)
           #:attr unexpanded (stx-car (syntax-property this-syntax 'data-ref-name))))

(define-syntax-class defined-id #:attributes (name)
  #:commit
  (pattern x:id
           #:fail-unless (syntax-property #'x 'def-ref-name) (format "error: ~a has no property 'def-ref-name" #'x)
           #:attr name (syntax-property #'x 'def-ref-name)))

(define-syntax-class axiom-id #:attributes (name)
  #:commit
  (pattern x:id
           #:fail-unless (syntax-property #'x 'axiom-ref-name) (format "error: ~a has no property 'axiom-ref-name" #'x)
           #:attr name (syntax-property #'x 'axiom-ref-name)))
           

(define (cur-expand syn)
  (local-expand syn 'expression null))

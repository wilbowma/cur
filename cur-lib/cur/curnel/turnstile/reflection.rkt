#lang racket/base
(require
 racket/syntax
 syntax/parse
 racket/function
 syntax/to-string
 syntax/stx
 racket/list
 ;"type-reconstruct.rkt"
 "eval.rkt"
; "runtime-utils.rkt"
 (rename-in "equiv.rkt" [cur-equal? _cur-equal?])
 "stxutils.rkt"
; (for-template "type-check.rkt")
 ;(for-template "runtime.rkt")
 (only-in macrotypes/stx-utils transfer-props)
 (for-template (only-in turnstile/lang add-orig infer typecheck? current-type-eval ~and ~parse expand/df ~literal ~fail type=? transfer-stx-props))
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
 cur-constructor-recursive-index-ls
 cur-constructor-telescope-length
 cur-normalize
 cur-rename
 cur-reflect-id
 ;;cur-step
 cur-equal?)
(define debug-reflect? #f)
(define debug-datatypes? #f)
(define debug-scopes? #f)


(require racket/trace debug-scopes)
(define (add-scopes maybe-ls)
  (cond
    [(syntax? maybe-ls)
     (+scopes maybe-ls)]
    [(list? maybe-ls)
     (cons (add-scopes (car maybe-ls))
           (add-scopes (cdr maybe-ls)))]
    [else maybe-ls]))
(current-trace-print-args
 (let ([ctpa (current-trace-print-args)])
   (lambda (s l kw l2 n)
     (ctpa s (map (compose add-scopes) l) kw l2 n))))
(current-trace-print-results
 (let ([ctpr (current-trace-print-results)])
   (lambda (s l n)
     (ctpr s (map (compose add-scopes) l) n))))

;copied from racket impl
(define current-env (make-parameter '()))

(define (call-with-env env t)
  ;; TODO: backwards-compatible, but perhaps very slow/memory intensive
  (parameterize ([current-env (append env (current-env))])
    (t)))

(define-syntax-rule (with-env env e)
  (call-with-env env (thunk e)))

(define (env->ctx env) ;`((,#'x . ,#'Type) ...) -> #'([x : type] ...)
  (let ([ctx (datum->syntax #f
                            (map (λ (pr)
                                   (let ([term (car pr)]
                                         [type (cdr pr)])
                                     #`[#,term : #,type])) (reverse env)))])

    ctx))

(define (turnstile-infer syn #:local-env [env '()])
  (let* ([ctx (env->ctx env)]
         [type (car (cadddr (infer (list syn) #:ctx ctx)))])
    type))

(define (turnstile-expand syn #:local-env [env '()]) ;returns ((tvs) (xs) (es) (τs))
  (let ([ctx (env->ctx env)])
    (infer (list syn) #:ctx ctx)))


(define (cur-type-infer syn #:local-env [env '()])
  (let ([t   (turnstile-infer syn #:local-env env)])
    #;(displayln (format "inferred stx: ~a\n inferred type: ~a\n\n" (syntax->datum syn) (syntax->datum t)))
    (cur-reflect (cur-expand t #:local-env env))))

(define (cur-type-check? term expected-type #:local-env [env '()])
  (let ([inferred-type (turnstile-infer term #:local-env env)])
    ;(displayln (format "inferred: ~a\nexpected: ~a" (syntax->datum inferred-type) (syntax->datum expected-type)))
    (typecheck? inferred-type (cur-expand expected-type #:local-env env))))

(define (cur->datum syn)
  (let ([expanded (cur-expand syn)])
    ;(displayln (format "expanded: ~a" expanded))
    (let ([reflected (cur-reflect expanded)])
      ;(displayln (format "reflected: ~a" reflected))
      (syntax->datum reflected))))

(define (cur-normalize syn #:local-env [env '()])
    (let ([evaled (cur-expand syn #:local-env env)])
    #;(displayln (format "in cur-normalize, syn: ~a, evaled: ~a" syn evaled))
      (cur-reflect evaled)))

(define (cur-equal? term1 term2 #:local-env [env '()])
  (let ([term1-evaled (cur-expand term1 #:local-env env)]
        [term2-evaled (cur-expand term2 #:local-env env)])
    #;(displayln (format "in cur-equal? term1: ~a \n term2: ~a" term1-evaled term2-evaled))
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

(define (cur-constructor-telescope-length syn)
  (length (syntax->list (syntax-property (cur-expand syn) 'constructor-args))))

(define (cur-constructor-recursive-index-ls syn) ;TODO
  (let* ([expanded (cur-expand syn)]
         [args (syntax-property expanded 'constructor-args)]
         [rec-args (syntax-property expanded 'constructor-rec-args)])
 #; (displayln (format "expanded: ~a\n\nargs:~a\n\nrec-args:~a\n\n" (syntax->datum expanded) (syntax->datum args) (syntax->datum rec-args)))
    (syntax->list rec-args)))


(define (cur-reflect syn) 
  (syntax-parse syn
    #:literals (quote #%expression void #%plain-lambda #%plain-app list )
    #:datum-literals (:)
    [x:id
     #:do [(when debug-reflect? (displayln (format "id: ~a\n\n" (syntax->datum this-syntax))))]
     (cur-reflect-id syn)]
    [Type:expanded-Type
     #:with i #'Type.n
     #:do [(when debug-reflect? (displayln (format "Type stx class: ~a\n\n" (syntax->datum this-syntax))))]
     #'(cur-Type i)]
    [(#%plain-lambda (x:id) body)
     #:with (~Π ([y : t]) _) (syntax-property syn ':)
     #:do [(when debug-reflect?(displayln (format "lambda: ~a\n\n" (syntax->datum this-syntax))))]
     #`(cur-λ (x : #,(cur-reflect #'t)) #,(cur-reflect #'body))]
    [pi:expanded-Π
     #:with arg #'pi.arg
     #:with τ_arg #'pi.τ_arg
     #:with body #'pi.body
     #:do [(when debug-reflect? (displayln (format "Π stx class: ~a\n\n" (syntax->datum this-syntax))))]
     #`(cur-Π (arg : #,(cur-reflect #'τ_arg)) #,(cur-reflect #'body))]
    [d:expanded-datatype
      #:do [(when debug-reflect? (displayln (format "expanded-datatype case: ~a\n\n" (syntax->datum this-syntax))))]
     #'d.unexpanded]
    [e:expanded-app
     #:with fn #'e.rator
     #:with arg #'e.rand
     #:do [(when debug-reflect? (displayln (format "app stx class: ~a\n\n" (syntax->datum this-syntax))))]
     #`(cur-app #,(cur-reflect #'fn) #,(cur-reflect #'arg))]))

(define-syntax-class expanded-app #:attributes (rator rand) #:literals (#%plain-app)
  #:commit
  (pattern (#%plain-app fn arg)
           #:fail-unless (syntax-property this-syntax 'app) (format "not an app: ~a" (syntax->datum this-syntax))
           #:attr rator #'fn
           #:attr rand #'arg))

(define-syntax-class expanded-Π #:attributes (arg τ_arg body)
  #:commit
  (pattern (~Π ([x : arg-type]) body-type)
           #:fail-unless (syntax-property this-syntax 'Π) (format "not a Π: ~a" (syntax->datum this-syntax))
           #:attr arg #'x
           #:attr τ_arg #'arg-type
           #:attr body #'body-type))

(define-syntax-class expanded-Type #:attributes (n) #:literals (#%plain-app #%plain-lambda #%expression list void quote)
  #:commit
  (pattern (#%plain-app
           _
           (#%plain-lambda () (#%expression void) (#%plain-app list (quote i))))
           #:fail-unless (syntax-property this-syntax 'Type) (format "error: not Type: ~a" this-syntax)
           #:attr n #'i))

(define-syntax-class constructor-id #:attributes (name)
  #:commit
  (pattern c:id
           #:fail-unless (syntax-property #'c 'c-ref-name) (format "error: ~a has no property 'c-ref-name" #'c)
           #:attr name (syntax-local-introduce (syntax-property #'c 'c-ref-name))))

(define-syntax-class expanded-datatype #:attributes (unexpanded) #:literals (#%plain-app #%expression void list #%plain-lambda)
  #:commit
  (pattern (#%plain-app T (#%plain-lambda () (#%expression void) (plain-#%app list A+i+x ... )))
           #:fail-unless (syntax-property this-syntax 'data-ref-name) (format "error: ~a has no property 'data-ref-name" this-syntax)
           #:with expanded-args #'(A+i+x ...)
           #:with data-ref-name (syntax-local-introduce (syntax-property this-syntax 'data-ref-name))
           #:with D (car (syntax->list #'data-ref-name))
           #:with reflected-args (cdr (syntax->list #'data-ref-name))
           #:do [(when debug-datatypes? (displayln (format "expanded datatype:~a\nreflected datatype: ~a" (syntax->datum this-syntax) (syntax->datum #'data-ref-name))))]
           #:do [(when debug-datatypes? (displayln (format "expanded A+i+x:~a\ntypes of expanded A+i+x:~a\nreflected A+i+x:~a\nTypes of reflected A+i+x:~a\nfree-id=?~a"
                                                           (map syntax->datum   (syntax->list #'expanded-args))
                                                           (map turnstile-infer  (syntax->list #'expanded-args))
                                                           (map syntax->datum  (syntax->list #'reflected-args))
                                                           (map turnstile-infer (syntax->list #'reflected-args))
                                                           (map free-identifier=? (syntax->list #'expanded-args) (syntax->list #'reflected-args)))))]
           #:attr unexpanded #'(D A+i+x ...))

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

(define (cur-expand syn #:local-env [env '()])
 (trace-let cur-expand ([syn syn]
                        [env env])
  (let* ([expanded (turnstile-expand syn #:local-env env)]
         [xs-ls (syntax->list (second expanded))]
         [es-ls (syntax->list (third expanded))]
         [env-ids (reverse (map car env))])
    (displayln (add-scopes xs-ls))
    (displayln (add-scopes es-ls))
    (displayln (add-scopes expanded))
    (displayln (add-scopes (subst* env-ids xs-ls (first es-ls))))
    #;(displayln (format "in cur-expand, syn: ~a\n\n env-ids: ~a \n\n expanded: ~a \n\n xs-ls: ~a \n\n es-ls: ~a"
                         syn env-ids expanded xs-ls es-ls))
    (transfer-props syn (subst* env-ids xs-ls (first es-ls))))
  ))

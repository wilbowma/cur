#lang racket/base
(require
 racket/syntax
 syntax/parse
 racket/function
 syntax/to-string
 syntax/stx
 racket/list
 cur/curnel/racket-impl/stxutils
 (for-template (only-in turnstile/lang infer typecheck? type=?))
 (for-template turnstile/examples/dep-ind-cur)
 (for-template cur/curnel/turnstile/cur-to-turnstile)
 (for-template (only-in racket/base quote #%expression void #%plain-lambda #%plain-app list)))

;; copy/paste/modified from macrotype/stx-utils
;; transfer single prop, unless it exists already
;; this isn't enough to get rid of all the duplicate properties, since turnstile
;; doesn't do this internally.
;; but hopefully it helps
(define (transfer-prop p from to)
  (define v (syntax-property from p))
  (if (syntax-property to p)
      to
      (syntax-property to p v)))

;; transfer all props except 'origin, 'orig, and ':
(define (transfer-props from to #:except [dont-transfer '(origin orig :)])
  (define (transfer-from prop to) (transfer-prop prop from to))
  (define props (syntax-property-symbol-keys from))
  (define props/filtered (foldr remove props dont-transfer))
  (foldl transfer-from to props/filtered))

(provide
 with-env
 call-with-env
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
 cur-step
 cur-equal?)
(define debug-reflect? #f)
(define debug-datatypes? #f)
(define debug-scopes? #f)


(require racket/trace debug-scopes)
(provide add-scopes)
(define (add-scopes maybe-ls)
  (cond
    [(syntax? maybe-ls)
     (+scopes maybe-ls)]
    [(pair? maybe-ls)
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
  (with-env env
    (let* ([ctx (env->ctx (current-env))]
           [type (car (cadddr (infer (list syn) #:ctx ctx)))])
    type)))

(define (turnstile-expand syn #:local-env [env '()] . ls) ;returns ((tvs) (xs) (es) (τs))
  (with-env env
    (let ([ctx (env->ctx (current-env))])
      (infer (list syn) #:ctx ctx
            ; #:stop-list? ls future work
             ))))

(define (cur-type-infer syn #:local-env [env '()])
  (with-env env (cur-get-type syn)))

;; XXX: Probably way too much prop transfer going on
(define (cur-get-type syn)
  (let* ([expanded (turnstile-expand syn)]
         [xs-ls (syntax->list (second expanded))]
         [es-ls (syntax->list (third expanded))]
         [τs-ls (fourth expanded)]
         [env-ids (reverse (map car (current-env)))])
    (transfer-props (first τs-ls) (transfer-props syn (cur-reflect (transfer-props syn (transfer-props (first τs-ls) (subst* env-ids xs-ls  (first τs-ls)))))))))

(define (cur-type-check? term expected-type #:local-env [env '()])
  (with-env env
    (let ([inferred-type (turnstile-infer term)])
      (typecheck? inferred-type (cur-expand expected-type)))))

(define (cur->datum syn)
  (let ([expanded (cur-expand syn)])
    (let ([reflected (cur-reflect expanded)])
      (syntax->datum reflected))))

(define (cur-normalize syn #:local-env [env '()])
  (with-env env
    (let ([evaled (cur-expand syn)])
      evaled)))

(define (cur-equal? term1 term2 #:local-env [env '()])
  (with-env env
    (let ([term1-evaled (cur-expand term1)]
          [term2-evaled (cur-expand term2)])
      (type=? term1-evaled term2-evaled))))

(define (cur-constructors-for syn)
  (let ([constructor-ls (syntax-property (cur-expand syn) 'constructors)])
    ;; XXX: This pattern is caused by a similar issue as the XXX above.
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

(define (cur-constructor-recursive-index-ls syn)
  (let* ([expanded (cur-expand syn)]
         [rec-args-ls (syntax->list (syntax-property expanded 'constructor-rec-args))])
    (for/fold ([ls empty])
              ([arg-pair rec-args-ls]
               [i (in-range (length rec-args-ls))])
      (if (cdr (syntax->datum arg-pair)) (cons i ls) ls))))

(define (cur-reflect syn)
  (syntax-parse syn
    #:literals (quote #%expression void #%plain-lambda #%plain-app list )
    #:datum-literals (:)
    [x:id
     (cur-reflect-id syn)]
    [(~Type (quote i))
     (quasisyntax/loc this-syntax
       (cur-Type i))]
    [(#%plain-lambda (x:id) body)
     #:with (~Π ([y : t]) _) (syntax-property syn ':)
     (quasisyntax/loc this-syntax
       (cur-λ (x : #,(cur-reflect #'t)) #,(cur-reflect #'body)))]
    [(~Π ([arg : τ_arg]) body)
     (quasisyntax/loc this-syntax
       (cur-Π (arg : #,(cur-reflect #'τ_arg)) #,(cur-reflect #'body)))]
    [d:expanded-datatype
      ;; XXX: Caused by duplicating syntax properties
      (if (pair? (attribute d.unexpanded)) (car (attribute d.unexpanded)) (attribute d.unexpanded))]
    [(#%plain-app fn arg)
     (quasisyntax/loc this-syntax
       (cur-app #,(cur-reflect #'fn) #,(cur-reflect #'arg)))]))

(define-syntax-class constructor-id #:attributes (name)
  #:commit
  (pattern c:id
           #:fail-unless (syntax-property #'c 'c-ref-name) (format "error: ~a has no property 'c-ref-name" #'c)
           #:attr name (syntax-local-introduce (syntax-property #'c 'c-ref-name))))

(define-syntax-class expanded-datatype #:attributes (unexpanded) #:literals (#%plain-app #%expression void list #%plain-lambda)
  #:commit
  (pattern (#%plain-app T (#%plain-lambda () (#%expression void) (#%plain-app list A+i+x ... )))
           #:fail-unless (syntax-property this-syntax 'data-ref-name) (format "error: ~a has no property 'data-ref-name" this-syntax)
           #:with data-ref-name (syntax-local-introduce (syntax-property this-syntax 'data-ref-name))
           #:with D (car (syntax->list #'data-ref-name))
           #:with reflected-args (cdr (syntax->list #'data-ref-name))
           #:attr unexpanded
           (for/fold ([head #'D])
                     ([a (attribute A+i+x)])
             #`(cur-app #,head #,(cur-reflect a))))

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

;; XXX: currently ignores stop list; this is bad.
;; requires updated turnstile to support
(define (cur-expand syn #:local-env [env '()] . ls)
  (with-env env
    (let* ([expanded (apply turnstile-expand syn (append
                                                  (syntax-e #'(cur-Type cur-λ cur-app cur-Π cur-data cur-define cur-new-elim))
                                                  ls))]
           [xs-ls (syntax->list (second expanded))]
           [es-ls (syntax->list (third expanded))]
           [env-ids (reverse (map car (current-env)))])
      (transfer-props
       (first es-ls)
       (transfer-props
        syn
        (cur-reflect
         (transfer-props (first es-ls)
                       (transfer-props syn (subst* env-ids xs-ls (first es-ls))))))))))

(define (cur-step syn #:local-env [env '()])
  (printf "Warning: cur-step is not yet supported.~n")
  (cur-normalize syn #:local-env env))

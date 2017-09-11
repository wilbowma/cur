#lang racket
(require
 racket/require-syntax
 racket/provide-syntax
 (for-syntax
  ;; imported for export
  (except-in racket import export)
  racket/syntax
  syntax/parse
  ;racket/require-transform
  racket/provide-transform
  "stxutils.rkt"
  "runtime-utils.rkt"
  
  (rename-in "dep-ind.rkt"
             [* dep-*]
             [ Π dep-Π]
             [→ dep-→]
             [∀ dep-∀]
         [= dep-=]
         [eq-refl dep-eq-refl]
         [eq-elim dep-eq-elim]
         [λ dep-λ]
         [#%app dep-#%app]
         [ann dep-ann]
         [define-datatype dep-define-datatype]
         [define dep-define]
         [define-type-alias dep-define-type-alias])
  
  "reflection.rkt")
 (rename-in "runtime.rkt"
             [cur-Type run-Type]
             [cur-Π run-Π]
             [cur-apply run-apply]
             [cur-λ run-λ]
             [cur-elim run-elim])
            
 (rename-in "type-check.rkt"
           [typed-Type typecheck-Type]
           [typed-define typecheck-define]
           [typed-λ typecheck-λ]
           [typed-Π typecheck-Π]
           [typed-app typecheck-app]
           [typed-axiom typecheck-axiom]
           [typed-data typecheck-data]
           [typed-elim typecheck-new-elim]
           [deprecated-typed-elim typecheck-elim]
           [cur-void typecheck-void])
 )
(provide
 (rename-out [run-Type turn-Type])
; turn-define
 turn-λ
; turn-Π
; turn-app
; turn-axiom
; turn-data
; turn-new-elim
; turn-elim
; turn-void
  #;[cur-require require]
  
  (rename-out [cur-provide turn-provide]
  )
 provide-with-types)


(define-syntax (turn-Type syn)
   (syntax-parse syn
    [(_ i:exact-nonnegative-integer)
     syn]))

(define-syntax (turn-define syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_:top-level-id name:id body:cur-expr)
     #:with delta (format-id #'name "delta:~a" #'name #:source #'name)

     #'(define name (~datum :) τ body)]))

 (define-syntax (turn-λ syn)
   (syntax-parse syn
    #:datum-literals (:)
    [(_ (x:id : t1:cur-kind) (~var e (cur-expr/ctx (list (cons #'x #'t1.reified)))))

     #'(λ ([x : t1]) e)])) 
 
(define-syntax (turn-Π syn)
  syn)

#;(define-syntax (turn-Π syn)
    #:datum-literals (:)
    [(_ (x:id : t1:cur-kind) (~var e (cur-expr/ctx (list (cons #'x #'t1.reified)))))
     #:with (~var _ (cur-kind/ctx (list (cons #'x #'t1.reified)))) #'e.reified
     #'(Π ([x : t1]) e)])
 
(define-syntax (turn-app syn)
  (syntax-parse syn
    [(_ e1:cur-procedure (~var e2 (cur-expr-of-type #'e1.ann)))
     
      (make-cur-runtime-app syn #'e1.reified #'e2.reified)]))

 (define-syntax (turn-axiom syn)
   syn)
 
 (define-syntax (turn-data syn)
   syn)
 
 (define-syntax (turn-new-elim syn)
   syn)
 
 (define-syntax (turn-elim syn)
   syn)
 
 (define-syntax (turn-void syn)
   syn)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#| (define-syntax (typed-Type syn)
  (syntax-parse syn
    [(_ i:nat)
     (make-cur-runtime-universe syn #'i)]))

(define-syntax (typed-Π syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_ (x:id : t1:cur-kind) (~var e (cur-expr/ctx (list (cons #'x #'t1.reified)))))
     #:with (~var _ (cur-kind/ctx (list (cons #'x #'t1.reified)))) #'e.reified
     (make-cur-runtime-pi
      syn
      #'t1.reified
      (syntax-local-identifier-as-binding (syntax-local-introduce #'x))
      (syntax-local-introduce #'e.reified))]))

(define-syntax (typed-λ syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_ (x:id : t1:cur-kind) (~var e (cur-expr/ctx (list (cons #'x #'t1.reified)))))
     (make-cur-runtime-lambda
      syn
      #'t1.reified
      (syntax-local-identifier-as-binding (syntax-local-introduce #'x))
      (syntax-local-introduce #'e.reified))]))

(define-syntax (typed-app syn)
  (syntax-parse syn
    [(_ e1:cur-procedure (~var e2 (cur-expr-of-type #'e1.ann)))
     (make-cur-runtime-app syn #'e1.reified #'e2.reified)]))

(define-syntax (typed-define syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_:top-level-id name:id body:cur-expr)
     #:with delta (format-id #'name "delta:~a" #'name #:source #'name)
     ;; TODO: Can we avoid duplicating the syntax of the body?
     #`(begin
         (define-for-syntax delta #'body.reified)
         (define name body.reified)
         (define-for-syntax name (identifier-info #'body.type delta)))]))

(define-syntax (typed-axiom syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_:definition-id name:id : type:cur-axiom-telescope)
     #:with c (format-id this-syntax "constant:~a" #'name #:source #'name)
     #`(begin
         (struct c constant (#,@(attribute type.name-ls)) #:transparent
;           #:extra-constructor-name name1
           #:reflection-name 'name)
         (define name ((curry c)))
         (define-for-syntax name
           (constant-info #'type.reified #f 0 #f #f #f #f #f #f #f #f)))]))





|#

















 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#;(define-syntax (cur-require syn)
  (syntax-parse syn
    [(_ specs ...)
     #'(require (require-with-type spec) ...)]))

(define-syntax (cur-provide syn)
  (syntax-parse syn
    [(_ spec ...)
     #'(provide (provide-with-types spec) ...)]))

;(define-require-syntax (require-with-type stx)
;  (syntax-case stx ()
;    [(_ spec)
;     (let-values ([(imports _) (expand-import #'spec))]
;       #`(combine-in
;          spec
;          (for-syntax
;           #,@(for/list ([i (in-list imports)])
;                (import-src-sym i))))
;       )]))

(define-provide-syntax (provide-with-types stx)
  (syntax-case stx ()
    [(_ spec)
     (let ([exports (expand-export #'spec '())])
       #`(combine-out
          spec
          (for-syntax
           #,@(for/list ([i (in-list exports)]
                         #:when (with-handlers ([values (lambda _ #f)])
                                  (identifier-info? (syntax-local-eval (export-local-id i)))))
                #`(rename-out [#,(export-local-id i) #,(export-out-sym i)])))))]))

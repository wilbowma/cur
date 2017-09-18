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

  (rename-in turnstile/examples/dep-ind
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
 turn-define
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
(module+ test
  (require
   chk
   (only-in (submod "..")
            [turn-Type Type]
            [turn-define define]
            [turn-λ λ]
;            [turn-Π Π]
;            [turn-app #%app]
;            [turn-axiom axiom]
;            [turn-data data]
#;            [turn-new-elim elim]))
  (chk
   ;; #:t means "doesn't error"
   #:t (Type 1)

   ;; #:exn means "throws an exception"; takes a predicate or string to detect the right error
   ;; message.
   ;; The particular error messages here probably aren't right.
   ;; As long as the error produced is sort of close, change the expected string to make the test pass.
   #:exn #rx"expected universe level but found|unbound identifier z"
   (Type z)

   ;; These three may not work, since define may need to be at top-level
   #:t (define x (Type 1))

   #:exn #rx"expected exactly one expression in the body of define but found two"
   (define y (define z (Type 1)) z)

   #:exn #rx"expected exactly one expression in the body of define but found two"
   (define y (define z (Type 1) x) z)

   #:exn #rx"invalid syntax Type"
   (define x Type)

   #:exn #rx"expected exactly one expression in the body of define but found two"
   (define x (Type 1) (Type 1)))

  ;; Uncomment this if the earlier defines don't work inside a (chk) block
  #;(define x (Type 1))
  (chk

   #:t x
   #:t (λ (y : x) x)
   #:t (Π (x : (Type 1)) (Type 1))
   #:t (Π (x : (Type 1)) (Type 2))

   #:exn #rx"expected function but found x"
   (Π (x : (x (Type 1))) (Type 1))

   #:exn #rx"expected function but found x"
   (Π (x : (Type 1)) (x (Type 1)))

   #:exn #rx"expected function but found x"
   (Π (y : (Type 1)) (x (Type 1)))

   #:exn #rx"expected a kind (a term whose type is a universe) but found a term of type (Π (x : (Type 0)) (Type 0))"
   (Π (y : (λ (x : (Type 0)) x)) (x (Type 1)))

   #:t (define id (λ (x : (Type 2)) x))
   #:t ((λ (x : (Type 2)) x) (Type 1))))

#;(module+ test
;; Should fail with good error, do (TODO Ish. Error messages still need polish)

((λ (x : (Type 2)) x) (Type 1))

;; Should fail with good error, do (ish; see above)
;((λ (x : (Type 2)) x) (Type 2))
;((Type 1) (Type 2))

(id (Type 1))

(define id2 (λ (A : (Type 3)) (λ (a : A) a)))
((id2 (Type 2)) (Type 1))

; Should fail with good error, does
;((id2 (Type 2)) (Type 2))

(((λ (Nat : (Type 3))
     (λ (z : Nat)
       (λ (s : (Π (n : Nat) Nat))
         z)))
  (Type 2))
 (Type 1))

(axiom Nat : (Type 0))
(axiom z : Nat)
(axiom s : (Π (y : Nat) Nat))
(axiom meow : (Π (x : (Type 1)) (Type 0)))

;; should fail with good error, does
;(axiom meow2 : ((Type 1) (Type 2)))

;; should fail, does
;(axiom meow3 : (λ (x : (Type 0)) x))

; Should fail with good error, does
;(define y (axiom Nat : (Type 0)))

z
; should fail with good error, does
;(z (Type 0))
(meow (Type 0))
; Should fail with good error, does
;(meow 1)
meow

(axiom Vec : (Π (A : (Type 0)) (Π (n : Nat) (Type 0))))
(axiom nil : (Π (A : (Type 0)) ((Vec A) z)))
(nil Nat)
;
((λ (a : ((Vec Nat) z)) z) (nil Nat))
(axiom NotVec : (Π (A : (Type 0)) (Π (n : Nat) (Type 0))))
;; Should fail, does
;;((λ (a : ((NotVec Nat) z)) z) (nil Nat))
;
(define test1 (λ (a : (Π (x : Nat) Nat)) (a z)))
s
; should fail; does, with good error
;(test1 z)
(test1 s)

; TODO this is bad:
; (require racket/base)
; looks like #%app gets redefined by racket/base...
; but this behavior is consistent with typed/racket... redefine require to emit warnings when base
; forms are redefined

;; should fail with good error, does
;(require (only-in racket/base list))
;(meow (list 1))

;; Should fail with good error, does
#;(data Nat : 0 (Type 0)
      (z : Nat)
      (s : (Π (x : Nat) Nat)))

#;(data Nat2 : 0 (Type 0)
      (z : Nat2)
      (s : (Π (x : Nat) Nat)))

;; TODO: goodish error: types need resugaring
#;(data Nat2 : 0 (Type 0)
      (z2 : Nat2)
      (s2 : (Π (x : Nat) Nat)))

;; TODO: Should fail, does but with wrong error.
#;(data Nat2 : 0 (id (Type 1))
      (z2 : Nat2)
      (s2 : (Π (x : Nat) Nat)))

(data Nat2 : 0 (Type 0)
      (z2 : Nat2)
      (s2 : (Π (x : Nat2) Nat2)))

z2

;; should fail with good error, does
#;(new-elim z (λ (x : Nat) Nat)
      (z (λ (n : Nat) n)))

;; TODO Should fail with type error, does, but needs improvement
#;(new-elim z2 (λ (x : Nat2) Nat2)
      (z2 (λ (n : Nat2) n)))

#;(require (only-in racket displayln [#%app unsafe-racket-apply]))
#;(unsafe-racket-apply displayln "mark")
(new-elim (s2 z2) (λ (x : Nat2) Nat2)
      ((s2 z2) (λ (n : Nat2) (λ (IH : Nat2) (s2 IH)))))

;; should fail with good error, does
#;(new-elim (s2 z2) Nat2
      (z2 (λ (n : Nat2) n)))

;; should fail with good error, does
#;(new-elim (s2 z2) (λ (x : Nat2) Nat2)
      (z2))

;; TODO: should fail with good error, doish. needs resugaring/syntax->datum
#;(new-elim (s2 z2) (λ (x : Nat) Nat2)
      (z2))

;; Should fail with good error, does
#;(new-elim (s2 z2) (λ (x : Nat2) (λ (y : Nat) (Type 0)))
      (z2 (λ (x : Nat2) (λ (IH : Nat) IH))))

;; TODO: Should fail with good error, does ish
#;(new-elim (s2 z2) (λ (x : Nat2) Nat)
      (z2 (λ (x : Nat2) (λ (IH : Nat) IH))))

(data Maybe : 1 (Π (A : (Type 0)) (Type 0))
      (none : (Π (A : (Type 0)) (Maybe A)))
      (just : (Π (A : (Type 0)) (Π (a : A) (Maybe A)))))

((just Nat) z)

((λ (f : (Π (A : (Type 0)) (Type 0))) z) Maybe)

(new-elim (none Nat) (λ (x : (Maybe Nat)) Nat)
      (z (λ (a : Nat) a)))

(new-elim ((just Nat) (s z)) (λ (x : (Maybe Nat)) Nat)
      (z (λ (a : Nat) a)))

;; TODO Should fail with type error, does but needs improvement
#;((λ (x : (new-elim z2 (λ (x : Nat2) (Type 1))
               ((Type 0) (λ (x : Nat2) (Type 0))))) x) Nat)

((λ (x : (new-elim (s2 z2) (λ (x : Nat2) (Type 1))
               ((Type 0) (λ (x : Nat2) (λ (IH : (Type 1)) IH))))) x) Nat)
  )

















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

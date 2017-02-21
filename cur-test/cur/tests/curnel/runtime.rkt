#lang racket/base

(require
 chk
 syntax/parse
 cur/curnel/racket-impl/runtime
 cur/curnel/racket-impl/runtime-utils
 (for-syntax
  cur/curnel/racket-impl/stxutils
  racket/base))
(provide (all-defined-out) (for-syntax (all-defined-out)))

(struct constant:Nat constant () #:transparent
  #:extra-constructor-name Nat
  #:reflection-name 'Nat
  #:property prop:parameter-count 0)

(define-for-syntax Nat
  (constant-info
   ;; TODO PERF: When not a dependent type, can we avoid making it a function?
   (lambda () #`(#%plain-app cur-Type '0))
   0
   (list) (list) (list) (list)
   2
   (list #'z #'s)
   #f
   #f))

(define Nat-dispatch (box #f))

(struct constant:z constant () #:transparent
  #:extra-constructor-name z
  #:reflection-name 'z
  #:property prop:parameter-count 0
  #:property prop:dispatch Nat-dispatch
  #:property prop:recursive-index-ls null)

(define-for-syntax z
  (constant-info
   (lambda () #`(#%plain-app Nat))
   0 (list) (list) (list) (list)
   2 (list #'z #'s)
   0
   (list)))

(struct constant:s constant (pred) #:transparent
  #:extra-constructor-name s
  #:reflection-name 's
  #:property prop:parameter-count 0
  #:property prop:dispatch Nat-dispatch
  #:property prop:recursive-index-ls (list 0))

(define-for-syntax s
  (constant-info
   (lambda (x) #`(#%plain-app Nat))
   0
   (list) (list) (list #'n) (list #'Nat)
   2 (list #'z #'s)
   1 (list 1)))

(set-box! Nat-dispatch (build-dispatch (list constant:z? constant:s?)))

(require (for-syntax racket/syntax))
(define-syntax (define-from-delta stx)
  (syntax-case stx ()
    [(_ arg)
     (syntax-local-eval #'arg)]))

(define-for-syntax delta:two #'(#%plain-app s (#%plain-app s (#%plain-app z))))
(define two (define-from-delta delta:two))
(define-for-syntax two
  (identifier-info #`(#%plain-app Nat) #'delta:two))

;; TODO PERF: Could we remove λ procedure indirect for certain defines? The type is given
;; separately, so we may not need the annotations we use the λ indirect for.
;; However, the delta: definition has to remain, so it would only be the run-time definition that is
;; optimized, resulting in code duplication. Perhaps should be opt-in
(define-for-syntax delta:plus
  #`(#%plain-app cur-λ (#%plain-app Nat)
                 (#%plain-lambda (n1)
                                 (#%plain-app cur-λ (#%plain-app Nat)
                                              (#%plain-lambda (n2)
                                                              (#%plain-app cur-elim n1 (#%plain-app cur-λ (#%plain-app Nat)
                                                                                                    (#%plain-lambda (n) (#%plain-app Nat)))
                                                                           n2
                                                                           (#%plain-app cur-λ (#%plain-app Nat) (#%plain-lambda (n1-1)
                                                                                                                                (#%plain-app cur-λ (#%plain-app Nat)
                                                                                                                                             (#%plain-lambda
                                                                                                                                              (ih)
                                                                                                                                              (#%plain-app s ih)))))))))))


(define plus (define-from-delta delta:plus))
(define-for-syntax plus
  (identifier-info
   #`(#%plain-app cur-Π (#%plain-app Nat) (#%plain-lambda (x) (#%plain-app cur-Π (#%plain-app Nat)
                                                                           (#%plain-lambda (y)
                                                                                           (#%plain-app
                                                                                            Nat)))))
   #'delta:plus))

;; TODO PERF: When the constant has no fields, optimize into a singleton structure. this can be
;; detected at transformer time using struct-info, by a null field-accessor list
;; TODO PERF: When we make singletons, should be possible to optimize equality checks into eq?
;; instead of equal?.
;; "A structure type can override the default equal? definition through the gen:equal+hash generic interface."

(chk
 #:t (cur-Type 0)
 #:t (cur-Type 1)
 #:t (cur-λ (Type 1) (#%plain-lambda (x) x))
 #:t (cur-Π (Type 1) (#%plain-lambda (x) (cur-Type 1)))
 #:= (#%plain-app (cur-λ (cur-Type 1) (#%plain-lambda (x) x)) (cur-Type 0)) (cur-Type 0)
 #:? constant:z? (z)
 #:? constant:s? (s (z))
 #:= (cur-elim (z) void (z) (lambda (p) (lambda (ih) p))) (z)
 #:! #:= (cur-elim (s (s (z))) void (z) (lambda (p) (lambda (ih) p))) (z)
 #:= (cur-elim (s (s (z))) void (z) (lambda (p) (lambda (ih) p))) (s (z))
 #:= ((plus (s (s (z)))) (s (s (z)))) (s (s (s (s (z))))))

(begin-for-syntax
  (require
   chk
   ; NB: For testing renaming
   (for-template (rename-in cur/curnel/racket-impl/runtime [cur-Type meow] [cur-Type Type])))

  (define-values (universe? id? lambda? pi? constant? app? elim? term?)
    (apply
     values
     (for/list ([f (list cur-runtime-universe? cur-runtime-identifier? cur-runtime-lambda?
                         cur-runtime-pi? cur-runtime-constant? cur-runtime-app? cur-runtime-elim?
                         cur-runtime-term?)])
       (compose f local-expand-expr))))

  (chk
   #:? universe? #'(cur-Type 0)
   #:? universe? #'(meow 0)
   #:? universe? #'(Type 0)
   #:? term? #'(cur-Type 0)
   #:! #:? identifier? #'(cur-Type 0)
   #:! #:? constant? #'(cur-Type 0)
   #:! #:? lambda? #'(cur-Type 0)
   #:! #:? pi? #'(cur-Type 0)
   #:! #:? app? #'(cur-Type 0)
   #:! #:? elim? #'(cur-Type 0)
   #:? identifier? #'two
   #:? term? #'two
   #:! #:? constant? #'two
   #:! #:? universe? #'two
   #:! #:? pi? #'two
   #:! #:? lambda? #'two
   #:! #:? app? #'two
   #:! #:? elim? #'two
   #:? pi? #'(cur-Π (cur-Type 0) (lambda (x) x))
   #:? term? #'(cur-Π (cur-Type 0) (lambda (x) x))
   #:! #:? lambda? #'(cur-Π (cur-Type 0) (lambda (x) x))
   #:! #:? app? #'(cur-Π (cur-Type 0) (lambda (x) x))
   #:! #:? elim? #'(cur-Π (cur-Type 0) (lambda (x) x))
   #:! #:? universe? #'(cur-Π (cur-Type 0) (lambda (x) x))
   #:! #:? identifier? #'(cur-Π (cur-Type 0) (lambda (x) x))
   #:! #:? constant? #'(cur-Π (cur-Type 0) (lambda (x) x))
   #:? constant? #'(z)
   #:! #:? identifier? #'(z)
   #:! #:? app? #'(z)
   #:! #:? universe? #'(z)
   #:? constant? #'(s (z))
   #:! #:? app? #'(s (z))
   #:? lambda? #'(cur-λ (Type 0) (lambda (x) x))
   #:! #:? pi? #'(cur-λ (Type 0) (lambda (x) x))
   #:! #:? app? #'(cur-λ (Type 0) (lambda (x) x))
   #:? app? #'(cur-apply plus (z))
   #:? term? #'(cur-apply plus (z))
   #:! #:? constant? #'(cur-apply plus (z))
   #:! #:? elim? #'(cur-apply plus (z))
   #:! #:? identifier? #'(cur-apply plus (z))
   #:! #:? universe? #'(cur-apply plus (z))
   #:! #:? lambda? #'(cur-apply plus (z))
   #:! #:? pi? #'(cur-apply plus (z))
   #:? app? #'(cur-apply (cur-apply plus (z)) (z))
   #:? term? #'(cur-apply (cur-apply plus (z)) (z))
   #:? elim? #'(cur-elim (z) void (z) (s (z)))
   #:? term? #'(cur-elim (z) void (z) (s (z)))
   #:! #:? app? #'(cur-elim (z) void (z) (s (z)))
   #:! #:? constant? #'(cur-elim (z) void (z) (s (z)))
   #:! #:? lambda? #'(cur-elim (z) void (z) (s (z)))
   #:! #:? pi? #'(cur-elim (z) void (z) (s (z)))))

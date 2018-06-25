#lang racket
(require
 (for-syntax
  ;; imported for export
  (except-in racket import export)
  racket/syntax
  syntax/parse
  "stxutils.rkt"
  "runtime-utils.rkt"
  syntax/to-string)

 (only-in turnstile/lang define- infer)
 (only-in
  turnstile/examples/dep-ind-cur
  assign-type
  [* dep-*]
  [Type dep-Type]
  [Π dep-Π]
  [λ dep-λ]
  [#%app dep-#%app]
  [ann dep-ann]
  [define-datatype dep-define-datatype]
  [define dep-define]))

(provide
 cur-Type
 cur-define
 cur-λ
 cur-Π
 cur-app
 cur-axiom
 cur-data
 cur-new-elim
 cur-void)

(define-syntax (cur-Type syn)
   (syntax-parse syn
    [(_ i:exact-nonnegative-integer)
     (quasisyntax/loc syn (dep-Type i))]))

(define-syntax (cur-define syn)
  (syntax-parse syn
    [(_:top-level-id name:id body:expr)
     (quasisyntax/loc syn (dep-define name body))]))

(define-syntax (cur-λ syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_ (x:id : t1:expr) e:expr)
     (quasisyntax/loc syn (dep-λ [x : t1] e))]))

(define-syntax (cur-Π syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_ (x:id : t1:expr) e:expr)
     (quasisyntax/loc syn (dep-Π [x : t1] e))]))

(define-syntax (cur-app syn)
  (syntax-parse syn
    [(_ e1:expr e2:expr)
      (quasisyntax/loc syn (dep-#%app e1 e2))]))

(begin-for-syntax
  (define (parse-telescope-names type)
    (syntax-parse (local-expand type 'expression (syntax-e #'(cur-Π cur-Type)))
      #:datum-literals (:)
      #:literals (cur-Π)
      [(cur-Π (x : t) telescope) (cons (quasisyntax/loc type x) (parse-telescope-names #'telescope))]
      [result '()]))
  (define (parse-telescope-annotations type)
    (syntax-parse (local-expand type 'expression (syntax-e #'(cur-Π cur-Type)))
      #:datum-literals (:)
      #:literals (cur-Π)
      [(cur-Π (x : t) telescope) (cons (quasisyntax/loc type [x : t]) (parse-telescope-annotations #'telescope))]
      [result '()]))
  (define (parse-telescope-result type)
    (syntax-parse (local-expand type 'expression (syntax-e #'(cur-Π cur-Type)))
      #:datum-literals (:)
      #:literals (cur-Π)
      [(cur-Π (x : t) telescope) (parse-telescope-result #'telescope)]
      [result type])))

(define-syntax (cur-data syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_ Name:id : p:nat type
        (c-name:id : c-type) ...)
     #:with (cur-Π (x : ty) body) (local-expand (attribute type) 'expression (syntax-e #'(cur-Π cur-Type)))
     #:with Result (parse-telescope-result (attribute type))
     #:do [(define param-count (syntax->datum #'p))
           (define telescope-anns (parse-telescope-annotations (attribute type)))]
     #:with ([A : AT] ...) (take telescope-anns param-count)
     #:with ([I : IT] ...) (drop telescope-anns param-count)
     #:do [(define c-telescope-anns
             (for/list ([t (attribute c-type)])
               (parse-telescope-annotations t)))]
     #:with (([cA : cAT] ...) ...) (for/list ([as c-telescope-anns])
                                     (take as param-count))
     #:with (([r : rT] ...) ...) (for/list ([as c-telescope-anns])
                                   (drop as param-count))
     #:with (c_result ...) (for/list ([t (attribute c-type)])
                             (parse-telescope-result t))
     (quasisyntax/loc syn
       (dep-define-datatype Name (A : AT) ... : (I : IT) ... -> Result
                            [c-name : (dep-Π [cA : cAT] ...
                                             (dep-Π [r : rT] ...
                                                    c_result))]
                            ...))]
    [(_ Name:id : 0 type ;;per dep-ind-cur-tests, still need special case for (Type 0): must use * or Type?
        (c-name:id : c-type) ...)
     #:with (cur-Type n) (local-expand (attribute type) 'expression (syntax-e #'(cur-Π cur-Type)))
     #:with (([r : rT] ...) ...) (for/list ([t (syntax->list #'(c-type ...))])
                                   (parse-telescope-annotations t))
     #:with (c_result ...) (for/list ([t (syntax->list #'(c-type ...))])
                             (parse-telescope-result t))
     (quasisyntax/loc syn
       (dep-define-datatype Name : dep-*
                            [c-name :  (dep-Π [r : rT] ...
                                             c_result)] ...))]))

;; TODO: Rename this to cur-elim
(define-syntax (cur-new-elim syn)
  (syntax-parse syn
    [(_ target:expr motive:expr (method:expr ...))
     #:with elim-name (let ([possible-pair (syntax-property (first (fourth (infer (list #'target))))
                                       'elim-name)])
                        ;; XXX: This pattern caused by accidentally duplicating syntax properties
                        (if (pair? possible-pair) (car possible-pair) possible-pair))
     (quasisyntax/loc syn (elim-name target motive method ...))]))


(define-syntax (cur-axiom syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_ name:id (~datum :) type)
     #:with c (format-id this-syntax "constant:~a" #'name #:source #'name)
     #:with (arg ...) (parse-telescope-names #'type)
     #:with name- (syntax-property (format-id syn "~a-" #'name #:source #'name) 'axiom-ref-name #'name)
     (quasisyntax/loc syn
       (begin
         (struct c (arg ...) #:transparent #:reflection-name 'name)
         (define name- ((curry c)))
         (define-syntax name
           (make-rename-transformer
            (assign-type #'name- #'#,(local-expand #'type 'expression null))))))]))


;; TODO: Copy pasted from racket lang
(define-syntax-rule (cur-void)
  (#%plain-app void))

#lang s-exp "../main.rkt"

;; differs from curnel/racket-impl:
;; -> is normal arrow type and not alias for Π,
;; but ∀ and forall is alias for Π

(provide (all-from-out cur/curnel/turnstile-impl/dep-ind-cur2+sugar)
         let
         match
         define-implicit
         define/rec/match)

(require cur/curnel/turnstile-impl/dep-ind-cur2+sugar
         (prefix-in r: racket/base)
         (for-syntax (for-syntax syntax/parse)
                     syntax/stx racket/pretty
                     macrotypes/stx-utils 
                     turnstile/type-constraints))

(define-typed-syntax let
  [(_ ((~or (~describe "unannotated" [x:id ex])
            (~describe "annotated" [(y:id (~datum :) τ) ey])) ...) body) ≫
   [⊢ ex ≫ ex- ⇒ τx] ...
   [⊢ ey ≫ ey- ⇐ τ] ...
   [([x ≫ x- : τx] ...) ([y ≫ y- : τ] ...) ⊢ body ≫ body- ⇒ τout]
   ------------------
   ;; will this type-eval properly? expand to (typed) app and λ instead?
   ;; TODO: xs and ys out of order
   [⊢ (r:let ([x- ex-] ... [y- ey-] ...) body-) ⇒ τout]])
   ;  [⊢ ((λ [x- : τ] ... body-) e- ...)]

(begin-for-syntax
  (define ((mk-method τout name) eis clause) ; 2 args: ei tys and clause
    (syntax-parse (list eis clause)
      [(_ [x:id body]) #'body] ; no subst, bc x is just nullary constructor
      ;; TODO: combine the following 4 cases
      [((_ ([y:id τin] ...) ()) ; no rec, no anno
        [(con:id x:id ...) body])
       #:with body* (substs #'(y ...) #'(x ...) #'body)
       #`(λ [y : τin] ... body*)]
      [((_ ([y:id τin] ...) ()) ; no rec, with anno
        [(con:id [x:id tag:id ty] ...) body])
       ;; TODO: for this to work, must inst τin
       ;; - add params to extra info?
       ;; #:fail-unless (typechecks? #'(ty ...) #'(τin ...))
       ;;                "match: pattern annotation type mismatch"
       #:with body* (substs #'(y ...) #'(x ...) #'body)
       #`(λ [y : ty] ... body*)]
      [((_ ([y:id τ] ...) ((yrec . _) ...)) ; rec, no anno
        [(con:id x:id ...) body])
       #:with (ih ...) (generate-temporaries #'(yrec ...)) ; yrec is dup of y; must gen tmp
       #:with body/ys (substs #'(y ...) #'(x ...) #'body)
       #'(λ y ... ih ... body/ys)]
      [((_ ([y:id τin] ...) ((yrec))) ; rec, with anno
        [(con:id [x:id tag:id ty] ...) body])
       ;; TODO: for this to work, must inst τin
       ;; - add params to extra info?
       ;; #:fail-unless (typechecks? #'(ty ...) #'(τin ...))
       ;;                "match: pattern annotation type mismatch"
       #:with yrec* (generate-temporary #'yrec)
       #:with body* (substs #'(y ...) #'(x ...) #'body)
       #`(λ [y : ty] ... [yrec* : #,(subst #'yrec name τout)] body*)])))

;; TODO:
;; - for now, explicit #:return arg required
;; - assuming clauses appear in order
;; - must use #:as for return type that uses `e`
;; - x should be xs?
;; - match clauses *do not* include params
;;   - bc elim methods do not re-bind params
;; TODO: handle nested patterns, like define/rec/match?
;; - use #:with-indices for dependent pattern match
;;   - ie, #:in is not a pattern like in coq
(define-typed-syntax match
  [(_ e (~optional (~seq #:as x) #:defaults ([x #'x])) #:return τout . clauses) ≫
   [⊢ e ≫ e- ⇒ τin]
   -----
   [≻ (match+ e- #:as x #:with-indices #:in τin #:return τout . clauses)]]
  [(_ e (~optional (~seq #:as x) #:defaults ([x #'x])) #:in τin #:return τout . clauses) ≫
   [⊢ e ≫ e- ⇐ τin]
   -----
   [≻ (match+ e- #:as x #:with-indices #:in τin #:return τout . clauses)]]
  [(_ e (~optional (~seq #:as x) #:defaults ([x #'x]))
        #:with-indices i ...
        #:in τin #:return τout
        . clauses) ≫
   [⊢ e ≫ e- ⇐ τin]
   -----
   [≻ (match+ e- #:as x #:with-indices i ... #:in τin #:return τout . clauses)]])

;; the main match form
;; e- expanded
(define-typed-syntax (match+ e #:as x #:with-indices i ... #:in τin_ #:return τout . clauses) ≫
  #:with τin (expand/df #'τin_)
;  #:do[(printf "match τin: ~a\n" (stx->datum #'τin))]
  #:do[(define exinfo (get-match-info #'τin))]
;  #:do[(printf "exinfo: ~a\n" (stx->datum exinfo))]
  #:fail-unless exinfo (format "could not infer extra info from type ~a" (stx->datum #'τ))
  #:with (elim-Name ([orig-param:id _] ...) _ ei ...) exinfo
  ;; use params and indices from τin, not exinfo (bc that's what elim does)
  #:with params (stx-take
                 (stx-drop #'τin 2) ; drop #%app and cons-name
                 (stx-length #'(orig-param ...)))
  ;; ;; #:do[(displayln #'elim-Name)
  ;; ;;      (displayln (identifier-binding #'elim-Name))]
  ;; ;; TODO: the following is a workound for the "kind stx prop" problem
  ;; ;; ie, stxobj stx props are not visible to the expander, causing potential issues,
  ;; ;; it's frequently seen with "kinds", ie props on types, eg extra-info
  ;; ;; - sometimes the elim-name loses its proper module-path-index
  ;; ;; - in these situations, unhygienically use the ctx here
  ;; #:do[(define-values (modulepath basepath)
  ;;        (module-path-index-split (car (identifier-binding #'elim-Name))))]
;;  #:do[(printf "ei: ~a\n" (stx->datum #'(ei ...)))]
  #:fail-unless (stx-length=? #'(ei ...) #'clauses)
                "extra info error: check that number of clauses matches type declaration"
;;  #:with (m ...) (stx-map (mk-method #'e- #'τ #'τout modulepath this-syntax) #'(ei ...) #'clauses)
  #:with (m ...) (stx-map
                  (mk-method #'τout #'x)
                  (substs #'params #'(orig-param ...) #'(ei ...)) ; use params from τin, not ei
                  #'clauses)
  ;; #:do[(printf "match methods for ~a:\n" #'e)
  ;;      (map pretty-print (stx->datum #'(m ...)))]
  ; [⊢ body ≫ body- ⇐ τout] ...
;;   #:with elim-Name* (if modulepath
;;                         #'elim-Name
;;                         (datum->syntax this-syntax (syntax->datum #'elim-Name)))
;; ;  #:do[(displayln (identifier-binding #'elim-Name*))]
  #:with out (quasisyntax/loc this-syntax
               (elim-Name e (λ i ... x τout) m ...))
;  #:do[(pretty-print (syntax->datum #'out))]
  ------------
  [≻ out])

(begin-for-syntax
  (define (mk-eval id) (format-id id "eval-~a" id))
  (define (mk-~ id) (format-id id "~~~a" id)))

; Π  λ ≻ ⊢ ≫ → ∧ (bidir ⇒ ⇐) τ⊑ ⇑

;; helper fns for define/rec/match
(begin-for-syntax
  ;; - input stx arg must be fully expanded
  (define (get-app stx name n)
    (syntax-parse stx
      [((~literal #%plain-app) f:id arg)
       #:when (= 1 n)
       #:when (free-id=? #'f name)
       (list #'f #'arg)]
      [((~literal #%plain-app) f arg)
       (let ([rst (get-app #'f name (sub1 n))])
         (and rst (append rst (list #'arg))))]
      [_ #f]))
  ;; - input stx arg must be fully expanded
  (define (unsubst-app name name-eval num-args)
    (syntax-parser
      [_
       #:do[(define the-app (get-app this-syntax name num-args))]
       #:when the-app
       #:with (_ . args) the-app
       (datum->syntax
        this-syntax
        (cons (mk-reflected name-eval #'#%plain-app name) #'args)
        this-syntax this-syntax)]
      [:id this-syntax]
      [(x ...)
       (datum->syntax
        this-syntax
        (stx-map (unsubst-app name name-eval num-args) #'(x ...))
        this-syntax this-syntax)])))
;; usage:
;; (define/rec/match name : [x : ty_in1] ... ty-to-match ... [y : ty_in2] ... -> ty_out
;;  [pat ... => body] ...
;; where:
;; - the [x : ty_in1] ... and [y : ty_in2] ... are telescopic
;; - ty-to-match are not named
;; - but other tys are named
;; - in each clause, there must be one pat per ty-to-match,
;;   where the pats are stx-parse pats
;; TODO:
;; - check smaller arg for rec calls
;; - check coverage of pats
;; - check that body has type ty_out; currently, mismatch wont error
;;(require (for-syntax racket/pretty))
(define-typed-syntax define/rec/match 
  [(_ name:id
      (~datum :)
      [x (~datum :) ty_in1] ...
      (~and ty-to-match (~not [_ (~datum :) _]) (~not (~datum ->))) ...
      [y (~datum :) ty_in2] ...
      (~datum ->) ty_out
      [pat ... (~datum =>) body] ...) ≫
     #:fail-unless (or (zero? (stx-length #'(x ...)))
                       (zero? (stx-length #'(y ...))))
     "cannot have both pre and post pattern matching args"
 ;    #:do[(printf "fn: ~a ----------------\n" (stx->datum #'name))]
     #:with (([xpat xpatτ] ...) ...)
     (stx-map
      (λ (pats)
        (stx-appendmap pat->ctxt pats #'(ty-to-match ...)))
      #'((pat ...) ...))
;     #:do[(printf "pattern binders: ~a\n" (stx->datum #'(([xpat xpatτ] ...) ...)))]
     #:with (x0 ...) (generate-temporaries #'(ty-to-match ...))
     #:with (([x+pat x+patτ] ...) ...) (stx-map
                                        (λ (x+τs)
                                          #`(#,@#'((x ty_in1) ...)
                                             #,@x+τs))
                                        #'(([xpat xpatτ] ...) ...))
     [([x+pat ≫ x+pat- : x+patτ] ...)
      ([y ≫ y*- : ty_in2] ...
       ;; for now, assume recursive references are fns
       [name ≫ name- : (Π [x : ty_in1] ... [x0 : ty-to-match] ... [y : ty_in2] ... ty_out)])
      ⊢ body ≫ body- ⇐ ty_out] ...
     #:do[(define arity (stx-length #'(x ... ty-to-match ... y ...)))]
     ;; #:do[
     ;;      (displayln 'body-)
     ;;      (stx-map (compose displayln syntax->datum) #'(body- ...))]
     #:with ((x*- ...) ...) (stx-map
                             (λ (x+pats)
                               (stx-take x+pats (stx-length #'(x ...))))
                             #'((x+pat- ...) ...))
     #:with ((xpat- ...) ...) (stx-map
                               (λ (x+pats)
                                 (stx-drop x+pats (stx-length #'(x ...))))
                               #'((x+pat- ...) ...))
     #:with (x0- ...) (generate-temporaries #'(x0 ...))
     #:with (x- ...) (generate-temporaries #'(x ...))
     #:with (y- ...) (generate-temporaries #'(y ...))
     #:with ((x-for-pat ...) ...) (stx-map (λ _ #'(x ...)) #'((pat ...) ...))
     #:with (ys-for-pat ...) (stx-map (λ _ #'(y ...)) #'((pat ...) ...))
     #:with name-eval (mk-eval #'name)
     ;; need to "unsubst" recursive references to (to-be-defined) calls to name-eval
     #:with (body-- ...) (stx-map
                          (λ (n- b)
                            (reflect
                             ((unsubst-app n- #'name-eval arity) b)))
                          #'(name- ...)
                          #'(body- ...))
     ;; #:do[
     ;;      (displayln 'body--)
     ;;      (stx-map (compose displayln syntax->datum) #'(body-- ...))]
     ;; TODO: dont need to typecheck again on recursive call?
     #:with ((pat- ...) ...) (stx-map
                              substs
                              #'((xpat- ...) ...)
                              #'((xpat ...) ...)
                              #'((pat ...) ...))
;     #:with (red-pat ...) #'((#%plain-app x-for-pat ... pat ... . ys-for-pat) ...)
     #:with (red-pat ...) #'((#%plain-app x*- ... pat- ... y*- ...) ...)
     #:with OUT
     #'(begin
         ;; this macro uses the patvar reuse technique
         ;; ie, references to x in x0 will be instantiated to the type bound to x
         (define-typed-syntax name
           [(_ x ... x0 ... y ... ~!) ≫
            [⊢ x ≫ x- ⇐ ty_in1] ...
            [⊢ x0 ≫ x0- ⇐ ty-to-match] ...
            [⊢ y ≫ y- ⇐ ty_in2] ...
            ----------
            [⊢ (name-eval x- ... x0- ... y- ...) ⇒ ty_out]]
           ; non-full application cases: η expand
           [:id ≫ --- [≻ (name)]]
           [(_ arg (... ...)) ≫ 
            ----
            [≻ ((λ [x : ty_in1] ... [x0 : ty-to-match] ... [y : ty_in2] ...
                  (name x ... x0 ... y ...))
                arg (... ...))]])
         (define-red name-eval #:display-as name [red-pat ~> body--] ...))
     ;     #:do[(pretty-print (syntax->datum #'OUT))]
     -----
     [≻ OUT]])

(begin-for-syntax
  (define (infer? stx) (equal? (stx-e stx) 'inf)))

;; (define-implicit name* = name n (~or _ inf) ...)
;; n = number of args to infer
;; _ = concrete arg
;; inf = infer type of this arg
;; TODO:
;; - check consistency of solved constraints
;; - define a form that combines define/rec/match and define-implicit
(define-typed-syntax define-implicit
  [(_ name* (~datum =) name n:exact-nonnegative-integer) ≫ ; rest of args are concrete (ie _)
   [⊢ name ≫ name- ⇒ (~Π [X : _] ... _)]
   #:when (not (= (stx-length #'(X ...)) (stx-e #'n))) ; go to next case
   #:with args (stx-map (λ _ #'_) (stx-drop #'(X ...) (stx-e #'n)))
   ----
   [≻ (define-implicit name* = name n . args)]]
  [(_ name* (~datum =) name n:exact-nonnegative-integer . infers) ≫
   [⊢ name ≫ name- ⇒ (~Π [X : τ] ... τout)]
  #:with τexplicits (stx-drop #'(τ ...) (stx-e #'n)) ; type of explicit args
  #:with (Ximplicit ...) (stx-take #'(X ...) (stx-e #'n)) ; binders of implicit args
  #:with (dontcare ...) (stx-map (λ _ #'_) #'(Ximplicit ...))
  #:with out-def
  #`(begin
      (begin-for-syntax
      #,(if (= (stx-length #'(X ...)) (stx-e #'n)) ; pattern expander
            #'(define-syntax name*
                (pattern-expander
                 (syntax-parser
                   [(~var _ id) #'(name Ximplicit ...)]
                   [(_ . rst) #'((name Ximplicit ...) . rst)])))
            #'(define-syntax name*
                (pattern-expander
                 (syntax-parser
                   [(_ . rst) #'(name Ximplicit ... . rst)])))))
        
      (define-syntax name*
        (datacons
        (λ (stx)
        (syntax-parse/typecheck stx
      #,@(if (= (stx-length #'(X ...)) (stx-e #'n)) ; all args are implicit
             (list #'[:id ≫ --- [≻ (name*)]]) ; add id case
             null)
        [(_ X ... ~!) ≫ --- [≻ (name X ...)]] ; can still use name* with explicit args
        [(_ . Ys) ⇐ τ_expected ≫ #:with ~! #'commit-dont-backtrack
;        [⊢ Y ≫ Y- ⇒ τY] ... ; cant do this bc may have to skip some (eg the args to infer types)
       #:do[(define constraints ; = [Pair typeof-Y τexplicit], but only for non 'inf args
              (for/list ([maybe-infer (in-stx-list #'infers)]
                         [y (in-stx-list #'Ys)] ; (len Ys) can be < (len τexplicit ...)
                         [t (in-stx-list #'τexplicits)]
                         #:unless (infer? maybe-infer))
                (list (typeof (expand/df y)) t)))
            (define substs
              (add-constraints
               #'(X ...) ; this must be X, not Ximplicit ..., see tests/ntac/assert.rkt for fail case
               null
               (cons (list #'τ_expected
                           ; if partial #%app, add remaining types to result type
                           (expand/df #`(-> #,@(stx-drop #'τexplicits (stx-length #'Ys)) τout)))
                     constraints)))]
       ;; TODO: fail if couldnt infer all Ximplicit?
       #:with τexplicits/inst (inst-types/cs/orig #'(Ximplicit ...) substs #'τexplicits datum=?)
;       [⊢ Y ≫ Y- ⇐ τexplicit/inst] (... ...) ; TODO: Turnstile not liking this (... ...) ellipses syntax
       #:with Ys- (for/list ([y (in-stx-list #'Ys)]
                             [t (in-stx-list #'τexplicits/inst)])
                    (expand/df (add-expected-type y t)))
       #:fail-unless (for/and ([y (in-stx-list #'Ys-)]
                               [t (in-stx-list #'τexplicits/inst)])
                       (typecheck? (typeof y) t))
                     (typecheck-fail-msg/multi #'τexplicits/inst
                                               (stx-map typeof #'Ys-)
                                               #'Ys)
       #:with (τimplicit (... ...)) (lookup-Xs/keep-unsolved #'(Ximplicit ...) substs)
       ------
       [≻ (name τimplicit (... ...) . Ys-)]]
      [(_ . Ys) ≫ ; same as above case, except no expected type ; TODO: merge dup code?
        #:fail-when (stx-null? #'Ys) ; fail when no types to infer from
                    (format "could not infer args for ~a; add annotations" 'name)
;        [⊢ Y ≫ Y- ⇒ τY] ... ; cant do this bc it does not consider args that must be inferred
        #:do[(define constraints ; = [Pair typeof-Y τexplicit], but only for non 'inf args
              (for/list ([maybe-infer (in-stx-list #'infers)]
                         [y (in-stx-list #'Ys)]
                         [t (in-stx-list #'τexplicits)]
                         #:unless (infer? maybe-infer))
                (list (typeof (expand/df y)) t)))
            (define substs
              (add-constraints
               #'(X ...)
               null
               constraints))]
        ;; TODO: fail if couldnt infer type for all Ximplicit?
        #:with τexplicits/inst (inst-types/cs/orig #'(Ximplicit ...) substs #'τexplicits datum=?)
;        [⊢ Y ≫ Y- ⇐ τexplicit/inst] (... ...) ; Turnstile doesnt like this nested ellipsis
       #:with Ys- (for/list ([y (in-stx-list #'Ys)]
                             [t (in-stx-list #'τexplicits/inst)])
                    (expand/df (add-expected-type y t)))
       #:fail-unless (for/and ([y (in-stx-list #'Ys-)]
                               [t (in-stx-list #'τexplicits/inst)])
                       (typecheck? (typeof y) t))
                     (typecheck-fail-msg/multi #'τexplicits/inst
                                               (stx-map typeof #'Ys-)
                                               #'Ys)
        #:with (τimplicit (... ...)) (lookup-Xs/keep-unsolved #'(Ximplicit ...) substs)
        ------
        [≻ (name τimplicit (... ...) . Ys-)]]))
        (λ (pat t) ; pat->ctxt
          ;; add missing pats as "_"
          (pat->ctxt
           #`(name dontcare ... #,@(if (identifier? pat)
                                       #'()
                                       (stx-cdr pat)))
           t)))))
;  #:do[(pretty-print (syntax->datum #'out-def))]
  ------------
  [≻ out-def]])

      

(provide
;;   Type
;;   ->
;;   lambda
;;   (rename-out
;;     [-> →]
;;     [-> forall]
;;     [-> ∀]
;;     [-> Π]
;;     [-> Pi]
;;     [lambda λ])
;;   #%app
;;   define
;;   :
;;   define-type
;;   match
;;   recur
;;   let

;;   ;; type-check
;;   ::

;;   ;; reflection in syntax
;;   run
;;   step
;;   step-n
;;   query-type

  ;; extension abstractions
  (for-syntax
   cur-match))

;; (require
;;   (only-in "../main.rkt"
;;     [#%app real-app]
;;     [λ real-lambda]
;;     [Π real-Π]
;;     [define real-define]
;;     [Type real-Type]))

;; (begin-for-syntax
;;   (define-syntax-class result-type
;;     (pattern type:expr))

;;   (define-syntax-class parameter-declaration
;;     (pattern (name:id (~datum :) type:expr))

;;     (pattern
;;      type:expr
;;      #:attr name (format-id #'type "~a" (gensym 'anon-parameter)))))

;; (define-syntax (Type syn)
;;   (syntax-case syn ()
;;     [(_ i) (quasisyntax/loc syn (real-Type i))]
;;     [_ (quasisyntax/loc syn (real-Type 0))]))

;; ;; A multi-arity function type; takes parameter declaration of either
;; ;; a binding (name : type), or type whose name is generated.
;; ;; E.g.
;; ;; (-> (A : Type) A A)
;; (define-syntax (-> syn)
;;   (syntax-parse syn
;;     [(_ d:parameter-declaration ...+ result:result-type)
;;      (foldr (lambda (src name type r)
;;               (quasisyntax/loc src
;;                 (real-Π (#,name : #,type) #,r)))
;;             #'result
;;             (attribute d)
;;             (attribute d.name)
;;             (attribute d.type))]))

;; ;; TODO: Add forall macro that allows specifying *names*, with types
;; ;; inferred. unlike -> which require types but not names
;; ;; E.g.
;; ;; (forall x (y : Nat) (== Nat x y))

;; ;; TODO: Allows argument-declarations to have types inferred, similar
;; ;; to above TODO forall
;; (begin-for-syntax
;;   ;; eta-expand syntax-class for error messages
;;   (define-syntax-class argument-declaration
;;     (pattern
;;      e:parameter-declaration
;;      #:attr name #'e.name
;;      #:attr type #'e.type))

;;   (define current-function-arg-ids
;;     (make-parameter #f #;(raise-syntax-error "Not currently in a function definition")))
;;   (define current-function-arg-types
;;     (make-parameter #f #;(raise-syntax-error "Not currently in a function definition"))))

;; (define-syntax (lambda syn)
;;   (syntax-parse syn
;;     [(_ d:argument-declaration ...+ body:expr)
;;      (foldr (lambda (src name type r)
;;               (quasisyntax/loc src
;;                 (real-lambda (#,name : #,type) #,r)))
;;             #'body
;;             (attribute d)
;;             (attribute d.name)
;;             (attribute d.type))]
;;     ;; Support for non-zero number of arguments is handy for meta-programming
;;     [(_ body:expr) #'body]))

;; ;; TODO: This makes for really bad error messages when an identifier is undefined.
;; (define-syntax (#%app syn)
;;   (syntax-case syn ()
;;     [(_ e)
;;      (quasisyntax/loc syn e)]
;;     [(_ e1 e2)
;;      (quasisyntax/loc syn
;;        (real-app e1 e2))]
;;     [(_ e1 e2 e3 ...)
;;      (quasisyntax/loc syn
;;        (#%app (#%app e1 e2) e3 ...))]))

;; ;; NB: No syntax rules if you want to traverse syntax
;; (define-syntax (define-type syn)
;;   (syntax-case syn ()
;;     [(_ (name (a : t) ...) body)
;;      #`(define name (-> (a : t) ... body))]
;;     [(_ name type)
;;      #`(define name type)]))

;; ;; Cooperates with define to allow Haskell-esque type annotations
;; #| TODO NB:
;;  | This method of cooperating macros is sort of a terrible
;;  | hack. Instead, need principled way of adding/retrieving information
;;  | to/from current module. E.g. perhaps provide extensions an interface to
;;  | module's term environment and inductive signature. Then, :: could add
;;  | new "id : type" to environment, and define could extract type and use.
;;  |#
;; (begin-for-syntax
;;   (define annotation-dict (make-hash))
;;   (define (annotation->types type-syn)
;;     (let loop ([ls '()]
;;                [syn type-syn])
;;       (syntax-parse (cur-expand syn)
;;         #:datum-literals (:)
;;         [(real-Π (x:id : type) body)
;;          (loop (cons #'type ls) #'body)]
;;         [_ (reverse ls)]))))

;; (define-syntax (: syn)
;;   (syntax-parse syn
;;     [(_ name:id type:expr)
;;      ;; NB: Unhygenic; need to reuse Racket's identifiers, and make this type annotation a syntax property
;;      (syntax-parse (cur-expand #'type)
;;       #:datum-literals (:)
;;       [(real-Π (x:id : type) body) #'(void)]
;;       [_
;;        (raise-syntax-error
;;         ':
;;         "Can only declare annotations for functions, but not a function type"
;;         syn)])
;;      (dict-set! annotation-dict (syntax->datum #'name) (annotation->types #'type))
;;      #'(void)]))

;; ;; TODO: These parameters should be syntax-parameters, but trying to use them resulted in
;; ;; strange error
;; (begin-for-syntax
;;   (define current-definition-id (make-parameter #f))
;;   (define current-definition-param-decl (make-parameter #f))

;;   )
;; ;(define-syntax-parameter current-definition-id #f)

;; ;; TODO: Allow inferring types as in above TODOs for lambda, forall
;; (require (for-syntax (only-in racket/trace trace-define)))
;; (require (only-in racket/trace trace-define-syntax))
;; (define-syntax (define syn)
;;   (syntax-parse syn
;;     #:datum-literals (:)
;;     [(define (name:id x:id ...) body)
;;      (cond
;;        [(dict-ref annotation-dict (syntax->datum #'name)) =>
;;         (lambda (anns)
;;           (quasisyntax/loc syn
;;             (define (name #,@(for/list ([x (syntax->list #'(x ...))]
;;                                         [type anns])
;;                                #`(#,x : #,type)))
;;               body)))]
;;        [else
;;         (raise-syntax-error
;;          'define
;;          "Cannot omit type annotations unless you have declared them with (: name type) form first."
;;          syn)])]
;;     [(define (name (x : t) ...) body)
;;      (current-definition-param-decl (syntax->list #`((x : t) ...)))
;;      (quasisyntax/loc syn
;;        (define name (lambda (x : t) ... body)))]
;;     [(define id body)
;;      ;; TODO: without syntax-parameterize, or similar, this information will become stale and may
;;      ;; result in incorrect expansion
;;      (current-definition-id #'id)
;;      (quasisyntax/loc syn
;;        (real-define id body))]))


;; #|
;; (begin-for-syntax
;;   (define (type->telescope syn)
;;     (syntax-parse (cur-expand syn)
;;       #:literals (real-Π)
;;       #:datum-literals (:)
;;       [(real-Π (x:id : t) body)
;;        (cons #'(x : t) (type->telescope #'body))]
;;       [_ '()]))

;;   (define (type->body syn)
;;     (syntax-parse syn
;;       #:literals (real-Π)
;;       #:datum-literals (:)
;;       [(real-Π (x:id : t) body)
;;        (type->body #'body)]
;;       [e #'e]))

;;   (define (constructor-indices D syn)
;;     (let loop ([syn syn]
;;                [args '()])
;;       (syntax-parse (cur-expand syn)
;;         #:literals (real-app)
;;         [D:id args]
;;         [(real-app e1 e2)
;;          (loop #'e1 (cons #'e2 args))])))

;;   (define (inductive-index-telescope D)
;;     (type->telescope (cur-type-infer D)))

;;   (define (inductive-method-telescope D motive)
;;     (for/list ([syn (cur-constructor-map D)])
;;       (with-syntax ([(c : t) syn]
;;                     [name (gensym (format-symbol "~a-~a" #'c 'method))]
;;                     [((arg : arg-type) ...) (type->telescope #'t)]
;;                     [((rarg : rarg-type) ...) (constructor-recursive-args D #'((arg : arg-type) ...))]
;;                     [((ih : ih-type) ...) (constructor-inductive-hypotheses #'((rarg : rarg-type) ...) motive)]
;;                     [(iarg ...) (constructor-indices D (type->body #'t))]
;;                     )
;;         #`(name : (forall (arg : arg-type) ...
;;                           (ih : ih-type) ...
;;                           (motive iarg ...)))))))

;; (define-syntax (elim syn)
;;   (syntax-parse syn
;;     [(elim D:id U e ...)
;;      (with-syntax ([((x : t) ...) (inductive-index-telescope #'D)]
;;                    [motive (gensym 'motive)]
;;                    [y (gensym 'y)]
;;                    [disc (gensym 'disc)]
;;                    [((method : method-type) ...) (inductive-method-telescope #'D #'motive)])
;;        #`((lambda
;;             (motive : (forall (x : t) ... (y : (D x ...)) U))
;;             (method : ) ...
;;             (x : t) ...
;;             (disc : (D x ...)) ...
;;             (real-elim D motive (x ...) (method ...) disc))
;;           e ...)
;;        )
;;      ]))
;; |#

;; ;; Quite fragie to give a syntactic treatment of pattern matching -> eliminator. Replace with "Elimination with a Motive"
;; (begin-for-syntax
;;   (define ih-dict (make-hash))

;;   (define-syntax-class curried-application
;;     (pattern
;;      ((~literal real-app) name:id e:expr)
;;      #:attr args
;;      (list #'e))

;;     ;; TODO BUG: will not match when a is not expanded yet
;;     (pattern
;;      ((~literal real-app) a:curried-application e:expr)
;;      #:attr name #'a.name
;;      #:attr args
;;      ;; TODO BUG: repeated appends are not performant; cons then reverse in inductive-type-declaration
;;      (append
;;       (attribute a.args)
;;       (list #'e))))

;;   (define-syntax-class inductive-type-declaration
;;     (pattern
;;      x:id
;;      #:attr inductive-name
;;      #'x
;;      #:attr params
;;      '()
;;      #:attr indices
;;      '()
;;      #:attr decls
;;      (list #`(#,(gensym 'anon-discriminant) : x))
;;      #:attr abstract-indices
;;      values)

;;     (pattern
;;      ;; BUG TODO NB: Because the inductive type may have been inferred, it may appear in Curnel syntax, i.e., nested applications starting with dep-app
;;      ;; Best to ensure it *always* is in Curnel form, and pattern match on that.
;;      a:curried-application
;;      #:attr inductive-name
;;      (attribute a.name)
;;      #:attr params
;;      (take (attribute a.args) (cur-data-parameters (attribute a.name)))
;;      #:attr indices
;;      (drop (attribute a.args) (cur-data-parameters (attribute a.name)))
;;      #:attr names
;;      (for/list ([e (attribute indices)])
;;        (format-id e "~a" (gensym 'anon-index)))
;;      #:attr types
;;      ;; TODO: Detect failure, report error/suggestions
;;      (for/list ([e (attribute indices)])
;;        (or (cur-type-infer e)
;;            (raise-syntax-error
;;             'match
;;             (format
;;              "Could not infer type of index ~a"
;;              e)
;;             e)))
;;      #:attr decls
;;      (append
;;       (for/list ([name (attribute names)]
;;                  [type (attribute types)]
;;                  [src (attribute indices)])
;;         (quasisyntax/loc src
;;           (#,name : #,type)))
;;       (list
;;        (quasisyntax/loc #'a
;;          (#,(gensym 'anon-discriminant) : (inductive-name #,@(attribute params) #,@(attribute names))))))
;;      #:attr abstract-indices
;;      (lambda (return)
;;        ;; NB: unhygenic
;;        ;; Normalize at compile-time, for efficiency at run-time
;;        (cur-normalize
;;         #`((lambda
;;               ;; TODO: utterly fragile; relies on the indices being referred to by name, not computed
;;               ;; works only for simple type families and simple matches on them
;;              #,@(for/list ([name (attribute indices)]
;;                            [type (attribute types)])
;;                  #`(#,name : #,type))
;;             #,return)
;;           #,@(attribute names))))))

;;   (define-syntax-class telescope
;;     (pattern ((~literal real-Π) (x:id (~datum :) t:expr) e:telescope)
;;              #:attr decls (cons #'(x : t) (attribute e.decls))
;;              #:attr names (cons #'x (attribute e.names))
;;              #:attr types (cons #'t (attribute e.types)))

;;     (pattern e:expr
;;              #:attr decls '()
;;              #:attr names '()
;;              #:attr types '()))

;;   ;; TODO: Error checking
;;   (define (rename t ls)
;;     (define type (cur-expand t))
;;     (syntax-parse type
;;       #:literals (real-Π)
;;       #:datum-literals (:)
;;       [(real-Π (x:id : t:expr) e:expr)
;;        #`(real-Π (#,(car ls) : t)
;;                  #,(rename
;;                     (with-env
;;                      `((,(car ls) . ,#'t))
;;                      (cur-normalize
;;                       #`((lambda (x : t) e) #,(car ls))))
;;                     (cdr ls)))]
;;       [e #'e]))

;;   (define (instantiate t ls)
;;     (define type (cur-expand t))
;;     (syntax-parse type
;;       #:literals (real-Π)
;;       #:datum-literals (:)
;;       [(real-Π (x:id : t:expr) e:expr)
;;        (if (not (null? ls))
;;            (instantiate
;;                (cur-normalize #`((λ (x : t) e) #,(car ls)))
;;                (cdr ls))
;;            type)]
;;       [e #'e]))

;;   (define-syntax-class match-declaration
;;     (pattern
;;      name:id
;;      #:attr type #f)

;;     (pattern
;;      (name:id (~datum :) type:expr)))

;;   (define (is-constructor-for x name)
;;     (ormap (curry cur-equal? x) (cur-constructors-for name)))

;;   (define-syntax-class (match-prepattern D-expr)
;;     (pattern
;;      x:id
;;      #:with D D-expr
;;      #:declare D inductive-type-declaration
;;      #:attr name (attribute D.inductive-name)
;;      #:fail-unless (is-constructor-for #'x (attribute name))
;;      (raise-syntax-error
;;       'match
;;       (format "The constructor ~a in match clause is not a constructor for the type being eliminated ~a"
;;               (syntax-e #'x)
;;               (syntax-e (attribute name)))
;;       #'x)
;;      #:attr constr #'x
;;      #:attr local-env
;;      '()
;;      #:attr decls
;;      '()
;;      #:attr types
;;      '()
;;      #:attr names
;;      '())

;;     (pattern
;;      (x:id d:match-declaration ...+)
;;      ;; TODO: Copy-pasta from above
;;      #:with D:inductive-type-declaration D-expr
;;      #:attr name (attribute D.inductive-name)
;;      #:fail-unless (is-constructor-for #'x (attribute name))
;;      (raise-syntax-error
;;       'match
;;       (format "The constructor ~a in match clause is not a constructor for the type being eliminated ~a"
;;               (syntax-e #'x)
;;               (syntax-e (attribute name)))
;;       #'x)

;;      #:attr constr #'x
;;      #:attr types
;;      (syntax-parse (instantiate (cur-type-infer #'x) (attribute D.params))
;;        [t:telescope (attribute t.types)])
;;      #:attr local-env
;;      (for/fold ([d `()])
;;                ([name (attribute d.name)]
;;                 [type (attribute d.type)]
;;                 [itype (attribute types)])
;;        (when type
;;          (unless (cur-equal? type itype #:local-env (reverse d))
;;            (raise-syntax-error 'match
;;                                (format
;;                                 "Type annotation ~a did not match inferred type ~a"
;;                                 (syntax->datum type)
;;                                 (syntax->datum itype))
;;                                #'x
;;                                type)))
;;        (cons (cons name type) d))
;;      #:attr decls
;;      (map (lambda (x y) #`(#,x : #,y)) (attribute d.name) (attribute types))
;;      #:attr names
;;      (attribute d.name)))

;;   (define-syntax-class (match-pattern D motive)
;;     (pattern
;;      (~var d (match-prepattern D))
;;      #:with D:inductive-type-declaration D
;;      #:attr constr (attribute d.constr)
;;      #:attr decls
;;      ;; Infer the inductive hypotheses, add them to the pattern decls
;;      ;; and update the dictionarty for the recur form
;;      (for/fold ([decls (attribute d.decls)])
;;                ([type-syn (attribute d.types)]
;;                 [name-syn (attribute d.names)]
;;                 [src (attribute d.decls)]
;;                 ;; NB: Non-hygenic
;;                 )
;;        ;; TODO: Need decls->env
;;        (with-env (reverse (map (lambda (x) (syntax-parse x
;;                                     #:datum-literals (:)
;;                                     [(x : t)
;;                                      `(,#'x . ,#'t)]))
;;                       decls))
;;          (begin
;;            (define/syntax-parse type:inductive-type-declaration (cur-expand type-syn))
;;            (if (cur-equal? (attribute type.inductive-name) (attribute D.inductive-name))
;;                (let ([ih-name (format-id name-syn "ih-~a" name-syn)]
;;                      ;; Normalize at compile-time, for efficiency at run-time
;;                      [ih-type (cur-normalize #`(#,motive #,@(attribute type.indices) #,name-syn))])
;;                  (dict-set! ih-dict (syntax->datum name-syn) ih-name)
;;                  (append decls (list #`(#,ih-name : #,ih-type))))
;;                decls)))
;;        )))

;;   (define-syntax-class (match-preclause D maybe-return-type)
;;     (pattern
;;      ((~var p (match-prepattern D)) b:expr)
;;      #:attr return-type
;;      ;; TODO: Check that the infered type matches maybe-return-type, if it is provied
;;      (or maybe-return-type
;;          ;; Ignore errors when trying to infer this type; other attempt might succeed
;;          (with-handlers ([values (lambda _ #f)])
;;            ;; TODO: all these reverse's are garbage; should keep track of the env in the right order
;;            (cur-type-infer #:local-env (reverse (attribute p.local-env)) #'b)))))

;;   ;; TODO: Perhaps this should be part of the application macro. That could simply test the operator
;;   ;; against the current-definition-id, rather than walk over the syntax tree.
;;   (define (replace-recursive-call body)
;;     (syntax-parse (cur-expand body)
;;       #:literals (real-lambda real-Π real-app elim)
;;       #:datum-literals (:)
;;       [(real-lambda (x : t) e)
;;        (quasisyntax/loc this-syntax
;;          (real-lambda (x : #,(replace-recursive-call #'t)) #,(replace-recursive-call #'e)))]
;;       [(real-Π (x : t) e)
;;        (quasisyntax/loc this-syntax
;;          (real-Π (x : #,(replace-recursive-call #'t)) #,(replace-recursive-call #'e)))]
;;       [(real-app e:id a:expr)
;;        ;; TODO: Need proper identifiers to do the right thing
;;        #:when (and (current-definition-id) (eq? (syntax-e #'e) (syntax-e (current-definition-id))))
;; ;       #:when (bound-identifier=? #'e (syntax-parameter-value #'current-definition-id))
;;        (quasisyntax/loc this-syntax
;;          (lambda #,@(cdr (current-definition-param-decl)) (recur #,(replace-recursive-call #'a))))]
;;       [(real-app e:expr e2:expr)
;;        (quasisyntax/loc this-syntax
;;          (#,(replace-recursive-call #'e) #,(replace-recursive-call #'e2)))]
;;       [(elim e:expr ...)
;;        (quasisyntax/loc this-syntax
;;          (elim #,@(map replace-recursive-call (attribute e))))]
;;       [x:id this-syntax]))

;;   (define-syntax-class (match-clause D motive)
;;     (pattern
;;      ((~var p (match-pattern D motive))
;;       b:expr)
;;      #:attr constr (attribute p.constr)
;;      #:attr method
;;      (let ([b (with-env
;;                 (reverse (map (lambda (x)
;;                        (syntax-parse x
;;                          #:datum-literals (:)
;;                          [(x : t) `(,#'x . ,#'t)]))
;;                      (attribute p.decls)))
;;                 (replace-recursive-call #'b))])
;;        (quasisyntax/loc #'p
;;          #,(if (null? (attribute p.decls))
;;                b
;;                #`(lambda #,@(attribute p.decls) #,b)))))))

;; (define-syntax (recur syn)
;;   (syntax-case syn ()
;;     [(_ id)
;;      ;; TODO XXX HACK: Backwards compatibility hack; recur should be use syntax-paramterize
;;      (datum->syntax #'id (syntax->datum (dict-ref
;;       ih-dict
;;       (syntax->datum #'id)
;;       (lambda ()
;;         (raise-syntax-error
;;          'match
;;          ;; TODO: Detect when inside a match to provide better error
;;          (format
;;           "Cannot recur on ~a. Either not inside a match or ~a is not an inductive argument."
;;           (syntax->datum #'id)
;;           (syntax->datum #'id))
;;          syn)))))]))

;; (define-syntax (match syn)
;;   (syntax-parse syn
;;     [(_ d
;;         ~!
;;         (~optional
;;          (~seq #:in ~! t)
;;          #:defaults
;;          ([t (or (cur-type-infer #'d)
;;                  (raise-syntax-error
;;                   'match
;;                   "Could not infer discrimnant's type. Try using #:in to declare it."
;;                   syn))]))
;;         (~parse D:inductive-type-declaration (cur-expand (attribute t)))
;;         (~optional (~seq #:return ~! maybe-return-type))
;;         (~peek (~seq (~var prec (match-preclause (attribute D) (attribute maybe-return-type))) ...))
;;         ~!
;;         (~bind (return-type (ormap values (attribute prec.return-type))))
;;         (~do (unless (attribute return-type)
;;                (raise-syntax-error
;;                 'match
;;                 "Could not infer return type. Try using #:return to declare it."
;;                 syn)))
;;         ;; BUG TODO: return-type is inferred with the indexes of the branches, but those must be abstracted in the motive...
;;         ;; Replace each of the D.indices with the equivalent name from D.decls
;;         (~bind (motive (quasisyntax/loc syn
;;                          (lambda #,@(attribute D.decls)
;;                            #,((attribute D.abstract-indices) (attribute return-type))))))
;;         (~var c (match-clause (attribute D) (attribute motive))) ...)
;;      ;; TODO: Make all syntax extensions type check, report good error, rather than fail at Curnel
;;      (define (sort-methods name mconstrs-stx methods)
;;        ;; NB: Casting identifiers to symbols is a bad plan
;;        (define constrs (map syntax-e (cur-constructors-for name)))
;;        (define mconstrs (map syntax-e mconstrs-stx))
;;        (unless (eq? (length mconstrs) (length constrs))
;;          (raise-syntax-error
;;           'match
;;           (format "Missing match clause for the following constructor(s): ~a"
;;                   (remf* (lambda (x) (memq x mconstrs)) constrs))
;;           syn))
;;        ;; TODO: This seems like a generally useful function
;;        (define constr-index (build-list (length constrs) values))
;;        (define sorted
;;          (sort (map cons mconstrs methods) <
;;                #:key
;;                (lambda (x)
;;                  (dict-ref
;;                   (map cons constrs constr-index)
;;                   (car x)))))

;;        (map cdr sorted))

;;      (quasisyntax/loc syn
;;        (elim
;;         D.inductive-name
;;         motive
;;         #,(sort-methods (attribute D.inductive-name) (attribute c.constr) (attribute c.method))
;;         d))]))

;; (begin-for-syntax
;;   (define-syntax-class let-clause
;;     (pattern
;;       (~or (x:id e) ((x:id (~datum :) t) e))
;;       #:attr id #'x
;;       #:attr expr #'e
;;       #:attr type (cond
;;                     [(attribute t)
;;                      ;; TODO: Code duplication in ::
;;                      (unless (cur-type-check? #'e #'t)
;;                        (raise-syntax-error
;;                          'let
;;                          (format "Term ~a does not have expected type ~a. Inferred type was ~a"
;;                                  (cur->datum #'e) (cur->datum #'t) (cur->datum (cur-type-infer #'e)))
;;                          #'e (quasisyntax/loc #'x (x e))))
;;                      #'t]
;;                     [(cur-type-infer #'e)]
;;                     [else
;;                       (raise-syntax-error
;;                         'let
;;                         "Could not infer type of let bound expression"
;;                         #'e (quasisyntax/loc #'x (x e)))]))))
;; (define-syntax (let syn)
;;   (syntax-parse syn
;;     [(let (c:let-clause ...) body)
;;      #'((lambda (c.id : c.type) ... body) c.e ...)]))

;; ;; Normally type checking will only happen if a term is actually used/appears at top-level.
;; ;; This forces a term to be checked against a particular type.
;; (define-syntax (:: syn)
;;   (syntax-case syn ()
;;     [(_ pf t)
;;      (begin
;;        ;; TODO: Code duplication in let-clause pattern
;;        (unless (cur-type-check? #'pf #'t)
;;          (raise-syntax-error
;;            '::
;;            (format "Term ~a does not have expected type ~a. Inferred type was ~a"
;;                    (cur->datum #'pf) (cur->datum #'t) (cur->datum (cur-type-infer #'pf)))
;;            syn))
;;        #'(void))]))

;; (define-syntax (run syn)
;;   (syntax-case syn ()
;;     [(_ expr) (cur-normalize #'expr)]))

;; (define-syntax (step syn)
;;   (syntax-case syn ()
;;     [(_ expr)
;;      (let ([t (cur-step #'expr)])
;;        (displayln (cur->datum t))
;;        t)]))

;; (define-syntax (step-n syn)
;;   (syntax-case syn ()
;;     [(_ n expr)
;;      (for/fold
;;        ([expr #'expr])
;;        ([i (in-range (syntax->datum #'n))])
;;        #`(step #,expr))]))

;; (define-syntax (query-type syn)
;;   (syntax-case syn ()
;;     [(_ term)
;;      (begin
;;        (printf "\"~a\" has type \"~a\"~n" (syntax->datum #'term) (syntax->datum (cur-type-infer #'term)))
;;        #'(void))]))

(begin-for-syntax
  (require (for-syntax racket/base))
  (define-syntax (cur-match syn)
    (syntax-case syn ()
      [(_ syn [pattern body] ...)
       #'(syntax-parse syn
           [pattern body] ...)])))

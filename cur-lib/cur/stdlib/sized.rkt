#lang s-exp "../main.rkt"

;; differs from curnel/racket-impl:
;; -> is normal arrow type and not alias for Π,
;; but ∀ and forall is alias for Π

(provide define-sized-datatype
         define/rec/match2)

(require "nat.rkt"
         (prefix-in r: racket/base)
         (for-syntax (for-syntax syntax/parse racket/base)
                     syntax/stx racket/pretty
                     macrotypes/stx-utils
                     cur/curnel/stxutils
                     turnstile+/type-constraints))


;; features:
;; 1) termination check: recursive call arg must have smaller size
;;    - fn binding must specify smaller size
;;    - pat->ctxt must return binding with type that also has matching smaller size
;; 2) must be able to declare size-preserving fns, eg pred, minus
;; 3) checking size-preserving fns
;;    - what to do about base cases, eg zero?
;; 4) what to do about succ case??, eg div
;; 5) TODO: sometimes you just need constructor with explicit size,
;; eg in map, need to convert nil A to nil B, preserving the size
(begin-for-syntax
  (define SZPROP '$)
  (define (mk-sz id [ctx id]) (format-id ctx "~a/sz" id))
  (define (get-size t)
    (ca*r (syntax-property t SZPROP)))
  (define (add-size t sz)
    (syntax-property t SZPROP sz))
  (define (ty-sz->datum t)
    (define sz (get-size t))
    (if sz (stx->datum sz) "inf"))
  (define ((mk-tycheck/sz oldcheck) t1 t2)
    (and (oldcheck t1 t2)
         ;; (printf "new check (1): ~a\n" (stx->datum t1))
         ;; (printf "new check (2): ~a\n" (stx->datum t2))
         (or (not (get-size t2))
             (let ([size-ok?
                    (let L ([t1sz (get-size t1)] [t2sz (get-size t2)])
                      ;; (printf "size1: ~a\n" t1sz)
                      ;; (printf "size2: ~a\n" t2sz)
                      (syntax-parse (list t1sz t2sz)
                        [(x:id y:id) (free-id=? #'x #'y)]
                        [(((~datum <) x)
                          ((~datum <) y)) (L #'x #'y)]
                        [(((~datum <) x) y) (L #'x #'y)]
                        [_ #f]))])
               (begin0 size-ok?
                 (unless size-ok?
                   (current-check-relation oldcheck)
                   (current-typecheck-relation oldcheck)
                   (fprintf (current-error-port)
                            "Failed size check for arg of type ~a: expected ~a, given ~a\n"
                            (stx->datum (resugar-type t1))
                            (ty-sz->datum t2) (ty-sz->datum t1)))))))))

(begin-for-syntax

; Π  λ ≻ ⊢ ≫ → ∧ (bidir ⇒ ⇐) τ⊑ ⇑

  ;; decrements size prop of `ty`
  (define (dec-size ty)
    (define sz (syntax-property ty '$))
    (syntax-property ty '$ (if sz #`(< #,sz) (generate-temporary))))

  ;; helper fns for define/rec/match2

  ;; TODO: why do these fns need to be defined here
  ;; (as opposed to curnel/stxutils)
  ;; helper fns for define/rec/match2
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
  ;; name-orig needed for higher order uses
  (define (unsubst-app name name-orig name-eval num-args)
    (syntax-parser
      [_
       #:do[(define the-app (get-app this-syntax name num-args))]
       #:when the-app
       #:with (_ . args) the-app
       (datum->syntax
        this-syntax
        (cons (mk-reflected name-eval #'#%plain-app name) #'args)
        this-syntax this-syntax)]
      [:id #:when (datum=? this-syntax name-orig) name-orig]
      [:id this-syntax]
      [(x ...)
       (datum->syntax
        this-syntax
        (stx-map (unsubst-app name name-orig name-eval num-args) #'(x ...))
        this-syntax this-syntax)])))

;; size must be added to type, not term, if we want size info to propagate
;; through fn calls (via the fn type)
(define-syntax define-sized-datatype
  (syntax-parser
    [(_ TY:id)
     #:with TYC (let L ([t ((current-type-eval) #'TY)])
                  (syntax-parse t ; extract type from HO fn
                    [((~literal #%plain-lambda) _ body)
                     (L #'body)]
                    [_ t]))
     ;; #:do[(printf "Creating sized: ~a\n" (stx->datum #'TY))]
     #:do[(define exinfo (get-match-info #'TYC))] ; TYC is an application of TY
     ;; #:do[(printf "exinfo: ~a\n" (stx->datum exinfo))]
     #:fail-unless exinfo (format "could not infer extra info from type ~a" (stx->datum #'τ))
     #:with (_ elim-Name ([A _] ...) _ _ [C ([x τin] ... τout) ((xrec _ ...) ...)] ...) exinfo
     #:with (C/sz ...) (stx-map (λ (t) (mk-sz t #'TY)) #'(C ...))
     #`(begin
         (begin-for-syntax ; pattern expander
           (define-syntax C/sz (make-rename-transformer #'C)) ...)
         (define-syntax C/sz
           (datacons
           (syntax-parser
             [(_ (~optional (~seq #:size j:id) #:defaults ([j (generate-temporary)]))
                 A ... x ...) ;; TODO: rename A ...? dont want subst to be done by stx template here
              #:do[(define maybe-sz
                     (if (not (stx-null? #'(xrec ...)))
                         ;; check for obvious xrec first
                         (get-size (typeof (expand/df (stx-car #'(xrec ...)))))
                         ;; else look for nested TYs
                         (let L1 ([xs #'(x ...)])
                           (and (not (stx-null? xs))
                                (let ([t (typeof (expand/df (stx-car xs)))])
                                  (if (let has-TY? ([t t]) ; check if t has nested TY
                                        (syntax-parse t
                                          [:id #f]
                                          [(_ (~datum TY) . _) #t]
                                          [(ty (... ...)) (stx-ormap has-TY? #'(ty (... ...)))]))
                                      (get-size t)
                                      (L1 (stx-cdr xs))))))))]
              #:with sz (cond [maybe-sz
                               (syntax-parse maybe-sz
                                 [((~datum <) i) #'i]
                                 [_ #'j])]
                              [else #'j])
              #:with C+ (local-expand #'(C A ... x ...) 'expression null)
              #:with Cty (typeof #'C+)
              #:with Cty/sz (add-size #'Cty #'sz)
              (syntax-property #'C+ ': #'Cty/sz)])
           (λ (p t)
             (define x+tys
               ((datacons-pat->ctxt (syntax-local-value #'C)) p t))
             (stx-map
              (λ (x+ty)
                (list (stx-car x+ty) ; x
                      (dec-size (stx-cadr x+ty)))) ; ty
              x+tys))
           ))
         ...)]))
     
; Π  λ ≻ ⊢ ≫ → ∧ (bidir ⇒ ⇐) τ⊑ ⇑
; experimental define/rec/match2, uses sized types
(define-typed-syntax define/rec/match2
  ;; in this case, all params are named and patmatched
  [(_ name:id
      (~datum :)
      [x (~datum :) ty_in (~optional (~seq #:size n-or-#f) #:defaults ([n-or-#f #'#f]))] ...
      (~datum ->) ty_out_ (~optional (~seq #:size m-or-#f) #:defaults ([m-or-#f #'#f]))
      ~!
      [pat ... (~datum =>) body] ...) ≫
;   #:do[(printf "def/rec/match ~a\n" (stx->datum #'name))]
   #:with (ty-to-match ... ty_out) (stx-map
                                    (λ (t i) (if (stx-e i) (add-size t i) t))
                                    #'(ty_in ... ty_out_) #'(n-or-#f ... m-or-#f))
   ;; args with explicit sizes are required decreasing args
   #:with (ty-to-match< ... ty_out<) (stx-map
                                      (λ (t i) (if (stx-e i) (add-size t #`(< #,i)) t))
                                      #'(ty_in ... ty_out_)
                                      #'(n-or-#f ... m-or-#f))
     #:with (n ...) (stx-map (λ (y) (if (stx-e y) y (generate-temporary))) #'(n-or-#f ...))
     #:with m (if (stx-e #'m-or-#f) #'m-or-#f (generate-temporary))
     #:with (([xpat xpatτ] ...) ...) (stx-map
                                      (λ (pats)
                                        (stx-appendmap pat->ctxt pats #'(ty-to-match ...)))
                                      #'((pat ...) ...))

     #:with (([x+pat x+patτ] ...) ...) (stx-map
                                        (λ (x+τs)
                                          #`(#,@#'((x ty-to-match) ...) ; append x+tyin to pat binders+tys
                                             #,@x+τs))
                                        #'(([xpat xpatτ] ...) ...))
     ;; check-rel used by (turnstile+) bidir judgements
     ;; - needed to check size-preservation fns
     ;; tycheck-rel used by typerules themselves
     ;; - needed for termination check of rec calls
     [([x+pat ≫ x+pat- : x+patτ] ...)
      ([name ≫ name- : (Π [x : ty-to-match<] ... ty_out<)])
      ⊢ [body ≫ body- ⇐ ty_out]
      #:where typecheck-relation (mk-tycheck/sz old-typecheck-relation)
      #:where check-relation (current-typecheck-relation)] ...
     #:do[(define arity (stx-length #'(x ...)))]
     #:with ((x*- ...) ...) (stx-map
                             (λ (x+pats)
                               (stx-take x+pats (stx-length #'(x ...))))
                             #'((x+pat- ...) ...))
     #:with ((xpat- ...) ...) (stx-map
                               (λ (x+pats)
                                 (stx-drop x+pats (stx-length #'(x ...))))
                               #'((x+pat- ...) ...))
     #:with (x- ...) (generate-temporaries #'(x ...))
     #:with name-eval (mk-eval #'name)
     ;; need to "unsubst" recursive references to (to-be-defined) calls to name-eval
     #:with (body-- ...) (stx-map
                          (λ (nm- b)
                            (reflect
                             ((unsubst-app nm- #'name #'name-eval arity) b)))
                          #'(name- ...)
                          #'(body- ...))
     ;; TODO: dont need to typecheck again on recursive call?
     #:with ((pat- ...) ...) (stx-map
                              substs
                              #'((xpat- ...) ...)
                              #'((xpat ...) ...)
                              #'((pat ...) ...))
     #:with (red-pat ...) #'((#%plain-app (~and x*- pat-) ...) ...)
     #:with OUT
     #'(begin
         ;; this macro uses the patvar reuse technique
         ;; ie, references to x in x0 will be instantiated to the type bound to x
         (define-typed-syntax name
           [(_ x ... ~!) ≫
            [⊢ x ≫ x- ⇐ ty_in] ...
            #:with (n ...) (stx-map (compose get-size typeof) #'(x- ...))
            #:with ty_out/sz (add-size #'ty_out #'m)
            ----------
            [⊢ (name-eval x- ...) ⇒ ty_out/sz]]
           ; non-full application cases: η expand
           [:id ≫ --- [≻ (name)]]
           [(_ arg (... ...)) ≫ 
            ----
            [≻ ((λ [x : ty_in] ... (name x ...))
                arg (... ...))]])
         (define-red name-eval #:display-as name [red-pat ~> body--] ...))
     ;     #:do[(pretty-print (syntax->datum #'OUT))]
     -----
     [≻ OUT]]
  ;; ----------------------------------------------------------------------
  ;; not all args patmatched ----------------------------------------------
  ;; ----------------------------------------------------------------------
  [(_ name:id
      (~datum :)
      [x (~datum :) ty_in1 (~optional (~seq #:size xsz))] ...
      (~and (~not [_ (~datum :) . _]) (~not (~datum ->))
            (~or (ty-to-match_ #:size n)
                 (~and ty-to-match_ (~parse n (generate-temporary))))) ...
      [y (~datum :) ty_in2] ...
      (~datum ->) ty_out (~optional (~seq #:size m) #:defaults ([m (generate-temporary)]))
      [pat ... (~datum =>) body] ...) ≫
     #:fail-unless (or (zero? (stx-length #'(x ...))) ; TODO: remove this restriction
                       (zero? (stx-length #'(y ...))))
     "cannot have both pre and post pattern matching args"
     #:with (ty-to-match ...) (cons (add-size ; first ty-to-match is "measure" arg
                                     (stx-car #'(ty-to-match_ ...))
                                     (stx-car #'(n ...)))
                                    (stx-cdr #'(ty-to-match_ ...)))
     #:with (ty-to-match< ...) (cons (add-size ; first ty-to-match is "measure" arg
                                     (stx-car #'(ty-to-match_ ...))
                                     (stx-car #'((< n) ...)))
                                     (stx-cdr #'(ty-to-match_ ...)))
            
 ;    #:do[(printf "fn: ~a ----------------\n" (stx->datum #'name))]
     #:with (([xpat xpatτ] ...) ...)
     (stx-map
      (λ (pats)
        (stx-appendmap pat->ctxt pats #'(ty-to-match ...)))
      #'((pat ...) ...))
;     #:do[(printf "pattern binders: ~a\n" (stx->datum #'(([xpat xpatτ] ...) ...)))]
     #:with (x0 ...) (if (stx-null? #'(ty-to-match_ ...))
                         (list (car (stx-rev #'(x ...))))
                         (generate-temporaries #'(ty-to-match ...)))
     #:with (([x+pat x+patτ] ...) ...) (stx-map
                                        (λ (x+τs)
                                          #`(#,@#'((x ty_in1) ...) ; append x+tyin1 with pat binders and tys
                                             #,@x+τs))
                                        #'(([xpat xpatτ] ...) ...))
     [([x+pat ≫ x+pat- : x+patτ] ...)
      ([y ≫ y*- : ty_in2] ...
       ;; for now, assume recursive references are fns
       [name ≫ name- : (Π [x : ty_in1] ... [x0 : ty-to-match<] ... [y : ty_in2] ... ty_out)])
      ⊢ [body ≫ body- ⇐ ty_out]
      #:where typecheck-relation (mk-tycheck/sz old-typecheck-relation)] ...
     #:do[(define arity (stx-length #'(x ... ty-to-match ... y ...)))]
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
                             ((unsubst-app n- #'name #'name-eval arity) b)))
                          #'(name- ...)
                          #'(body- ...))
     ;; TODO: dont need to typecheck again on recursive call?
     #:with ((pat- ...) ...) (stx-map
                              substs
                              #'((xpat- ...) ...)
                              #'((xpat ...) ...)
                              #'((pat ...) ...))
     #:with (red-pat ...) #'((#%plain-app x*- ... pat- ... y*- ...) ...)
     #:with OUT
     #'(begin
         ;; this macro uses the patvar reuse technique
         ;; ie, references to x in x0 will be instantiated to the type bound to x
         (define-typed-syntax name
           [(_ x ... x0 ... y ... ~!) ≫
            [⊢ x ≫ x- ⇐ ty_in1] ...
            [⊢ x0 ≫ x0- ⇐ ty-to-match] ...
            #:with (n ...) (stx-map (compose get-size typeof) #'(x0- ...))
            [⊢ y ≫ y- ⇐ ty_in2] ...
            #:with ty_out/sz (add-size #'ty_out #'m)
            ----------
            [⊢ (name-eval x- ... x0- ... y- ...) ⇒ ty_out/sz]]
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

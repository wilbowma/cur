#lang s-exp "../main.rkt"

(provide
 (for-syntax (all-defined-out)))

(require
 (for-syntax
  racket/bool
  racket/list
  racket/pretty
  racket/string)
 (only-in
  turnstile+/base subst))

;; This module defines the pattern tree structure for analyzing and translating
;; Cur match expressions.
;; Conceptually, we can consider the data structure defined in this module
;; as a prefix tree for Cur patterns.
;; By representing pattern matches in this way, we can determine totality and
;; produce eliminator-style programs.

;; GRAMMAR (denoting conversion from INPUT to NESTED)
;; ---------------
;; patvar := <some pattern variable, e.g. x>
;; pat := <any pattern, e.g. (s x)>
;; body := <any body, e.g. true>
;; INPUT := ((listof patvar) (listof (listof pat) body))
;; NESTED := (patvar (listof pat NESTED))
;;           | body

;; MINI GLOSSARY (clarification of language used)
;; ---------------
;; C-GROUP: a constructor group.
;; Essentially, it is used as a means to aggregate data to be displayed and
;;  the remaining match information for a specific constructor match case.
;; C-HASH: a hash values are C-groups.
;; HEAD PATTERN: the first pattern in a pattern row.
;; MATCH VARIABLE: positional arguments that are to be bound during the matching
;;   process.
;;   The number of these correspond to the number of patterns in a pattern list.
;;   These can also be generated dynamically to flatten complex patterns.
;; MATCH PATTERN: the specific pattern that a match variable should be bound to.
;;   Note that Unbound match patterns can occur when new temporaries are
;;   generated, and we treat these as a special case in the matcher.
;; PATTERN MATRIX: we interpret the input Cur match cases as a matrix:
;;   e.g. ([a b => A] [c d => B]) can be viewed as a 2x2 matrix leading to 2
;;   match bodies.
;; PATTERN COLUMN: a list of patterns at the nth position in their match case,
;;   which also corresponds to the nth match variable. To create the tree, we
;;   process pattern columns from left to right.
;; PATTERN ROW: a list of patterns, this corresponds to the lefthand side of a
;;   single input match case row.
;; PATTERN SUB-MATRIX: a subset of the input pattern matrix.
;;   e.g. ([a b => A] [c d => B]), after generating matches for the first match
;;   variable we still need to process the remaining sub-matrix
;;   ([b => A] [d => B])
;; PATTERN TREE: a new representation of Cur's match case as an aggregated
;;   decision tree.
;; PATTERN VARIABLE: a variable representing any pattern.
;;   If these are provided within match cases, then we eliminate the pattern
;;   variable and distribute the corresponding match bodies to all other match
;;   cases at the same level.
;;   It is important to be able to distinguish between pattern variables and
;;   constructors; e.g. [z => A] and [a => A] mean different things; the former
;;   matches zero only while the latter matches anything.
;; TEMPORARY: a newly generated identifier to reduce pattern complexity.
;;   e.g. (s (s x)) can be re-written as (s temp1) where temp1 is a new match
;;   variable with a match pattern (s x).
;;   Note: in our representation, we explicitly choose to allow the reference
;;   to temp1 above to be unbound; this means that the matching function must
;;   explicitly process temporaries first whenever they are used.

; TODO PR103: Ideally, this wouldn't be defined for-syntax, but imported for-syntax at
; its use.
; However, it might assume it's running the macro-expander to have access to
; type information.
; If so, it should remain in a begin-for-syntax.
(begin-for-syntax
  ;; Pattern tree structures; see NESTED grammar above.
  (struct pt-decl (match-var matches) #:transparent)
  (struct pt-match (pattern decl-or-body) #:transparent)
  (struct pt-body (value) #:transparent)

  ;; C-group; represents match data for a constructor and the associated pattern
  ;; sub-matrix
  (struct C-group
    (head-patterns [pattern-sub-matrix #:mutable] bodies temporaries-map
                   is-pattern-variable? sort-order)
    #:transparent)

  ;; For an input of form
  ;; ((n m)
  ;;  ([z z => A]
  ;;   [z (s x) => B])
  ;;
  ;; We create the following resulting tree:
  ;; (pt-decl n (list (pt-match z (pt-decl m (list (pt-match z A)
  ;;                                               (pt-match (s x) B))))
  ;; Note: if no type environment is provided, all inputs are treated as either
  ;; pattern variables or exact syntax matches.
  (define (create-pattern-tree stx #:env [env '()])
    (syntax-parse stx
      [((match-vars:id ...) ((pattern-matrix ... (~datum =>) bodies) ...))
       #:fail-unless (for/and ([pattern-row (attribute pattern-matrix)])
                       (= (length pattern-row) (length (attribute match-vars))))
       "expected all match cases to have same number of patterns as number of matching variables"
       #:fail-unless (not (zero? (length (attribute match-vars))))
       "expected at least one matching variable"
       (create-pattern-tree-decl-helper
        ; HACK PR103: this map lets us can keep track of which match vars were not
        ; generated
        (map (lambda (mv) (syntax-property mv 'is-pos-arg? #t))
             (attribute match-vars))
        (attribute pattern-matrix)
        (attribute bodies)
        env)]))

  ;; Create a prefix tree by keying on the constructor type of the first pattern.
  ;; Conceptual step-by-step example:
  ;; 1. (x y z) ([a b c => body1]
  ;;             [d e f => body2])
  ;;
  ;; 2. (y z) (x [a ([b c => body1])]
  ;;             [d ([e f => body2])]))
  ;;
  ;; 3. (z) (x [a (y [b ([c => body1])])]
  ;;           [d (y [e ([f => body2])])]))
  ;;
  ;; 4. () (x [a (y [b (z [c (body1)])])]
  ;;          [d (y [e (z [f (body2)])])]))
  ;;
  ;; Nested constructor patterns example: (x) ([(C1 (C2 a1)) => body])
  ;; We rewrite this as (x temp1) ([(C1 temp1) (C2 a1) => body])
  ;; before proceding as shown above.
  ;; Observe that the bindings for the new temporaries are reversed; this is
  ;; addressed in the matching function.
  ;; NOTE: Imperative code, sensitive to order of expressions!
  (define (create-pattern-tree-decl-helper match-vars pattern-matrix bodies env)
    (let* (; create a hash to store results for the leading pattern column
           [C-hash (make-hash)]
           [current-match-var (first match-vars)]
           ; for each match case, process the first pattern and store the
           ; resulting C-group into a hash indexed by constructor or pattern
           ; variable
           [merged-entries
            (begin
              (for ([head-pattern (map first pattern-matrix)]
                    [remaining-patterns (map rest pattern-matrix)]
                    [body bodies]
                    [idx (in-naturals)])
                (process-pattern! current-match-var
                                  head-pattern
                                  remaining-patterns
                                  body idx C-hash env))
              (hash->list C-hash))]
           ; for deterministic results, sort the entries by order of first
           ; occurrence in the input list; note that an entry is the tuple
           ; (unique-key, C-group)
           [sorted-entries (sort merged-entries < #:key (lambda (e) (C-group-sort-order (cdr e))))]
           ; if a pattern variable is used, then the match cases for it need to be distributed among
           ; all other potential match paths
           [pattern-var-entry (for/or ([entry sorted-entries])
                                (and (C-group-is-pattern-variable? (cdr entry)) entry))]
           [remaining-entries (filter (lambda (e) (not (equal? e pattern-var-entry))) sorted-entries)]
           ; always put pattern variable branches at the end; this will make pattern matching easier
           [entries (append remaining-entries (if pattern-var-entry (list pattern-var-entry) empty))]
           ; now, finalize the current match variable; we can consider this as declaring the match variable as
           ; a new identifier, and subsequently providing bindings for it using the corresponding matches)
           ; additional bookkeeping property to know if the current match variable was generated or passed in
           [pt (pt-decl current-match-var
                        ; process previous results to produce list of match cases
                        (for/list ([entry entries])
                          (let* ([group (cdr entry)]
                                 [key (car entry)]
                                 ; having processed the first pattern of each case, we now know how many temporaries we need
                                 ; to generate in a nested scenario: for example, (s (s a) (s b)) -> (s temp1 temp2)
                                 ; and this would correspond to a map of (#f #t #t) which we convert to (#f temp1 temp2)
                                 [tmp-map-with-ids
                                  (map
                                   (lambda (t)
                                     (and t
                                          (syntax-property
                                           ; TODO PR103: Can we use fresh here instead?
                                           (generate-temporary 'temp)
                                           'is-temp? #t)))
                                   (C-group-temporaries-map group))]
                                 ; for each of the remaining patterns, we may need to add temporary matches to them.
                                 ; following the example above: temp1 matches against (s a) and temp2 matches against (s b)
                                 [pattern-sub-matrix (for/list ([pattern-row (C-group-pattern-sub-matrix group)]
                                                                [head-pattern (C-group-head-patterns group)])
                                                       (append (generate-tmp-patterns head-pattern tmp-map-with-ids)
                                                               pattern-row))]
                                 ; artificially inject a pattern variable case into the current entry
                                 [merged-group (begin
                                                 (set-C-group-pattern-sub-matrix! group pattern-sub-matrix)
                                                 (if (and pattern-var-entry (not (equal? pattern-var-entry entry)))
                                                     (merge-c-groups group (cdr pattern-var-entry) #:allow-merge-pattern-variable? #t)
                                                     group))]
                                 ; after creating our new temporaries, we should also associate them with types
                                 ; based on proper inference
                                 [extended-env (extend-env-with-tmps
                                                env
                                                (first (C-group-head-patterns merged-group))
                                                tmp-map-with-ids
                                                current-match-var)]
                                 ; to ensure that we don't erroneously shadow any bindings, we need to generate temporaries for
                                 ; inner arguments too; (s x) -> (s x1)
                                 [fresh-result (generate-fresh-arguments (C-group-head-patterns merged-group) (C-group-bodies merged-group) tmp-map-with-ids current-match-var extended-env)]
                                 [fresh-head-patterns (car fresh-result)]
                                 [fresh-bodies (cdr fresh-result)]
                                 ; for the match pattern, just fetch anything that's not a pattern variable
                                 [match-pat (first fresh-head-patterns)]
                                 ; hack: attach the temporary type based on the value we've assigned to it in the environment
                                 ; TODO PR103: This can't possibly work... we're
                                 ; trying to add a type to t by using t's type?
                                 ; No, because the extended-env might contain
                                 ; types for them computed from the pattern.
                                 [tmp-map-with-ids-typed (map (lambda (t) (and t (syntax-property t ': (get-typeof t #:env extended-env))))
                                                              tmp-map-with-ids)]
                                 [new-match-vars (append (filter (compose not false?) tmp-map-with-ids-typed) (rest match-vars))])
                            (create-pattern-tree-match-helper
                             new-match-vars
                             ; it may make our lives easier to keep track of the property on the match pattern itself
                             (syntax-property match-pat 'is-pattern-variable? (C-group-is-pattern-variable? merged-group))
                             (C-group-pattern-sub-matrix merged-group)
                             fresh-bodies
                             extended-env))))])
      pt))

  ;; For the current match variable and the head pattern for a particular pattern row, either creates a new
  ;; C-group entry within the constructor hash or merges the remaining patterns to form a new pattern sub-matrix.
  ;; NOTE PR103: the caller does an explicit hash->list C-hash, and then
  ;; the callee does hash->list again. One is unnecessary.
  (define (process-pattern! match-var head-pattern remaining-patterns body idx C-hash env)
    ; for each head pattern, first check to see if it matches existing patterns stored in the constructor hash;
    ; if not, create a new key using the head pattern
    ; note: we do this because key-equal? uses free-identifier=? which cannot be encoded with hashing
    (let* ([key (or
                 ; check if there is a key that equals the current one.
                 ; otherwise, just use the pattern itself as the key
                 (findf
                  (lambda (k)
                    (key-equal? head-pattern k match-var #:env env))
                  (hash-keys C-hash))
                 head-pattern)]
           ; from the current pattern, generate a map for locations containing new temporaries
           ; e.g. (s (s a) (s b)) -> (s temp1 temp2) = (#f #t #t)
           [tmp-map (generate-tmp-map head-pattern)]
           [pat-is-pattern-variable? (is-pattern-variable? head-pattern match-var env)]
           [new-body (if pat-is-pattern-variable?
                         (subst match-var head-pattern body (lambda (a b)
                                                              (and (identifier? a)
                                                                   (identifier? b)
                                                                   (bound-identifier=? a b))))
                         body)]
           [new-data (C-group (list head-pattern)
                              (list remaining-patterns)
                              (list new-body)
                              tmp-map
                              pat-is-pattern-variable?
                              idx)])
      ; if the key already exists, we can merge data onto the same key
      ; e.g. we have two match cases that begin with constructor z, we can join the remaining match cases
      (if (hash-has-key? C-hash key)
          (let* ([old-data (hash-ref C-hash key)])
            (hash-set! C-hash key (merge-c-groups old-data new-data)))
          (hash-set! C-hash key new-data))))

  ;; Equality check between patterns to be used as keys. First check if both
  ;; of the two patterns are pattern variables, in which case we can trivially
  ;; mark the two as equal. Next, check if they're both the same constructors.
  (define (key-equal? k1 k2 match-var #:env [env '()])
    (or
     ; case: both keys structurally match
     (structural-match? k1 k2)
     ; case: both keys represent pattern variables
     (and (is-pattern-variable? k1 match-var env)
          (is-pattern-variable? k2 match-var env))))

  ;; Returns true if either nullary constructor-like; if arguments are present, only
  ;; checks to see that the number of arguments are the same and that the head symbol matches
  (define (structural-match? k1 k2)
    (let ([k1-list (syntax->list k1)]
          [k2-list (syntax->list k2)])
      ; if one key is a list and the other isn't, then don't bother checking further
      ;; TODO PR103: Why would this ever fail? You just did syntax->list.
      (and (equal? (list? k1-list)
                   (list? k2-list))
           ;; TODO PR103: Why would this ever fail? You just did syntax->list.
           (if (list? k1-list)
               (and (= (length k1-list) (length k2-list))
                    (free-identifier=? (first k1-list) (first k2-list)))
               (free-identifier=? k1 k2)))))

  ;; Returns true if a pattern is a pattern variable.
  ;; Assumption: if a variable doesn't have any arguments and is not a known constructor
  ;; for the type then it must be a wildcard variable
  (define (is-pattern-variable? head-pat match-var env)
    (and (not (list? (syntax->list head-pat)))
         (not (is-constructor? head-pat match-var #:env env))))

  ;; Check if an argument is a pattern variable, e.g. (c a1 a2) and whether a1 is a pattern variable
  (define (is-arg-pattern-variable? constructor-id match-var args idx env)
    (let ([arg (list-ref args idx)])
      (and (not (list? (syntax->list arg)))
           (let* ([metadata (get-constructor constructor-id match-var #:env env)]
                  [arg-binding-types (and metadata (map (compose second syntax->list) (second metadata)))]
                  [type-parameters (and metadata (third metadata))]
                  [match-var-type-for-env (and metadata (syntax->list (fourth metadata)))]
                  [match-var-type-values (and match-var-type-for-env
                                              (> (length match-var-type-for-env) 2)
                                              (rest (rest match-var-type-for-env)))]
                  [match-var-type-bindings (and match-var-type-values (map cons type-parameters match-var-type-values))]
                  [new-arg-binding-types (and match-var-type-bindings
                                              (append match-var-type-values
                                                      (for/list ([ty arg-binding-types])
                                                        (subst-bindings ty match-var-type-bindings #:equality? (lambda (a b) (equal? (syntax->datum a)
                                                                                                                                     (syntax->datum b)))))))]
                  ;; TODO PR103: This is probably wrong now since I changed the
                  ;; behavior to fail when matching on a type without
                  ;; constructors.
                  ; conveniently, the Type type doesn't have any constructors, so we can use it as the default
                  [expected-ty (or (and new-arg-binding-types (> (length new-arg-binding-types) idx) (list-ref new-arg-binding-types idx))
                                   #'Type)]
                  [dummy-var #'foo])
             ; case: the argument is a pattern variable if it's in the slot of a generic type
             ; argument but doesn't correspond to the environment
             (or (and type-parameters
                      (< idx (length type-parameters))
                      (not (equal? (syntax->datum arg)
                                   (syntax->datum expected-ty))))
                 ; case: the argument is a pattern variable if it's not a constructor
                 (not (is-constructor? arg dummy-var #:env (cons (cons dummy-var expected-ty) env))))))))

  ;; Given a pattern of form
  ;; (C1 (C2 (C3 a1) a2) a3)
  ;; produces a flat map
  ;; (#f #t #f)
  ;; which denotes the position in which new temporaries should be generated
  (define (generate-tmp-map pattern)
    (let ([pattern-as-list (syntax->list pattern)])
      (if (false? pattern-as-list)
          ;; TODO PR103: Odd that in this case we return a list, which suggest
          ;; the input was a valid pattern, but it wasn't?
          (list #f)
          (map (compose list? syntax->datum) pattern-as-list))))

  ;; Given a head pattern, find all the inner variables and create new temporaries.
  ;; If a temporary has already been generated, then just use that instead.
  ;; Return the updated pattern and body with substitutions performed.
  (define (generate-fresh-arguments head-patterns bodies tmp-map-with-ids match-var env)
    (let* ([head-pattern-lists (map syntax->list head-patterns)]
           ; hack: we can rely on the fact that pattern variable paths are always appended to the end
           [head-pattern-list-template (first head-pattern-lists)])
      (if (not (list? head-pattern-list-template))
          ; trivial case: no arguments, so return head pattern and body as is
          (cons head-patterns bodies)
          ; otherwise, we need to replace all pattern variables
          (let* ([arg-list (rest head-pattern-list-template)]
                 [fresh-arg-map (cons (first tmp-map-with-ids)
                                      (for/list ([arg arg-list]
                                                 [t (rest tmp-map-with-ids)]
                                                 [idx (in-naturals)])
                                        (or t (and (is-arg-pattern-variable? (first head-pattern-list-template) match-var arg-list idx env)
                                                   (syntax-property (generate-temporary arg) 'is-pattern-variable? #t)))))]
                 ; update the patterns
                 [new-head-patterns (for/list ([head-pattern-list head-pattern-lists]
                                               [idx (in-naturals)])
                                      ; we can have a mix of (s x) and x if we have pattern variables
                                      (if head-pattern-list
                                          #`#,(for/list ([f fresh-arg-map]
                                                         [p head-pattern-list])
                                                (or f p))
                                          (list-ref head-patterns idx)))]
                 ; replace all occurrences in the bodies
                 [new-bodies (map (lambda (head-pattern-list body)
                                    (if head-pattern-list
                                        (foldr (lambda (arg-freshness-pair rsf)
                                                 (if (cdr arg-freshness-pair)
                                                     (subst (cdr arg-freshness-pair)
                                                            (car arg-freshness-pair)
                                                            rsf
                                                            (lambda (a b)
                                                              (and (identifier? a)
                                                                   (identifier? b)
                                                                   (bound-identifier=? a b))))
                                                     rsf))
                                               body
                                               (map cons head-pattern-list fresh-arg-map))
                                        body))
                                  head-pattern-lists
                                  bodies)])
            (cons new-head-patterns new-bodies)))))

  ;; Given two C-groups, merge the data together
  (define (merge-c-groups old-data new-data #:allow-merge-pattern-variable? [allow-merge-pattern-variable? #f])
    (let* ([old-temps (C-group-temporaries-map old-data)]
           [new-temps (C-group-temporaries-map new-data)]
           ; make sure that the two lists are the same length by augmenting both
           [missing-len-new (max 0 (- (length old-temps) (length new-temps)))]
           [missing-len-old (max 0 (- (length new-temps) (length old-temps)))]
           [old-temps-augmented (append old-temps (build-list missing-len-old (lambda (n) #f)))]
           [tmp-map-augmented (append new-temps (build-list missing-len-new (lambda (n) #f)))]
           ; in general, we want to generate the maximum number of temporaries, so we perform
           ; a logical OR operation on the two temporaries maps
           [new-map (for/list ([old-tmp old-temps-augmented]
                               [new-tmp tmp-map-augmented])
                      (or old-tmp new-tmp))]
           ; in some particular edge cases, if we propagate information along a
           ; branch where we have generated new temporaries it happens that the rows will have
           ; mismatched lengths; we resolve this by adding a new pattern variable pattern to
           ; balance it out
           [old-sub-matrix (C-group-pattern-sub-matrix old-data)]
           [new-sub-matrix (C-group-pattern-sub-matrix new-data)]
           [new-sub-matrix-augmented (if (and (not (empty? old-sub-matrix))
                                              (not (empty? new-sub-matrix))
                                              (> (length (first old-sub-matrix))
                                                 (length (first new-sub-matrix))))
                                         ; TODO PR103: Can we use fresh here instead?
                                         (let ([tmp (generate-temporary (first (first old-sub-matrix)))])
                                           (map (lambda (matrix-row) (cons tmp matrix-row)) new-sub-matrix))
                                         new-sub-matrix)]
           ; sanity check: if one of these are pattern variables, the other should be too!
           [group-is-pattern-variable? (begin (and (not allow-merge-pattern-variable?)
                                                   (not (equal? (C-group-is-pattern-variable? old-data)
                                                                (C-group-is-pattern-variable? new-data)))
                                                   (raise (exn
                                                           (format "Expected merging groups to both be pattern variables or neither:\nGroup 1: ~a\nGroup 2: ~a\n"
                                                                   old-data
                                                                   new-data)
                                                           (current-continuation-marks))))
                                              (C-group-is-pattern-variable? old-data))])
      (C-group (append (C-group-head-patterns old-data) (C-group-head-patterns new-data))
               (append old-sub-matrix new-sub-matrix-augmented)
               (append (C-group-bodies old-data) (C-group-bodies new-data))
               new-map
               group-is-pattern-variable?
               (min (C-group-sort-order old-data) (C-group-sort-order new-data)))))

  ;; Returns a list of new patterns to be generated given the temporaries map.
  ;; Example:
  ;; (C1 a1 a2 (C2 a3 a4)) (#f #t #f #t)
  ;; produces
  ;; (#f a1 #f (C2 a3 a4))
  ;; which is filtered to
  ;; (a1 (C2 a3 a4))
  ;;
  ;; Note from the above that since our data is merged, it may be the case that
  ;; there is no nested data at an index marked as requiring a new temporary
  ;; since that may have been a result of a different iteration.
  (define (generate-tmp-patterns head-pattern tmp-map-with-ids)
    (filter (compose not false?)
            (for/list ([tmp tmp-map-with-ids]
                       [sub-pattern (or (syntax->list head-pattern) empty)])
              ; if we have a tmp, then add the patterns for it
              (and (not (false? tmp)) sub-pattern))))

  ;; Given an environment and a set of temporaries, infers the types of the temporaries
  ;; by pulling constructor context information
  (define (extend-env-with-tmps env head-pattern tmp-map-with-ids match-var)
    (let ([head-pattern-as-list (syntax->list head-pattern)])
      (if (false? head-pattern-as-list)
          env
          (let* ([constructor-id (first head-pattern-as-list)]
                 [metadata (get-constructor constructor-id match-var #:env env)]
                 ;; TODO PR103: All these ands could be short-circuited. If
                 ;; get-constructor fails, we could just return env.
                 ;; However, if it fails, it looks like something else has gone
                 ;; wrong.
                 [arg-binding-types (and metadata (map (compose second syntax->list) (second metadata)))]
                 [type-parameters (and metadata (third metadata))]
                 [match-var-type-for-env (and metadata (syntax->list (fourth metadata)))]
                 [match-var-type-values (and match-var-type-for-env
                                             (> (length match-var-type-for-env) 2)
                                             (rest (rest match-var-type-for-env)))]
                 [match-var-type-bindings (and match-var-type-values (map cons type-parameters match-var-type-values))]
                 [new-arg-binding-types (and arg-binding-types
                                             (append (or match-var-type-values empty)
                                                     (for/list ([ty arg-binding-types])
                                                       (if match-var-type-bindings
                                                           (subst-bindings ty match-var-type-bindings
                                                                           #:equality? (lambda (a b) (equal? (syntax->datum a)
                                                                                                             (syntax->datum b))))
                                                           ty))))])
            (append (reverse
                     (filter
                      (compose not false?)
                      (for/list ([ctype (or new-arg-binding-types '())]
                                 [tmp-id (if (empty? tmp-map-with-ids)
                                             empty
                                             (rest tmp-map-with-ids))])
                        (and tmp-id (cons tmp-id ctype)))))
                    env)))))

  ;; Returns a match object
  (define (create-pattern-tree-match-helper match-vars match-pattern pattern-sub-matrix bodies env)
    (pt-match match-pattern
              (if (empty? (first pattern-sub-matrix))
                  (pt-body (first bodies))
                  (create-pattern-tree-decl-helper match-vars pattern-sub-matrix bodies env))))

  ;; Generic fold over the pattern tree data structure; procs occur on decls (associated matches can
  ;; be trivially retrieved by the `matches` property, see usage below in definition of total?)
  ;; Bottom-up traversal.
  (define (fold-pt proc init d #:context [context empty])
    (proc d context (foldl (lambda (m i) (fold-pt-match proc m i #:context (cons d context)))
                           init
                           (pt-decl-matches d))))

  ;; Mutual ref case for matches
  (define (fold-pt-match proc match rsf #:context [context empty])
    (if (pt-body? (pt-match-decl-or-body match))
        rsf
        (fold-pt proc rsf (pt-match-decl-or-body match) #:context (cons match context))))

  ;; Equality check
  (define (pt-equal? n1 n2 #:raise-exn? [raise-exn? #t])
    (let ([res (and (equal? (syntax->datum (pt-decl-match-var n1))
                            (syntax->datum (pt-decl-match-var n2)))
                    (= (length (pt-decl-matches n1))
                       (length (pt-decl-matches n2)))
                    (for/and ([m1 (pt-decl-matches n1)]
                              [m2 (pt-decl-matches n2)])
                      (pt-match-equal? m1 m2 #:raise-exn? raise-exn?)))])
      (begin (and raise-exn? (not res)
                  (raise (exn (string-append "Failed at:\nn1:\n"
                                             (pretty-format n1)
                                             "\nn2:\n"
                                             (pretty-format n2))
                              (current-continuation-marks))))
             res)))

  (define (pt-match-equal? m1 m2 #:raise-exn? [raise-exn? #t])
    (let ([res (and (equal? (syntax->datum (pt-match-pattern m1))
                            (syntax->datum (pt-match-pattern m2)))
                    (or (and (pt-body? (pt-match-decl-or-body m1))
                             (pt-body? (pt-match-decl-or-body m2))
                             (equal? (syntax->datum (pt-body-value (pt-match-decl-or-body m1)))
                                     (syntax->datum (pt-body-value (pt-match-decl-or-body m2)))))
                        (and (pt-decl? (pt-match-decl-or-body m1))
                             (pt-decl? (pt-match-decl-or-body m2))
                             (pt-equal? (pt-match-decl-or-body m1) (pt-match-decl-or-body m2) #:raise-exn? raise-exn?))))])
      (begin (and raise-exn? (not res)
                  (raise (exn (string-append "Failed at:\nm1:\n"
                                             (pretty-format m1)
                                             "\nm2:\n"
                                             (pretty-format m2))
                              (current-continuation-marks))))
             res)))

  ;; Alternative approach to pattern matching in Racket using the pattern tree structure.
  (define (match stx-args pt #:bindings [bindings empty] #:temp-bindings [temp-bindings empty])
    (let* ([current-stx-arg (if (empty? stx-args)
                                (raise (exn "Expected at least one argument for match" (current-continuation-marks)))
                                (first stx-args))]
           [is-temp? (not (syntax-property (pt-decl-match-var pt) 'is-pos-arg?))]
           [next-matches (filter (compose not false?)
                                 (map (lambda (m)
                                        (let ([match-res (pattern-match current-stx-arg m (pt-decl-match-var pt))])
                                          (and match-res
                                               (let ([new-m (first match-res)]
                                                     [new-bindings (second match-res)]
                                                     [new-stx-args (third match-res)])
                                                 (if is-temp?
                                                     (list new-m bindings (append (reverse new-bindings) temp-bindings) new-stx-args)
                                                     (list new-m (append new-bindings (merge-temp-bindings bindings temp-bindings)) empty new-stx-args))))))
                                      (pt-decl-matches pt)))])
      (and (not (empty? next-matches))
           (for/or ([r next-matches])
             (let* ([m (first r)]
                    [new-bindings (second r)]
                    [temp-bindings (third r)]
                    [new-stx-args (fourth r)])
               (if (pt-body? (pt-match-decl-or-body m))
                   (subst-bindings (pt-body-value (pt-match-decl-or-body m)) (merge-temp-bindings bindings new-bindings))
                   (match (append new-stx-args (rest stx-args)) (pt-match-decl-or-body m) #:bindings new-bindings #:temp-bindings temp-bindings)))))))

  (define (merge-temp-bindings bindings temp-bindings)
    (if (empty? temp-bindings)
        bindings
        (if (empty? bindings)
            temp-bindings
            (append bindings temp-bindings (list (first bindings))))))

  (define (subst-bindings body bindings #:equality? [equality? (lambda (a b)
                                                                 (and (identifier? a)
                                                                      (identifier? b)
                                                                      (bound-identifier=? a b)))])
    ; perform substitutions from innermost to outermost scopes
    (foldr (lambda (binding rsf)
             (subst (cdr binding)
                    (car binding)
                    rsf
                    equality?))
           body bindings))

  (define (pattern-match stx m match-var)
    (and
     (not (false? stx))
     (if (syntax-property (pt-match-pattern m) 'is-pattern-variable?)
         (list m (list (cons match-var stx)) empty)
         (and (structural-match? stx (pt-match-pattern m))
              (let* ([stx-list (syntax->list stx)]
                     [pattern-list (syntax->list (pt-match-pattern m))]
                     [new-bindings (if (list? stx-list)
                                       (cons
                                        (cons match-var stx)
                                        (for/list ([binding (filter (lambda (p) (syntax-property (car p) 'is-pattern-variable?))
                                                                    (map cons (rest pattern-list) (rest stx-list)))])
                                          binding))
                                       (list (cons match-var stx)))]
                     ; note: temporaries are only generated for nested arguments; ie. must not be nullary constructor
                     [new-stx-args (if (list? stx-list)
                                       (for/list ([temp-pair (filter (lambda (p) (syntax-property (car p) 'is-temp?))
                                                                     (map cons (rest pattern-list) (rest stx-list)))])
                                         (cdr temp-pair))
                                       empty)])
                (list m new-bindings new-stx-args))))))

;; TODO PR103: These look like they should be in the reflection lib...
  ;; In practice, it doesn't matter if we label a variable as a non-constructor
  ;; when it is, in fact, bound as a constructor elsewhere. For instance, if we
  ;; see the variable `s` for a pattern match on Nat, we simply say that it's a
  ;; non-constructor given that structurally, `s` does not match the only other
  ;; zero-arg constructor `z`. We can defer semantic errors until later phases!
  (define (is-constructor? stx match-var #:env [env '()])
    (let* ([metadata (get-constructors-metadata match-var #:env env)]
           [constructors (and metadata (first metadata))])
      (and (list? constructors)
           ;; TODO PR103: This length check should be unnecessary, since for/or
           ;; should do the right thing on empty lists.
           ;; TODO: Should be a better way to decide whether something is a
           ;; constructor... syntax-property?
           (> (length constructors) 0)
           (for/or ([c constructors])
             (and (not (syntax->list c))
                  (free-identifier=? c stx))))))

  ;; Given a syntax object, try to get the corresponding constructor
  (define (get-constructor stx match-var #:env [env '()])
    (let* ([metadata (get-constructors-metadata match-var #:env env)]
           [constructors (and metadata (first metadata))]
           [constructor-arg-bindings (and metadata (second metadata))]
           [constructor-ty-params (and metadata (third metadata))]
           [type-for-constructor (and metadata (fourth metadata))])
      (and (list? constructors)
           ;; TODO PR103: length check should be unnecessary.
           (> (length constructors) 0)
           (for/or ([c constructors]
                    [binding constructor-arg-bindings])
             ; we don't actually have the constructor yet, so we can just structurally check equality with equal?
             (and (or (equal? (syntax->datum c) (syntax->datum stx))
                      (and (syntax->list c) (equal? (syntax->datum (first (syntax->list c))) (syntax->datum stx))))
                  (list c (syntax->list binding) constructor-ty-params type-for-constructor))))))

  ;; Returns the type of a variable in the current environment context
  ;; or false otherwise
  (define (get-typeof match-var #:env [env '()])
    ; note: if the environment is empty then it'll probably error out; assumption then
    ; is that this was done on purpose so we don't print the error and if you're seeing
    ; unbound id errors otherwise, it's likely that the constructors are not being called
    ; properly, e.g. (s a b c) will leave b and c as undefined
    (with-handlers (#;[exn:fail? (lambda (e) (begin (and (not (empty? env))
                                                       (printf "Failed to determine type of ~a\nERROR: ~a\n" match-var e))
                                                  #f))])
      (curnel-type-infer match-var #:local-env env)))

  ;; Given a match variable with an optional environment, returns
  ;; the set of constructors for the corresponding type and associated metadata
  (define (get-constructors-metadata match-var #:env [env '()])
    ;; TODO PR103: Should never use syntax-property ': directly.
    (let* ([match-var-type (or (syntax-property match-var ':)
                               (get-typeof match-var #:env env))])
      ; NOTE: if we don't have the 'constructors property attached, it's likely that
      ; the module for the type definition wasn't imported
      (and match-var-type (syntax-property match-var-type 'constructors) (syntax-property match-var-type 'constructors-env)
           (list (syntax-property match-var-type 'constructors)
                 (syntax-property match-var-type 'constructors-env)
                 (syntax-property match-var-type 'type-parameters)
                 match-var-type)))))

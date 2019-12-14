#lang s-exp "../main.rkt"

(provide (for-syntax (all-defined-out)))

(require (for-syntax racket/bool
                     racket/list
                     racket/pretty
                     racket/string)
         (only-in turnstile+/base
                  subst))

;; Conceptually, we can consider the data structure defined in this module
;; as a prefix tree for Racket patterns. By representing pattern matches in
;; this way, we can determine totality and produce eliminator-style programs.

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
;; C-GROUP: a constructor group. Essentially, it is used as a means to aggregate data to
;;   be displayed and the remaining match information for a specific constructor match case.
;; C-HASH: a hash values are C-groups.
;; HEAD PATTERN: the first pattern in a pattern row.
;; MATCH VARIABLE: positional arguments that are to be bound during the matching process.
;;   The number of these correspond to the number of patterns in a pattern list. These can
;;   also be generated dynamically to flatten complex patterns.
;; MATCH PATTERN: the specific pattern that a match variable should be bound to. Note that
;;   Unbound match patterns can occur when new temporaries are generated, and we treat
;;   these as a special case in the matcher.
;; PATTERN MATRIX: we interpret the input Racket match cases as a matrix:
;;   e.g. ([a b => A] [c d => B]) can be viewed as a 2x2 matrix leading to 2 match bodies.
;; PATTERN COLUMN: a list of patterns at the nth position in their match case, which also
;;   corresponds to the nth match variable. To create the tree, we process pattern columns
;;   from left to right.
;; PATTERN ROW: a list of patterns, this corresponds to the lefthand side of a single input
;;   match case row.
;; PATTERN SUB-MATRIX: a subset of the input pattern matrix.
;;  e.g. ([a b => A] [c d => B]), after generating matches for the first match variable
;;  we still need to process the remaining sub-matrix ([b => A] [d => B])
;; PATTERN TREE: a new representation of Racket's match case as an aggregated decision tree.
;; PATTERN VARIABLE: a variable representing any pattern. If these are provided within
;;   match cases, then we eliminate the pattern variable and distribute the corresponding
;;   match bodies to all other match cases at the same level.
;;   It is important to be able to distinguish between pattern variables and constructors;
;;   e.g. [z => A] and [a => A] mean different things; the former matches zero only while
;;   the latter matches anything.
;; TEMPORARY: a newly generated identifier to reduce pattern complexity.
;;   e.g. (s (s x)) can be re-written as (s temp1) where temp1 is a new match variable
;;   with a match pattern (s x). Note: in our representation, we explicitly choose to
;;   allow the reference to temp1 above to be unbound; this means that the matching
;;   function must explicitly process temporaries first whenever they are used.

(begin-for-syntax
  ;; Pattern tree structures; see NESTED grammar above.
  (struct pt-decl (match-var matches) #:transparent)
  (struct pt-match (pattern decl-or-body) #:transparent)
  (struct pt-body (value) #:transparent)

  ;; C-group; represents match data for a constructor and the associated pattern sub-matrix
  (struct C-group (head-patterns pattern-sub-matrix bodies temporaries-map is-pattern-variable? sort-order) #:transparent)

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
                       (= (length pattern-row)
                          (length (attribute match-vars))))
       "expected all match cases to have same number of patterns as number of matching variables"
       #:fail-unless (not (zero? (length (attribute match-vars))))
       "expected at least one matching variable"
       (create-pattern-tree-decl-helper (map (lambda (mv) (syntax-property mv 'is-pos-arg? #t)) ; hack: we can keep track of which
                                             (attribute match-vars))                            ; match vars were not generated
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
  ;; Observe that the bindings for the new temporaries are reversed; this is addressed
  ;; in the matching function.
  (define (create-pattern-tree-decl-helper match-vars pattern-matrix bodies env)
    (let* (; create a hash to store results for the leading pattern column
           [C-hash (make-hash)]
           [current-match-var (first match-vars)]
           ; for each match case, process the first pattern and store the
           ; resulting C-group into a hash indexed by constructor or pattern variable
           [merged-entries (begin (for ([head-pattern (map first pattern-matrix)]
                                        [remaining-patterns (map rest pattern-matrix)]
                                        [body bodies]
                                        [idx (in-naturals)])
                                    (process-pattern current-match-var
                                                     head-pattern
                                                     remaining-patterns
                                                     body idx C-hash env))
                                  (hash->list C-hash))]
           ; for deterministic results, sort the entries by order of first occurrence in the input list;
           ; note that an entry is the tuple (unique-key, C-group)
           [sorted-entries (sort merged-entries < #:key (lambda (e) (C-group-sort-order (cdr e))))]
           ; if a pattern variable is used, then the match cases for it need to be distributed among
           ; all other potential match paths
           [entries (elim-pattern-vars sorted-entries current-match-var env)]
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
                                 [tmp-map-with-ids (map (lambda (t) (and t (syntax-property (generate-temporary 'temp) 'is-temp? #t)))
                                                        (C-group-temporaries-map group))]
                                 ; to ensure that we don't erroneously shadow any bindings, we need to generate temporaries for
                                 ; inner arguments too; (s x) -> (s x1)
                                 [fresh-result (generate-fresh-arguments (C-group-head-patterns group) (C-group-bodies group) tmp-map-with-ids current-match-var env)]
                                 [fresh-head-patterns (car fresh-result)]
                                 [fresh-bodies (cdr fresh-result)]
                                 ; for the match pattern, just fetch anything that's not a pattern variable
                                 [match-pat (first fresh-head-patterns)]
                                 ; for each of the remaining patterns, we may need to add temporary matches to them.
                                 ; following the example above: temp1 matches against (s a) and temp2 matches against (s b)
                                 [pattern-sub-matrix (for/list ([pattern-row (C-group-pattern-sub-matrix group)]
                                                                [head-pattern (C-group-head-patterns group)])
                                                       (append (generate-tmp-patterns head-pattern tmp-map-with-ids)
                                                               pattern-row))]
                                 ; after creating our new temporaries, we should also associate them with types
                                 ; based on proper inference
                                 [extended-env (extend-env-with-tmps
                                                env
                                                (first (C-group-head-patterns group))
                                                tmp-map-with-ids
                                                current-match-var)]
                                 ; hack: attach the temporary type based on the value we've assigned to it in the environment
                                 [tmp-map-with-ids-typed (map (lambda (t) (and t (syntax-property t ': (get-typeof t #:env extended-env))))
                                                              tmp-map-with-ids)]
                                 [new-match-vars (append (filter (compose not false?) tmp-map-with-ids-typed) (rest match-vars))])
                            (create-pattern-tree-match-helper
                             new-match-vars
                             ; it may make our lives easier to keep track of the property on the match pattern itself
                             (syntax-property match-pat 'is-pattern-variable? (C-group-is-pattern-variable? group))
                             pattern-sub-matrix
                             fresh-bodies
                             extended-env))))])
      pt))

  ;; For the current match variable and the head pattern for a particular pattern row, either creates a new
  ;; C-group entry within the constructor hash or merges the remaining patterns to form a new pattern sub-matrix.
  (define (process-pattern match-var head-pattern remaining-patterns body idx C-hash env)
    ; for each head pattern, first check to see if it matches existing patterns stored in the constructor hash;
    ; if not, create a new key using the head pattern
    ; note: we do this because key-equal? uses free-identifier=? which cannot be encoded with hashing
    (let* ([key (or (for/or ([entry (hash->list C-hash)])
                      ; check if there is a key that equals the current one (based on the pattern and context)
                      (and (key-equal? head-pattern (car entry) match-var #:env env) (car entry)))
                    ; otherwise, just use the pattern itself as the key
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
    (let ([k1-list (syntax->list k1)]
          [k2-list (syntax->list k2)])
      (and (equal? (list? k1-list)
                   (list? k2-list))
           (or
            ; case: both keys are constructors and match
            (if (list? k1-list)
                (and (= (length k1-list) (length k2-list))
                     (free-identifier=? (first k1-list) (first k2-list)))
                (free-identifier=? k1 k2))
            ; case: both keys represent pattern variables
            (and (is-pattern-variable? k1 match-var env)
                 (is-pattern-variable? k2 match-var env))))))

  ;; Returns true if a pattern is a pattern variable.
  ;; Assumption: if a variable doesn't have any arguments and is not a known constructor
  ;; for the type then it must be a wildcard variable
  (define (is-pattern-variable? head-pat match-var env)
    (and (not (list? (syntax->list head-pat)))
         (not (is-constructor? head-pat match-var #:env env))))

  ;; Given a pattern of form
  ;; (C1 (C2 (C3 a1) a2) a3)
  ;; produces a flat map
  ;; (#f #t #f)
  ;; which denotes the position in which new temporaries should be generated
  (define (generate-tmp-map pattern)
    (let ([pattern-as-list (syntax->list pattern)])
      (if (false? pattern-as-list)
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
          (let* ([fresh-arg-map (cons (first tmp-map-with-ids)
                                      (for/list ([arg (rest head-pattern-list-template)]
                                                 [t (rest tmp-map-with-ids)])
                                        (or t (and (is-pattern-variable? arg match-var env)
                                                   (generate-temporary arg)))))]
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
  
  ;; Given a set of entries, look for the presence of pattern variables and propagate them into
  ;; the sub-matrix of each adjacent entry in the same pattern column
  (define (elim-pattern-vars entries match-var env)
    ; assumption: pattern variables are merged properly prior to this step, so we should only
    ; be able to find at most one wildcard entry
    (let* ([pattern-var-entry (for/or ([entry entries])
                                (and (C-group-is-pattern-variable? (cdr entry)) entry))]
           [remaining-entries (filter (lambda (e) (not (equal? e pattern-var-entry))) entries)])
      (if (and pattern-var-entry (not (empty? remaining-entries)))
          (append (for/list ([entry remaining-entries])
                    (cons (car entry) (merge-c-groups (cdr entry) (cdr pattern-var-entry) #:allow-merge-pattern-variable? #t)))
                  (list pattern-var-entry))
          entries)))

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
                 [constructor-arg-types (get-constructor constructor-id match-var #:env env)]
                 [constructor-env (and constructor-arg-types (syntax->list (cdr constructor-arg-types)))]
                 [constructor-env-types (and constructor-env (map (compose second syntax->list) constructor-env))])
            (append (reverse
                     (filter
                      (compose not false?)
                      (for/list ([ctype (or constructor-env-types '())]
                                 [tmp-id (if (empty? tmp-map-with-ids) empty (rest tmp-map-with-ids))])
                        (and tmp-id (cons tmp-id ctype)))))
                    env)))))
  
  ;; In practice, it doesn't matter if we label a variable as a non-constructor
  ;; when it is, in fact, bound as a constructor elsewhere. For instance, if we
  ;; see the variable `s` for a pattern match on Nat, we simply say that it's a
  ;; non-constructor given that structurally, `s` does not match the only other
  ;; zero-arg constructor `z`. We can defer semantic errors until later phases!
  (define (is-constructor? stx match-var #:env [env '()])
    (let* ([constructors-pair (get-constructors-for-match-var match-var #:env env)]
           [constructors (and constructors-pair (car constructors-pair))])
      (and (list? constructors)
           (> (length constructors) 0)
           (for/or ([c constructors])
             (and (not (syntax->list c))
                  (free-identifier=? c stx))))))

  ;; Given a syntax object, try to get a constructor belonging to the type of a
  ;; match variable.
  (define (get-constructor stx match-var #:env [env '()])
    (let* ([constructors-pair (get-constructors-for-match-var match-var #:env env)]
           [constructors (and constructors-pair (car constructors-pair))]
           [constructors-env (and constructors-pair (cdr constructors-pair))])
      (and (list? constructors)
           (> (length constructors) 0)
           (for/or ([c constructors]
                    [c-env constructors-env])
             ; try to find a matching constructor via free-identifier=?
             (if (not (syntax->list c))
                 (and (free-identifier=? c stx) c)
                 (and (free-identifier=? (first (syntax->list c)) stx) (cons c c-env)))))))

  ;; Returns the type of a variable in the current environment context
  ;; or false otherwise
  (define (get-typeof match-var #:env [env '()])
    (with-handlers ([exn:fail? (lambda (e) #f)])
      (turnstile-infer match-var #:local-env env)))
  
  ;; Given a match variable (no nesting) with an optional environment, returns
  ;; the set of constructors for the corresponding type
  (define (get-constructors-for-match-var match-var #:env [env '()])
    (let* ([match-var-type (or (syntax-property match-var ':)
                               (get-typeof match-var #:env env))])
      ; IMPORTANT: if we don't have the 'constructors property attached, it's likely that
      ; the module for the type definition wasn't imported
      (and match-var-type (cons (syntax->list (syntax-property match-var-type 'constructors))
                                (syntax->list (syntax-property match-var-type 'constructors-env))))))

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

  (define (match pt)
    ; TODO
    pt))
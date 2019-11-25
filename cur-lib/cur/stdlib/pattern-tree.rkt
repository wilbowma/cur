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
;;

(begin-for-syntax
  ;; racket representations of the NESTED grammar above
  (struct nested (patvar matches) #:transparent)
  (struct nested-match (pat nested-or-body is-wildcard?) #:transparent)
  (struct nested-body (body) #:transparent)

  ;; For an input of form
  ;; ((n m)
  ;;  ([z z => A]
  ;;   [z (s x) => B])
  ;;
  ;; We create the following resulting tree structure:
  ;; (nested n (list (nested-match z (nested m (list (nested-match z A)
  ;;                                                 (nested-match (s x) B))))
  (define (create-nested-pattern stx #:env [env '()])
    (syntax-parse stx
      [((pat-vars:id ...) ((pat ... (~datum =>) bodies) ...))
       #:fail-unless (for/and ([pat (attribute pat)])
                       (= (length pat)
                          (length (attribute pat-vars))))
       "expected pattern cases to have same length as number of matching pattern variables"
       #:fail-unless (not (zero? (length (attribute pat-vars))))
       "expected at least one pattern variable"
       (create-nested-pattern-helper-nested (attribute pat-vars)
                                            (attribute pat)
                                            (attribute bodies)
                                            env)]))

  ;; C-group represents the aggregated data for a given key in the constructor hash
  (struct C-group (head-pats remaining-pats bodies temporaries-map wildcard-tmp sort-order) #:transparent)

  ;; Create prefix tree by keying on the constructor type of the first pattern.
  ;; If the current pattern is not a constructor, then treat it as a wildcard.
  ;;
  ;; Step-by-step example (conceptual):
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
  (define (create-nested-pattern-helper-nested pat-vars pats-list bodies env)
    (let* ([C-hash (make-hash)]
           [merged-entries (begin (for ([head-pat (map first pats-list)]
                                        [remaining-pats (map rest pats-list)]
                                        [body bodies]
                                        [idx (in-naturals)])
                                    (update-entries-with-pattern (first pat-vars) head-pat remaining-pats body idx C-hash env))
                                  (hash->list C-hash))]
           [sorted-entries (sort merged-entries < #:key (lambda (map-entry) (C-group-sort-order (cdr map-entry))))]
           ; TODO: do we need to merge wildcard paths into the others, or can we simply use the annotated information to our
           ; advantage?
           #;[merged-res (merge-wildcard-entries sorted-entries (first pat-vars) env)]
           [wildcard-tmp #f #;(car merged-res)]
           [new-env env #;(if wildcard-tmp
                        (cons (cons wildcard-tmp (get-typeof (first pat-vars) #:env env)) env)
                        env)]
           #;[augmented-entries (cdr merged-res)])
      (nested (or wildcard-tmp (first pat-vars))
              (for/list ([entry sorted-entries])
                (let* ([group (cdr entry)]
                       [key (car entry)]
                       [tmp-map-with-ids (map (lambda (t) (and t (generate-temporary 'temp))) (C-group-temporaries-map group))]
                       [new-pats (for/list ([remaining-pats-single (C-group-remaining-pats group)]
                                            [head-pat (C-group-head-pats group)])
                                   (append (generate-remaining-pat-for-tmp head-pat tmp-map-with-ids) remaining-pats-single))]
                       [match-pat (generate-match-pat group tmp-map-with-ids)]
                       [is-wildcard? (and (not (list? (syntax->list match-pat)))
                                          (not (is-constructor? match-pat (first pat-vars) #:env new-env)))])
                  (create-nested-pattern-helper-match
                   (append (filter (compose not false?) tmp-map-with-ids) (rest pat-vars))
                   match-pat
                   ; at this point we know where all the temporaries are, so we can reference
                   ; the map and artificially insert matches on the values at those indices
                   new-pats
                   (C-group-bodies group)
                   is-wildcard?
                   (extend-env-with-tmps new-env (first (C-group-head-pats group)) tmp-map-with-ids (first pat-vars))))))))

  (define (is-wildcard? head-pat pat-var env)
    (and (not (list? (syntax->list head-pat)))
         (not (is-constructor? head-pat pat-var #:env env))))

  ;; TODO: figure out if we actually need this, the ideal case is we don't manipulate the tree
  ;; struct any further than annotating wildcards, and traverse through this in the totality check
  ;; concurrently. However, this would entail also designing a top-down traversal method, unlike
  ;; the current bottom-up fold.
  (define (merge-wildcard-entries entries pat-var env)
    (let* ([wildcard-map (map (compose not false? C-group-wildcard-tmp cdr) entries)]
           [wildcard-entry (for/or ([w wildcard-map]
                                    [idx (in-naturals)])
                             (and w (list-ref entries idx)))])
      (if (and wildcard-entry (> (length entries) 1))
          (cons (C-group-wildcard-tmp (cdr wildcard-entry))
                (for/list ([w wildcard-map]
                           [idx (in-naturals)])
                  (let ([entry (list-ref entries idx)])
                    (if w
                        entry
                        ; hack: important that we append the wildcard data, so that original cases take precedence
                        (cons (car entry) (merge-c-groups (cdr entry) (cdr wildcard-entry)))))))
          (cons #f entries))))

  (define (merge-c-groups old-data new-data)
    (let* ([old-temps (C-group-temporaries-map old-data)]
           [new-temps (C-group-temporaries-map new-data)]
           [missing-len-new (max 0 (- (length old-temps) (length new-temps)))]
           [missing-len-old (max 0 (- (length new-temps) (length old-temps)))]
           [old-temps-augmented (append old-temps (build-list missing-len-old (lambda (n) #f)))]
           [tmp-map-augmented (append new-temps (build-list missing-len-new (lambda (n) #f)))]
           [new-map (for/list ([old-tmp old-temps-augmented]
                               [new-tmp tmp-map-augmented])
                      (or old-tmp new-tmp))]
           [old-remaining-pats (C-group-remaining-pats old-data)]
           [new-remaining-pats (C-group-remaining-pats new-data)]
           [new-remaining-pats-augmented (if (and (not (empty? new-remaining-pats))
                                                  (not (empty? old-remaining-pats))
                                                  (> (length (first old-remaining-pats))
                                                     (length (first new-remaining-pats))))
                                             (let ([tmp (generate-temporary)])
                                               (map (lambda (l) (cons tmp l)) new-remaining-pats))
                                             new-remaining-pats)])
      (C-group (append (C-group-head-pats old-data) (C-group-head-pats new-data))
               (append (C-group-remaining-pats old-data) new-remaining-pats-augmented)
               (append (C-group-bodies old-data) (C-group-bodies new-data))
               ; for tmp-map merging, we need to OR the indices
               ; ASSUMPTION: the two lists must be the same length
               ; given that they keyed to the same thing
               new-map
               (C-group-wildcard-tmp old-data)
               (min (C-group-sort-order old-data) (C-group-sort-order new-data)))))

  (define (count-args head-pat)
    (if (list? (syntax->list head-pat))
        (foldr (lambda (p rsf) (if (not (equal? (syntax->datum p) '_)) (add1 rsf) rsf))
               0 (syntax->list head-pat)) 0))
  
  (define (generate-match-pat cgroup tmp-map-with-ids)
    (let* ([template-as-single (first (C-group-head-pats cgroup))]
           [template-as-list (syntax->list (first (sort (C-group-head-pats cgroup) > #:key (lambda (p) (count-args p)))))])
      (if (list? template-as-list)
          #`#,(for/list ([tmp tmp-map-with-ids]
                         [t template-as-list])
                (or tmp t))
          template-as-single)))

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
  (define (generate-remaining-pat-for-tmp head-pat tmp-map-with-ids)
    (filter (compose not false?)
            (for/list ([tmp tmp-map-with-ids]
                       [sub-pat (or (syntax->list head-pat) empty)])
              ; if we have a tmp, then add the patterns for it
              (and (not (false? tmp)) sub-pat))))

  ;; Given a pattern of form
  ;; (C1 (C2 (C3 a1) a2) a3)
  ;; produces a flat map
  ;; (#f #t #f)
  ;; which denotes the position in which new temporaries should be generated
  (define (generate-tmp-map pat)
    (let ([pat-as-list (syntax->list pat)])
      (if (false? pat-as-list)
          (list #f)
          (map (compose list? syntax->datum) pat-as-list))))

  (define (extend-env-with-tmps env pat tmp-map-with-ids pat-var)
    (let ([pat-as-list (syntax->list pat)])
      (if (false? pat-as-list)
          env
          (let* ([pat-id (if (syntax->list pat) (first (syntax->list pat)) pat)]
                 [constructor-arg-types (get-constructor pat-id pat-var #:env env)]
                 [constructor-env (and constructor-arg-types (syntax->list (cdr constructor-arg-types)))]
                 [constructor-env-types (and constructor-env (map (compose second syntax->list) constructor-env))]
                 [b (append (reverse (filter (compose not false?)
                                             (for/list ([ctype (or constructor-env-types '())]
                                                        [tmp-id (if (empty? tmp-map-with-ids) empty (rest tmp-map-with-ids))])
                                               (and tmp-id (cons tmp-id ctype)))))
                            env)])
            (append (reverse (filter (compose not false?)
                                     (for/list ([ctype (or constructor-env-types '())]
                                                [tmp-id (if (empty? tmp-map-with-ids) empty (rest tmp-map-with-ids))])
                                       (and tmp-id (cons tmp-id ctype)))))
                    env)))))

  ;; In practice, it doesn't matter if we label a variable as a non-constructor
  ;; when it is, in fact, bound as a constructor elsewhere. For instance, if we
  ;; see the variable `s` for a pattern match on Nat, we simply say that it's a
  ;; non-constructor given that structurally, `s` does not match the only other
  ;; zero-arg constructor `z`.
  (define (is-constructor? stx pat-var #:env [env '()])
    (let* ([constructors-pair (get-constructors-for-pat-var pat-var #:env env)]
           [constructors (and constructors-pair (car constructors-pair))])
      (and (list? constructors)
           (> (length constructors) 0)
           (for/or ([c constructors])
             (and (not (syntax->list c))
                  (free-identifier=? c stx))))))

  (define (get-constructor stx pat-var #:env [env '()])
    (let* ([constructors-pair (get-constructors-for-pat-var pat-var #:env env)]
           [constructors (and constructors-pair (car constructors-pair))]
           [constructors-env (and constructors-pair (cdr constructors-pair))])
      (and (list? constructors)
           (> (length constructors) 0)
           (for/or ([c constructors]
                    [c-env constructors-env])
             (if (not (syntax->list c))
                 (and (free-identifier=? c stx) c)
                 (and (free-identifier=? (first (syntax->list c)) stx) (cons c c-env)))))))

  (define (get-typeof-literal pat-var #:env [env '()])
    (let* ([ty (get-typeof pat-var #:env env)]
           [ty-list (and ty (syntax->list ty))])
      (and ty-list (second ty-list))))
  
  (define (get-typeof pat-var #:env [env '()])
    (with-handlers ([exn:fail? (lambda (e) (for/or ([e env])
                                             (and (free-identifier=? (car e) pat-var)
                                                  (cdr e))))])
      (turnstile-infer pat-var #:local-env env)))
  
  ;; Given a pattern variable (no nesting) with an optional environment, returns
  ;; the set of constructors for the corresponding type
  (define (get-constructors-for-pat-var pat-var #:env [env '()])
    (let* ([pat-var-type (get-typeof pat-var #:env env)])
      ; if we don't have the 'constructors property attached, it's likely that the module for the
      ; type definition wasn't imported
      (and pat-var-type (cons (syntax->list (syntax-property pat-var-type 'constructors))
                              (syntax->list (syntax-property pat-var-type 'constructors-env))))))

  ;; Equality check between patterns to be used as keys. First check if both
  ;; of the two patterns are pattern variables, in which case we can trivially
  ;; mark the two as equal. Next, check if they're both the same constructors.
  (define (key-equal? k1 k2 pat-var #:env [env '()])
    (let ([k1-list (syntax->list k1)]
          [k2-list (syntax->list k2)])
      (and (equal? (list? k1-list)
                   (list? k2-list))
           (or (and (not (list? k1-list))
                    (not (is-constructor? k1 pat-var #:env env))
                    (not (list? k2-list))
                    (not (is-constructor? k2 pat-var #:env env)))
               (if (list? k1-list)
                   (and (= (length k1-list) (length k2-list))
                        (free-identifier=? (first k1-list) (first k2-list)))
                   (free-identifier=? k1 k2))))))
    
  ;; Updates the constructor hash with a specific path - that is, a combination of
  ;; the pattern variable, the subset of remaining patterns, and a single result body
  (define (update-entries-with-pattern pat-var head-pat remaining-pats body idx C-hash env)
    (let* ([key (or (for/or ([entry (hash->list C-hash)]) ; unhappy side-effect of needing free-identifier=?
                      (and (key-equal? head-pat (car entry) pat-var #:env env) (car entry)))
                    head-pat)]
           [tmp-map (generate-tmp-map head-pat)])
      (if (hash-has-key? C-hash key)
          (let* ([old-data (hash-ref C-hash key)]
                 [old-wildcard-tmp (C-group-wildcard-tmp old-data)]
                 [new-bodies (if old-wildcard-tmp
                                 ; substitute the body using the new temporary representing the wildcard
                                 (list (subst old-wildcard-tmp head-pat body))
                                 (list body))]
                 [new-data (C-group (list head-pat)
                                    (list remaining-pats)
                                    new-bodies
                                    tmp-map
                                    old-wildcard-tmp
                                    idx)])
            ; key exists, so we merge the result
            (hash-set! C-hash key (merge-c-groups old-data new-data)))
          (let* ([wildcard-tmp (and (is-wildcard? head-pat pat-var env)
                                    (generate-temporary head-pat))]
                 [head-pats (if wildcard-tmp
                                (list wildcard-tmp)
                                (list head-pat))]
                 [new-bodies (if wildcard-tmp
                                 (list (subst wildcard-tmp head-pat body))
                                 (list body))]
                 [new-data (C-group head-pats
                                    (list remaining-pats)
                                    new-bodies
                                    tmp-map
                                    wildcard-tmp
                                    idx)])
            (hash-set! C-hash key new-data)))))

  ;; returns a nested-match object
  (define (create-nested-pattern-helper-match pat-vars pat pats-list bodies is-wildcard? env)
    (nested-match pat (if (empty? (first pats-list))
                          (nested-body (first bodies))
                          (create-nested-pattern-helper-nested pat-vars pats-list bodies env))
                  is-wildcard?))

  ;; generic fold over the nested data structure; procs occur on nested (associated matches can
  ;; be trivially retrieved by the `matches` property, see usage below in definition of total?)
  ;; -- apply proc to leaves first, and work upwards --
  (define (fold-nested proc init n #:context [context empty])
    (proc n context (foldl (lambda (m i) (fold-nested-match proc m i #:context (cons n context)))
                           init
                           (nested-matches n))))

  ;; mutual ref case for matches
  (define (fold-nested-match proc match rsf #:context [context empty])
    (if (nested-body? (nested-match-nested-or-body match))
        rsf
        (fold-nested proc rsf (nested-match-nested-or-body match) #:context (cons match context))))
  
  ;; equality check
  (define (nested-equal? n1 n2 #:raise-exn? [raise-exn? #t])
    (let ([res (and (equal? (syntax->datum (nested-patvar n1))
                            (syntax->datum (nested-patvar n2)))
                    (= (length (nested-matches n1))
                       (length (nested-matches n2)))
                    (for/and ([m1 (nested-matches n1)]
                              [m2 (nested-matches n2)])
                      (nested-match-equal? m1 m2 #:raise-exn? raise-exn?)))])
      (begin (and raise-exn? (not res)
                  (raise (exn (string-append "Failed at:\nn1:\n"
                                             (pretty-format n1)
                                             "\nn2:\n"
                                             (pretty-format n2))
                              (current-continuation-marks))))
             res)))

  (define (nested-match-equal? m1 m2 #:raise-exn? [raise-exn? #t])
    (let ([res (and (equal? (syntax->datum (nested-match-pat m1))
                            (syntax->datum (nested-match-pat m2)))
                    (or (and (nested-body? (nested-match-nested-or-body m1))
                             (nested-body? (nested-match-nested-or-body m2))
                             (equal? (syntax->datum (nested-body-body (nested-match-nested-or-body m1)))
                                     (syntax->datum (nested-body-body (nested-match-nested-or-body m2))))
                             (equal? (nested-match-is-wildcard? m1)
                                     (nested-match-is-wildcard? m2)))
                        (and (nested? (nested-match-nested-or-body m1))
                             (nested? (nested-match-nested-or-body m2))
                             (nested-equal? (nested-match-nested-or-body m1) (nested-match-nested-or-body m2) #:raise-exn? raise-exn?))))])
      (begin (and raise-exn? (not res)
                  (raise (exn (string-append "Failed at:\nm1:\n"
                                             (pretty-format m1)
                                             "\nm2:\n"
                                             (pretty-format m2))
                              (current-continuation-marks))))
             res))))
#lang s-exp "../main.rkt"

(provide (for-syntax (all-defined-out)))

(require (for-syntax racket/bool
                     racket/list
                     racket/pretty
                     racket/string))

;; Conceptually, we can consider the data structure defined in this module
;; as a prefix tree for Racket patterns. By representing pattern matches in
;; this way, we can efficiently determine totality and perform chained elimination.

;; GRAMMAR (conversion from INPUT to NESTED)
;; ---------------
;; patvar := <some pattern variable, e.g. x>
;; pat := <any pattern, e.g. (s x)>
;; body := <anything>
;; INPUT := ((listof patvar) (listof (listof pat) body))
;; NESTED := (patvar (listof pat NESTED))
;;           | body
;;

(begin-for-syntax
  ;; racket representations of the NESTED grammar above
  (struct nested (patvar matches) #:transparent)
  (struct nested-match (pat nested-or-body) #:transparent)
  (struct nested-body (body) #:transparent)
  
  ;; given an input of form:
  ;; ((n m)
  ;;  ([z z => A]
  ;;   [z (s x) => B])
  ;;
  ;; returns:
  ;; (nested n (list (nested-match z (nested m (list (nested-match z A)
  ;;                                                 (nested-match (s x) B))))
  (define (create-nested-pattern stx)
    (syntax-parse stx
      [((patvars:id ...) ((pat ... (~datum =>) bodies) ...))
       #:fail-unless (for/and ([pat (attribute pat)])
                       (= (length pat) (length (attribute patvars))))
       "expected pattern cases to have same length as number of matching pattern variables"
       #:fail-unless (not (zero? (length (attribute patvars))))
       "expected at least one pattern variable"
       (create-nested-pattern-helper-nested (attribute patvars) (attribute pat) (attribute bodies))]))

  ;; helper structs for generating the nested pattern tree
  ;; temp-args is used for recursively building up temporaries from complicated patterns  
  (struct temp-args (pat-with-temps temp-indices counter) #:transparent)
  ;; payload represents the data to be aggregated on a key, based on the temp-args
  (struct payload (pat remaining-pat body temp-indices pats min-idx) #:transparent)

  ;; returns a nested object
  ;; create prefix tree by keying on the datum of the first pattern of the match case
  ;; e.g. [a b c => body1] [d e f => body2] -> (list a (list [b c] [e f]) (list body1 body2))
  ;; and then we process each case in individual recursive calls:
  ;; [b c => body1] -> (list b (list [c]) (list body1))
  ;; [c => body1] -> (list c (list []) (list body1))
  ;; [=> body1] DONE, add body1
  ;;
  ;; the same happens for the other yet-to-be-processed branch:
  ;; [e f => body2] -> (list e (list [f]) (list body2))
  ;; ...
  ;; [=> body2] DONE, add body2
  ;;
  ;; note: each of a, b, c, d, e, f are constructors of form (name args ...) or name
  ;;
  ;; now the tricky case is when we have nested constructors:
  ;; [(name1 (name2 arg1)) => body]
  ;; in which case we want to rewrite it first as
  ;; [(name1 temp1) (name2 arg1) => body]
  ;; and ensure that we use the right fresh ID temp1 in the subsequent tree structure
  (define (create-nested-pattern-helper-nested patvars pats-list bodies)
    (nested (first patvars)
            (let* ([pat-hash (make-hash)]
                   [unique-entries
                    (begin
                      ; examine each row of the input - the first pattern of the match, the remaining patterns
                      ; and the resulting body
                      (for ([pat (map first pats-list)]
                            [sub-pat-list (map rest pats-list)]
                            [body bodies]
                            [idx (in-naturals)])
                        (let* ([pat-datum (syntax->datum pat)]
                               ; in general, we can group by the constructor pattern and the number of arguments
                               ; by representing arguments using a literal * - e.g. (s x) -> (s *)
                               [key (if (list? pat-datum)
                                        (cons (first pat-datum)
                                              (map (lambda (e) '*)
                                                   (rest pat-datum)))
                                        (syntax->datum pat))]
                               [pat-as-list (syntax->list pat)]
                               [constructor-args (and (not (or (false? pat-as-list)
                                                               (empty? pat-as-list)))
                                                      (rest pat-as-list))]
                               ; if we have a non-trivial pattern (ie. constructors with arguments), loop through it
                               ; while reconstructing the pattern when encountering temporaries:
                               ; (s (s x)) -> (s temp1)
                               ; if we process a subsequent match, we try to re-use the temporary generated at that
                               ; "slot":
                               ; (s (s (s x))) -> (s temp1)
                               ; while still recording the pattern.
                               ; we also produce a list the length of the number of arguments for the constructor
                               ; denoting which indices use temporaries (a reference to the temporary) and which
                               ; do not (false).
                               ; TODO #1: probably need to generate temporaries for everything, and rewrite the usages
                               ; within the bodies correspondingly
                               ; TODO #2: we probably need to lookup whether or not a pattern variable is a constructor
                               ; or not, if it is then we should generate a new match case for it. e.g. (s z) has a very
                               ; different meaning from (s x)!
                               [t (if (not (false? constructor-args))
                                      (foldl (lambda (v rsf)
                                               ; is this a nested constructor?
                                               (if ((compose list? syntax->datum) v)
                                                   ; check if there is a temp already generated at this index
                                                   (let* ([existing-temp (and (hash-has-key? pat-hash key)
                                                                              (list-ref (payload-temp-indices (hash-ref pat-hash key))
                                                                                        (temp-args-counter rsf)))]
                                                          [sub (if (not (false? existing-temp))
                                                                   existing-temp
                                                                   (generate-temporary 'temp))]) ; TODO: append typing info to temp
                                                     (temp-args (append (temp-args-pat-with-temps rsf) (list sub))
                                                                (append (temp-args-temp-indices rsf) (list sub))
                                                                (add1 (temp-args-counter rsf))))
                                                   (temp-args (append (temp-args-pat-with-temps rsf) (list v))
                                                              (append (temp-args-temp-indices rsf) (list #f))
                                                              (add1 (temp-args-counter rsf)))))
                                             ; fold over constructor args, start pattern with just the constructor
                                             (temp-args (list (first pat-as-list)) empty 0)
                                             constructor-args)
                                      ; if this is a pattern variable, we don't have anything to traverse
                                      (temp-args pat empty -1))]
                               ; build the payload to be aggregated on the current key - this includes the remaining
                               ; match patterns of the row as well as the body; no new patterns are generated for
                               ; the complicated nested constructors at this time but we have a generated temporary map
                               ; to accomplish this later
                               [p (payload #`#,(temp-args-pat-with-temps t)
                                           (list sub-pat-list)
                                           (list body)
                                           (temp-args-temp-indices t)
                                           (list pat)
                                           idx)])
                          ; now we insert the payload into the hash
                          (if (hash-has-key? pat-hash key)
                              (let* ([old-res (hash-ref pat-hash key)]
                                     ; generally prefer names with as many "temps" in them for pattern variables
                                     ; e.g. (s a b) (s temp1 b) might end up with a match on either a or temp1,
                                     ; in which case we prefer temp1
                                     ; TODO: for the non-temporary variables, we should likely rebind with fresh temporaries too
                                     [num-temps (lambda (p) (foldl (lambda (t r) (if (false? t) r (add1 r))) 0 (payload-temp-indices p)))]
                                     [new-name (if (> (num-temps old-res) (num-temps p))
                                                   (payload-pat old-res)
                                                   (payload-pat p))])
                                ; key exists, so we merge the result in; temporary indices should be OR'd on
                                ; so that we can generate the correct branching
                                (hash-set! pat-hash key (payload new-name
                                                                 (append (payload-remaining-pat old-res) (payload-remaining-pat p))
                                                                 (append (payload-body old-res) (payload-body p))
                                                                 (for/list ([old-temp (payload-temp-indices old-res)]
                                                                            [new-temp (payload-temp-indices p)])
                                                                   (or old-temp new-temp))
                                                                 (append (payload-pats old-res) (payload-pats p))
                                                                 (min (payload-min-idx p) (payload-min-idx old-res)))))
                              (hash-set! pat-hash key p))))
                      (hash->list pat-hash))])
              ; iterate over key-value pairs of the map, for each value generate a new pattern match branch each with its
              ; own remaining set of branches and bodies to explore
              ; might be worth it to do extra work to keep things sorted
              (for/list ([ordered-entry (sort unique-entries < #:key (lambda (e) (payload-min-idx (cdr e))))])
                (let ([unique-val (cdr ordered-entry)]
                      [unique-key (car ordered-entry)])
                  (create-nested-pattern-helper-match (append (filter (compose not false?) (payload-temp-indices unique-val)) (rest patvars))
                                                      (payload-pat unique-val)
                                                      ; at this point we know where all the temporaries are, so we can reference
                                                      ; the map and artificially insert matches on the values at those indices
                                                      (for/list ([l (payload-remaining-pat unique-val)]
                                                                 [pat (payload-pats unique-val)])
                                                        (append (filter (compose not false?)
                                                                        (for/list ([t (payload-temp-indices unique-val)]
                                                                                   [p (if (syntax->list pat)
                                                                                          (rest (syntax->list pat))
                                                                                          empty)])
                                                                          (and (not (false? t)) p))) l))
                                                      (payload-body unique-val)))))))

  ;; returns a nested-match object
  (define (create-nested-pattern-helper-match patvars pat pats-list bodies)
    (nested-match pat (if (empty? (first pats-list))
                          (nested-body (first bodies))
                          (create-nested-pattern-helper-nested patvars pats-list bodies))))

  ;; generic fold over the nested data structure; procs occur on nested (associated matches can
  ;; be trivially retrieved by the `matches` property, see usage below in definition of total?)
  ;; -- apply proc to leaves first, and work upwards --
  (define (fold-nested proc init n #:context [context empty])
    (proc n context (foldl (lambda (m i) (fold-nested-match proc m i #:context (append context (list n))))
                           init
                           (nested-matches n))))

  ;; mutual ref case for matches
  (define (fold-nested-match proc match rsf #:context [context empty])
    (if (nested-body? (nested-match-nested-or-body match))
        rsf
        (fold-nested proc rsf (nested-match-nested-or-body match) #:context context)))
  
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
                  (raise (exn (format "Failed at:\nn1:\n~a\nn2:\n~a\n" n1 n2)
                              (current-continuation-marks))))
             res)))

  (define (nested-match-equal? m1 m2 #:raise-exn? [raise-exn? #t])
    (let ([res (and (equal? (syntax->datum (nested-match-pat m1))
                            (syntax->datum (nested-match-pat m2)))
                    (or (and (nested-body? (nested-match-nested-or-body m1))
                             (nested-body? (nested-match-nested-or-body m2))
                             (equal? (syntax->datum (nested-body-body (nested-match-nested-or-body m1)))
                                     (syntax->datum (nested-body-body (nested-match-nested-or-body m2)))))
                        (and (nested? (nested-match-nested-or-body m1))
                             (nested? (nested-match-nested-or-body m2))
                             (nested-equal? (nested-match-nested-or-body m1) (nested-match-nested-or-body m2) #:raise-exn? raise-exn?))))])
      (begin (and raise-exn? (not res)
                  (raise (exn (format "Failed at:\nm1:\n~a\nm2:\n~a\n" m1 m2) (current-continuation-marks))))
             res)))

  ;; for any identifier that's not a type constructor (e.g. s, cons)
  ;; we want to generate fresh temporaries so that we don't introduce
  ;; weird binding issues when we rewrite
  ;;
  ;; TODO: actually test if the substitution works
  (define (subst-bodies bodies old new)
    (for/list ([body bodies])
      (subst-body body old new)))
  
  (define (subst-body body old new)
    (syntax-parse body
      [x:id (if (equal? (syntax->datum old) (syntax->datum #'x)) new #'x)]
      [(x:id rest ...)
       (cons (if (equal? (syntax->datum old) (syntax->datum #'x)) new #'x)
             (subst-body #'(rest ...) old new))]
      [((x:id irest ...) orest ...)
       (cons (if (equal? (syntax->datum old) (syntax->datum #'x)) new #'x)
             (if (zero? (length (attribute irest)))
                 (subst-body #'(orest ...) old new)
                 (subst-body #'((irest ...) orest ...) old new)))]
      [() empty])))


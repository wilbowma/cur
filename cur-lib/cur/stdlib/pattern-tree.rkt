#lang s-exp "../main.rkt"

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

  ;; TODO: for any identifier that's not a type constructor (e.g. s, cons)
  ;; we want to generate fresh temporaries so that we don't introduce
  ;; weird binding issues when we rewrite
  (define (fresh-temporaries pats-list body) #'void)

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
       (create-nested-pattern-helper-nested (attribute patvars) (attribute pat) (attribute bodies))]))

  ;; helper structs for generating the nested pattern tree
  ;; temp-args is used for recursively building up temporaries from complicated patterns  
  (struct temp-args (pat-with-temps temp-indices counter) #:transparent)
  ;; payload represents the data to be aggregated on a key, based on the temp-args
  (struct payload (pat remaining-pat body temp-indices pats) #:transparent)

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
                            [body bodies])
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
                                                                   (generate-temporary 'temp))])
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
                                           (list pat))])
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
                                                                 (append (payload-remaining-pat p) (payload-remaining-pat old-res))
                                                                 (append (payload-body p) (payload-body old-res))
                                                                 (for/list ([old-temp (payload-temp-indices old-res)]
                                                                            [new-temp (payload-temp-indices p)])
                                                                   (if (false? old-temp)
                                                                       new-temp
                                                                       old-temp))
                                                                 (append (payload-pats p) (payload-pats old-res)))))
                              (hash-set! pat-hash key p))))
                      (hash->list pat-hash))])
              ; iterate over key-value pairs of the map, for each value generate a new pattern match branch each with its
              ; own remaining set of branches and bodies to explore
              (for/list ([unique-entry unique-entries])
                (let ([unique-val (cdr unique-entry)]
                      [unique-key (car unique-entry)])
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
  (define (fold-nested proc init n)
    (proc n (foldl (lambda (m i) (fold-nested-match proc m i))
                   init
                   (nested-matches n))))

  ;; mutual ref case for matches
  (define (fold-nested-match proc match rsf)
    (if (nested-body? (nested-match-nested-or-body match))
        rsf
        (fold-nested proc rsf (nested-match-nested-or-body match))))

  ;; matches tokens only; wildcards for input consume an entire token while
  ;; for the matching token we need to ensure that it doesn't match composite
  ;; terms - TODO: is this what we want? also, using * instead of _ since actual
  ;; input may contain _
  (define (token-match tok-input tok-to-match)
    (or (or
         (equal? tok-input '_)
         (and (equal? tok-to-match '_)
              (not (list? tok-input))))
        (equal? tok-input tok-to-match)))

  ;; recursively checks the first element of a pattern, e.g. (s x) and (s _) match.
  ;; both patterns must be either pattern variables or constructors of the same length.
  ;; allow pattern to be wildcard, in which case we trivially return true
  (define (typecase-match pat ty-pat)
    (or (and (not (list? pat))
             (equal? pat '_))
        (and (equal? (list? ty-pat) (list? pat))
             (if (not (list? ty-pat))
                 (token-match pat ty-pat)
                 (and (= (length ty-pat) (length pat))
                      (or (empty? ty-pat)
                          (and (token-match (first pat) (first ty-pat))
                               (typecase-match (rest pat) (rest ty-pat)))))))))

  ;; given a list of patterns associated with a pattern variable and a list of expected
  ;; type cases, returns true if all type cases can be matched
  (define (patvar-is-total? patvar patterns ty-pats)
    (or (empty? ty-pats)
        (and (or (for/or ([pat patterns])
                   (typecase-match pat (first ty-pats)))
                 ; TODO: raise exception instead of returning bool?
                 (begin (printf "Missing case for ~a:\n~a\n" patvar (first ty-pats)) #f))
             (patvar-is-total? patvar patterns (rest ty-pats)))))

  ;; retrieves the case patterns associated with a pattern variable's type
  ;; TODO: actually pull the information over, not just offer the Nat stubs
  (define (pats-for-typeof patvar)
    (syntax->datum #'(z (s _))))
    
  ;; a pattern match is total if every layer of the nested representation is total
  (define (total? in-pat)
    (fold-nested (lambda (n init)
                   (and init ; let's just go for performance over exhaustive warnings
                        (patvar-is-total? (syntax->datum (nested-patvar n))
                                          (map (compose syntax->datum nested-match-pat) (nested-matches n))
                                          (pats-for-typeof (nested-patvar n)))))
                 #t
                 (create-nested-pattern in-pat))))

;; TODO: delete these temporary test functions
;; TODO2: most likely move the totality checking into a separate file that imports this
;; ----------------------------------------------
(define-syntax (print-nested stx)
  (syntax-parse stx
    [(_ pat) (begin (printf "INPUT:\n") (pretty-print (syntax->datum #'pat))
                    (printf "NESTED:\n") (pretty-print (create-nested-pattern #'pat))
                    #'void)]))

(define-syntax (test stx)
  (syntax-parse stx
    [(_ in-pat) (begin (printf "TOTALITY CHECK:\n~a\n" (syntax->datum #'in-pat))
                       (printf "RESULT:\n~a\n" (total? (attribute in-pat)))
                       #'void)]))

;; ----------------------------------------------

;; NESTED TREE TESTS

(print-nested
 ((n m) ([z z => A] [z (s x) => B])))

(print-nested
 ((n m)
  ([z _ => z]
   [(s n-1) z => (s n-1)]
   [(s n-1) (s m-1) => (bad-minus n-1 (s m-1))])))

(print-nested
 ((n m o)
  ([z _ (s o-1) => z]
   [(s n-1) z (s o-1) => (s n-1)]
   [(s n-1) (s m-1) z => (bad-minus n-1 (s m-1))])))

(print-nested
 ((a b)
  ([(nil _) (nil _) => true]
   [(nil _) (cons _ _ _) => false]
   [(cons _ _ _) (nil _) => false]
   [(cons _ a rsta) (cons _ b rstb) => (and (f a b) (andmap2 A B f rsta rstb))])))

;; ADDITIONAL NESTING

(print-nested
 ((e1 e2)
  ([z z => A]
   [(s (s e2)) (s m) => B])))

(print-nested
 ((e1 e2)
  ([z z => A]
   [(s (s e2)) z => B]
   [(s (s e2)) (s m) => C])))

(print-nested
 ((e1 e2)
  ([z z => A]
   [(s a b c d) (s c d) => B]
   [(s (s a) x (s d) (s b)) (s c d) => C]
   [(s (s a) x (s d) (s e f)) (s c d) => D]
   [(s (s (s a)) x (s d) (s c)) (s c d) => E]))) ; bogus example

;; TOTALITY TESTS

;; TOTAL
(test
 ((n m)
  ([z z => A]
   [z (s x) => B]
   [(s x) z => C]
   [(s x) (s x) => D])))

(test
 ((n m)
  ([z _ => A]
   [(s x) z => C]
   [(s x) (s x) => D])))

;; NOT TOTAL
(test
 ((n m)
  ([z z => A]
   [(s x) z => C]
   [(s x) (s x) => D])))

(test
 ((n m)
  ([z z => A]
   [z (s x) => B]
   [(s x) z => C]
   [(s (s n)) (s x) => D])))

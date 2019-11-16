#lang s-exp "../main.rkt"

(provide (for-syntax (all-defined-out)))
(require "pattern-tree.rkt"
         (for-syntax racket/bool
                     racket/list
                     cur/curnel/reflection))

(begin-for-syntax
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
  (define (patvar-total-check patvar patterns ty-pats #:warnings [warnings empty])
    (cond [(empty? ty-pats) warnings]
          [else (let* ([patvar-datum (syntax->datum patvar)]
                       [matched? (for/or ([pat patterns])
                                   (typecase-match (syntax->datum pat)
                                                   (syntax->datum (first ty-pats))))]
                       [new-warnings (if matched?
                                         warnings
                                         (cons (first ty-pats) warnings))])
                  (patvar-total-check patvar patterns (rest ty-pats) #:warnings new-warnings))]))

  ;; retrieves the case patterns associated with a pattern variable's type
  ;; TODO: actually pull the information over, not just offer the Nat stubs
  ;; if this proves far too difficult to implement, let's just fetch type
  ;; information from analysis of the patvar's cases? we could do something
  ;; like check the constructors which map to types and if they differ, well,
  ;; I suppose we just give the big red wall of text?
  (define (pats-for-typeof env patvar)
    (let ([patvar-type (turnstile-infer patvar #:local-env env)])
      (cond [(false? patvar-type) empty]
            [(equal? (syntax->datum patvar-type) '(#%plain-app Bool)) (syntax->list #'(true false))]
            [(equal? (syntax->datum patvar-type) '(#%plain-app Nat)) (syntax->list #'(z (s _)))]
            [else empty]))) ; trivially pass for other types
    
  ;; a pattern match is total if every layer of the nested representation is total
  (define (total? in-pat #:env [env '()])
    (let ([warnings (fold-nested (lambda (n context init)
                                   (let* ([patterns (cons (nested-patvar n) (map nested-match-pat (nested-matches n)))]
                                          [warnings (patvar-total-check (nested-patvar n)
                                                                        patterns
                                                                        (pats-for-typeof env (nested-patvar n)))]
                                          [result (string-append "failed totality check\n"
                                                                 (format "match path: ~a\n" (append (map nested-match-pat context) (list (nested-patvar n))))
                                                                 (foldr (lambda (w i) (string-append (format "missing: ~a\n" w) i)) "" warnings))])
                                     (if (not (empty? warnings))
                                         (cons (cons patterns result) init)
                                         init)))
                                 empty
                                 (create-nested-pattern in-pat))])
      (or (empty? warnings)
          (raise (exn:fail:syntax (foldr (lambda (w i) (string-append w i)) "" (map cdr warnings))
                                  (current-continuation-marks)
                                  (foldr append empty (map car warnings))))))))

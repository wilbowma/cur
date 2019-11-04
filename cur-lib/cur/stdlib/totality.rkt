#lang s-exp "../main.rkt"

(provide (for-syntax total?))
(require "pattern-tree.rkt"
         (for-syntax racket/list))

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
  (define (patvar-is-total? patvar patterns ty-pats #:raise-exn? [raise-exn? #t])
    (let ([patvar-datum (syntax->datum patvar)])
      (or (empty? ty-pats)
          (and (or (for/or ([pat patterns])
                     (typecase-match (syntax->datum pat)
                                     (syntax->datum (first ty-pats))))
                   (and raise-exn?
                       (raise (exn (format "missing case for ~a:\nmissing: ~a\nactual cases: ~a"
                                           patvar (first ty-pats) patterns)
                                   (current-continuation-marks)))))
               (patvar-is-total? patvar patterns (rest ty-pats) #:raise-exn? raise-exn?)))))

  ;; retrieves the case patterns associated with a pattern variable's type
  ;; TODO: actually pull the information over, not just offer the Nat stubs
  ;; if this proves far too difficult to implement, let's just fetch type
  ;; information from analysis of the patvar's cases? we could do something
  ;; like check the constructors which map to types and if they differ, well,
  ;; I suppose we just give the big red wall of text?
  (define (pats-for-typeof patvar)
    (syntax->list #'(z (s _))))
    
  ;; a pattern match is total if every layer of the nested representation is total
  (define (total? in-pat)
    (fold-nested (lambda (n init)
                   (and init ; let's just go for performance over exhaustive warnings
                        (patvar-is-total? (nested-patvar n)
                                          (map nested-match-pat (nested-matches n))
                                          (pats-for-typeof (nested-patvar n)))))
                 #t
                 (create-nested-pattern in-pat))))

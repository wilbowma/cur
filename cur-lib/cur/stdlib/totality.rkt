#lang s-exp "../main.rkt"

(provide (for-syntax (all-defined-out)))
(require "pattern-tree.rkt"
         (for-syntax racket/base
                     racket/bool
                     racket/list
                     racket/pretty
                     cur/curnel/reflection))

(begin-for-syntax
  ;; checks to see if the identifiers match
  (define (constructor-match in-id match-id)
    (free-identifier=? in-id match-id))

  ;; checks if a pattern has the same constructor and number of arguments
  (define (typecase-match pat ty-pat patvar #:env [env '()])
    (let ([patlist (syntax->list pat)]
          [ty-patlist (syntax->list ty-pat)])
      (or (and (false? patlist)
               (not (is-constructor? pat patvar #:env env))
               (begin #;(printf "~a is not a constructor!\n" pat) #t))
          (and (equal? (false? patlist)
                       (false? ty-patlist))
               (if (false? ty-patlist)
                   (constructor-match pat ty-pat)
                   (and (= (length ty-patlist) (length patlist))
                        (constructor-match (first patlist) (first ty-patlist))))))))

  ;; given a list of patterns associated with a pattern variable and a list of expected
  ;; type cases, returns true if all type cases can be matched
  (define (patvar-total-check patvar patterns ty-pats #:warnings [warnings empty] #:env [env '()])
    (cond [(empty? ty-pats) warnings]
          [else (let* ([matched? (for/or ([pat patterns])
                                   (typecase-match pat
                                                   (first ty-pats)
                                                   patvar
                                                   #:env env))]
                       [new-warnings (if matched?
                                         warnings
                                         (cons (first ty-pats) warnings))])
                  (patvar-total-check patvar patterns (rest ty-pats) #:warnings new-warnings #:env env))]))
    
  ;; a pattern match is total if every layer of the nested representation is total
  (define (total? in-pat #:env [env '()])
    (let* ([ns (create-nested-pattern in-pat #:env env)]
           [warnings (fold-nested (lambda (n context init)
                                    (let* ([patterns (map nested-match-pat (nested-matches n))]
                                           [constructors-res (get-constructors-for-pat-var (nested-patvar n) #:env env)]
                                           [constructors (if constructors-res
                                                             (car constructors-res)
                                                             empty)]
                                           [warnings (if (and (> (length context) 0)
                                                              (nested-match-is-wildcard? (first context))
                                                              (> (length (nested-matches (second context))) 1))
                                                         empty
                                                         (patvar-total-check (nested-patvar n)
                                                                         patterns
                                                                         constructors
                                                                         #:env env))]
                                           [result (string-append "failed totality check\n"
                                                                  (format "match path: ~a\n" (append (map nested-match-pat (reverse (filter nested-match? context))) (list (nested-patvar n))))
                                                                  (foldr (lambda (w i) (string-append (format "missing: ~a\n" w) i)) "" warnings))])
                                      (if (not (empty? warnings))
                                          (cons (cons (cons (nested-patvar n) patterns) result) init)
                                          init)))
                                  empty
                                  ns)])
      (or (empty? warnings)
          (raise (exn:fail:syntax (string-append (foldr (lambda (w i) (string-append w i)) "" (map cdr warnings))
                                                 (pretty-format ns))
                                  (current-continuation-marks)
                                  (foldr append empty (map car warnings))))))))

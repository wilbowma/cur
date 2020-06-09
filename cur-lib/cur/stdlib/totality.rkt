#lang s-exp "../main.rkt"

(provide (for-syntax (all-defined-out)))
(require "pattern-tree.rkt"
         (for-syntax racket/base
                     racket/bool
                     racket/list
                     racket/pretty
                     cur/curnel/reflection))

;; TODO: Lower to relative phase 1 and change import
(begin-for-syntax
  ;; A pattern match is total if and only if each match variable in the tree contains a match case for each
  ;; of the corresponding type constructors
  (define (total? in-pat #:aliases [aliases '()] #:env [env '()])
    (let* ([pt (create-pattern-tree in-pat #:env env)]
           [warnings (fold-pt
                      (lambda (d context init)
                        (let* ([patterns (map pt-match-pattern (pt-decl-matches d))]
                               [constructors-res (get-constructors-metadata (pt-decl-match-var d) #:env env)]
                               [constructors (if constructors-res
                                                 (car constructors-res)
                                                 ;; TODO PR103: Better error
                                                 (error
                                                  'total?
                                                  (format "Expected pattern match on an inductively defined type, but ~a is not inductive"
                                                          (pt-decl-match-var d))
                                                  (pt-decl-match-var d)))]
                               ; handle implicit constructors
                               [updated-constructors
                                (map (lambda (c)
                                       (let* ([c-list (syntax->list c)]
                                              [alias-match
                                               (if c-list
                                                   (for/or ([a aliases])
                                                     (and (free-identifier=? (first c-list) (second a)) a))
                                                   (for/or ([a aliases])
                                                     (and (free-identifier=? c (second a)))))])
                                         (if alias-match
                                             (if c-list
                                                 #`#,(cons (first alias-match) (drop (rest (syntax->list c)) (third alias-match)))
                                                 (first alias-match))
                                             c)))
                                     constructors)]
                               ; if the current match pattern is marked as a pattern variable, then
                               ; we actually don't need to worry about failures at this level; subsequent
                               ; nested ones we do
                               ; note: context is currently a list alternating between a decl object and a match object
                               [warnings (if (and (> (length context) 0)
                                                  (syntax-property (pt-match-pattern (first context)) 'is-pattern-variable?)
                                                  (> (length (pt-decl-matches (second context))) 1))
                                             empty
                                             (match-var-total-check (pt-decl-match-var d)
                                                                    patterns
                                                                    updated-constructors
                                                                    #:env env))]
                               [result (string-append "failed totality check\n"
                                                      (format "match path: ~a\n" (append (map pt-match-pattern (reverse (filter pt-match? context))) (list (pt-decl-match-var d))))
                                                      (foldr (lambda (w i) (string-append (format "missing: ~a\n" w) i)) "" warnings))])
                          (if (not (empty? warnings))
                              (cons (cons (cons (pt-decl-match-var d) patterns) result) init)
                              init)))
                      empty
                      pt)])
      (or (empty? warnings)
          (raise (exn:fail:syntax (string-append (foldr (lambda (w i) (string-append w i)) "" (map cdr warnings))
                                                 (pretty-format pt))
                                  (current-continuation-marks)
                                  (foldr append empty (map car warnings)))))))

  ;; Given a list of patterns associated with a pattern variable and a list of expected
  ;; type cases, returns true if all type cases can be matched
  (define (match-var-total-check match-var patterns ty-pats #:warnings [warnings empty] #:env [env '()])
    (cond [(empty? ty-pats) warnings]
          [else (let* ([matched? (for/or ([pat patterns])
                                   (or
                                    (syntax-property pat 'is-pattern-variable)
                                    (typecase-match pat
                                                    (first ty-pats)
                                                    match-var
                                                    #:env env)))]
                       [new-warnings (if matched?
                                         warnings
                                         (cons (first ty-pats) warnings))])
                  (match-var-total-check match-var patterns (rest ty-pats) #:warnings new-warnings #:env env))]))

  ;; checks to see if the identifiers match
  (define (constructor-match in-id match-id)
    (free-identifier=? in-id match-id))

  ;; checks if a pattern has the same constructor and number of arguments
  (define (typecase-match pat ty-pat match-var #:env [env '()])
    (let ([patlist (syntax->list pat)]
          [ty-patlist (syntax->list ty-pat)])
      (or (and (false? patlist)
               (not (is-constructor? pat match-var #:env env)))
          (and (equal? (false? patlist)
                       (false? ty-patlist))
               (if (false? ty-patlist)
                   (constructor-match pat ty-pat)
                   (and (= (length ty-patlist) (length patlist))
                        (constructor-match (first patlist) (first ty-patlist)))))))))

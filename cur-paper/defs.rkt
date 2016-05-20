#lang racket

(require
 scribble/base)

(provide todo omit title* section* subsubsub*section*)

;; TODO: made this disable-able in main.scrbl via parameters or
;; something
(define (todo . x)
  (void)
  #;(apply margin-note* "TODO: " x))

(define-syntax (omit syn) #'(void))

(define (first-word x)
  (first (string-split (first x) #px"\\W")))

(define (title* . x)
  (apply title #:tag
    (format "sec:~a" (string-downcase (first-word x)))
    x))

;; TODO: really, tag should be sec:section:subsection
(define (section* . x)
  (apply section #:tag
    (format "subsec:~a" (string-downcase (first-word x)))
    x))

(define (subsubsub*section* . x)
  #;(apply elem #:style "SSubSubSubSection" x)
  (list ~ (apply subsubsub*section x)))


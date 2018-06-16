#lang cur

(require
 cur/stdlib/ascii
 cur/stdlib/list
 cur/stdlib/sugar
 cur/stdlib/bool
 cur/stdlib/nat
 rackunit)

(check-equal?
 ""
 (nil Ascii))

(check-equal?
 "a"
 (cons
  Ascii
  (ascii true true false false false false true)
  (nil Ascii)))

(check-equal?
 "aZ"
 (cons
  Ascii
  (ascii true true false false false false true)
  (cons
   Ascii
   (ascii true false true true false true false)
   (nil Ascii))))

(begin-for-syntax
  (require rackunit)

  (check-equal?
   ""
   (ascii-str->meta-string #'(nil Ascii)))

  (check-equal?
   "a"
   (ascii-str->meta-string
    #'(cons
       Ascii
       (ascii true true false false false false true)
       (nil Ascii))))

  (check-equal?
   "aZ"
   (ascii-str->meta-string
    #'(cons
       Ascii
       (ascii true true false false false false true)
       (cons
        Ascii
        (ascii true false true true false true false)
        (nil Ascii))))))

(check-equal?
 "Hello, world!"
 (ascii-str-concat "Hello," " world!"))

(check-equal?
 13
 (ascii-str-length "Hello, world!"))

(check-equal?
 0
 (ascii-str-length empty-ascii-str))

(check-equal?
 0
 (ascii-str-length ""))

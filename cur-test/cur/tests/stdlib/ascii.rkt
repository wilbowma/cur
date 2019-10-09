#lang cur

(require
 cur/stdlib/ascii
 cur/stdlib/list
 cur/stdlib/sugar
 cur/stdlib/bool
 cur/stdlib/nat
 rackunit/turnstile+)

(check-type ascii : (-> Bool Bool Bool Bool Bool Bool Bool Ascii))

(check-type "" : (List Ascii) -> (nil Ascii))

(check-type "a" : (List Ascii)
            -> (cons
                Ascii
                (ascii true true false false false false true)
                (nil Ascii)))

(check-type
 "aZ"
 : (List Ascii)
 -> (cons
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

(check-type ascii-str-concat : (-> (List Ascii) (List Ascii) (List Ascii)))
(check-type "Hello," : (List Ascii) -> "Hello,")
(check-type (ascii-str-concat "Hello,") : (-> (List Ascii) (List Ascii)))
(check-type (ascii-str-concat " world!" "Hello,")
            : (List Ascii) -> "Hello, world!")

(check-type (ascii-str-length "Hello, world!") : Nat -> 13)

(check-type (ascii-str-length empty-ascii-str) : Nat -> 0)

(check-type (ascii-str-length "") : Nat -> 0)

(check-type "" : String)
(check-type (string-equal? "" "") : Bool -> true)
(check-type (string-equal? "a" "a") : Bool -> true)
(check-type (string-equal? "b" "b") : Bool -> true)
(check-type (string-equal? "a" "b") : Bool -> false)
(check-type (string-equal? "ab" "ab") : Bool -> true)
(check-type (string-equal? "ab" "ac") : Bool -> false)
(check-type (string-equal? "ab" "a") : Bool -> false)
(check-type (string-equal? "ab" "abc") : Bool -> false)

cur [![Build Status](https://travis-ci.org/stchang/cur.svg?branch=turnstile-core)](https://travis-ci.org/stchang/cur/)
===

A language with static dependent-types and dynamic types, type
annotations and parentheses, theorem proving and meta-programming.

```
Noun
cur (plural curs)

1. (archaic) A mongrel.
2. (archaic) A detestable person.
```

Disclaimer
==========
Cur is currently under active hackery and is not fit for use for any
particular purpose. It is fraught with unreadable code, errors,
performance bugs, and hacks that should never have been written by a
reasonable human being.
These may or may not be fixed shortly.

Versioning
=======
Cur is in alpha. Version numbers are 0.N, where N increases when an
API changes, or a sub-package depends on a new feature (e.g. if
cur-test depends on a feature that did not exist in a previous version).

Getting started
===============

## Easy mode:
You'll need Racket v7.6

First, you need to install Turnstile's experimental branch:
- raco pkg install https://github.com/stchang/macrotypes.git?path=macrotypes-lib#cur
- raco pkg install https://github.com/stchang/macrotypes.git?path=turnstile-lib#cur

Then, install cur via `raco pkg install cur`.
Come ask questions in IRC, `#cur` on Freenode.

See the docs: `raco docs cur`. Unfortunately, they're very out of date and I'm
working on updating them.

## Advanced mode:
Cur is distributed as several packages.
`cur-lib` provides the implementation and all standard libraries.
`cur-doc` provides the documentation.
`cur-test` provides a test suite and examples.

You can install the individual packages from the Racket package server, or from
local copies of the files:

```sh
> git clone https://github.com/wilbowma/cur
> cd cur
> pushd cur-lib; raco pkg install; popd
...
> pushd cur-doc; raco pkg install; popd
...
> raco test cur-test
...
... tests passed
```

```sh
> raco test cur-test/cur/tests/stdlib/nat.rkt
```

## Example code
Try it out: open up DrRacket and put the following in the definition area:


```racket
#lang cur
(require
 cur/stdlib/sugar
 rackunit/turnstile+)

;; Write typed code
(define-datatype Nat : Type
  (z : Nat)
  (s : (forall (x : Nat) Nat)))

(define/rec/match + : Nat (m : Nat) -> Nat
  [z => m]
  [(s x) => (s (+ x m))])

(+ (s z) z)

;; Write dependently-typed code

(define-datatype = [A : Type] [a : A] : (forall (b : A) Type)
  (refl : (= A a a)))

(refl Nat (s z))

(check-type
 (refl Nat (s z))
 :
 (= Nat (+ z (s z)) (s z)))

;; Write some macros and Racket meta-programs over dependently-typed code
(begin-for-syntax
  (define (nat->unary n)
    (if (zero? n)
        #`z
        #`(s #,(nat->unary (sub1 n))))))

(define-syntax (define-numbers syn)
  (syntax-case syn ()
    [(_)
     #`(begin
         #,@(for/list ([i (in-range 10)])
              #`(define #,(format-id syn "Nat-~a" i) #,(nat->unary i))))]))

(define-numbers)
;; (define-numbers) generates the following definitions at macro-expansion time:
#|
 |  (define Nat-0 z)
 |  (define Nat-1 (s z))
 |  (define Nat-2 (s (s z)))
 |  (define Nat-3 (s (s (s z))))
 |  (define Nat-4 (s (s (s (s z)))))
 |  (define Nat-5 (s (s (s (s (s z))))))
 |  (define Nat-6 (s (s (s (s (s (s z)))))))
 |  (define Nat-7 (s (s (s (s (s (s (s z))))))))
 |  (define Nat-8 (s (s (s (s (s (s (s (s z)))))))))
 |  (define Nat-9 (s (s (s (s (s (s (s (s (s z))))))))))
 |  (define Nat-10 (s (s (s (s (s (s (s (s (s (s z)))))))))))
 |#

Nat-0
Nat-5

;; Of course, you could just define #%datum to do the right thing:
(require (only-in cur [#%datum super.datum]))
(define-syntax (#%datum syn)
  (syntax-parse syn
    [(_ . x:nat)
     (nat->unary (syntax->datum #'x))]
    [(_ . e)
     #`(super.datum e)]))

0
5

(refl Nat 1)

(check-type
 (refl Nat 1)
 :
 (= Nat (+ 0 1) 1))
```

Going further
=============

See https://williamjbowman.com/papers#cur or
https://williamjbowman.com/papers#depmacros for some papers on Cur's design and
technologies.

Open up `cur-tests/cur/tests/ntac/software-fondations` to see example from the
Software Foundations text book redone in Cur.

Open up anything in `cur-lib/cur/stdlib/` to see some standard dependent-type
formalisms.

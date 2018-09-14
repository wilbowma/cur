cur [![Build Status](https://travis-ci.org/wilbowma/cur.svg?branch=master)](https://travis-ci.org/wilbowma/cur)
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
You'll need Racket v7.0
Install cur via `raco pkg install cur`. See the docs: `raco docs cur`. Come ask questions in IRC,
`#cur` on Freenode.

## Advanced mode:
You can actually get away with v6.12, and maybe as far back as v6.6 according to
Travis, but you'll have issues with locally built documentation.
Cur is distributed as several packages.
`cur-lib` provides the implementation and all standard libraries; this works
fine in Racket v6.6--7.0.
`cur-doc` provides the documentation; most of this works fine in pre v7.0, but
some examples in the documentation do not run in the sandbox correctly except in
v7.0.
`cur-test` provides a test suite and examples; this works fine in Racket
v6.6--v7.0.

You can install the individual packages from the Racket package server, or from local copies of the
files:

```sh
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
 cur/stdlib/bool
 cur/stdlib/nat
 cur/stdlib/sugar)

;; Write dependently-typed code
(if true
    false
    true)

(: + (-> Nat Nat Nat))
(define + plus)
(+ z (s z))

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
(require (only-in cur [#%datum old-datum]))
(define-syntax (#%datum syn)
  (syntax-parse syn
    [(_ . x:nat)
     (nat->unary (syntax->datum #'x))]
    [(_ . e)
     #`(old-datum e)]))

0
5
```

Try entering the following in the interaction area:
```racket
(sub1 (s (s z)))
```

Don't like parenthesis? Use Cur with sweet-expressions:
```racket
#lang sweet-exp cur
require
 cur/stdlib/sugar
 cur/stdlib/bool
 cur/stdlib/nat

if true
   false
   true

define + plus

{z + s(z)}
```

Going further
=============

See https://williamjbowman.com/papers#cur for a draft of a paper on Cur.

Open up `cur-tests/cur/tests/stlc.rkt` to see an example of the
simply-typed lambda-calculus modeled in Cur, with a parser and syntax
extension to enable deeply embedding.

Open up `examples/proofs-for-free.rkt` to see an implementation of the
translation defined in [Proofs for Free](http://staff.city.ac.uk/~ross/papers/proofs.html) as a meta-program.

Open up `cur-lib/cur/ntac` to see one way to implement tactics in Cur.

Open up anything in `cur-lib/cur/stdlib/` to see some standard dependent-type
formalisms.

Open up `cur-model/cur/curnel/model/core.rkt` to see a model of the core
language, <600 lines of code.
You can run some Cur code using this model, but the
`cur-lib/cur/curnel/racket-impl/core.rkt` (the default Curnel) is much
faster and supports more features.

Differences Between Legacy Cur Legacy and Cur with Turnstile Core
=================================================================
Lega: forall same as Pi
Turn: forall has no annotations

Turn:
- `match` requires #:return
- no function signature forward declaration (`:`)

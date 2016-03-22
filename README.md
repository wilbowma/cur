cur
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

Getting started
===============

Easy mode:
Install cur via `raco pkg install cur`.

Advanced mode:
Cur is actually distributed as several packages.
`cur-lib` provides the implementation and all standard
libraries.
`cur-doc` provides the documentation.
`cur-test` provides a test suite and examples.


Try it out: open up DrRacket and put the following in the definition area:

```racket
#lang cur
(require
 cur/stdlib/bool
 cur/stdlib/nat)

(if true
    false
    true)

(: + (-> Nat Nat Nat))
(define + plus)
(+ z (s z))
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

See the docs: `raco docs cur`.

Going further
=============

Open up `cur-tests/cur/tests/stlc.rkt` to see an example of the
simply-typed lambda-calculus modeled in Cur, with a parser and syntax
extension to enable deeply embedding.

Open up `examples/proofs-for-free.rkt` to see an implementation of the
translation defined in [Proofs for Free](http://staff.city.ac.uk/~ross/papers/proofs.html) as a meta-program.

Open up `cur-lib/cur/stdlib/tactics` to see one way to implement tactics in Cur.

Open up anything in `cur-lib/cur/stdlib/` to see some standard dependent-type
formalisms.

Open up `cur-lib/cur/curnel/redex-core.rkt` to see the entire
implementation of the core language, <600 lines of code.

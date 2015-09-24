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
particular purpose. It is fraught with unreadable code, errors, and
hacks that should never have been written by a reasonable human being.
These may or may not be fixed shortly.

Getting started
===============

Install cur via `raco pkg install cur`.

Try it out: open up DrRacket and put the following in the definition area:

```racket
#lang cur
(require 
 cur/stdlib/bool
 cur/stdlib/nat)

(if true
    false
    true)
```

Try entering the following in the interaction area:
```racket
(sub1 (s (s z)))
```

See the docs: `raco docs cur`.

Most of the standard library is currently undocumented, so just see the source.

Going further
=============

Open up `examples/example.rkt` to see a tour of Cur's features.

Open up `examples/stlc.rkt` to see an example of what advanced meta-programming can let you do.

Open up `oll.rkt` to see the implementation of the meta-programs used to
enable `examples/stlc.rkt`, including the parsers for BNF syntax and inference rule
syntax, and Coq and LaTeX generators.

Open up `examples/proofs-for-free.rkt` to see an implementation of the
translation defined in [Proofs for Free](http://staff.city.ac.uk/~ross/papers/proofs.html) as a meta-program.

Open up `stdlib/tactics` to see tactics, implemented entirely via
meta-programming.

Open up anything in `stdlib/` to see some standard dependent-type
formalisms.

Open up `curnel/redex-core.rkt` to see the entire "trusted" (after a
large test suite) core.

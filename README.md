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

Getting started
===============

Requires redex-lib version 1.6 if you want answers in a reasonable amount
of time. Otherwise, the type-checker may require exponential time
or worse.

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

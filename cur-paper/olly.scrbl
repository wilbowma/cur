#lang scribble/base
@(require
  "defs.rkt"
  "bib.rkt"
  scribble/manual
  scriblib/footnote
  scriblib/figure)

@title*{Olly - Ott-Like LibrarY}
All the previous extensions are features of existing proof assistants.
In this section we present Olly, a domain-specific language (DSL) for modeling
programming languages, which provides features that no other proof assistant
supports.
Olly provides BNF notation for generating inductive types that represent
programming language syntax.
The BNF notation automatically converts variables in the syntax to de Bruijn
indices.
Olly also supports inference rule notation for modeling relations.
Both notations support extracting the models to LaTeX and Coq, in addition to
using the models directly in Cur.

Olly is inspired by Ott@~citea{sewell:2007}, a tool for generating models of
programming language semantics in different proof assistants from a single
model written in a DSL.
Ott is an external tool that generates files for each proof assistant, while
Olly is integrated into the object language of Cur as a language extension.

@subsubsub*section*{BNF Notation}
We begin with an example of defining of the syntax of the simply-typed
λ-calculus using the @racket[define-language] form.
This language includes booleans, the unit type, pairs, and functions.
Note that the @racket[let] form is the elimination form for pairs in this
language, and binds two names.
@racketblock[
define-language stlc
  #:vars (x)
  #:output-coq "stlc.v"
  #:output-latex "stlc.tex"
  val  (v)   ::= true false unit
  type (A B) ::= boolty unitty (-> A B) (* A A)
  term (e)   ::= x v (lambda (#:bind x : A) e)
             (app e e) (cons e e)
             (let (#:bind x #:bind x) = e in e)
]
The first argument to the form is a name for the language---@racket[stlc] in
this case.
The next three lines are optional keyword arguments.
The @racket[#:vars] argument is a set of meta-variables that represent variables
in the syntax.
The @racket[#:output-coq] argument is a string representing a file name;
when given, a Coq representation of the language syntax is written to the
specified file during compilation.
Similarly, the @racket[#:output-latex] argument is a string representing a file
name; when given, a Latex rendering of the BNF grammar is written to the
specified file during compilation.
After the optional arguments, @racket[define-language] expects an arbitrary
number of non-terminal definitions from which it generates inductive types.

To better understand @racket[define-language] non-terminal clauses, let us
first look at the code generated for the @racket[term] non-terminal.
@racketblock[
data stlc-term : Type
  Nat->stlc-term : {Nat -> stlc-term}
  stlc-val->stlc-term : {stlc-value ->
                             stlc-term}
  stlc-lambda : {stlc-type -> stlc-term ->
                     stlc-term}
  stlc-app : {stlc-term -> stlc-term -> stlc-term}
  stlc-cons : {stlc-term -> stlc-term ->
                   stlc-term}
  stlc-let : {stlc-term -> stlc-term ->
                  stlc-term}
]
References to other non-terminals, such as the reference to @racket[x], result
in @emph{conversion constructors} which simply inject one non-terminal into the
other.
The names of the conversion constructors are generated from the types of the
non-terminals with the sigil @racket[->] between them, indicating
conversion.
For example, @racket[Nat->stlc-term] is a @racket[stlc-term]
constructor that converts a @racket[Nat] (representing a de Bruijn index) to a
@racket[stlc-term].
Other constructor names are generated from the name of the language,
@racket[stlc], and the name of the constructor given in the syntax.
For example, the constructor name generated from the @racket[lambda] syntax is
@racket[stlc-lambda].

More formally, the syntax of a non-terminal definition is @racket[(nt-name
(meta-variables ...) ::= syn-clause ...)]. 
As Cur does not currently support mutual inductive definitions, all
non-terminal definitions must be appear in order of their dependencies.
Each @racket[syn-clause] must be either a reference to a previously defined
non-terminal, a terminal represented by a unique identifier, or an s-expression
whose first element is a unique identifier.

For each non-terminal, we generate a new inductive type.
We generate a constructors for the inductive type for each @racket[syn-clause].
We prefix the name of each inductive type and each constructor by the language name.
For references to previously defined non-terminals, we generate a constructor
that act as a tag and injects the previous non-terminal into the new one.

For terminals, we generate a constructor that take no arguments and whose name
is based on the terminal.

For s-expressions, we create a new constructor whose name is based on
the identifier at the head of the s-expression and whose arguments' types are
computed from the meta-variables that appear in the rest of the s-expression.
We only use the non-meta-variable symbols such as @racket[:] 
in the Latex rendering of the BNF grammar.
The syntax @racket[#:bind x] declares @racket[x] to be a binding position, so
it is not treated as an argument.
Since we use de Bruijn indices for binding, binding positions are erased.

The @racket[define-language] form allows us to create the model using BNF
notation, but working with the model requires using the generated constructor
names.
Instead of using the constructors directly, we can write an extension that
parses the @racket[stlc] syntax into the appropriate constructors@note{It
should be possible to generate this parser in the @racket[define-language]
extension, but we have not yet implemented that feature.}.
@Figure-ref{fig:stlc-parse} presents an excerpt of the parser.
The form @racket[begin-stlc] simply calls the metalanguage function
@racket[parse-stlc] with the syntax object @racket[e] and a new hashtable.
The @racket[parse-stlc] function declares each of the constructor names and
syntactic symbols as literals, and loops over the syntax object generating the
constructors that correspond to the @racket[stlc] syntax.
It uses the hashtable to map variable names to de Bruijn indices.
When parsing a @racket[lambda], it shifts each index in the hashtable.
For convenience, the parser accepts the syntax @racket[(e1 e2)] for
application instead of @racket[(app e1 e2)] and @racket[1] for the unit type
instead of @racket[unitty].
@figure["fig:stlc-parse" "Parser for STLC Syntax (excerpt)"
@#reader scribble/comment-reader #:escape-id UNSYNTAX
(RACKETBLOCK0
define-syntax (begin-stlc syn)
  syntax-case syn ()
    [(_ e) (parse-stlc #'e (make-immutable-hash))]

begin-for-syntax
  define (parse-stlc syn d)
    syntax-case syn (lambda : prj * ->
                     let in cons bool
                     unit true false)
      [(lambda (x : t) e)
       #`(stlc-lambda
           #,(parse-stlc #'t d)
           #,(parse-stlc #'e
               (dict-set
                 (dict-shift d)
                 (syntax->datum #'x)
                 #`z)))]
      [(e1 e2)
       #`(stlc-app
           #,(parse-stlc #'e1 d)
           #,(parse-stlc #'e2 d))]
      [(cons e1 e2)
       #`(stlc-cons
           #,(parse-stlc #'e1 d)
           #,(parse-stlc #'e2 d))]
      ....
      [false #'(stlc-val->stlc-term stlc-false)]
      [bool #'stlc-boolty]

  define (dict-shift d)
    for/fold ([d (make-immutable-hash)])
             ([(k v) (in-dict d)])
      dict-set d k #`(s #,v)
)]

@subsubsub*section*{Inference-rule Notation}
@Figure-ref{fig:has-type} presents an example of using the inference rule
notation.
We use the @racket[define-relation] form to model a type system for
@racket[stlc].
The @racket[define-relation] form takes as its first argument a name for the
new relation applied to the types of its arguments.
This example defines the inductive type @racket[has-type] which relates a list
of @racket[stlc-type]s, an @racket[stlc-term], and an @racket[stlc-type].
Like the @racket[define-language] form, @racket[define-relation] takes optional
arguments for generating Coq and Latex output.
The rest of the form is interpreted as a sequence of inference rules.
Each inference rule is a list of assumptions, followed by a horizontal line
represented by an arbitrary number of hyphens, a name for the rule that will
become the name of the constructor, and a conclusion that must be the relation
applied to its arguments.
@figure-here["fig:has-type" "STLC Type System Model (excerpt)"
@#reader scribble/comment-reader
(racketblock0
define-relation
  (has-type (List stlc-type) stlc-term stlc-type)
  #:output-coq "stlc.v"
  #:output-latex "stlc.tex"
  [(g : (List stlc-type))
   ------------------------ T-Unit
   (has-type g (begin-stlc unit) (begin-stlc 1))]
  ....

;; Generates:
data has-type : (-> (List stlc-type)
                     stlc-term
                     stlc-type
                     Type)
  T-Unit : (forall (g : (List stlc-type))
              (has-type
                g
                (stlc-val->stlc-term stlc-unit)
                stlc-unitty))
  ....
)]

@Figure-ref{fig:define-relation-impl} presents an excerpt of the implementation
for @racket[define-relation].
To implement this form, we use @racket[syntax-parse]@~citea{ryan2012}, but
only present enough of @racket[syntax-parse] to undeerstand the key ideas in
our implementation.

The @racket[syntax-parse] form allows parsing syntax objects rather than merely
pattern matching on them.
The form allows specifying patterns as in @racket[syntax-case], but also
support refining the patterns using syntax classes that specify subpatterns and
side-conditions.
We can apply a syntax class to a pattern variable by using the syntax
@racket[pv:class], or by using the syntax @racket[(~var pv class)].
Both declare the pattern variable @racket[pv] must match the syntax class
@racket[class], but the @racket[~var] syntax is required when the syntax class
takes arguments.

In the definition of @racket[define-relation], we declare that the name of the
relation must be an identifier using the colon syntax and the syntax class
@racket[id].

We declare that the next two arguments are optional using the special form
@racket[~optional], which takes a pattern as its argument.
We specify the pattern is a sequence of the keyword @racket[#:output-coq]
followed by a pattern variable @racket[coq-file].
We use the syntax class @racket[str] to refine the @racket[coq-file] pattern,
indicating that it must be a string literal.
If this optional pattern matches, then the @racket[coq-file] pattern variable
is bound in an attribute map.
The form @racket[attribute] references the attribute map and returns
@racket[false] if the attribute is not bound.

After the optional arguments, we declare a pattern variable @racket[rule] using
the @racket[~var] syntax, refine it using the @racket[inference-rule] syntax
class, and use @racket[...] to match a list of inference rules.

Next we define the syntax class @racket[inference-rule].
The @racket[inference-rule] syntax class takes two arguments: the name of the
relation and the list of indices.
This syntax class matches when the syntax has the pattern of a list of
hypothesis, followed by a horizontal line, a name, and a conclusion.
The rule name must be an identifier.

The syntax class for a horizontal line converts the syntax to a string and uses
a regular expression to match when the string is an arbitrary number of
hyphens.

The syntax class for a conclusion uses the name of the relation and the indices
to ensure the conclusion is the original relation applied to the right number
of arguments.
@figure["fig:define-relation-impl" @elem{Implementation of @racket[define-relation] (excerpt)}
@#reader scribble/comment-reader
(racketblock0
define-syntax (define-relation syn)
  syntax-parse syn
    [(_ (name:id index ...)
        (~optional
          (~seq #:output-coq coq-file:str))
        (~optional
          (~seq #:output-latex latex-file:str))
        (~var rule (inference-rule
                     (attribute name)
                     (attribute index)))
        ...)
      ....]

begin-for-syntax
  define-syntax-class horizontal-line
    pattern
     x:id
     #:when (regexp-match?
              #rx"-+" (syntax->string #'x))

  define-syntax-class (conclusion n args r)
    pattern
     (name:id arg ...)
     #:fail-unless
       (equal? (syntax->symbol #'name)
               (syntax->symbol #'n))
       (format "Rule ~a: conclusion mismatch" r)
     ....

  define-syntax-class (inference-rule name
                                       indices)
    pattern (h ...
              line:horizontal-line
              rule-name:id
              (~var t (conclusion
                        name
                        indices
                        (attribute rule-name))))
     ....
)]
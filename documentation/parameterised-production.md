# Parameterised productions

## Summary

ApusApus should support parameterised productions: grammar definitions whose parameters are grammar
symbols or subgraphs.

A definition such as:

```text
ifConfig(Body) =
    "#if" compilationCondition newline Body?
    { "#elseif" compilationCondition newline Body? }
    [ "#else" newline Body? ]
    "#endif"
```

can then be applied as:

```text
ifConfig(statements)
ifConfig(members)
ifConfig(postfixSuffixes)
ifConfig(attributes)
```

Applications are checked and specialised while the grammar is constructed. The result is an
ordinary `GrammarNode` graph. Parsing has no parameter calls, callbacks or additional runtime
state, and the BSR and Oracle require no new semantics.

## Rationale

Swift conditional compilation is one syntactic protocol embedded in several grammatical contexts.
Its directive sequence, clause ordering, line boundaries and nesting are common, while the grammar
of a clause body depends on the caller.

Representing every body category as an independent family of ordinary productions duplicates the
protocol and makes small Swift-specific distinctions spread through many rules. It has already led
to extensive special handling for statement, member, postfix and attribute conditional blocks.

The body category is not a semantic property discovered after parsing. It is part of the grammar at
the point where the conditional block is referenced. A grammar parameter expresses that fact
directly.

The feature is more general than conditional compilation. It can provide reusable definitions for
options, lists, separated lists and delimited regions. Existing EBNF syntax already covers many of
these cases, so `#if` is the motivating application rather than a reason to replace working EBNF.

## Intended semantics

A parameterised production is a compile-time grammar abstraction.

- Formal parameters denote terminals, nonterminals or other fully applied parameterised
  productions.
- Every application supplies the correct number and kind of arguments.
- An application is specialised to a stable ordinary nonterminal.
- Equal applications share the same specialisation.
- Recursive definitions are allowed when their expanded graph is well formed.
- Specialisation must terminate.
- Annotations on the definition and its productions have explicit, testable propagation rules.
- Diagnostics refer to both the definition and the application that caused an invalid expansion.

The specialised graph must behave exactly as an equivalent handwritten grammar. This includes
ambiguity, BSR shape, Oracle annotations and builder/converter behaviour.

## What this is not

Parameterised productions must not become:

- arbitrary Swift closures embedded in the grammar;
- semantic predicates that inspect parser state;
- a way to mutate scanner or parser modes;
- dynamic parameters carried by every GLL descriptor;
- an alternative disambiguation system;
- a generic balanced-token escape hatch.

Those mechanisms have different costs and semantics. If ApusApus later needs lexical regions for
raw strings, interpolation, regexes, embedded languages or indentation, they should be designed as
a separate controlled-recognition facility. Any state affecting future recognition would have to
participate in descriptor identity and, therefore, must not enter through this feature accidentally.

Likewise, conditional-compilation conditions should own their line-boundary protocol as part of
the `#if` construct, not through a production parameter.

## Lessons learned

### Parameterisation should disappear before parsing

Menhir and Happy both use parameterised productions as statically expanded grammar abstractions.
Their successful use is largely for reusable grammar structure: options, lists, separated lists,
delimiters and families of context-specific productions.

ApusApus should follow that model. It retains the declarative grammar and lets the existing parser
operate on the resulting graph without knowing that parameterisation existed.

### Contextual recognition must remain explicit

Tree-sitter external scanners and ANTLR lexer modes show that genuinely context-sensitive lexical
regions sometimes need state. That state is deliberately isolated rather than hidden inside normal
productions.

ApusApus is a generalized parser, so hidden state is especially dangerous: two descriptors at the
same grammar position and input position are equivalent only when all recognition-relevant state is
also equal. Static specialisation avoids changing that invariant.

### Avoid general semantic predicates

ANTLR semantic predicates are powerful, but their placement affects prediction and their
implementation is tied to generated target-language code. They make grammar behaviour harder to
reason about and test independently.

ApusApus already has explicit grammar constraints and a separate Oracle. Parameterised productions
should compose those existing mechanisms, not introduce executable conditions.

### Share protocols, not accidental similarities

The complete conditional-compilation clause protocol is worth sharing. Category-specific admission
rules should usually remain outside it:

```text
postfixIfConfig =
    startsPostfixContinuation ifConfig(postfixSuffixes)

attributeIfConfig =
    ifConfig(nonemptyAttributeBody)
```

This is preferable to adding loosely defined flags such as
`ifConfig(Body, specialCase: true)`. A second parameter is justified only when it denotes another
grammar symbol, not an imperative behaviour switch.

### Preserve the generated tree contract

Expansion is not merely a recognizer transformation. Builders and converters depend on recognizable
grammar structure. The initial design must decide which specialised symbols remain visible in the
BSR and resulting tree, rather than adding expansion first and repairing tree conversion later.

## Initial scope

The first implementation should support symbol parameters only:

```text
definition(parameter, ...)
application(argument, ...)
```

Arguments may be terminals, ordinary nonterminals, formal parameters or fully applied
parameterised productions. Anonymous production arguments, higher-order parameters and lexical-mode
parameters are out of scope until a concrete use requires them.

The first client is the common conditional-compilation skeleton. Initial specialisations should
cover the body categories already represented in `Swift.apus`:

1. Statement or file-item bodies.
2. Member bodies.
3. Postfix-suffix bodies.
4. Attribute bodies.

The migration should not change accepted input, ambiguity or produced SwiftSyntax trees.

## Implementation plan

### 1. Specify syntax and identity

Choose an unambiguous grammar syntax for definitions and applications. Define a canonical
specialisation key from the parameterised definition plus canonical argument symbol identities.

Document:

- arity and argument validation;
- recursive applications;
- visibility and naming of generated symbols;
- annotation propagation;
- builder/converter naming;
- source locations used by diagnostics.

Do not begin parser changes until these rules are settled.

### 2. Extend the grammar model

Represent an unapplied definition separately from ordinary grammar nodes during grammar loading.
Represent applications in the parsed meta-grammar long enough to resolve and validate them.

Add no parameter state to `MessageParser`, GLL descriptors, BSR values or Oracle data.

### 3. Specialise during grammar construction

Resolve each application through a memoized specialisation table:

```text
(definition identity, argument identities) -> specialised nonterminal
```

Create the specialised nonterminal before expanding its body so recursive applications can refer
back to it. Substitute formal parameters with arguments, clone or share immutable graph structure
as appropriate, and then run the existing grammar analyses on the completed ordinary graph.

Detect non-terminating specialisation, such as applications that continually construct new argument
shapes, and report it as a grammar error.

### 4. Define annotation and conversion behaviour

Test each existing annotation category:

- structural/parser annotations;
- Oracle annotations;
- layout and lookaround constraints;
- builder/converter annotations.

Prefer preserving one visible specialised rule boundary in the BSR. Generated internal names should
be deterministic, but converters should not be forced to depend on encoded implementation names.

### 5. Add focused generator tests

Before migrating Swift, test:

- option and delimited examples;
- nested and recursive applications;
- repeated identical applications sharing one specialisation;
- distinct arguments producing distinct specialisations;
- invalid arity and invalid argument diagnostics;
- annotation propagation;
- BSR and tree equivalence with handwritten productions;
- ambiguous and nullable parameterised bodies.

Include a grammar-size assertion so accidental exponential expansion is caught early.

### 6. Migrate conditional compilation incrementally

First express the shared directive skeleton without removing the existing rules. Compare generated
grammar structure and run the full suite with deterministic hashing.

Migrate one body category at a time:

1. statements/file items;
2. members;
3. postfix suffixes;
4. attributes.

After each step compare acceptance, residual ambiguity and tree results against the handwritten
version. Keep category-specific admission constraints in their caller unless they are genuinely part
of the shared protocol.

### 7. Remove obsolete mechanisms only after equivalence

Once all conditional-compilation forms are equivalent, remove duplicated rule families and reassess
the remaining uses of:

- `ifConfigBody` flavors;
- the conditional-compilation line-boundary protocol;
- special lookaround routes;
- duplicated conditional-clause converters.

Removal is an outcome of demonstrated equivalence, not a prerequisite for the new facility.

## Success criteria

The change succeeds when:

- the parser, BSR and Oracle remain unaware of production parameters at runtime;
- the `#if` directive skeleton has one authoritative definition;
- all existing Swift acceptance and correctness tests still pass;
- residual ambiguity does not increase;
- produced tree shapes remain stable;
- the resulting Swift grammar is materially smaller and easier to explain;
- no new imperative special-case flags are introduced.

Performance is secondary for this feature. Grammar construction may do additional work, but parsing
should have the same runtime model and approximately the same cost as the equivalent handwritten
specialisations.

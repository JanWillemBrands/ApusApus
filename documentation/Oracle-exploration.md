# Oracle exploration

## Outcome

The dependency-Oracle experiment was removed on 2026-10-28. It established useful semantic and
performance facts, but it did not produce a replacement that was both substantially faster and
simpler than `Oracle`.

The production implementation remains `Oracle.swift`. The experiment's parallel source and tests
were deleted; fixes made independently to the production Oracle remain.

## What was tried

The experiment kept the BSR as the parse-forest representation and built a separate dependency
index for Oracle execution. It went through three representations:

1. A direct `Set`/`Dictionary` model of BSR steps, completed segments and requirements.
2. A dense model that assigned integer IDs to steps and requirements and propagated removals through
   arrays and counters.
3. A reduced sparse model using BSR values directly, resolving supporters lazily from segment maps.

It implemented structural dead-wood pruning, root reachability, `@prefer`/`@avoid`, and execution of
the remaining rule passes. Bracket-sensitive extent selection still required one compatibility walk
through the production Oracle.

The Bend twin was valuable as a semantic reference, especially for strict preference ranks and loop
round dependencies. It should specify observable pruning semantics, not prescribe Swift's runtime
representation.

## Measurements

Debug timings on two real Swift source files varied somewhat as the sources and instrumentation
changed, but the stable conclusion did not. Representative medians were:

| Implementation | `Grammar.swift` (~51k yields) | `MessageParser.swift` (~143k yields) |
| --- | ---: | ---: |
| Production Oracle | ~1.1 s | ~3.5 s |
| Dense dependency prototype | ~0.38 s | ~1.39 s |
| Reduced sparse prototype | ~0.60 s | ~2.1 s |

The dense prototype was about 2.5–2.9 times faster than the production Oracle, but the sparse model
was clearer and smaller conceptually. Simply exchanging arrays for hash tables made the same broad
dependency graph slower. Caching static grammar rule locations improved the sparse result by only
about five percent.

These figures are engineering measurements, not a maintained benchmark. Any future work must add a
repeatable benchmark target before drawing new conclusions.

## Findings

### The main cost is not ID representation

Dense IDs made propagation cheaper, but they did not change how much information was constructed or
traversed. The larger problem was building a universal dependency graph for every BSR yield even
though most disambiguation rules inspect a narrow subset of nodes and spans.

### Support and reachability are different relations

A step can need a witness to remain structurally supported without that witness being part of every
root-reachable derivation, and vice versa. Treating both as one edge relation produced incorrect loop
and nullable behavior. A future implementation must name these relations separately.

### Bracket extent needs an explicit carrier

The production Oracle deliberately retains some closure-prefix yields so bracket
`@longest`/`@shortest` can rank feasible extents. Bend's direct loop-round dependency does not need
those prefixes. Agreement must not be forced by retaining or deleting arbitrary dead BSR elements;
extent choice needs an explicit semantic carrier in both implementations.

### Preference is simple

`@avoid < plain < @prefer` is a strict three-rank comparison among sibling alternatives completing
the same span. Equal-ranked siblings stay. Bracket skipping is not a sibling. This rule does not need
a universal dependency graph.

### Static rule discovery is cheap

Separating grammar-only rule locations from per-parse snapshots is architecturally clean, but it was
not a major speedup. Raw-forest predicates and subsequent forest work dominate rule-registration
costs.

### A complete parallel Oracle would be too large

Completing the discarded design was projected to produce roughly 800–1,100 lines alongside the
existing implementation. That is the wrong maintenance trade: two overlapping semantic engines for
a measured 2–3x improvement.

## Recommendation for any future Oracle work

Do not restart with a universal graph.

1. Profile the production Oracle by rule and dead-wood phase on maintained real-source fixtures.
2. Keep rule implementations separate from structural propagation.
3. Build small, lazy indexes directly over `parser.yields`, only for rules present in the grammar.
4. After a rule removes yields, propagate from those removals through a small structural work queue.
5. Give bracket extent an explicit carrier before replacing the production reachability walk.
6. Prove each slice against Bend and compare it with the production Oracle before adding the next.
7. Use an early stop criterion: a proposed engine must be simpler and demonstrate a material
   real-source gain before it grows into a second Oracle.

The best first slice remains `@prefer`/`@avoid` plus removal-driven dead-wood propagation. It is
frequent, has simple Bend semantics, and can be evaluated without implementing every other rule.

## Conditional-compilation line boundaries

### Present situation

The former line-span rule was about 200 lines because it reconstructed a derivation through an ambiguous BSR,
tracks whether each token gap is inside delimiters, looks up the exact terminal commit for each tile,
memoises recursive grammar walks, and handles cycle cuts without caching provisional failures.

That machinery was once defensible when a deep single-line interpolation constraint used it. It no
longer does. Its last use was `compilationCondition` in `Swift.apus`.

The required Swift behavior is narrower than the annotation's generic name suggests. SwiftSyntax's
`poundIfDirective` expression flavor prevents the condition's expression spine from continuing at a
new line, while expressions nested inside delimiters use ordinary expression parsing. The initial
condition token is already guarded by `>n<`.

### Options

#### Keep the Oracle rule

This preserves current behavior with no grammar work, but retains a large recursive BSR algorithm for
one shallow language-specific use. It is not recommended.

#### Add a lexer-affecting parser flavor

A `poundIfDirective` or `noNewlineTrivia` flavor could make terminal matching reject leading newline
trivia and be cleared inside delimiters. This matches SwiftSyntax's implementation model, but it adds
a new effect to the otherwise compile-time-only flavor system and risks multiplying expression
specializations. It is viable, but more machinery than this single use warrants.

#### Express the SwiftSyntax continuation points in the grammar

This is the recommended direction. Add a scoped `poundIfDirective` flavor and a tiny conditional
zero-width layout gate built from existing features:

```apus
@flavors(poundIfDirective)
directiveLine =
    | @requiresFlavor(poundIfDirective) >n<
    | @rejectsFlavor(poundIfDirective) ""
    .
```

Set the flavor on the `compilationCondition` expression. Insert `directiveLine` at the expression
spine continuation points SwiftSyntax checks: before a postfix suffix, before an infix operator, and
before its right operand. Clear or stop carrying the flavor when entering delimited expression
contents, which already have explicit grammar productions and declared flavor scopes.

This uses the existing specialization system and existing gap predicate. It expresses the actual
Swift rule instead of asking the Oracle to rediscover token paths after parsing. It should remove:

- the generic grammar pragma and parser support,
- its `GrammarNode` property,
- the line-span Oracle rule, and
- its Oracle registration path.

### Required prototype checks

Before adopting the grammar replacement:

1. Record the current accept/reject and residual-ambiguity results for all `#if` condition fixtures.
2. Cover newlines before postfix suffixes, before infix operators, after infix operators, and inside
   calls, subscripts, tuples, collection literals and closures.
3. Verify that multiline token contents and trailing trivia after the completed condition remain
   legal.
4. Compare grammar node/copy counts and grammar-load time before and after specialization.
5. Run the full SwiftSyntax acceptance and ambiguity suites.

If the scoped flavor causes broad specialization or requires annotations throughout the expression
grammar, use a small dedicated `directiveExpression` spine instead. Do not restore a generic
post-parse BSR walker merely to avoid a localized grammar variant.

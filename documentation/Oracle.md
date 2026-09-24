# Oracle: BSR Disambiguation

The GLL parser is permissive: it finds ALL valid derivations and records them as
per-node BSR yield sets (`Set<BinarySpan>`, each span `(i, k, j)` = left extent,
pivot, right extent). The Oracle narrows that forest toward a single tree,
operating entirely on yield sets — no tree construction.

Two phases (`Oracle.disambiguate`):

1. **Prune dead wood** — top-down reachability walk from the root; drop yields not
   on any complete derivation. After this, every surviving yield is productive, so
   phase 2 can prune without destroying the only valid parse.
2. **Disambiguate** — apply grammar-annotated rules to a fixpoint, then re-prune.

## Three flavors of ambiguity

Any two distinct parse trees for the same input differ in at least one of these,
and every pragma maps to exactly one axis:

| Flavor | What varies (same node) | Pragma | Meaning |
|---|---|---|---|
| **Extent** | end `j` from a common start | `@longest` / `@shortest` | keep the longest / shortest span |
| **Pivot** | pivot `k` for a fixed span `(i,j)` | `@left` / `@right` | associativity: keep leftmost / rightmost split |
| **Alternate** | which `\|` alternate tiles `(i,j)` | `@prefer` / `@avoid` | rank alternates that tile the *same* span |

Other ambiguities reduce to these: epsilon (nullable) → extent or pivot; cyclic
(`A = A | "x"`) → degenerate alternate; Schrödinger (token duals) → alternate.

`@avoid A` is exactly the dual of `@prefer`: it is pruned wherever any sibling
covers the same `(i, j)`, i.e. `@avoid A` ≡ `@prefer` on all of A's siblings.

## Implemented rules

| Pragma | Placement | Rule / locus |
|---|---|---|
| `@longest` / `@shortest` | before a **nonterminal** LHS | `Long/ShortestMatchRule` — global: keep max/min length per start `i` |
| `@longest` / `@shortest` | before a **bracket** `[ ] { } < > ( )` | walk-local (see below) |
| `@left` / `@right` | before a group / on a nonterminal | `Left/RightAssocRule` — keep max/min pivot `k` per span |
| `@prefer` / `@avoid` | alternate prefix (after `=`, `\|`, or `(`/`[`/`{`/`<`) | `PreferRule` — same-span: prune a loser `(i,j)` where a winner covers the exact same `(i,j)` |
| `@avoid` | first token inside `[ ] { }` (optional-skip) | `AvoidOptionalRule` — legacy spelling of `@shortest` on the optional; see below |

`@prefer`/`@avoid` are **strictly same-span**. Keying on the start `i` alone was
extent-blind and silently pruned genuinely *longer* same-start neighbours (broke
`a?.b`, multi-arg subscripts). Every "prefer the longer alternate" use is `@longest`,
not `@prefer` (e.g. `functionCallArgument` for `baz(/,/)`, `genericIdentifier` for
`A<B>.c()`). A preferred/avoided alternate must be non-empty to be keyable on its
last body symbol. (LHS-position `@prefer` is a grammar-parse error; only
`@longest`/`@shortest` may prefix an LHS.)

## Extent on a bracket = a constrained optimisation

Extent on a bracket is "minimise/maximise this node's span **subject to a complete
parse still existing**" — the constraint-solver reading (objective + feasibility).
For bodies that contain an extent-annotated bracket, the phase-1 walk enumerates
complete body tilings, filters those tilings by the bracket's objective, then marks
only the surviving steps reachable. Bodies without an extent-annotated bracket keep
the cheaper frontier fold.

This unifies two apparent flavors that both have wider effect from a local
annotation (like a layout constraint):
- **siblings absorb the slack** — `@shortest [ x ] [ x ]`, `@longest { x }{ x }{ x }`;
- **the follower absorbs it** — the optional-skip: `@shortest [ prefixOperator ] postfixExpression`
  prefers the empty optional (regex wins over prefix-operator), else the shortest take.

The **optional-skip is just `@shortest` on the optional**. The Swift grammar's five
former `[ @avoid X ]` sites (`prefixExpression`, `parameter`×2, `closureParameter`×2)
are `@shortest [ X ]`. The older `[ @avoid X ]` spelling is still accepted and
compiled to `AvoidOptionalRule` (follower keep-min-pivot, alternate-aware so a
non-avoided sibling sharing a pivot is not collateral-pruned); it is behaviourally the
same as `@shortest [ X ]` for the single-body case.

Nonterminal extent stays on the global per-start rule; only brackets use the
walk-local rule (a nonterminal has many followers, so "one enclosing context" is not
defined for it).

## Moved-start extent

The tiling-wide rule handles cases where the annotated node's **start position itself
moves**, e.g.

```apus
S = [ x ] @shortest [ x ] .        // input "x"
```

The second `[ x ]`'s two readings — take `x` at `(0,1)` vs empty at `(1,1)` — live in
different midpoint choices for the preceding optional. The old head-local tiler never
compared them, so both enclosing body tilings survived. `Oracle.pruneUnproductive`
now compares the annotated bracket's consumed length across complete tilings of the
same body span, so `@shortest` keeps the empty second optional and prunes the stale
first-optional-empty/second-optional-take path.

## Operator precedence (a separate concern)

Precedence is not one problem:
- **Left-recursive** grammars (`E = E "+" E | …`) make precedence a *real* BSR
  ambiguity (pivot + alternate); the Oracle resolves it by pruning. A future `>`
  priority separator plus `@left`/`@right` would express it directly.
- **Flat-chain** grammars (Swift's `infixExpressions = infixExpression infixExpressions?`)
  have **no** parse ambiguity — one right-recursive chain. Turning it into a
  precedence-nested tree is **tree folding** done in AST generation, reading precedence
  metadata off the operator alternates — the same split as swift-syntax
  (`SequenceExprSyntax` → `SwiftOperators` folding). It is not a disambiguation step.

## Architecture

```
Parser (permissive)
  → BSR yield sets on GrammarNodes
  → Oracle phase 1: prune dead wood (+ walk-local bracket extent)
  → Oracle phase 2: rules to a fixpoint (extent / pivot / alternate)
  → DerivationBuilder (unambiguous derivation)
  → AST generator (fold flat operator chains via precedence metadata)
  → swift-syntax-style AST
```

## See also

- `Oracle.swift` — implementation (`AvoidOptionalRule`, `PreferRule`,
  `Long/ShortestMatchRule`, `Left/RightAssocRule`, the phase-1 walk + `tileBody`).
- `Trivia Oracle.md` — boundary gates (`>s<`, `<n>`, …), which are zero-width.
- `DerivationBuilder.swift` — rebuilds the tree and reports the residual ambiguities.
  (The Graphviz derivation diagram it used to emit was removed 2026-09-15; use tinyGLL's
  explorer, which outlines ambiguous nodes in orange.)
- `AdventTests/OracleDisambiguationTests.swift` — the flavor/probe suite.

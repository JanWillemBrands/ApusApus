# Oracle Disambiguation Unification — plan

**Status:** planning / pre-implementation. Work happens on an **isolated branch**.
**Goal:** make *every* Oracle disambiguation pragma (`@prefer`, `@longest`, `@shortest`,
`@left`, `@right`; `@avoid` already done) work at **any ALT-bearing node** — not just the
top-level `nt.alt` of a nonterminal, but also the alternate clusters produced by inline
`( a | b )` selection, `[ … ]` (OPT), `{ … }` (KLN) and `< … >` (POS). Expected payoff:
one uniform code path (major simplification), and grammar rules like the factored
`keyPathExpression` become expressible.

Motivating cases:
- FAILED today: `keyPathExpression = "\\" ( @prefer keyPathRootType keyPathComponents? | keyPathComponents ) .`
  — `@prefer` inside the group is inert → ambiguity explodes (1 → 40, measured).
- WORKS today: `parameter = attributes? [ @avoid parameterDeclarationModifiers ] parameterNames … .`
  — `@avoid` is nested and works, because it is the one rule already registered by a full-graph walk.

---

## Why the asymmetry exists (grounded in the code)

The rule *mechanisms* are already **level-agnostic** — they key on BSR spans/pivots `(i, j, k)`,
never on nesting depth (`Oracle.swift`):
- `pruneByExtent` (group by start `i`, keep max/min `j`) → `LongestMatchRule`/`ShortestMatchRule`
- `pruneByPivot` (group by `(i, j)`, keep max/min `k`) → `LeftAssocRule`/`RightAssocRule`/`AvoidOptionalRule`
- `PreferRule` (prune a non-preferred span `(i, j)` where a preferred sibling covers the exact same `(i, j)`)

And **Phase-1 productivity pruning already recurses through nested clusters**
(`visitAlternates` / `iterEndPositions` / `visitBracket` walk `bracket.alt`). So pruning at a
nested level is already *safe* — the "never destroy the only complete derivation" net exists.

The asymmetry is only in **registration** (Oracle `init`):

| pragma | registration site | attaches where | nested today? |
|---|---|---|---|
| `@avoid` | **full-graph walk** (`Oracle.swift:199–209`) | symbol after any bracket | ✅ yes |
| `@prefer` | walks **only `nt.alt`** (`177–193`) | non-preferred sibling's last symbol | ❌ |
| `@longest`/`@shortest` | `nt.disambiguation` on the **nonterminal LHS** (`156–161`) | the nonterminal node | ❌ |
| `@left`/`@right` | walks **only `nt.alt`** bodySymbols (`162–171`) | each body symbol | ❌ |

Attachment facts (from `ApusParser.swift` / `GrammarNode.swift`):
- `@prefer` sets `isPreferred` on the **sequence node** (`ApusParser:408`), inside `selection()` —
  which runs for `( … )` groups too. **So `isPreferred` ALREADY lands on nested alternates**; the
  grouped grammar loaded fine — the Oracle simply never scanned the cluster. → nested `@prefer` is
  almost entirely a *registration-walk* change.
- `@longest`/`@shortest`/`@left`/`@right` are read at production start (`ApusParser:185–187`) and
  stored on the LHS (`lhsNode.disambiguation`, `:363`). They are **not placeable on a cluster**
  today → nested support needs parser + model plumbing.
- Node kinds (`GrammarNode.swift:41`): `EOS T TI C B EPS N ALT END DO OPT POS KLN`.
  `isBracket = DO|OPT|KLN|POS` (`:55`); `isClosure = KLN|POS` (`:57`). Clusters carry an `.alt`
  chain (their alternates) exactly like a nonterminal.

---

## Clean end-state (the target)

**One graph walk that treats every ALT-bearing node uniformly.** For each node that owns an
`.alt` chain (a nonterminal, or a `DO`/`OPT`/`KLN`/`POS` cluster):
1. read disambiguation annotations attached to the node (`@longest`/`@shortest`/`@left`/`@right`)
   and to its alternates (`@prefer`), and
2. register the matching, already-existing rule keyed on **that node's own `.alt`** (and its
   body symbols), reusing `PreferRule`/`LongestMatchRule`/… verbatim.

This folds today's separate `@avoid` walk + the two `nt.alt` loops into a single recursion,
sharing the traversal — the "major simplification" the branch is chasing.

---

## Work plan (branch)

Tests first (this is the risky bit — lock behaviour before touching the engine):

1. **Extract** the existing pragma tests from `CoreGrammarTests.swift` (~461–562) into a new
   `OracleDisambiguationTests` suite (helpers `parsePostOracle` / `parseAndDisambiguate` in
   `TestInfrastructure.swift`):
   - `@left`/`@right`: `leftAssocPrunes`, `rightAssocPrunes`, `leftAssocFourOperands`
   - `@longest`: `longestExtent`
   - `@prefer` under OPT: `preferUnderOptFlat`, `preferUnderOptLeftRecursive`
   - `@avoid`: `avoidSkipsOptional`, `avoidKeepsTakenWhenSkipFails`
2. **Add NESTED-cluster test grammars** (the new capability), one per pragma × cluster kind,
   using tiny inline grammars — e.g.
   - `@prefer` in a selection group: `S = "\" ( @prefer A B? | B ) .`
   - `@longest`/`@shortest` on `{ }` / `< >` / `( )`
   - `@left`/`@right` on a nested cluster
   Assert both **acceptance preserved** and **residual ambiguity → expected** (mirror the
   top-level assertions).
3. **Implement** the unified registration walk in `Oracle.swift`; add parser/model support for
   cluster-attached `@longest`/`@shortest`/`@left`/`@right` (a `disambiguation` slot on cluster
   nodes + apus parse).
4. **Validate**: new suite green; then the full Swift sweep must hold **accept 0 / reject 79 /
   ambiguity 1** (run 2–3× — non-deterministic hashing is the fuzzer). Re-test the factored
   `keyPathExpression` group as the headline win.

Tiering (safe increments):
- **Tier A — `@prefer` on non-repeating selection `( a | b )`** (the `keyPathExpression` case):
  LOW risk. Registration-walk generalization only; `isPreferred` already attaches; `PreferRule`
  reused as-is. ✅ **DONE** (commit `3685f3f`). `registerPrefer(altChainHead:)` extracted and
  called per BRACKET node inside the existing `@avoid` full-graph walk. Verified: every `@prefer`
  in `Swift.apus` is a top-level nonterminal alternate (none inside an inline group), so the change
  is purely additive on the real grammar — full sweep unchanged at accept 0 / reject 79 / residual
  ambiguity 1. New nested test `preferInSelectionGroup` green.
- **Tier B — `@longest`/`@shortest`/`@left`/`@right` on clusters, incl. `{ }` / `< >`**: MEDIUM.
  ✅ **DONE**. **Design (final, pivoted from the first cut):** the extent/associativity pragmas are
  a **node-level prefix placed BEFORE the group** — `@left ( E "+" E | n )`, `@longest < word >`,
  `@shortest [ mod ] …` — mirroring the production-start form `@longest X = …` that sits before a
  LHS. (The earlier iteration parsed them as alternate-prefixes *inside* the bracket,
  `( @left … | … )`; that was replaced because "annotate the whole group" reads more naturally and
  unifies the nonterminal and bracket cases on one field.) `@prefer`/`@avoid` remain
  **alternate-level** (same-span, keyed on the last body symbol), parsed at the alternate's start.
  Implementation:
  - `ApusParser.factor()`: a `@longest/@shortest/@left/@right` pragma immediately before a bracket
    → `node.disambiguation`. `production()`'s legacy LHS form is unchanged.
  - `ApusParser.sequence()`: `@prefer` → `isPreferred`, `@avoid` → `isAvoided`, both on the `.ALT`
    node. `consumeAvoid()` still handles the distinct bracket-level `[ @avoid X ]` optional-skip.
  - `Oracle.registerNodeDisambiguation(owner:)`: reads `owner.disambiguation` off ANY owner
    (nonterminal or bracket); extent registers on the owner, assoc on each alternate's body symbols.
    `registerPrefer(altChainHead:)` now handles both `@prefer` (winners) and alt-prefix `@avoid`
    (loser ≡ prefer-the-siblings). The old `registerAltDisambiguation` is folded away.
  - **Extent now compares interval LENGTH `j − k`, not the end `j`** (`pruneByExtent(input:)`), so a
    bracket whose start moved under a variable-length prefix (the S2 case) is handled, not just the
    fixed-start S1 case.
  - **Closures honor extent.** `endPositions`/`visitBracket` read an ANNOTATED bracket's own
    Oracle-prunable yields (filtered by `k == from`) instead of recomputing the body, so an extent
    prune propagates through phase-1 and the DerivationBuilder. Unannotated brackets keep the exact
    original body-recompute path (global operator/regex reachability untouched).
  - Legacy production-start form (`@longest X = …`, `nt.disambiguation`) untouched → zero Swift.apus
    migration. **Full sweep holds: accept 0 / reject 79 / residual ambiguity 1** (28/28 Oracle tests
    green, incl. the new S1/S2 two-optional and `{X}{X}{X}` longest/shortest closure probes).

  **Findings (recorded, orthogonal to this branch):**
  1. **KLN yield-identity hazard did NOT bite** — the shared-cluster conflation concern (below) did
     not manifest, now including the `@longest {X}{X}{X}` and `@shortest {X}{X}{X}` closure-extent
     probes. Not proven safe in general; revisit if a cluster-extent over genuinely-varying
     repetition extents misbehaves.
  2. **`@right` under-prunes on 3+ operands** — `@right ( E "+" E | n )` on `1 + 2 + 3` prunes only
     1 pivot and leaves residual ambiguity (`isUnambiguous: false`), whereas `@left` fully resolves.
     Verified **level-independent** (same at top level and in a cluster), so it is a PRE-EXISTING
     `RightAssocRule` limitation, not a Tier-B/cluster issue. `rightOnCluster` therefore asserts
     `pruned > 0` (parity with the top-level `rightAssocPrunes`), not `isUnambiguous`. Fixing the
     right-assoc keep-min-pivot rule to cascade to a fixpoint is a separate task.
  3. **Alt-prefix `@avoid` on a general alt chain now works** (`oneAvoidEqualsThreePrefer` is green,
     no longer `withKnownIssue`): `S = A | B | C | @avoid D` prunes `D` via its siblings, exactly
     like marking the other three `@prefer`. Distinct from the bracket-level `[ @avoid X ]`
     optional-skip, which stays a follower-pivot rule (NOT `@shortest`) — see the finding below.

---

## The one real hazard (why this is risky)

**EBNF cluster sharing / yield identity.** Per the project's EBNF-closure work, `KLN`/`POS`
re-entry reuses a **single** CRF cluster ("cluster index is a node ref, not a position"), so a
**repetition** cluster node's yields can conflate multiple textual occurrences. Span/pivot pruning
assumes yields separate cleanly by `(i, j)` / `(i, j, k)`. That holds for **non-repeating
selection groups** (`DO`/choice) — Tier A is safe — but repetition brackets (`{ }` / `< >`) need
verification that a cluster's yields don't collapse distinct occurrences before we prune them.
Mitigation: land Tier A first; for Tier B, add repetition-specific nested tests and check
yield identity at shared cluster nodes before trusting the prune.

Also mind: `@prefer`'s preferred branch must be **non-empty** (it keys on the last body symbol);
`@prefer` is same-span only (extent preference is `@longest`'s job) — these invariants carry over
to clusters unchanged.

---

## Epsilon watertightness & the `@avoid` model (findings, 2026-08-10)

Stress suite `OracleDisambiguationTests.EpsilonAndAvoidModel`, grounded in Scott/Johnstone/van
Binsbergen "Derivation representation using binary subtree sets" (SCICO 2019): an empty derivation
is a real degenerate BSR element `(X ::= ε, j, j, j)` (§3.1 rule 1); the paper explicitly **punts**
on nullable `X ::= BBβ`, which makes `(BB,i,i)` a multigraph with two `(B,i,i)` children (§1.1 p4,
§3.2 p8: "easy to add if required"). That punt is our KLN/POS shared-cluster hazard, by name.

1. **Same-span `@prefer`/`@avoid` are epsilon-watertight.** `@prefer` keys correctly through an
   explicit-ε tail and a skipped-OPT tail: an empty alternate is an addressable `(i,i)` element on
   its last symbol, so `PreferRule` keys on it. Empty vs non-empty are different spans → no false
   cross-prune.
2. **The engine does NOT conflate nullable `A A`.** `A = "a" | ""` on `"a"` is represented as a
   genuine two-tree ambiguity — we close the gap Scott left open (no ε-multigraph collapse).

   **Regressed, then re-closed 2026-09-03 (TODO.md 23).** This claim was FALSE for a period: the
   case degraded to `(postMatch: false, isUnambiguous: true)` — the Oracle pruned away the only
   derivation *and* conflated the two ε-readings, i.e. strictly worse than Scott's punt, since the
   punt merely conflates whereas this lost the parse. Two ε blind-spots in the dead-wood passes:
   `pruneUnproductive` validated an ε alternate without marking its EPS nodes reachable (so the
   sweep deleted their yields), and `hasEmptyAlt` recognised only a syntactically empty body, not
   an alternate spelled `""` (whose body holds an EPS node). Both are fixed and
   `nullableRepetitionAmbiguity` is the standing guard.

   Note the shape of the failure for next time: an ε-related claim about the ENGINE was recorded
   here as settled, while the only thing keeping it true was a test nobody was reading as red.
3. **`@avoid A` ≡ `@prefer` on all siblings** for **same-span** groups (the "3 = 1" equivalence
   holds via `PreferRule`, winners unranked). ✅ **Now implemented**: alt-prefix `@avoid` is parsed
   in `sequence()` (→ `isAvoided` on the `.ALT` node) and compiled in `registerPrefer` as
   "prefer the siblings", so `S = A | B | C | @avoid D` prunes `D` exactly like marking the other
   three `@prefer`. `oneAvoidEqualsThreePrefer` is green (the `withKnownIssue` is removed). This is
   the **alternate-level** `@avoid`, distinct from the **bracket-level** `[ @avoid X ]` optional-skip
   consumed by `consumeAvoid` right after `[`/`{`/`<` (a follower-pivot rule — see below).

### Should Swift.apus replace `[ @avoid X ]` with `@shortest [ X ]`? — **No.**

They are equivalent **only locally**, when skip and take converge to the **same end** (verified: the
two original `@avoid` cases pass with `@shortest`). But the two rules differ in *scope*:
- `@avoid` = `pruneByPivot` on the **following symbol**, grouped by the follower's `(i,j)` — surgical:
  it only pits skip against take when they reach the **same overall span**.
- `@shortest [X]` = `pruneByExtent` on the **OPT node**, grouped by the OPT's **start `i`** — coarser:
  it prunes *every* take `(i,m)` in favour of skip `(i,i)` from that start, **ignoring the follower**.

Swift.apus's five `@avoid` uses (`prefixExpression`, `closureParameter`×2, `parameter`×2) are
*deliberately* shared-end (the comments at `Swift.apus:899,1620` engineer a "common end" so
`pruneByPivot` groups correctly), so a swap would *probably* hold — but `@shortest` is a blunter
instrument with real over-prune risk if any optional-start ever has take-readings that complete at
different extents, it buys nothing, and `@avoid` already works. **Keep `@avoid`.** The valuable
direction is the opposite: generalise `@avoid` to any alt chain as "prefer the siblings" (finding 3),
not replace it with `@shortest`.

### Open shape: conditional same-span sibling choice (`@avoidIf`?)

The remaining `testInverseTypes#3`-class problem exposed a gap between the existing
same-span mechanisms:

- `@left` / `@right` choose between **same node, same span `(i,j)`, different pivot `k`**.
- `@prefer` / alternate-level `@avoid` choose between **sibling alternates that tile the same
  span `(i,j)`**, unconditionally.
- `@cannotParse(N)` / `@canParse(N)` are start predicates: they ask whether `N` can parse at
  the alternate's start, not whether `N` covers this alternate's exact span.

`[any P & ~Copyable]()` wants a conditional same-span sibling choice:

```apus
arrayLiteralItem = @prefer expression .
arrayLiteralItem = typeExpression .
```

The expression route is normally preferred because swift-syntax spells array elements such as
`(Int, Double) -> Bool` as a `SequenceExpr`, not a `TypeExpr`. But when the exact array element
span is also a `boxedProtocolType` (`any P & ~Copyable`), swift-syntax keeps it as one
`TypeExpr(SomeOrAnyType(CompositionType))`, not `(any P) & ~Copyable`.

The current `@cannotParse(boxedProtocolType)` is too blunt here: it prunes by start position and
can destroy the full parse. The current working fix is deliberately local in
`GenerateSwiftSyntaxAST`: when converting an array element through the preferred `expression`
alternate, it checks whether the post-Oracle forest still contains a full-span
`boxedProtocolType` yield and emits that as a `TypeExpr`. This is acceptable as a narrow tree
fidelity bridge because it does not affect parsing, acceptance or Oracle pruning, but it is a
conversion-time parse-shape choice and should not become the general pattern.

If this recurs, the orthogonal Oracle primitive is likely a conditional same-span alternate
constraint, for example:

```apus
arrayLiteralItem = @avoidIf(boxedProtocolType) @prefer expression .
arrayLiteralItem = typeExpression .
```

Semantics sketch:

```text
@avoidIf(N) on alternate A:
  prune A's yield (i,j) iff N has a yield with the exact same (i,j).
```

This is closer to `@prefer`/`@avoid` than to lookahead: it is an equal-span sibling/tree-shape
selector, analogous to `@left`/`@right` choosing a pivot for a fixed span. Keep it distinct from
start-based parse predicates (`@cannotParse`) and from containment predicates
(`@confinedTo`/`@excludedFrom`). Do not add it for one isolated case; look for at least one more
concrete use, probably another equal-span type/expression or key-path-root ambiguity.

---

## Key file references

- `Oracle.swift`: rules (`28–98`), registration `init` (`152–210`), Phase-1 `pruneUnproductive`
  (`268–453`, already cluster-aware).
- `GrammarNode.swift`: kinds `:41`, `isBracket` `:55`, `isClosure` `:57`, `isPreferred` `:161`,
  `isAvoided` `:169`, `disambiguation` `:200`.
- `ApusParser.swift`: disambiguation pragma parse `:185–187` + LHS attach `:363`; `@prefer` attach
  `:405–409`; `@avoid` (`consumeAvoid`) `:639–696`.
- Tests: `CoreGrammarTests.swift:461–562`; harness `TestInfrastructure.swift:237` / `:261`.

**Repo state at plan time:** `main` at the pushed grammar-cleanup commit (+ the `operatorBody`
`.matchingSemantics` tidy, now pushed). This unification proceeds on a fresh isolated branch.

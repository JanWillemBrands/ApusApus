# The rise and fall of Schrödinger, Frankenstein and other dead-ends

A short obituary of mechanisms this project invented, shipped, and later retired or
superseded. Kept so we don't re-invent them. (Absorbs the old `Schrodinger Tokens.md`
and `Frankenstein Tokens.md`.)

The recurring lesson: **most of these existed to fake sub-token granularity or to
patch ambiguity from a remote site. The LCNP / multi-lex rewrite (`CharPosition =
String.Index`, an on-demand parser-driven lexer) and the on-the-term Oracle
annotations made them unnecessary.**

---

## Frankenstein tokens — *dead, fully removed*

**What it was.** A partial-token sentinel (`≋`) plus bit-packed `Int32`
token-index + sub-index positions (stride / negative-position schemes, on-the-fly
remainder), so a single lexed `>>` could be split into `>` `>` to close nested
generics (`Array<Array<Int>>`).

**Why it died.** All that machinery existed only to express a position *inside* a
token when positions were token-indices. LCNP made `CharPosition = String.Index`, so a
split just ends at an ordinary character position — the short `>` at `[p,p+1)`, the
next at `[p+1,p+2)`, both plain positions the descriptor/CRF/BSR keys already handle.

**What replaced it.** Default maximal munch (`@literalMunch`) + munch-exempt
single-char regex terminals (`closeAngle - />/`, `openAngle - /</`). No sub-token
positions, no sentinel. Zero references remain in the source.

## Schrödinger tokens — *the runtime object is gone; the concept lives on differently*

**What it was.** The eager scanner emitted, at one position, a token carrying a
`.dual` pointer to an alternative reading when two terminals matched the **same span**
(e.g. `if` as keyword vs identifier). The GLL parser explored both.

**Why it declined.** The eager single-committed-token-stream scanner was replaced by
the on-demand LCNP lexer, which simply *returns multiple matches* for a position —
there is no dual-linked token object to carry around.

**What remains.** Only the *concept* of same-span overlap, handled two ways:
a load-time diagnostic (`GrammarDiagnostics.detectSchrödingerConflict`, warns about
overlapping terminals) and the `---(…)` **exclusion** annotation that suppresses the
unwanted reading in context. (Strictly-shorter prefixes are a *different* problem,
solved by maximal munch — see `TODO.md` #0.)

## `@unless(X)` — *dead, retired 2026-07-30*

**What it was.** An alternate-level predicate: prune this alternate when nonterminal
`X` could start where the alternate ends (encoding swift's `canParseAsXxx`). Used 3×
for `@unless(genericArgumentClause)` (`Foo` vs `Foo<Int>`).

**Why it died.** (1) Readability — it pointed at a *remote* target, away from the term
it affected. (2) Its job split cleanly between the two on-the-term annotations:
extent preference is `@longest`'s job, same-span preference is `@prefer`'s. The generic
cases migrated to `@longest genericIdentifier`/`moduleGenericIdentifier`, leaving
`@unless` used by no grammar. Retired; engine scaffolding deleted.

**What replaced it.** `@longest` / `@shortest` (extent), `@prefer` (same-span),
`@avoid` (optional-skip) — all placed **directly on the affected term**.

## `@within(Ctx)` / `WithinRule` — *dead, retired 2026-08-23*

**What it was.** A production-level prefix (`@within(Ctx…) LHS = rhs .`) marking a POST-PARSE
FILTER production. The Oracle compiled it to a `WithinRule` that, for each `LHS` yield contained
in ALL of `Ctx…`'s BSR extents, evaluated a boundary gate declared in the filter RHS and removed
the yield if it failed. It carried the B2 trailing-closure-in-condition rejects (disc-1 newline-
after-`{`, disc-3 `}`→`else`).

**Why it died.** The gate was **procedural**: `WithinRule.gateFails` re-scanned the raw input
(`wordAt`, `openBraceStartsNewLine`) and pattern-matched two hardcoded gate shapes — violating the
invariant *the Oracle never re-reads input*. It was also a bespoke second mechanism for containment
that overlapped the declarative predicate family.

**What replaced it.** The **grammar-predicate lookahead** family (`Ambiguity.md`): `@confinedTo(N)` / `@excludedFrom(N)` containment (a `ContainmentRule` BSR query) plus
the token-set `>->`/`>+>` forward gate — which now fires at **nonterminal completion** too
(`MessageParser.forwardGateAllows`, wired at the CRF continuation sites), not just after a terminal.
B2 became two disjoint partitioned alternates + `@excludedFrom`; both discriminators are now fully
declarative with no Oracle input re-read. Engine scaffolding (`WithinRule`, `registerFilter`,
`Grammar.FilterProduction`/`grammar.filters`, the production-level `@within` parse) deleted.

## Scanner-mode annotations `>>>` / `<<<` / `===` — *two rises, two falls*

Scanner modes are a stack of lexer states (à la ANTLR modes / Flex start conditions):
a terminal can be gated to fire only in a given mode, and can push/pop the stack after
it matches. The point was context-sensitive lexing — most famously **nested multiline
comments** (`/* … /* … */ … */`), where a flat regex can't count depth.

**Rise 1 — bare `>>>` / `<<<` (ungated push/pop).** The first form was just
`>>> "mode"` (push) and `<<<` (pop) hung on a terminal, with mode membership implied.
**Fall 1.** This **conflated the pre-filter with the post-action**: whether a terminal
was *eligible* in the current mode and what it *did* to the stack were tangled
together, so when `multilineCommentText`'s regex won longest-match but its state check
failed there was no fallback → **19 test regressions**, needing try/rollback.

**Rise 2 — gated transitions `===` (the current form).** The fix (2026-04-28) made the
annotation a structured triple `(gate, pop, push)` and cleanly **separated pre-filter
from post-action** — see `apus.md` and `Scanner Mode Design.md`:

| Syntax | Meaning |
|--------|---------|
| `=== "X"` | eligible only in mode X (pre-filter — regex never even runs otherwise) |
| `=== "X" >>> "Y"` | eligible in X, **push** Y after match |
| `=== "X" <<<` | eligible in X, **pop** after match |
| `=== "X" <<< >>> "Y"` | eligible in X, **replace** X with Y |

The gate is checked *before* matching, so the post-action's pop/push is unconditional
(the stack was already verified) — no rollback. `>>>`/`<<<` survive, but only ever as
the post-action half of a `===`-gated triple; the **bare, ungated** forms are gone.
This mechanism is alive and correct, and is how f-string-style mode switching would be
expressed.

**Fall 2 — Swift stopped using scanner modes at all.** For the flagship case (nested
multiline comments), even the gated-transition version — *three* mode terminals +
*six* `===` annotations — was **retired (Jun 13 2026)** in favour of a single recursive
trivia non-terminal that lets the ordinary GLL machinery count the nesting:

```apus
multilineComment structured : "/*" { /(?s)(?:[^*\/]|\*(?!\/)|\/(?!\*))+/ | multilineComment } "*/" .
```

Recognised as trivia during `OnDemandLiteralLexer.skipTrivia`. So `Swift.apus` no longer
carries a single scanner-mode annotation. **Lesson:** if the only reason you reach for
a lexer mode is *recursive nesting*, a recursive grammar rule is simpler and needs no
lexer state at all. Modes still earn their keep for genuinely *non-recursive* state
switches (string ↔ interpolation-expression ↔ format-spec), which is why the mechanism
stays.

---

## Postfix chain as an ITERATION — *tried 2026-10-02, not adopted*

**What it was.** swift-syntax parses postfix suffixes as a loop
(`parsePostfixExpressionSuffix`) with three exit conditions, one of them a cardinality
rule:

```swift
if let implicitCall = self.parsePostfixExpressionTrailingClosureSuffixIfPresent(…) {
  leadingExpr = implicitCall
  // We only allow a single trailing closure on a call.  This could be
  // generalized in the future, but needs further design.
  if self.at(.leftBrace) { break }
  continue
}
```

We model the same chain as LEFT RECURSION (`postfixExpression` + five
`postfixExpression <suffix>` rules), and left recursion cannot say "stop iterating".
Every loop exit therefore has to be re-expressed as something else — the `{`-cardinality
one became a `>n<` layout gate, which is an invention with no counterpart in the
reference. The idea: make the chain an iteration, so the cardinality rule becomes a
restriction on the suffix SEQUENCE and thus plain CFG:

```
postfixExpression = primaryExpression postfixSuffixes? .
postfixSuffixes = postfixSuffix postfixSuffixes?
                | closureSuffix                              // terminal: nothing may follow
                | closureSuffix postfixSuffix postfixSuffixes? .   // …except a non-closure suffix
```

**Why it was not adopted.** The analysis is right — "no two closure suffixes adjacent"
IS expressible this way, with no annotation. But the postfix chain carries several other
constraints, and the iteration redistributes rather than removes them:

* a call suffix ABSORBS its own trailing closure (`parsePostfixExpressionCallSuffixIfPresent`
  → Expressions.swift:866), so `callSuffix = functionCallArgumentClause trailingClosures?`
  overlaps with a following `closureSuffix` — `f(a: 1) { x in }` became
  `postfixSuffix ambiguous pivot`, measured. Removing the overlap needs TWO call-suffix
  variants (with/without closure) plus a no-leading-closure suffix list;
* B1 (a bare literal callee may not take a trailing closure, `1 {}`) lived in
  `nonLiteralPostfix`; under the iteration it needs its own split of the base;
* 588 → 594 rules in the prototype, BEFORE fixing either of the above;
* the converter resolves this family by NAME in 16 places and would become a left FOLD
  over suffixes instead of recursive descent on nested nonterminals.

**What we kept instead.** `>n<` on the parenless trailing-closure alternate only, chosen
on measurement: on 400 corpus files containing a `)`/`}` line followed by a `{` line it
scores 392 `same` against the gateless version's 391, and it keeps
`ExpressionTests.testClosureLiterals#3` passing. Two known divergences are documented at
the rule (`f(1) {}⏎{}` does not chain; `x.map⏎{…}` does not attach).

**The general lesson.** When the reference ITERATES with per-suffix break/continue rules,
left recursion loses exactly the break. `compilationCondition`, `statements`/`members`
and this all share that shape; the first two were fixed by iterating, this one is the case
where the surrounding constraints make the trade negative.

**Correction (2026-10-02).** The rule is NOT a cardinality — not "at most one closure
suffix per chain". `x.map {}.filter {}.sorted {}` has three and is legal; the reference
`break`s only when the next token is `{`, so a `.` lets the chain continue. It is an
ADJACENCY rule: no two closure suffixes in a row. An `@once`-style primitive would have
rejected that line. What the shape really wants is associativity as a FILTER, which is
what `@left`/`@right` became — see `apus.md`.

## Shorter obituaries

| Idea | What it was | Why it died / replacement |
|------|-------------|---------------------------|
| **Distance-2 lookahead** `>>2` `++2` `--2` | two-token lookahead/behind | nothing used it; scheme is distance-1 only |
| **Old spellings** `>>1`, `++1`/`--1` | pre-unification lookahead/behind | → `>+> >-> <+< <-<` (see `Ambiguity.md` §4.2) |
| **Start-keyed `@prefer`** | prune any loser sharing start `i` (extent-blind) | broke `a?.b`, multi-arg subscripts → narrowed to strictly same-span; prefer-longer → `@longest` |
| **`@greedy(class)` / `<suffix>`** | opt-in maximal munch | dropped for always-on default munch via `@literalMunch` |
| **Probe-alphabet / `regexExtenders`** | space-boundary munch heuristic | replaced by running the faithful `@literalMunch` regex directly |
| **Explicit Unicode-range regex classes** | faithful ident/operator code-point ranges in a Swift `Regex` | Swift `Regex` rejects canonically-decomposable range bounds → `\p{…}` approximation now; interval-table primitive is the endgame (`TODO.md` #8) |
| **`distributedPackedBySlot` dedup** | per-slot descriptor dedup mode | benchmarked identical to the global set → removed |
| **Eager single-token-stream scanner** | commit one token stream up front | → LCNP on-demand, parser-driven multi-lex |

---

*See `Ambiguity.md` for the surviving lookahead scheme and disambiguation annotations, and `TODO.md` #0 for maximal munch.*

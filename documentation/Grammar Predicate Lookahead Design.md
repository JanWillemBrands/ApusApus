# Grammar-Predicate Lookahead

**Status:** built & validated, 2026-08-23. Supersedes the retired `@unless` and the procedural
`@within` filter (now deleted) for the lookahead/lookbehind family. Companion: `Oracle.md`.

## What it is

A single declarative primitive for "commit to this reading **iff** grammar symbol `N`
does / does not derive at this point" — the general form of swift-syntax's ~32
`canParseAsXxx` / `atStartOfXxx` predicate-gated choices. The condition is an ordinary
grammar symbol, evaluated by the parser we already ran; there is no hand-written Swift
predicate.

It fills the gap that extent/associativity annotations cannot reach: `@longest`/`@shortest`
choose an **extent**, `@prefer` chooses among **same-span** alternates, `@left`/`@right`
choose a **pivot**. None can express "pick reading A here *because* `N` can (or cannot)
parse here" — a **conditional** choice. That condition is the payload swift-syntax's
recursive descent carries in its lookahead routines, and it is what this primitive adds.

## Current spelling

Oracle parse predicates use `@word` spelling. The old leading symbolic spelling
`>+>(N)` / `>->(N)` was retired for nonterminal operands so symbolic lookaround can
mean token lookaround only.

The annotation is written at the start of an alternate; its position is the
alternate start `p`:

| annotation | reads as | holds iff |
|---|---|---|
| `@canParse(N)` | *N must start here* | some yield of `N` **starts** at `p` |
| `@cannotParse(N)` | *N must not start here* | no yield of `N` starts at `p` |

## Uniform anchoring

All four share **one anchor `p`**. Direction does not move the anchor — it only selects
which end of the target's yield is compared to `p`:

- **forward** tests the target yield's **start** (`i == p`);
- **backward** tests the target yield's **end** (`j == p`).

Positive asks "does such a yield exist?", negative asks "is there none?". That is the whole
semantics: one position, one existence question over the yield set, two coordinates. There
is no separate scanner-time or terminal-definition anchoring — every case is the same
query at the same `p`.

## Operand shape

`N` is a **single grammar symbol** — a terminal (`"else"`, or a named terminal) or a
nonterminal (`expression`, `declaration`). Not an arbitrary inline fragment: the query path
needs a named, yield-bearing node to look up, and every swift-syntax predicate gates on one
nonterminal or one token anyway. For a composite condition, **name it** — declare
`elseBranch = "else" ifStatement .` and write `>->(elseBranch)` — which keeps the operand a
single symbol, gives it a yield node, and makes it reusable.

Evaluation splits by kind: a **terminal** operand is a lexical peek (is that token at `p` —
cheap, and free of derivation circularity); a **nonterminal** operand is the yield query /
seeded sub-parse below.

## Evaluation

The answer to "does `N` derive at `p`?" is already latent in a general parser that
produced all derivations, so evaluation is a **yield-set query**, not a re-scan:

- **Reachable target (default).** When the main grammar already attempts `N` at `p`, its
  yields are in the BSR. The query is an indexed membership test (`i == p` forward,
  `j == p` backward). For *disambiguation* this is always the case by construction: a
  predicate chooses among readings that compete here, and a reading that competes here was
  parsed here, so it yielded here.
- **Unreachable target (on-demand fallback).** When `N` is *not* otherwise attempted at
  `p`, seed an isolated GLL sub-parse from `(N, p)` — the same mechanism that runs
  structured `-`/structured `:` lexical sub-parses — collect whether `N` yields, memoise `(N, p) → Bool`,
  discard. The sub-parse honours every parse-time gate natively (it *is* a parse), so there
  is no procedural re-derivation of the condition.

**An empty yield set is ambiguous**, so the choice between the two is *not* "query, then
sub-parse if empty." Empty can mean "`N` was attempted and failed" (a real **false**) OR
"`N` was never attempted here" (the query is **blind**). These are indistinguishable from
the yields alone. The selector is therefore a **static property of the predicate site**:
if `N` is provably attempted at the anchor (the disambiguation case — `N` is a
sibling/reachable reading, so the parser necessarily created descriptors for it at `p`),
the query is authoritative and no sub-parse runs; otherwise the sub-parse is seeded
on demand.

**Invariant.** A predicate's target must be *parsed at `p`* — reachable (queried) or seeded
(sub-parsed). Nothing is deduced by re-scanning the input. A predicate whose target the
grammar never attempts at `p`, and which is not seeded, is a specification error, not a
silent false.

## Token lookaround is a sequence predicate

`>->("else")` and the other symbolic lookaround forms are token lookaround. They are
zero-width predicates in the sequence, evaluated locally at their boundary. Nonterminal
operands use the Oracle spelling instead: `@canParse(N)` and `@cannotParse(N)`.

This keeps the two mechanisms separate: symbolic lookaround talks about nearby tokens;
Oracle parse predicates talk about whether a nonterminal has a yield starting at the
alternate boundary.

## Containment (the fifth relation)

Some rules are valid/invalid depending on the **context they sit in** (swift-syntax's
inherited `ExprFlavor`, an enclosing member block, a function body). That is a **containment**
relation: the guarded span `[i,j]` is inside a yield `[a,b]` of `N` when `a ≤ i ∧ j ≤ b`.

It is **not** a grammar rewrite. The annotated alternate is an ordinary CFG alternate that
parses freely and adds its yields to the forest (it *augments*); the annotation is a
**post-parse filter** that removes some of those yields by where their span sits in the
derivation tree. The grammar stays context-*free*; the context-sensitivity lives entirely in
the Oracle reading the BSR — which is why it composes with GLL's "produce all derivations."
Nothing supersedes another rule; the annotation gates only its own alternate.

It has the same `+`/`-` polarity as the lookahead glyphs, keyed on the alternate's first body
symbol, stackable (stacking = conjunction over the containers):

| annotation | polarity | keep the alternate's yield `[i,j]` iff |
|---|---|---|
| **`@confinedTo(N)`** — valid ONLY inside `N` | positive | `∃` an `N`-yield `⊇ [i,j]` |
| **`@excludedFrom(N)`** — invalid inside `N` | negative | `∄` such an `N`-yield |

## Boundaries fold into nonterminals — the Oracle never re-reads input

Some rejects combine a context with a **boundary** (a `}` followed by `else`; a `{` that
opens with a newline). The boundary is **never evaluated in the Oracle**. It is folded into a
real, parsed nonterminal whose gate fires at **parse time** like anywhere else; the Oracle
then does a plain yield query on that nonterminal.

- **Layout boundary** (`<n>`/`>n<`) *must* fold — layout is a trivia fact, not a derivation:
  `newlineOpenedClosure = "{" <n> … "}"` parses only newline-opened closures.
- **Token boundary** (`}`→`else`) is a parse-time forward gate: `>->("else")` / `>+>("else")`
  fires when the closure nonterminal completes (the CRF `forwardGateAllows` site), partitioning
  `trailingClosures` into two disjoint alternates. The Oracle sees only the yields the parser
  chose to produce and does plain `@excludedFrom` containment — no end-query, no token peek.

**Invariant (hold the line):** every predicate the Oracle evaluates is a BSR yield query —
containment (`⊇`), start (`i==p`), end (`j==p`), or same-span co-occurrence. The parser
evaluates all layout/token gates. **Nothing in the Oracle re-reads the input.** (This is
exactly what the old procedural `@within`/`WithinRule` got wrong — it re-scanned trivia and
pattern-matched two hardcoded gate shapes.)

## Worked examples

`open⏎var foo` — `open` is a contextual keyword (a legal identifier) *and* a modifier, so
Advent finds both "one declaration `open var foo`" and "bare `open` reference + `var foo`".
swift-syntax routes to the declaration (`atStartOfDeclaration`). Declaratively:

```apus
statement = @cannotParse(declaration) expression .   // expression-statement only where a declaration does NOT start here
```

`testEnum11` — a top-level `case` is not a declaration; it's valid only inside a member block:

```apus
declaration = @confinedTo(memberDeclaration) enumCaseDeclaration .
```

`init {}` — a bare `init` reference is valid only inside a body (implicit `self.init`); the
same `@confinedTo` shape once the container nonterminal is chosen.

B2 (trailing closure in a condition) — the mixed case: containment + boundary. The `<n>` and the
`>->`/`>+>("else")` gates all fire at PARSE time; the Oracle only does `@excludedFrom` containment:

```apus
newlineOpenedClosure = "{" <n> closureSignature? statements? "}" .

// disc-3 — trailingClosures partitioned by the (now live at nonterminal completion) else-gate:
trailingClosures = closureExpression >-> ("else") labeledTrailingClosures? .                              // not before else — always OK
trailingClosures = @excludedFrom(conditionExpression) closureExpression >+> ("else") labeledTrailingClosures? .  // before else — pruned in a condition

// disc-1 — newline-opened closure is not a trailing closure / condition body:
closureExpression = @excludedFrom(conditionExpression) @excludedFrom(trailingClosures) newlineOpenedClosure .
```

## Why this is good

- **Declarative & faithful.** The condition is a grammar symbol evaluated by the real parser —
  exactly swift-syntax's predicate-gated choice, which CFG shape + extent/pivot/same-span
  annotations cannot express. No hand-written predicate, no input re-scan.
- **Uniform.** Five relations (forward/backward start-of / end-of, containment), both
  polarities, all one query family over the BSR. Terminal operands are the degenerate case.
- **Language-agnostic.** A C++/Rust grammar writes `@excludedFrom(theirNT)` / `>->(theirNT)`
  over its own symbols; the engine evaluates predicates generically, no per-language Swift.
- **Cheap.** The BSR is the memo; for disambiguation the answer is already computed.

## Status & remaining work

**Built and validated:**

- Parse predicates `@cannotParse(N)`/`@canParse(N)` with nonterminal operand, Way-1 BSR query
  (`LookaheadPredicateRule`) — fixes `open⏎var`.
- **Both containment polarities** `@confinedTo(N)` / `@excludedFrom(N)` (one `ContainmentRule`
  with a `negated` flag; positive prunes where ¬contained-in-all, negative prunes where
  contained-in-all). RHS-alternate placement (parsed in `sequence()` alongside `@prefer`/`@avoid`;
  fields `GrammarNode.confinedToContainers` / `.excludedFromContainers`; registered on the
  alternate's first body symbol). `@confinedTo(memberDeclaration)` fixes `testEnum11`;
  `@excludedFrom` has no customer until B2. (2026-08-22, increment A — behaviour-neutral,
  probe-confirmed.)

- **The B2 rewrite (increment B).** Both discriminators are now fully declarative — normal
  partitioned alternates that the parser produces and `@excludedFrom` prunes; NO procedural filter,
  NO Oracle input re-read. (2026-08-23, probe-confirmed; full sweep: accept-failures 0, reject count
  in-band, `testTrailingClosureInIfCondition#1` and `testTrailingClosureInGuard#1–4` REJECT,
  statement-level `foo {⏎ bar⏎}` ACCEPTs, `testEnum11` still rejects top-level `case`.) It rests on
  one engine addition and two grammar partitions:

  1. **Forward gate at nonterminal completion.** The token-set `>+>`/`>->` gate was always a
     PARSE-TIME follow gate, but it only fired after a *terminal* (inline in `tokenMatch`). It now
     also fires at *nonterminal / bracket completion* via a single shared helper
     `MessageParser.forwardGateAllows(slot:at:)`, called at the four CRF continuation sites
     (`call` pop-replay, `rtn`, `bracketCall`, `bracketRtn`) alongside `continuationViable`. One
     logical gate, one helper; the two invocation points only exist because GLL surfaces "the
     position after this slot" at different moments for terminals (inline) vs nonterminals (CRF
     return). This honours the invariant *the Oracle never re-reads input*: a token-set lookaround is
     a scanner query and belongs at parse time; only the nonterminal-*derivation* predicate
     (`@cannotParse(N)`) is an Oracle BSR query.
  2. **disc-3** (`}`→`else`): `trailingClosures` is partitioned by the now-live gate into two
     disjoint alternates, and `@excludedFrom` prunes the `else`-following one inside a condition:
     ```apus
     trailingClosures = closureExpression >-> ("else") labeledTrailingClosures? .
     trailingClosures = @excludedFrom(conditionExpression) closureExpression >+> ("else") labeledTrailingClosures? .
     ```
  3. **disc-1** (newline-after-`{`): the layout is folded into a real nonterminal so `<n>` fires at
     parse time, and `@excludedFrom` prunes it in a condition / as a trailing closure:
     ```apus
     newlineOpenedClosure = "{" <n> closureSignature? statements? "}" .
     closureExpression    = @excludedFrom(conditionExpression) @excludedFrom(trailingClosures) newlineOpenedClosure .
     ```
  The procedural path is deleted: `WithinRule` (`Gate` enum + `openBraceStartsNewLine`/`wordAt`
  input re-reads), `registerFilter`, `Grammar.FilterProduction`/`grammar.filters`, and the
  production-level `@within` parse in `ApusParser.production()`. `Within Filter Design.md` is
  superseded by this section.

**Remaining:** backward `<+<(N)`/`<-<(N)` with nonterminal operands and the Way-2 seeded sub-parse
are designed but unbuilt — no customer yet.

**Methodology note:** the reject-count seed variance (~54–57) means per-fix progress is measured by
snippet-level probes, not the aggregate count. (Worth capturing in `TESTING.md`.)

---

## Mimicking a deterministic parser: cuts with local viability tests

*(2026-08-29. Written after the C3 regex work; reframes C1, C3 and the B2 family as ONE problem and
records why the annotation family above cannot solve it.)*

### The pattern

Every persistent over-accept against swift-syntax has the same shape, and none of them is really
about the construct they appear in (regex, key paths, trailing closures):

> **swift-syntax's accepted language is defined by an ALGORITHM, not by a grammar.** It is
> deterministic recursive descent: at each decision point it commits to one alternative using a
> LOCAL test (a lookahead token, a `canParseX` probe, a lexer scan) and never reconsiders. Its
> language is "the inputs for which *that strategy* succeeds" — strictly smaller than the language of
> the underlying CFG.

Advent is a general parser: it explores all alternatives and accepts if **any** completes. So the
over-accepts are not scattered bugs; they are systematically the inputs where swift commits and then
errors, while a *different* derivation still completes. `\Foo.Bar.?.[1]` (C1), `/foo/{}`,
`qux(/, "(")/2`, `^/"/"`, `^/"[/"` (C3), the B2 condition trailing closures — one phenomenon.

### Why the annotations above cannot express it

Everything in this document, plus `@prefer`/`@avoid`/`@longest`/`@shortest`/`@left`/`@right`, is a
**post-parse filter over SURVIVORS**: it chooses among readings that reached the forest.

But the defining feature of the divergence is that the reading which should WIN **has already died**.
There is nothing to prefer it over. That is why `@longest` cannot see the greedy keypath in C1, why
the prototyped straddle rule fired with correct data yet changed nothing, and why the
lexicalisation-DAG reframing collapsed (see REJECTS.md C3). Three failures, one structural mismatch:

| | question answered |
|---|---|
| survivor-filtering (all current annotations) | which of the COMPLETED readings do we keep? |
| determinism (swift) | which alternative do we COMMIT to, before knowing who completes? |

No amount of the former expresses the latter.

### The mechanism: a cut

What is missing is **prioritized choice with commitment**. At a decision point: an order over
alternatives plus a *local* viability test. The first viable alternative wins and its siblings are
pruned **at decision time** — even if the winner later fails, in which case the parse fails, which is
exactly how swift produces its error.

`@preempt(X, N)` is the first instance, and its three parts are the general parts:

1. a **priority** (regex over operator),
2. a **local viability test** (the memoised speculative recogniser sub-parse — the general form of
   swift's `canParseX`),
3. pruning that **survives the winner's failure** (why the viability query must read the RAW forest,
   and why the recogniser must be exempt from the FOLLOW/predict gates).

What is ad hoc about it today is only that it is wired to ONE choice point — an operator token's
extent. The general form applies at any choice point, including a nonterminal's alternates.

This is deliberately **un-general parsing at named points**, and each cut must be justified against
the specific swift decision procedure it mirrors. That is the price of mimicking an algorithm; the
benefit is that it is declarative and language-agnostic (a C++/Rust grammar writes its own cuts).

### The distinction that matters: grammar ≠ viability test

Two different questions, easy to conflate — and conflating them is how the C3 work went wrong:

- **What is well-formed?** → the grammar. Strict, faithful, and it must NOT be loosened.
- **What would swift commit to here?** → the cut's viability test, which mirrors swift's own test and
  is frequently **weaker** than well-formedness.

Worked example (`151a/b`, `_ = ^/"[/"`). swift's test is a lexer scan — "is there a regex-shaped
lexeme here?" — which does not require a well-formed body; it then commits and errors on the body.
Advent's current test is "does the regex CFG parse?", strictly stronger, so the cut never fires and
the `^/`-operator reading survives. The tempting fix — admit `[` as a plain regex atom so the body
parses — was **tried and rejected**: it buys 41 → 39 rejects but costs `ambiguity 2` (`/([)])/` gains
a second reading), and more importantly it degrades the balance-aware regex CFG toward "scan to the
next `/`", which is precisely what the CFG existed to avoid. There is no floor to that slope.

**The correct fix keeps the grammar strict and weakens the TEST**: give `@preempt` a lexeme-level
viability scan. Predicted outcomes, all consistent and nothing loosened:

| input | lexeme scannable? | cut fires? | result |
|---|---|---|---|
| `_ = ^/"[/"` | yes | yes | body `"[` malformed → no parse → **reject** ✓ |
| `_ = ^/x` | no closing `/` | no | `^/` operator stands ✓ |
| `_ = /foo/ {}` | yes | yes | regex fine, but `{}` cannot follow → reject ✓ |

### Next step

Implement the lexeme-level viability option for `@preempt` and re-test `151a/b`. Falsifiable: it
should reach reject 39 with **accept 0 and ambiguity 0** — the ambiguity is the discriminator against
the grammar-loosening version, which reached 39 but at `ambiguity 2`.

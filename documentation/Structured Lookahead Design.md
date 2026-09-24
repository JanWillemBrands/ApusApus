# Structured Lookahead Design

> ## Status (authoritative, 2026-07-30) — what is ACTUALLY implemented
>
> The lookahead/lookbehind primitive that shipped is a **directional-polarity,
> distance-1** family — NOT the `@unless(X)` design that most of this document explores:
>
> | Token | Meaning | Direction | Polarity | Fires where |
> |-------|---------|-----------|----------|-------------|
> | `>+>(set)` | next token MUST be in set | forward | positive | on a terminal-use, in `MessageParser.tokenMatch()` (predict-set override) |
> | `>->(set)` | next token MUST NOT be in set | forward | negative | on a terminal-use, in `tokenMatch()` (drop match if an excluded terminal lexes at `triviaEnd`) |
> | `<+<(set)` | prev token MUST be in set | backward | positive | scanner-side, on a terminal *definition* |
> | `<-<(set)` | prev token MUST NOT be in set | backward | negative | scanner-side, on a terminal *definition* |
>
> `>…>` = forward, `<…<` = backward; middle `+`/`-` = polarity. These replaced the old
> `>>1`→`>+>` and `++1`/`--1`→`<+<`/`<-<`; the distance-2 variants (`>>2`/`++2`/`--2`)
> were dropped (unused). Forward gates are **slot-local** (one symbol-use in one
> production). They fire after a **terminal** inline in `tokenMatch()`, and — since
> 2026-08-23 — also at **nonterminal / bracket completion** via the shared
> `MessageParser.forwardGateAllows()` helper wired at the CRF continuation sites (so
> `closureExpression >-> ("else")` is now a live gate, not a no-op). One logical gate,
> two invocation points, because GLL surfaces "the position after this slot" at different
> moments for terminals (inline) vs nonterminals (CRF return). See `Grammar Predicate
> Lookahead Design.md`.
>
> **`@unless(X)` was implemented, then RETIRED (2026-07-30).** It was used by no grammar
> by the end — its "prefer the reading that continues with X" job is covered by
> `@longest` (extent) and its same-span cousin by `@prefer`, both placed *directly on
> the affected term*. The sections below (`## APUS Design: @unless(X)` onward) are
> **historical design exploration**, kept for the predicate background (PEG/ANTLR/GLL)
> and the `Array<Array<Int>>` / `a < b > c` worked examples. See
> *The rise and fall of Schrödinger, Frankenstein and other dead-ends.md*.
>
> The "≈32 `canParseAsXxx` predicates" goal (Pillar 2 in `SwiftSyntax Mapping.md`)
> remains — met with the directional lookahead above, the **grammar-predicate lookahead**
> family (`>->(N)` derivation predicate + `@confinedTo`/`@excludedFrom` containment, see
> `Grammar Predicate Lookahead Design.md`), and structural grammar fixes — NOT with `@unless`.

## Problem

`Array<Array<Int>>` has four valid CFG derivations under Swift's published grammar (TSPL):

1. `Array` followed by `<Array<Int>>` parsed as `genericArgumentClause`.
2. `Array < (Array<Int>) >` — infix `<` then postfix `>`.
3. `Array < Array < Int >>` — infix `<`, infix `<`, postfix `>>` (when `>>` is one token).
4. `Array < (Array < Int >) >` — infix `<`, infix `<`, postfix `>`, postfix `>`.

GLL faithfully reports all four. LL/LR would reject the grammar as ambiguous. Swift's grammar IS ambiguous as a CFG; the Swift compiler disambiguates in its hand-written recursive-descent parser via a function called `canParseAsGenericArgumentList` that speculatively parses ahead and commits only when the result looks like a generic argument list. That decision is procedural, not grammatical — it doesn't appear in TSPL.

APUS today has two related primitives that don't reach this case:

- `<<1` (`--1`/`++1`/`--2`/`++2`) — scanner-time lookbehind, single-token kind.
- `>>1` — parse-time lookahead, single-token kind.

Both atomic, both terminal-level. Neither can express "if a whole sub-grammar can parse here, suppress this competing interpretation".

## Swift's Approach: the `Lookahead` Module

`SwiftParser` has a dedicated `Lookahead.swift` (`SourcePackages/checkouts/swift-syntax/Sources/SwiftParser/Lookahead.swift`) that defines:

```swift
extension Parser {
  struct Lookahead {
    var lexemes: Lexer.LexemeSequence
    var currentToken: Lexer.Lexeme
    var tokensConsumed: Int = 0
    let swiftVersion: SwiftVersion
    let experimentalFeatures: ExperimentalFeatures

    fileprivate init(cloning other: Parser) { ... }
  }

  func lookahead() -> Lookahead { Lookahead(cloning: self) }

  func withLookahead<T>(_ body: (_: inout Lookahead) -> T) -> T { ... }
}
```

**The pattern:** clone the parser state, run a normal parsing routine on the clone, take a `Bool` (or other small value) back, **discard the clone**. The main parser's token stream is untouched. Predicates that use this pattern, by file:

| File                | Predicate                                           |
|---------------------|-----------------------------------------------------|
| Attributes.swift    | `canParseCustomAttribute`                           |
| Declarations.swift  | `atStartOfFreestandingMacroExpansion`               |
|                     | `atStartOfDeclaration`                              |
|                     | `atStartOfActor`                                    |
|                     | `atStartOfUsing`                                    |
| Expressions.swift   | `atStartOfExpression`                               |
|                     | `canParseNonisolatedAsSpecifierInExpressionContext` |
|                     | `atStartOfLabelledTrailingClosure`                  |
|                     | `canParseClosureSignature`                          |
|                     | `atStartOfPostfixExprSuffix`                        |
| Lookahead.swift     | `atStartOfGetSetAccessor`                           |
| Patterns.swift      | `canParsePattern`                                   |
|                     | `canParsePatternTuple`                              |
| Statements.swift    | `isStartOfReturnExpr`                               |
|                     | `atStartOfStatement`                                |
|                     | `atStartOfSwitchCase`                               |
|                     | `atStartOfConditionalSwitchCases`                   |
|                     | `atStartOfConditionalStatementBody`                 |
| Types.swift         | `canParseType`                                      |
|                     | `canParseTypeAttributeList`                         |
|                     | `canParseTypeScalar`                                |
|                     | `canParseSimpleOrCompositionType`                   |
|                     | `canParseSimpleType`                                |
|                     | `canParseStartOfInlineArrayTypeBody`                |
|                     | `canParseInlineArrayTypeBody`                       |
|                     | `canParseCollectionTypeBody`                        |
|                     | `canParseTupleBodyType`                             |
|                     | `canParseFunctionTypeArrow`                         |
|                     | `canParseTypeIdentifier`                            |
|                     | `canParseAsGenericArgumentList`                     |
|                     | `canParseIntegerLiteral`                            |
|                     | `canParseGenericArgument`                           |

**32 predicates.** Several are recursive (`canParseType` calls `canParseSimpleType` calls `canParseTypeIdentifier`, etc.). The Lookahead clone is itself cloneable (`Lookahead.lookahead()` returns a nested instance) so predicates compose.

### `canParseAsGenericArgumentList` walked through

```swift
mutating func canParseAsGenericArgumentList() -> Bool {
  guard self.at(prefix: "<"), !self.at(prefix: "<>") else { return false }
  var lookahead = self.lookahead()
  guard lookahead.consumeGenericArguments() else { return false }
  return lookahead.currentToken.isGenericTypeDisambiguatingToken
}
```

Two checks:

1. **Consume**: speculatively walk `<...>` as a `genericArgumentList`. If the walk fails, predicate is false.
2. **Follow-set commit**: the token immediately after the closing `>` must be one of:
   `)`, `]`, `{`, `}`, `.`, `,`, `;`, EOF, `!`, postfix-`?`, `:`, `&` (binaryOperator), `(` or `[` *only if not at start of line*.

The follow-set check is what we already encoded as `>>1(...)` on the closing `>`. The speculative walk — and the commit on its outcome — is what we are adding.

### Anti-predicates

`atStartOfStatement(preferExpr:)`, `atStartOfDeclaration`, `atStartOfExpression`, `atStartOfSwitchCase` ... are used in the *opposite* direction — "is the input here X? then route to X; otherwise route elsewhere". A grammar primitive must support both polarities, but in practice the asymmetry is always: a *fallback* interpretation needs to be suppressed when a *richer* one was possible. The annotation lives on the fallback.

## Conceptual antecedents

### PEG: `&E` and `!E`

Bryan Ford, *Parsing Expression Grammars: A Recognition-Based Syntactic Foundation* (POPL 2004), defines two syntactic-predicate operators:

| Operator | Semantics                                                        |
|----------|------------------------------------------------------------------|
| `&E`     | succeeds **without consuming input** iff `E` would succeed here. |
| `!E`     | succeeds **without consuming input** iff `E` would fail here.    |

PEG's ordered-choice `/` together with `&E`/`!E` collapses ambiguity *by definition* — once the first alternate of `/` succeeds, the second is never tried. PEG never produces multiple derivations.

**What we take from PEG:** the *concept* that disambiguation can be expressed as "this rule succeeds iff some other rule succeeds at this position". **What we don't take:** PEG's mid-parse implementation. PEG can afford to run the predicate mid-parse because PEG is greedy and never explores parallel branches anyway. GLL produces all parses, so we can read the predicate's answer off the finished BSR instead — much cheaper for a parser that's already doing the exploration.

### ANTLR: Syntactic and Semantic Predicates

Terence Parr, *The Definitive ANTLR Reference* (2007), §11.3:

- **Syntactic predicate** `(α)=>β` — try matching α (without consuming); if it succeeds, parse β; otherwise try the next alternative.
- **Semantic predicate** `{p}?` — runtime Boolean guard, evaluated against parser state.

ANTLR's syntactic predicate is PEG's `&E` packaged for an LL(\*) parser. It's the disambiguation mechanism behind ANTLR's Java grammar's handling of `T<T<T>>>`.

References:
- Parr & Quong, *ANTLR: A Predicated-LL(k) Parser Generator*, Software Practice & Experience 25(7), 1995.
- Parr, *LL(\*): The Foundation of the ANTLR Parser Generator*, PLDI 2011.

### GLL and Predicates: State of the Art

The published GLL literature (Scott & Johnstone 2010, 2016, 2019; Afroozeh 2018) does not include syntactic predicates as a standard feature. Two adjacent strands are relevant:

1. **Disambiguation via Oracles / post-parse pruning.** Afroozeh, *Practical General Top-Down Parsers* (PhD, 2018, in-tree at `articles/raw/Practical general top-down parsers.txt`), §1.4, discusses `List<List<T>>` as the motivating Java ambiguity and proposes declarative *disambiguation filters* applied after parsing. APUS's `Oracle` (Oracle.md) is in that tradition.

2. **Lookahead via lexer interaction.** Scott & Johnstone, *Multiple Lexicalisation — A Java Based Study* (SLE 2019, in-tree), §3.1: the parser can consult the lexer with the current grammar's local follow set, so the lexer returns only those lexicalisations consistent with the parser's state. This is upstream of our problem — it constrains *tokenisation*, not *parsing*.

There is **no canonical published treatment** of syntactic predicates in a GLL parser. This design is a synthesis: PEG's predicate semantics + GLL's grammar-faithful exploration + APUS's existing Oracle architecture. The key observation is that *in a parser that produces all derivations, the answer to "can X parse here?" is already in the BSR* — no sub-parse is needed.

Adoption of predicate-like mechanisms in adjacent general parsers:
- **Elkhound** (McPeak, 2002) — GLR with user-supplied disambiguation hooks.
- **DParser** (Plum, 2005) — scannerless GLR with `&` and `!` lookahead operators implemented mid-parse.
- **Marpa** (Kegler, 2010+) — Earley with event-driven external parsing.

APUS's Oracle-based approach is most similar to Elkhound's post-parse filters, applied as a declarative annotation rather than a user-written hook.

## APUS Design: `@unless(X)` as an Oracle Rule

> **RETIRED 2026-07-30 — historical.** Everything from here to "Alternative:
> Parser-Level `?(X)` / `!(X)`" describes the `@unless(X)` mechanism that was built,
> shipped, and then removed (used by no grammar). Read it for the predicate background
> and worked examples only; it does not reflect the current engine. See the Status
> banner at the top.

### Syntax

A single alternate-level annotation:

```
@unless(X)        — suppress this alternate's yield when X has a yield starting at this position
```

`X` is a single named nonterminal. The annotation appears as a trailing pragma on the alternate's production rule:

```apus
primaryExpression = identifier .                          @unless(genericArgumentClause)
primaryExpression = identifier genericArgumentClause .
```

Read aloud: *"Use the bare-identifier alternate **unless** a `genericArgumentClause` could parse from here."*

The annotation lives on the *fallback* alternate. The richer alternate that uses `X` is self-gating — it already requires `X` to parse — so no annotation is needed there. See "Why `@unless` and not `@if`" below.

### Semantics

The Oracle runs in phases (existing Oracle.md):

1. **Phase 1 — dead-wood pruning**: walk BSR top-down from root; remove yields not on any complete derivation.
2. **Phase 2 — predicates** (NEW): for each grammar slot tagged with `@unless(X)`, find each surviving yield of that slot starting at position `i`. If `X` has any yield starting at the same position `i`, prune the slot's yield.
3. **Phase 3 — extent/associativity rules** (existing): apply `@shortest`, `@longest`, `@left`, `@right`.
4. **Phase 1 (repeat)**: re-run dead-wood pruning to sweep yields that referenced pruned slots.

The predicate's question — *"can X parse from here?"* — is answered by a single BSR query:

```swift
grammar.lookup(X).yield.contains { $0.i == i }
```

That's the entire predicate evaluation. No sub-parse, no clone of MessageParser, no memoisation cache, no termination concerns. The BSR is finite, immutable, and already contains the answer.

### Memoisation

The BSR *is* the memo cache. Each `(X, i)` query is an O(log n) set membership test (or O(1) if we index yields by start position, which we likely will for this and other phase-3 rules).

### Termination

Trivial — the predicate phase is a single pass over annotated yields. No recursion, no fixed point.

### Composition with existing primitives

The Oracle predicate and `>>1` are complementary:

- `>>1(...)` on a literal inside `X` constrains *when X can yield*.
- `@unless(X)` on an alternate that does *not* use X constrains *that alternate's yields based on X's existence*.

For Swift:

```apus
genericArgumentClause = "<" genericArgumentList ","? ">" >>1("(" ")" "[" "]" "{" "}" "," ";" ":" "." "?" "!" ">") .
                       // >>1 brings the closing-`>` follow check inside X

primaryExpression = identifier .                          @unless(genericArgumentClause)
primaryExpression = identifier genericArgumentClause .
                       // @unless makes the commit observable at use sites
```

Together they reproduce Swift's `canParseAsGenericArgumentList` exactly:

| Swift step                                                                     | APUS encoding                  |
|--------------------------------------------------------------------------------|--------------------------------|
| Consume `<...>` speculatively                                                  | GLL parses `X` normally; result lives in BSR |
| Check `currentToken.isGenericTypeDisambiguatingToken` after the closing `>`    | `>>1(...)` inside `X`          |
| Return the Boolean to the caller                                               | BSR query at Oracle phase 2    |
| Caller routes to generic vs. non-generic parse                                 | `@unless(X)` on the fallback alternate prunes the wrong-side yield |

### Why `@unless` and not `@if`

`@if(X)` on the alternate that *uses* `X` is redundant — the alternate's body already requires `X` to yield. Adding `@if(X)` constrains nothing.

`@unless(X)` on the *fallback* alternate (which does *not* mention `X`) is non-redundant: it expresses a constraint the grammar body alone can't express.

This matches Swift's pattern: every `canParseAsXxx` decision routes a *simpler/fallback* path away when a *richer* path was available. The simpler path needs the gate; the richer path is self-gating. Asymmetric grammar primitive for asymmetric ambiguity.

A symmetric `@if(X)` could be added later if a real use case appears. We can revisit when the complete annotation set is reviewed.

### What `@unless` is *not* for

Three disambiguation problems land at three different layers:

| Problem | Lives at | APUS primitive |
|---|---|---|
| "Which token kind is this character?" (e.g. `/` as regex-start vs division operator) | scanner | `<<1` / `<<2` (positional gating, see `Regex Lookbehind Design.md`) |
| "Which alternate of this nonterminal applies here?" (e.g. generic-clause vs comparison-chain) | parser | `@unless(X)` (this document) |
| "Is the *content* of this candidate span structurally valid?" (e.g. is `/.../` actually a well-formed regex?) | scanner-after-match | candidate validator (proposed, see `Regex CFG Discussion.md`) |

`@unless(X)` is purely the middle row. It can't reach the scanner layer (positional gating) and it can't validate token content. Attempting to push regex disambiguation through `@unless` — by emitting both interpretations as Schrödinger duals — would mean running the regex pattern matcher unconditionally from every `/`, then doubling BSR exploration, then pruning back. The lexer-level `<<1` answers the same question with a single switch on `previousTokenKind`. Different problems, different layers.

### Related work: the regex CFG approach

A related design discussion (`Regex CFG Discussion.md`) explores expressing `plainRegularExpressionLiteral` as a parser-level CFG so malformed delimiter structure (e.g. `(/E.e).foo(/`) is rejected by grammar shape. That work is independent of `@unless` but composes with it: when both the regex CFG and an operator interpretation yield, `@unless` on the operator-side alternate can express "prefer regex". When the regex CFG fails to yield (because the body is unbalanced), no `@unless` is needed — natural CFG behaviour disambiguates. The parser-level regex CFG is the *first* of the three primitives that `@unless` can compose with directly.

## Walk-through: `Array<Array<Int>>`

Token stream: `Array < Array < Int > >`, positions 0–6.

After parse (with `>>1` in place), the BSR contains:

| Yield | Source |
|---|---|
| `genericArgumentClause[5,7]` | inner `<Int>` matches; closing `>` at 5 followed by `>` ∈ approved |
| `genericArgumentClause[1,7]` | outer `<Array<Int>>` matches; closing `>` at 6 followed by EOS ∈ approved |
| `primaryExpression[0,7]` via Alt 2 (`identifier genericArgumentClause`) | uses `genericArgumentClause[1,7]` |
| `primaryExpression[0,1]` via Alt 1 (`identifier` alone) | always yields after `Array` matches |
| Comparison-chain ancestors using `primaryExpression[0,1]` | yield |

**Oracle phase 2.** Walk yields whose slot has `@unless(genericArgumentClause)`. That's the Alt 1 slot at position `[0,1]`. Query: does `genericArgumentClause` yield starting at position `1`? **Yes** (`genericArgumentClause[1,7]`). Prune `primaryExpression[0,1]` via Alt 1.

**Re-run phase 1.** The comparison-chain ancestors are now dead-wood (they depended on the pruned `primaryExpression[0,1]`). Sweep them.

**Result.** One derivation: the generic interpretation.

## Walk-through: `a < b > c`

Token stream: `a < b > c`, positions 0–4.

After parse:

| Yield | Source |
|---|---|
| `genericArgumentClause[1,4]` | **does not yield** — `>>1` rejects: closing `>` at 3 followed by `c` ∉ approved |
| `primaryExpression[0,1]` via Alt 1 (bare) | yields |
| Comparison-chain ancestors using `primaryExpression[0,1]` | yield |

**Oracle phase 2.** `primaryExpression[0,1]` Alt 1 has `@unless(genericArgumentClause)`. Query: does `genericArgumentClause` yield starting at position `1`? **No.** Keep.

**Result.** One derivation: the comparison chain.

Both cases collapse to one derivation; the parser core was never touched.

## Comparison with parser-level syntactic predicates

| Aspect | Parser-level `?(X)` / `!(X)` | Oracle-level `@unless(X)` |
|---|---|---|
| When predicate evaluates | mid-parse, blocks descriptor enqueue | post-parse, prunes BSR yield |
| Engine touch points | new `.LA` GrammarNode kind, sub-parse mechanism, descriptor handling, memo cache | one new Oracle rule + alternate-level annotation |
| MessageParser changes | medium–large | **none** |
| Memoisation | explicit cache `(target, position) → Bool` | implicit — BSR yields |
| Parse-time work | failed alternates skipped | all alternates explored, pruned later |
| Final result | identical | identical |

The parser-level version saves *parse-time work* by skipping doomed alternates. The Oracle version trades that for *architectural simplicity*. For Swift.apus the difference is probably noise — the doomed alternates are short and GLL's CRF already memoises shared work between alternates that share prefixes.

The parser-level design is documented as the **fallback** in the Alternatives section at the end of this document, for the rare case where Oracle-level resolution is insufficient.

## Implementation Outline

### apus.apus meta-grammar

The `production` rule already accepts a trailing pragma (the `[pragma]` slot is used for `@longest`, etc., on the LHS). We add a *trailing* form on the alternate:

```apus
production  = [ pragma ] identifier
                ( ":" ( regex | literal ) "." context
                | "-" ( regex | literal ) "." context
                | "=" selection "." [ predicate ]
                ) .

predicate   = "@unless" "(" identifier ")" .
```

`@unless` is recognised as a `pragma` token at scan time (it's an `@`-prefixed identifier, already lexable).

### ApusTerminals.swift

No new meta-tokens. `@unless` is a pragma; `(`, `)`, and `identifier` are already present.

### ApusParser.swift

In `production()`, after consuming the alternate's terminating `.`, check for a trailing `@unless(identifier)`:

```swift
if token.kind == "pragma" && token.image == "@unless" {
    cI += 1
    try expect(["("])
    cI += 1
    try expect(["identifier"])
    let targetName = String(token.stripped)
    cI += 1
    try expect([")"])
    cI += 1
    altHeadNode.unlessTargetName = targetName
}
```

Where `altHeadNode` is the GrammarNode for the head of the current alternate (the `.ALT` node that anchors this production's RHS).

### GrammarNode.swift

```swift
var unlessTargetName: String?           // raw name, captured at parse time
var unlessTarget: GrammarNode?          // resolved during Grammar.finalize()
```

Only `.ALT` nodes carry these fields; other kinds ignore them.

### Grammar.swift

In the existing finalisation pass (where other cross-references resolve), walk all `.ALT` nodes and resolve `unlessTargetName` → `unlessTarget` against `nonTerminals`. Error if the name is unknown.

### Oracle.swift

New phase 2, between dead-wood pruning and the extent/associativity rules:

```swift
struct UnlessPredicateRule {
    let slot: GrammarNode             // the .ALT node carrying the @unless
    let target: GrammarNode           // the resolved unlessTarget

    func prune(_ yields: inout Set<BinarySpan>) -> Int {
        var pruned = 0
        let targetYieldStarts = Set(target.yield.map(\.i))
        for span in yields where targetYieldStarts.contains(span.i) {
            yields.remove(span)
            pruned += 1
        }
        return pruned
    }
}
```

Registered alongside `LongestMatchRule`, `ShortestMatchRule`, etc. during Oracle setup.

After the predicate phase, re-run dead-wood pruning (or fold the two together in a single fixpoint loop).

### Swift.apus

Add `@unless(genericArgumentClause)` to the bare-identifier alternates at every site that has `genericArgumentClause?`:

- `primaryExpression = identifier .` → `... . @unless(genericArgumentClause)`
- `typeIdentifier = typeName . | typeName "." typeIdentifier .` → both bare forms get `@unless(genericArgumentClause)`
- `explicitMemberExpression = postfixExpression "." identifier .` → `... . @unless(genericArgumentClause)`
- `macroExpansionExpression = macroIdentifier functionCallArgumentClause? trailingClosures? .` → `... . @unless(genericArgumentClause)`

The pair-with-generic alternates need no annotation — they're self-gating.

## Migration: `>>1` → `@unless(X)`?

They serve different jobs and both stay:

- `>>1(set)` constrains *when a terminal can match* based on the next token kind. It lives on a literal inside a rule.
- `@unless(X)` constrains *when an alternate's yield survives* based on another nonterminal's yield. It lives on a production's tail.

They compose, as the Swift case shows: `>>1` makes `genericArgumentClause` Swift-spec-correct about *when* it succeeds; `@unless(genericArgumentClause)` uses that correctness to suppress competing interpretations.

Earlier in the design we noted that `>>1` is conceptually a degenerate predicate — "the next token's kind matches one of these". That's still true; `@unless` on a tiny helper nonterminal would replicate it. But `>>1` is cheaper (one BitSet test, no Oracle phase), so we keep it as the specialised primitive for single-token follow checks.

## Open Questions

1. **Annotation placement.** Trailing pragma after the alternate's `.` reads naturally. An alternative is leading-pragma syntax (`@unless(X) primaryExpression = identifier .`) for consistency with `@longest`/`@shortest` which sit on the LHS. The two pragmas serve different scopes — `@longest` applies to the *nonterminal*, `@unless` applies to *this alternate* — so distinct placement is arguably clearer. Worth revisiting at the comprehensive annotation review.

2. **Ordering between predicate phase and extent rules.** If `@unless` runs before `@longest`, the predicate pruning happens first; if after, the longest-span pruning happens first. For the Swift case they're independent (different nodes), but with interacting annotations on the same node ordering could matter. Likely answer: predicates first, then extent/associativity, then dead-wood sweep — predicates are about *which interpretation*, extent rules are about *how to disambiguate within an interpretation*.

3. **Should `@if` be added?** Asymmetric grammar primitive (`@unless` only) matches asymmetric real ambiguity. Defer to the comprehensive annotation review.

4. **Predicates inside predicates.** Not applicable in the Oracle model — there is no recursive predicate evaluation. The BSR query is a single set-membership test.

5. **Interaction with Schrödinger tokens.** A token with dual kinds: does the predicate sub-parse try both? Yes — the BSR contains yields from all dual-kind paths the parser explored. The predicate query naturally sees them.

6. **Performance.** A worst-case Swift file could have many `@unless`-annotated alternates. Each predicate evaluation is a small set query; the cost scales with `|annotated alternates × yields per alternate|`. Benchmark on the 590-case SwiftSyntax sweep once implemented.

7. **Edge case — `@unless` on an alternate that also yields elsewhere.** The annotation is per-slot, so only the annotated occurrence is affected. An alternate reused in another production (via shared subgrammar) keeps its other yields untouched. Need to verify this is how slot identity is preserved.

## Summary of Changes Required

| File                          | Change                                                                 | Scope    |
|-------------------------------|------------------------------------------------------------------------|----------|
| `apus.apus`                   | Add `[predicate]` trailing slot on production alternates               | small    |
| `ApusTerminals.swift`         | No change — `@unless` lexes as `pragma`                                | none     |
| `ApusParser.swift`            | Parse trailing `@unless(X)` in `production()` → store on `.ALT` node   | small    |
| `GrammarNode.swift`           | Add `unlessTargetName: String?`, `unlessTarget: GrammarNode?` on `.ALT` nodes | trivial |
| `Grammar.swift`               | Resolve `unlessTargetName` references during finalisation              | small    |
| `Oracle.swift`                | New `UnlessPredicateRule` phase between dead-wood and extent rules     | **small–medium** |
| `MessageParser.swift`         | **No change.** Parser core untouched.                                  | none     |
| `SimpleMessageParser.swift`   | **No change.**                                                         | none     |
| `Swift.apus`                  | Add `@unless(genericArgumentClause)` to every bare-form alternate that competes with a generic-bearing alternate (4 sites estimated) | small |

Total: one new annotation, one new Oracle phase, ~4 grammar edits. The parser core is **untouched**.

## Alternative: Parser-Level `?(X)` / `!(X)`

If a case arises that can't be expressed as Oracle-level pruning — for example, a predicate whose answer depends on *parser-state* beyond the BSR (a `swiftVersion` flag, an experimental feature, a context counter) — the parser-level form remains a viable fallback.

### Sketch

```
?(X)        — positive syntactic predicate: succeed iff X can parse from here, consuming nothing
!(X)        — negative syntactic predicate: succeed iff X cannot parse from here, consuming nothing
```

Used in production rules:

```apus
primaryExpression = identifier ?(genericArgumentClause) genericArgumentClause .
primaryExpression = identifier !(genericArgumentClause) .
```

### Semantics

For descriptor `(slot, position)` reaching a `?(X)` body symbol:

1. Spawn a sub-parse of `X` starting at `position`.
2. If the sub-parse produces at least one yield whose start is `position`, the predicate succeeds; the descriptor advances past `?(X)` body symbol (position unchanged).
3. Otherwise the descriptor fails.

`!(X)` is the same with the boolean negated.

The yields generated inside the sub-parse are **not** added to the main parse's BSR. They exist only to determine the boolean answer.

### Cost

Substantially higher than the Oracle approach:

- New `.LA` GrammarNode kind.
- New sub-parse mechanism in MessageParser (either nested MessageParser or predicate-tagged descriptors).
- Explicit memoisation cache `(target, position) → Bool`.
- Termination analysis (left-recursion-like handling for predicates that depend on themselves).
- Parallel changes in `SimpleMessageParser.swift`.

### When the parser-level form is worth the cost

- The predicate's answer depends on parser state outside the BSR (Swift's `swiftVersion`, `experimentalFeatures` flags).
- The predicate must fire mid-parse to *prevent* expensive doomed exploration of dead alternates (a performance concern, not correctness).
- Recursion through a predicate target produces an unbounded BSR that the Oracle approach would need to traverse first.

For Swift.apus today, none of these apply. The Oracle approach handles every `canParseAsXxx` case identified in the SwiftParser catalogue.

If/when the parser-level form is needed, the meta-grammar can grow `?(X)` / `!(X)` factor-level forms alongside the existing Oracle `@unless(X)` annotation. The two are complementary, not competing.

## References

In-tree (`articles/raw/`):
- Scott & Johnstone, *GLL Syntax Analysers for EBNF Grammars*, SLE 2016.
- Scott & Johnstone, *Multiple Lexicalisation — A Java Based Study*, SLE 2019.
- Afroozeh, *Practical General Top-Down Parsers*, PhD thesis 2018.

External:
- Ford, *Parsing Expression Grammars: A Recognition-Based Syntactic Foundation*, POPL 2004.
- Parr & Quong, *ANTLR: A Predicated-LL(k) Parser Generator*, SP&E 25(7), 1995.
- Parr, *The Definitive ANTLR Reference*, Pragmatic Bookshelf 2007 (§11.3 on predicates).
- Parr, *LL(\*): The Foundation of the ANTLR Parser Generator*, PLDI 2011.
- swift-syntax `SwiftParser/Lookahead.swift` and the 32 `canParseAsXxx` / `atStartOfXxx` predicates listed above.

---

## Consolidated learnings (from agent memory, 2026-07-30)

**Unified directional-polarity annotations (adopted 2026-07-21), distance-1 only:**

| Token | Meaning | Direction | Polarity |
|-------|---------|-----------|----------|
| `>+>(set)` | next token MUST be in set | forward (lookahead) | positive |
| `>->(set)` | next token MUST NOT be in set | forward (lookahead) | negative |
| `<+<(set)` | prev token MUST be in set | backward (lookbehind) | positive |
| `<-<(set)` | prev token MUST NOT be in set | backward (lookbehind) | negative |

Mnemonic: `>…>` forward, `<…<` backward; middle `+`/`-` = polarity. Replaced the old
`>>1`→`>+>` and lookbehind `++1/--1`→`<+</<-<`; the distance-2 variants were dropped
(unused). Forward forms are **per-slot** on the terminal-use node
(`GrammarNode.followAhead[Exclude]` + BS mirrors), evaluated in
`MessageParser.tokenMatch()` (positive = predict-set override; negative = drop a match
whose next terminal lexes at `m.triviaEnd`). Lookbehind stays scanner-side on terminal
*definitions*.

**Slot-local vs terminal-global (the choice that matters):**
- `>->` (negative forward) is **slot-local** — gates ONE terminal-use in ONE
  production (e.g. the `yield` in `yieldStatement`) without touching the same lexeme's
  identifier reading elsewhere. This is why it fixes yield/discard stmt-vs-call
  (`preferPostfixExpr`) without breaking the call `yield(x)`.
- `<-<` (negative lookbehind) is **terminal-global** and backward — gates whether a
  terminal lexes at all based on the previous token; can't see grammatical context.
  Used for regex-vs-division.

**`>+>`/`>->` fire after a TERMINAL** (checked in `tokenMatch` at lex time) **and, since
2026-08-23, at nonterminal / bracket COMPLETION** (via `MessageParser.forwardGateAllows()`
at the CRF continuation sites). On the epsilon `""` they remain a silent no-op. When this
example was written, nonterminal-completion was NOT yet a firing site, so the postfix
`!rightBound` fix anchors on the `postfixOperatorToken`/`dotOperator` TERMINAL rather than
the `postfixOperator` nonterminal — a choice that still works and reads clearly:
```
postfixExpression = postfixExpression >s< postfixOperator <s> .                                  // spaced/newline after
postfixExpression = postfixExpression >s< postfixOperatorToken >+>("." ")" "]" "}" "," ";" ":") . // tight delim / EOF
postfixExpression = postfixExpression >s< dotOperator         >+>("." ")" "]" "}" "," ";" ":") . // postfix range at delim/EOF
```
(`<s>` covers whitespace-after but fails at bare EOF; the `>+>` alternate covers the
tight-delimiter/EOF case. Without `!rightBound`, `a+` was a spurious postfixExpression
that `@longest prefixExpression` then preferred, breaking tight infix `a+b`/`x*x`.)

**DEFERRED engine task:** make `>+>` fire at nonterminal COMPLETION (CRF pop/return
replay) so it can annotate a nonterminal — would collapse the two terminal-specific
postfix rules into one on `postfixOperator`. A negative *parse-time* lookahead in a
production is the likely next primitive; consolidate the meta-token surface then
(direction can be implied by position — after a terminal `.` = scanner-time backward,
after a literal in a production = parse-time forward, like `---`/`~~~` already do).

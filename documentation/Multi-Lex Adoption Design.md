# Multi-Lex (LCNP) Adoption Design

Plan to adopt Scott & Johnstone's **LCNP** (lex-call-no-precompute) parser-driven lexer interaction (SLE 2019, *Multiple Lexicalisation — A Java Based Study*, in-tree at `articles/raw/Multiple Lexicalisation - A Java Based Study.txt`) as the unifying replacement for APUS's accumulated lexer-level disambiguation machinery: Schrödinger duals, Frankenstein `~~~`, `<<1`/`<<2` regex lookbehind, `---()` exclusion sets, and the parser-level regex CFG that Codex sketched today.

This is a *design* doc — no code yet. 

## Motivation

APUS has accumulated five disambiguation mechanisms in front of the GLL parser:

| Mechanism | Solves | In-tree doc |
|---|---|---|
| Schrödinger duals + `---()` exclusion | Keyword/identifier overlap, "this dual is suppressed in this rule" | `Advent/Schrodinger Tokens.md` |
| Frankenstein `~~~` | `>>` / `==` / `&&` partial-token splits where multi-char scanner tokens need to be parser-split | `Advent/Frankenstein Tokens.md` |
| `<<1` / `<<2` (`++1` / `--1` / `++2` / `--2`) | Regex-vs-division and similar position-gated tokenisation | `Advent/Regex Lookbehind Design.md` |
| `>>1(...)` parse-time lookahead | Swift's `isGenericTypeDisambiguatingToken` follow-set commit | `Advent/Structured Lookahead Design.md` |
| Parser-level regex CFG (Codex's recent fix) | `(/E.e).foo(/0)` over-claim; balanced delimiters inside regex body | `Advent/Regex CFG Discussion.md` |

Today's debugging of `Array<Array<Int>>` ambiguity, the regex CFG roll-out, and the discovery that 10 of 47 Swift cases still fail at the *scanner* layer (categories B and E — invalid-hex inside regex, editor placeholders) made it clear these five mechanisms are all attacking facets of the same problem: **the lexer is making longest-match commitments before the parser has the context to validate them.**

LCNP collapses all five into one uniform interface and matches the published GLL state of the art (Scott & Johnstone 2019). The cost is a structural refactor — character-position addressing throughout the BSR/CRF/Oracle stack — but the design is well-defined in the paper with measured Java numbers (Life.java parses in <0.099s with 3×10⁷⁵⁸ indexed lexicalisations under no disambiguation).

## The LCNP Design (Paper Summary)

### Core API

The parser calls the lexer on demand, per requested terminal:

```
lex(u, t) = { j  |  u[0..j) ∈ language(t) }
```

For each character position `i` and each terminal `t` predicted by the grammar at that point, `lex(i, t)` returns the **set of valid end indices** at which `t` matches. Empty set means the terminal doesn't match here.

A second variant is exposed for lookahead-aware lexing:

```
lexLKH(t, i, β, X) = lex(i, t) ∩ { j  |  valid(j, predict(β, X)) }
```

where `predict(β, X) = first(β) ∪ (follow(X) if β nullable)` — i.e. the parser's local follow set is passed to the lexer to prune impossible matches. APUS already computes these sets (used in `continuationViable` and `testSelect`) so the data is available; the API hook is new.

### Position model

**Character positions throughout.** Token-position addressing disappears. BSRs are `(slot, i, k, j)` where i/k/j are character indices into the input string. From the paper:

> *"An indexed token string is a sequence of pairs of the form (t, h) where t is a token and h is an integer."* (l. 829-830)

Sharing in the BSR is dramatic when many lexicalisations coexist:

> *"so (t, 2) appears at positions 0 and 1 and so it is only considered twice even though it appears four times in the ITSs"* (l. 2019-2021)

For the canonical `aaab` example with `lexFull()` returning 11 indexed lexicalisations, the **BSR has 14 elements covering all 10 valid ITSs** (l. 1891-1894). Per the paper:

> *"our implementation does parse Life.java in under 0.099 seconds"* (l. 2531) — across 3×10⁷⁵⁸ non-disambiguated indexed lexicalisations.

### Descriptor forking on terminal match

The descriptor processing loop fans out when a terminal is consumed:

> *"If β = xγ where x is a terminal then lex(c_I, x) is called. For each k ∈ lex(c_I, x) there is a lexeme in the pattern of x between positions c_I and j = c_I + k... For each j ∈ J a descriptor (X ::= αx·γ, c_U, j) is created"* (l. 1328-1335)

That is: one descriptor per valid end-position. The CRF dedup (same `(slot, position)` clusters) keeps this tractable.

### What LCNP says about Schrödinger tokens

Scott explicitly compares (l. 2851-2856) and concludes LCNP **subsumes** Schrödinger tokens for same-span ambiguity (`if` as keyword/identifier — `lex(pos, "if")` and `lex(pos, identifier)` both return the same end-pos; parser disambiguates by which terminal a slot needs). LCNP additionally handles **different-span** alternatives (`--` as one token vs `-` `-` as two) that Schrödinger duals cannot express because they fuse at a fixed span. From the paper:

> *"a Schrodinger token is returned. When the parser reaches that token it decides... but only one token string is actually parsed, so this is not multi-parsing."* (l. 2851-2856)

### Complexity

> *"worst case cubic in the length of the underlying character string"* (l. 898-899)

Same asymptotic class as token-level GLL. Empirical measurements (Table 4): LCNP/NoD on Life.java records `|U|=48187` descriptors and `|ϒ|=15719` BSR yields, compared to character-level SGLLJ's `|U|=303585` and SPPF 114923 nodes. LCNP is **~6× fewer descriptors and ~7× fewer output nodes** than scannerless character-level GLL — the parser-driven lexer is structurally cheaper than the parser-as-lexer.

## Mapping to APUS — What Collapses, What Stays

### Mechanisms that LCNP replaces

1. **Schrödinger duals + `---("if" "let" …)` exclusion.** Same-span ambiguity (keyword vs identifier) is handled by parser-side terminal selection. The `Token.dual` chain, `propagateExcludeSets()`, and `excludeBS` checks in `tokenMatch()` / `testSelect()` become dead code.

2. **Frankenstein `~~~` partial-token-match sentinel.** ✅ **Removed Jun 9, 2026** — see "Frankenstein removal" below. (Originally planned to retire here in Phase B; pulled forward because the Swift grammar had already migrated to char-level operator assembly and Frankenstein was deadweight.)

3. **`<<1` / `<<2` regex lookbehind annotations (`++1`/`--1`/`++2`/`--2`).** Position-gated tokenisation — "this terminal only matches after certain previous tokens" — should disappear once the parser asks for terminals from grammar context instead of accepting one committed token stream. `lexLKH` can later prune matches with grammar-derived predict sets, but it is an optimisation/proof step, not the first semantic replacement for every existing lookbehind rule. `LookbehindSpec`, `LookbehindRule`, `LookbehindLine`, and the `lookbehindAllows` check in `Scanner.swift:308-332` retire only after the corresponding regex/operator cases are covered by LCNP terminal alternatives and validated.

4. **Parser-level regex CFG (today's `plainRegularExpressionLiteral = "/" >s< regexBody >s< "/" .`).** Under LCNP the regex is *back* in the lexer as `lex(pos, regexLiteral)`, where the implementation can run a CFG acceptor internally and only return an end-pos if the body parses. The grammar stays clean (regex is a single terminal again), the `(/E.e).foo(/0)` over-claim is rejected by the lex-side validator, and the operator-overlap workaround (`regexNonOperatorAtom` + `regexAtom = operatorHead | …`) disappears. This is also where the deferred **candidate-validator** primitive lands — LCNP's `lex(pos, t)` is naturally a candidate validator.

5. **`>>1(...)` parse-time follow-set commit.** Expected to become redundant, but not deleted by assumption. The equivalent LCNP pruning is `lexLKH` with `predict(β, X)`, where the lexer filters end positions against the parser's next-symbol expectations. Keep `followAheadBS` until each existing `>>1(...)` use is proven equivalent at its grammar slot.

### Mechanisms that LCNP does NOT replace

1. **Grammar-predicate lookahead parser-level alternate selection (`Grammar Predicate Lookahead Design`).** LCNP is a lexer interface. Grammar-level ambiguity — same token kinds parseable under multiple productions, e.g. `Array<Array<Int>>` as generic vs comparison-chain — stays, resolved by `>->(N)`/`@confinedTo`/`@excludedFrom` (the retired `@unless` was an earlier form of this).

2. **`@longest` / `@shortest` / `@left` / `@right` Oracle rules.** Post-parse disambiguation over the BSR is independent of how tokens were produced.

3. **Scanner modes (gated transitions `=== "X" >>> "Y"`).** LCNP does not automatically preserve today's mutable scanner mode stack. Prefer pure terminal-specific recognizers or grammar-encoded islands first; carry lexical state in descriptor keys only for concrete constructs that cannot be represented otherwise. See Open Questions §A.

4. **Layout-sensitive parsing** (`LayoutTokenInjection.swift`). Indentation-derived tokens still need synthesis from whitespace context. LCNP changes the coordinate model, but it does not by itself define layout policy.

## APUS-Shaped Lex API

The final parser should keep APUS's current fast identity model: terminals are integer IDs, and grammar sets are `BitSet`s. LCNP changes when terminal matching happens, not how terminals are identified.

There is still a one-pass setup phase for the grammar/scanner tables:

- assign stable `terminalID: Int` values in `Grammar.symbolToID`
- compile literal and regex `TokenPattern`s into terminal recognizers
- populate `firstBS`, `followBS`, `ambiguousBS`, and later predict sets as `BitSet`s

There should not be a final one-pass **committed token stream** that the parser must consume. The old scanner can remain behind a legacy adapter for baseline comparison and rollback, but the parser's normal input is the source string plus a parser-driven lexer.

Proposed Swift shape for the first implementation, keeping `String.Index` as the parser position type for now:

```swift
typealias CharPosition = String.Index

struct LexMatch: Hashable {
    let terminalID: Int
    let end: CharPosition
}

protocol LCNPLexer {
    /// Return all valid matches for `terminalID` starting at `pos`.
    /// Empty result means the terminal doesn't match here.
    func lex(at pos: CharPosition, terminalID: Int) -> [LexMatch]

    /// Same as `lex`, but filtered against the parser's next-symbol expectations.
    /// This is an optimisation/proof step; plain `lex` remains the semantic base.
    func lexLKH(at pos: CharPosition, terminalID: Int, predict: BitSet) -> [LexMatch]
}
```

`LexMatch` can grow if trivia/layout needs to be carried with the match, but the source string remains the source of truth. Callers slice `input[start..<end]` when they need the image.

For multi-char operator splits (`>>` example):
- `lex(pos, terminalID(">>"))` returns `[pos+2]` when the next 2 chars are `>>`
- `lex(pos, terminalID(">"))` returns `[pos+1]` when the next 1 char is `>`
- Both queries at the same position can succeed simultaneously
- The parser explores both via descriptor forking

For regex with body validation:
- `lex(pos, terminalID(plainRegularExpressionLiteral))` runs an internal regex-body recognizer
- Returns `[endPosOfValidBody+1]` (after the closing `/`) only when the body parses
- For `(/E.e).foo(/0)` the body recognizer rejects unbalanced `)`, returns `[]`
- For `^^/0xG/` the body recognizer accepts `0xG` as raw character content, returns `[endOfRegex]`

For keywords vs identifiers:
- `lex(pos, terminalID("if"))` returns `[pos+2]` when chars at pos..pos+2 are `if` AND not followed by an identifier-continuation char (so `iffy` won't match `if`)
- `lex(pos, terminalID(identifier))` returns `[pos+N]` where N is the identifier length — including `if` if the parser asks for `identifier`
- The current `---("if" …)` exclusion sets become unnecessary once same-span alternatives are queried independently by terminal ID

### Recognizer Layering

Most terminals should be **pure validators from a source position**: given the same input, `pos`, and `terminalID`, `lex` returns the same matches, with no global scanner cursor and no mutable scanner mode stack.

Some terminals are still single grammar terminals but need richer matching than one regex. These become **terminal-specific recognizers** behind `lex`: nested block comments, raw strings with custom pound delimiters, multiline strings, regex literal bodies, and editor placeholders if they need custom validation.

A construct should be **grammar-encoded** when it is real language syntax rather than lexical validation. String interpolation containing Swift expressions, regex syntax that needs a real AST, macro-like embedded syntax, or anything whose internal ambiguity matters should remain parser-owned grammar structure.

Thread lexical state through descriptors only if a concrete construct cannot be expressed as a pure terminal recognizer, trivia/layout summary, or grammar island. Carrying state in descriptor/CRF keys increases cardinality and weakens sharing, so it is the fallback, not the default.

## Phased Rollout

Big-bang migration is too risky, but the migration should still point at the final model from the start. Use `String.Index` directly as the first parser position type:

```swift
typealias CharPosition = String.Index
```

That keeps the first implementation simple. A later performance pass can replace the alias with an interned integer position if descriptor pressure proves that necessary.

### Phase 0 — Capture the baseline

Before touching parser behavior: run the full SwiftSyntax 590-case sweep and the 47-message embedded test bed under today's grammar. Record per-case pass/fail, per-message derivation counts, descriptor counts, BSR yield counts, and known scanner failures. This is the regression contract LCNP must meet.

#### Phase 0 Findings (Jun 2026)

Running the baseline surfaced three issues worth carrying into the LCNP work, even though two of them retire with the Schrödinger/exclude machinery in Phase D.

**1. Parser non-determinism via Schrödinger head selection.** Identical inputs produced different parse outcomes on consecutive runs (`RegexLookbehindIntegration` flipped between 11 and 7 failures across reruns). Root cause traced to `Scanner.swift` iterating the `patterns: [String: TokenPattern]` dictionary in Swift's hash-seeded order when partitioning into `literalPatterns` / `regexPatterns`. That order propagates into the equal-length candidate array, ultimately deciding which kindID becomes the *head* (`ordered[0]`) of a Schrödinger chain. The head's kindID then feeds the exclude check in `MessageParser.tokenMatch()` / `testSelect()`:

```swift
if current !== headToken && cL.excludeBS.contains(headToken.kindID) {
    // suppress this dual
}
```

The check is by design head-dependent ("if the canonical lex is excluded, all non-head duals are suppressed too"), so changing the head changes which alternates the parser even considers. GLL itself is order-invariant on the fixpoint; the bug lives in the deliberately-asymmetric Schrödinger exclude gate. **Not patching this in the current code** — Swift's per-process hash seed is doing useful work by surfacing exactly this category of subtle order-dependent semantics, and LCNP Phase D retires `Token.dual` / `excludeBS` / the whole `---()` mechanism. Worth keeping the test variance visible until then.

**2. Contingent-pops mechanism is correct.** Verified in response to the question "does GLL's contingent-pops handling explain the non-determinism?" Walked `CallReturnForest.swift` for the call/rtn rendezvous:

- `call()` joining an existing cluster: new return iterates `cluster.pops` to emit catch-up descriptors; if no pops yet (X still being parsed), the return is stored contingent.
- `rtn()` adding a new pop: iterates `cluster.returns` to notify every waiting caller, including all contingents accumulated since the cluster was created.
- The cartesian (return × pop) product is built bidirectionally — every new arrival on either side processes all existing arrivals on the other.

This is a sound fixpoint regardless of dispatch order, so it does not contribute to the non-determinism above and does not need rework in Phase A.

**3. Grammar caching contamination — was a downstream symptom, not its own bug.** An obvious Phase 0 speed-up is to load `Swift.apus` once per process instead of per-test (~1850 fresh loads → 1). First attempt failed: cached-grammar runs gave different pass/fail counts depending on test order (e.g. `Regex` alone failed; `Patterns` then `Regex` passed). The shared grammar accumulates *no* leaking mutable state — `GrammarNode.yield` is the only per-parse mutation and `clearNodes()` resets it. The contamination was actually the Scanner head-selection bug above, manifesting differently: with caching the patterns dict is iterated once at startup and stays in that order for the rest of the process, hiding the variance within a run but exposing it across test orderings. With the head bug present the cache must stay off; with the head bug fixed (or with Schrödinger retired in Phase D) the cache becomes safe.

Working baseline configuration kept in `AdventTests/SwiftSyntaxTests.swift`:

- `loadFreshSwiftGrammar()` — per-call load, no grammar caching.
- Per-source parse memoization (`parseCache`) — one canonical `runAdventOnce` result shared across `adventAccepts` / `unambiguous` / `treesMatch` for the same snippet, so each unique source still parses only once.
- Per-snippet baseline metrics streamed to `baseline-phase0.csv` (descriptors, dup/suppressed, CRF size, yield count, matched, oracle pruned).
- `.tags(.swiftSyntaxReference)` on every `swiftSyntaxAccepts(_:)` so the 1853 reference-only checks can be filtered out of the inner loop.

The CSV is the durable regression contract for Phase A. Because the non-determinism above is still live, expect ±5% variance in counts between runs — the LCNP comparison should test "in distribution," not exact equality, until Phase D removes the variance source.

#### Frankenstein removal (Jun 9, 2026)

The entire Frankenstein partial-token-match mechanism has been deleted. Originally scheduled for retirement in Phase B alongside the Schrödinger machinery, it was pulled forward because the Swift grammar had already migrated to char-level operator assembly (each operator character is its own token, multi-char operators assembled at parse time via `>s<`) — leaving Frankenstein with no remaining users.

Deleted:

- `MessageParser.tokenMatch()` — Frankenstein sub-position path (`charOff != 0` mid-token continuation) and the prefix-split fallback at the end of the function.
- `MessageParser.testSelect()` / `followCheck()` / `continuationViable()` — all `frankensteinID` membership checks; `continuationViable`'s `position.charOffset != 0` early-true branch.
- `CallReturnForest.swift` — `i.charOffset == 0` guard and `!X.firstBS.contains(grammar.frankensteinID)` guard in the `canEarlyTerminate` LL(1) early-termination check.
- `Grammar.swift` — `frankensteinID` field, `"≋"` symbol registration in `finalizeSymbolTable()`, all related comments.
- `ApusParser.swift` — the `~~~` parsing block after `literal()`, the "≋" FIRST-set insertion, and the `node.content = source` line in `literal()` (only Frankenstein read `node.content`).
- `ApusTerminals.swift` — `"~~~"` terminal kind definition.
- `GrammarNode.swift` — `content: String` field and the commented-out `frankensteinMatchAllowed` placeholder.
- `Descriptor.swift` — `TokenPosition.charOffset` accessor and the bit-packing; `init(token:charOffset:)` and `at(charOffset:)`; `TokenPosition.unused` sentinel (was Frankenstein-related). `TokenPosition` is now a thin `Int` wrapper around `tokenIndex`. `TokenPosition.charPosition(in:input:)` simplified to just look up `tokens[i].image.startIndex`.
- Grammar files — `~~~` references in `apus.apus`, `apusAmbiguous.apus`, `test.apus`, `Swift.apus` comment; `testFrankenstein.apus` deleted.
- Tests — `SpecialTokenTests.FrankensteinTokens` suite (9 cases) removed; file header comment updated.
- Docs — `Frankenstein Tokens.md` marked superseded with a banner pointing here.

Build green; focused suite (Patterns + RegexLookbehind + SpecialTokenTests + CoreGrammarTests) runs **173 pass / 29 fail of 202** — every Schrödinger / lookbehind / exclusion / core grammar test still passes; the 29 failures are the same Patterns + Regex baseline failures from Phase 0, well within the documented non-determinism band. The doc text and total estimate in Phase A's touch list still refer to `(tokenIndex, charOffset)` — accurate for what was there before, replaced by a simpler `tokenIndex`-only `TokenPosition` now.

### Phase A — Source positions everywhere, legacy scanner adapter

Replace `TokenPosition` (currently `(tokenIndex, charOffset)`) with `CharPosition` in BSR yields, CRF clusters, descriptors, Oracle walks, and derivation/SPPF spans. The old scanner may still run, but only behind an adapter that maps its committed tokens to source-position lex matches. That adapter exists for baseline comparison and rollback, not as the final parser input model.

Touch list (estimated):
- `BinarySubtreeRepresentation.swift` — `BinarySpan` field types
- `Descriptor.swift` — position field type
- `CallReturnForest.swift` — `ParsePosition` key type
- `MessageParser.swift` — every `cI` / `cU` / `i` / `k` / `j` site
- `Oracle.swift` — `pruneUnproductive` reachability walk
- `DerivationBuilder` and `SPPFExtractor` — character extents in tree spans
- `DerivationBuilder.swift` — diagram labels
- Test infrastructure (`parseMatches`, `parseLanguageMessage`) — return-value comparisons that today rely on `TokenPosition`

**Validation:** all 590 SwiftSyntax cases plus 47 embedded messages produce identical pass/fail outcomes and identical ambiguity profiles through the legacy adapter. Derivation counts should remain identical; if they change, Phase A changed behavior and should be investigated before moving on.

#### Phase A — Step 1 landed (Jun 2026)

Foundation types and the legacy adapter shell are in `Descriptor.swift`:

- `typealias CharPosition = String.Index` — the source-position type Phase A migrates *to*.
- `struct LexMatch` — `(terminalID, end: CharPosition)`, the LCNP result.
- `protocol LCNPLexer` — `lex(at:terminalID:)` + `lexLKH(at:terminalID:predict:)`, the LCNP API the parser will call.
- `struct LegacyScannerLexAdapter: LCNPLexer` — wraps a finished `Scanner` and answers `lex(pos, t)` by binary-searching the committed token stream and walking the Schrödinger dual chain at the matching position. This is the "old scanner runs behind an adapter" piece the doc names.
- `TokenPosition.charPosition(in:input:)` and `CharPosition.tokenIndex(in:input:)` — explicit bridges so the migration can proceed incrementally without breaking the build at any step.

Build is green; no behavior change. The bulk of Phase A — replacing `TokenPosition` field types in BSR/CRF/Descriptor and rewriting every `cI`/`cU`/`i`/`k`/`j` site in `MessageParser`/`Oracle`/`DerivationBuilder` — is staged behind these primitives and is the next focused PR.

#### Phase A — Step 2 landed (Jun 9, 2026)

`BinarySpan.{i,k,j}` is now `CharPosition`. The cascade required to keep the build green pulled in the entire downstream BSR consumer set in one commit:

- `BinarySubtreeRepresentation.swift` — `BSR` and `BinarySpan` field types, `addYield` parameter types, `Comparable` updated to lexicographic three-way compare since `String.Index` doesn't conform to `Comparable` for tuples.
- `MessageParser.swift` — every `addYield(i: cU, k: cI, j: ...)` bridged via a new private `charPos(_:)` helper that wraps `TokenPosition.charPosition(in: tokens, input: input)`. The success check at the end of `parse()` now compares against `input.startIndex` / `input.endIndex` instead of `.zero` / `TokenPosition(token: tokens.count - 1)`. `cI`/`cU` themselves still hold `TokenPosition` — that's Step 3.
- `CallReturnForest.swift` — five `addYield` call sites in `call`/`rtn`/`bracketCall`/`bracketRtn` bridged the same way.
- `Oracle.swift` — `NodeSpan`/`NodePos` and every `from`/`to` parameter now `CharPosition`; `disambiguate()` derives `n`/`origin` from `input.{end,start}Index`; `pruneByExtent`/`pruneByPivot` return-type fixed to `CharPosition`; constructor gains `input: String`.
- `DerivationBuilder.swift` — `ParseTreeNode.{from,to}`, `DerivationBuilder.{NodeSpan,NodePos}`, every method signature; the two `tokens[from.tokenIndex]` sites bridge to `from.tokenIndex(in: tokens, input: input)`; constructor gains `input: String`.
- `GenerateSwiftSyntaxAST.swift` — `SwiftSyntaxGenerator` fields, span tuples `(GrammarNode, CharPosition, CharPosition)`, `endCache`/`endGuard`, `tokenText(at:)` and `collectTerminalText` use the bridge; constructor gains `input: String`.
- `SPPF.swift` — `SPPFNode.i`, `SPPFNode.j` (now `CharPosition?` because the old `TokenPosition.unused` sentinel doesn't have a `String.Index` equivalent — packed nodes carry `nil`, extendable readers force-unwrap with comments explaining why), `SPPFNodeKey`, every position-typed parameter; constructor gains `input: String`. Two `let j = w.j!` sites enforce the invariant that only packed nodes carry `nil` and packed nodes are never extended.
- Test infrastructure — `parseMatches`, `parseLanguageMessage`, `parseAndDisambiguate`, `runAdventOnce`, the `RegexLookbehind` probe, and `SpecialTokenTests` all switched from `TokenPosition(token: tokens.count - 1)` / `.zero` to `input.{end,start}Index`; Oracle/DerivationBuilder/SwiftSyntaxGenerator constructions thread `scanner.input` through.

**Validation:** Pattern + RegexLookbehind suite — 13 pass / 23 fail vs. baseline 11 / 25, well within the ±5% Schrödinger non-determinism window. Three Pattern `adventAccepts` tests now pass that were intermittent before. Importantly, the diagnostic spans in residual-ambiguity messages now print as character-offset ranges (e.g. `[12[utf8]..24[utf8]]`), confirming the spans really are operating on `String.Index` rather than packed token positions.

#### Phase A — Step 3 landed (Jun 9, 2026)

All remaining position state is now `CharPosition`. `TokenPosition` survives only as a transitional value type used by the legacy adapter and a couple of diagnostics paths.

- `Descriptor.{k, i}` — `CharPosition`.
- `CallReturnForest.ParsePosition.index`, `ParseCluster.{index, pops}` — `CharPosition` / `Set<CharPosition>`.
- `MessageParser.{cI, cU, furthestMismatchIndex}` — `CharPosition`.
- Removed: `MessageParser.charPos(_:)` bridge helper; all six `charPos(...)` call sites collapsed since `addYield`/`addDescriptor` accept `CharPosition` directly.
- Added: `MessageParser.tokenIndexByStart: [CharPosition: Int]` — a sidecar built once per parse mapping each visible token's `image.startIndex` to its array index. `input.startIndex` is aliased to 0 so the initial cursor finds token 0 even when there's leading trivia. `input.endIndex` naturally points at the EOS token (whose image is `input[end..<end]`).
- Added two `@inline(always)` helpers:
  - `tokenIdx(at: CharPosition) -> Int` — O(1) dict lookup with binary-search fallback for diagnostic-only positions.
  - `nextTokenStart(after: Int) -> CharPosition` — returns `tokens[idx+1].image.startIndex`, or `input.endIndex` past the array. Replaces `cI.nextToken()` which advanced by token-array index.
- `tokenMatch()` now returns `CharPosition?` — the start of the next token on success.
- `boundaryMatches`, `testSelect`, `followCheck`, `continuationViable` all take `CharPosition` parameters and use `tokenIdx(at:)` to read the current token.

This required no changes to the legacy adapter (`LegacyScannerLexAdapter` was already CharPosition-native), no changes to Oracle/DerivationBuilder/SwiftSyntaxGenerator/SPPF (already migrated in Step 2), and no changes to test infrastructure (already on `input.{start,end}Index`).

**Validation:** Patterns + RegexLookbehind + SpecialTokens + Core suites — **182 pass / 20 fail of 202** vs. Step 2's 173/29 vs. pre-migration 11/25. All Schrödinger, lookbehind annotation, exclusion-set, and core grammar tests pass. The 20 remaining failures are the same Patterns + Regex baseline failures from Phase 0, drifting within the Schrödinger non-determinism band. Diagnostic spans continue to print as character offsets, e.g. `[21[utf8]..22[utf8]]`.

**What remains of `TokenPosition`:** `struct TokenPosition { var tokenIndex: Int }` is still used by the legacy adapter type definitions and the bridge helpers (`TokenPosition.charPosition(in:input:)`, `CharPosition.tokenIndex(in:input:)`). These are leftover infrastructure for the LCNPLexer protocol surface; they retire when Phase B introduces a real per-terminal lex implementation and the parser stops needing to think about tokens at all.

Phase A is structurally done — every BSR/CRF/Descriptor/Oracle/parser position is `CharPosition`. The next move is Phase B (parser-driven literal/operator LCNP) where `tokenMatch()` calls into `LCNPLexer.lex(at: cI, terminalID: cL.nameID)` instead of reading from a pre-committed token array — at which point the `tokens: [Token]` field, the dual chain, and most of the legacy adapter can be deleted.

### Phase B — Parser-driven literal/operator LCNP

#### Phase B — Step 1 landed (Jun 9, 2026)

The parser is now wired through the `LCNPLexer` protocol — `tokenMatch()` no longer reads `tokens[…]` directly. Behavior is preserved by using `LegacyScannerLexAdapter` as the implementation; Step 2 will swap it for a true on-demand lexer.

Changes:

- `LegacyScannerLexAdapter.init(input:tokens:)` — was `init(scanner:)`. Lets `MessageParser` construct it from the per-parse input without needing a `Scanner` reference.
- `LegacyScannerLexAdapter.lex(…)` now returns `LexMatch.end == nextTokenStart` (start of the next visible token, or `input.endIndex`) instead of `token.image.endIndex`. This preserves the Phase A invariant that the parser's cursor always sits at a visible-token boundary, so non-LCNP code (`testSelect`, `followCheck`, `continuationViable`) keeps working unchanged.
- `MessageParser.lexer: LCNPLexer!` field, constructed in `parse()` as `LegacyScannerLexAdapter(input: input, tokens: tokens)`.
- `MessageParser.tokenMatch()` rewritten:
  ```swift
  let matches = lexer.lex(at: cI, terminalID: cL.nameID)
  guard !matches.isEmpty else { return nil }

  // ---(…) exclude: suppress dual interpretations when head is excluded
  let headKindID = tokens[tokenIdx(at: cI)].kindID!
  if cL.nameID != headKindID && cL.excludeBS.contains(headKindID) {
      return nil
  }

  // >>1(…) followAhead lookahead (unchanged)
  if cL.followAheadBS.count > 0 { … }

  return matches[0].end
  ```
  The two parser-level filters (`---()` exclude, `>>1()` followAhead) stay in the parser because they're per-slot context the lexer protocol doesn't see.

What didn't change yet:

- `Token.dual` chain still produced by the eager scanner and still walked by `testSelect` / `followCheck` / `continuationViable` to handle Schrödinger same-span ambiguity.
- The lexer still answers from the pre-committed `tokens` array; different-extent alternatives (the motivating `>>` vs `>` `>` case) still don't work because the eager scanner pre-commits to longest match.

**Validation:** 175 / 202 of the focused suite (Patterns + RegexLookbehind + SpecialTokens + Core), within the Schrödinger non-determinism band that's been tracking every run during the migration. Every Schrödinger, lookbehind annotation, exclusion-set, and core grammar test still passes.

#### Phase B — Step 2 landed (Jun 9, 2026)

Real on-demand literal lexer that reads `input` directly per query. Architectural shift: literal terminal matches no longer come from the eager scanner's pre-baked `tokens` array — they come from `input.hasPrefix(literal)` against the source string. The eager scanner still produces tokens (consulted by `testSelect` and the regex fallback), but the literal slice of `tokenMatch()` is now genuinely LCNP-on-demand.

New `OnDemandLiteralLexer: LCNPLexer` in `Descriptor.swift`:

```swift
struct OnDemandLiteralLexer: LCNPLexer {
    let input: String
    let literalSourceByID: [Int: String]   // terminalID → literal text
    let triviaRegexes: [Regex<Substring>]  // grammar's isSkip patterns
    let fallback: LegacyScannerLexAdapter  // for regex terminals
    
    func lex(at pos, terminalID) -> [LexMatch] {
        if let literal = literalSourceByID[terminalID] {
            let scanStart = skipTrivia(from: pos)
            guard input[scanStart...].hasPrefix(literal) else { return [] }
            let literalEnd = input.index(scanStart, offsetBy: literal.count)
            let cursorEnd = skipTrivia(from: literalEnd)
            return [LexMatch(terminalID: terminalID, end: cursorEnd)]
        }
        return fallback.lex(at: pos, terminalID: terminalID)  // regex / non-literal
    }
}
```

`skipTrivia(from:)` advances past any sequence of `isSkip` pattern matches — derived per-parse from `grammar.terminals` where `isSkip == true`. The `cursorEnd` after trailing-trivia skip coincides with the next visible-token start in well-formed inputs, preserving the parser's cursor-at-token-boundary invariant.

`MessageParser.parse()` now builds the literal source map and trivia regex list from `grammar.terminals` + `grammar.symbolToID`, constructs the on-demand lexer with the legacy adapter as fallback, and assigns it to `self.lexer`.

**Validation:** 173 / 202 in the focused suite — within the Schrödinger non-determinism band. Every Schrödinger, lookbehind annotation, exclusion-set, and core grammar test still passes. The fact that behavior is preserved despite literal matching coming from a completely different code path (raw `input.hasPrefix` instead of `tokens[idx].kindID` lookup) confirms the equivalence.

What this *enables* but doesn't yet *exercise*:

- **Different-extent literal alternatives.** `lex(pos, ">")` against input `>>…` now returns `[pos+1]` directly — the lexer doesn't care that the eager scanner pre-committed to `>>` as a single token. The parser can't *use* this yet because `testSelect` still consults the pre-baked tokens to predict whether to enter a slot, and at a mid-original-token position `testSelect` sees the wrong token. Phase B Step 3 migrates `testSelect` through the lexer too.
- **Schrödinger duals retiring for literals.** `tokenMatch()` no longer walks `Token.dual` — the dual chain is only consulted for regex queries (via the fallback) and by `testSelect` / `followCheck` / `continuationViable`. Once those migrate too, `Token.dual` becomes dead.

#### Phase B — Step 3 landed (Jun 10, 2026)

All four parser predicates now operate through the LCNP lex cache. `Token.dual` is no longer walked by anything in the parser hot path for terminal queries — the dual chain is consulted only by the legacy adapter's regex fallback and by one residual head-kindID lookup in `tokenMatch` / `testSelect` / `addDecscriptorsForAlternates` that the Schrödinger `---()` exclude semantic still needs.

Changes:

- `MessageParser.lexCache: [LexCacheKey: [LexMatch]]` — memoization table keyed by `(pos, terminalID)`. Cleared at the start of each parse.
- `MessageParser.cachedLex(at:terminalID:)` — wraps `lexer.lex` with the cache. Used by every parser-side terminal query.
- `tokenMatch()` — now reads `cachedLex(at: cI, terminalID: cL.nameID)` (was a direct `lexer.lex` call).
- `testSelect(slot:bracket:)` — rewritten:
  ```swift
  let headKindID = tokens[tokenIdx(at: cI)].kindID!
  let excludeFiresOnDuals = slot.excludeBS.contains(headKindID)
  
  func anyTerminalMatches(in bs: BitSet) -> Bool {
      for kID in bs {
          if kID == grammar.epsilonID { continue }
          if excludeFiresOnDuals && kID != headKindID { continue }
          if !cachedLex(at: cI, terminalID: kID).isEmpty { return true }
      }
      return false
  }
  
  if anyTerminalMatches(in: slot.firstBS) { return true }
  if slot.firstBS.contains(grammar.epsilonID),
     anyTerminalMatches(in: bracket.followBS) { return true }
  return false
  ```
- `followCheck(bracket:)` — iterates `bracket.followBS`, queries via `cachedLex`. No Schrödinger dual walk.
- `continuationViable(continuation:at:)` — iterates `continuation.firstBS`, queries via `cachedLex`.

`addDecscriptorsForAlternates` adjusted to keep LL(1) early-termination correct under LCNP semantics:

```swift
let headIdx = tokenIdx(at: i)
let headKindID = tokens[headIdx].kindID!
let llBase = X.isLocallyLL1 && tokens[headIdx].dual == nil
var current = X.alt
while let alt = current {
    if testSelect(slot: alt, bracket: X) {
        addDescriptor(L: alt.seq!, k: k, i: i)
        // Early-terminate ONLY when the matched alternate aligns with the
        // eager scanner's head — preserves longest-match semantics where
        // multiple alternates can prefix-match the same input.
        if llBase && alt.firstBS.contains(headKindID) { return }
    }
    current = alt.alt
}
```

Without the head-alignment check, grammar `S = "x" | "xx" | "xxx".` on input `"xx"` early-terminates at the `"x"` alternate (because LCNP's per-terminal lex says `hasPrefix("x")` matches) and never tries `"xx"`. The head-alignment check restores the original longest-match early-termination semantics.

**Validation:** 190 / 202 in the focused suite — **+15 net pass vs. Step 2 (173)**. The 6 `PatternSyntaxTests/adventAccepts` cases that were always-failing for the Schrödinger non-determinism band now all pass — the per-terminal LCNP path independently confirms identifier matches against input regardless of which interpretation the eager scanner pre-committed. Schrödinger, lookbehind annotation, exclusion-set, and core grammar tests all pass. The 12 remaining failures are the pattern-matching unambiguity / treesMatch baseline failures plus one regex-lookbehind shift within the documented non-determinism band.

What's still wired to the eager scanner:

- The `LegacyScannerLexAdapter` fallback in `OnDemandLiteralLexer` — regex/identifier terminals still get answered from the pre-baked token array.
- `tokens[tokenIdx(at: cI)].kindID` lookup in `tokenMatch` / `testSelect` / `addDecscriptorsForAlternates` — feeds the Schrödinger `---()` exclude semantic.
- `tokens[nextIdx]` lookup in `tokenMatch` — feeds `>>1(…)` followAhead.

These three residual eager-scanner consumers are what Phase D retires. Phase C is the next step: on-demand regex recognizer to replace the `LegacyScannerLexAdapter` fallback.

#### Phase B — Step 4 landed (Jun 10, 2026)

LL(1) early-termination in `addDecscriptorsForAlternates` is now **forced off** for the duration of the LCNP migration. The decision is to keep the existing `canEarlyTerminate` variable and all supporting infrastructure (`GrammarNode.isLocallyLL1`, `hasLiteralPrefixOverlapAcrossAlternates` in `GrammarDiagnostics.swift`, the multi-lex prefix-overlap diagnostic) intact, but gate the optimisation behind a hard-coded `false` so the parser explores every selectable alternate during the transitional phase.

Change in `CallReturnForest.swift:addDecscriptorsForAlternates`:

```swift
// TODO: re-enable for multi-lex. Temporarily forced off while the
// LCNP migration proceeds — `X.isLocallyLL1` (and its supporting
// prefix-overlap diagnostic) is preserved so we can switch this back
// on once the parser-driven lex path is in place.
let canEarlyTerminate = false && X.isLocallyLL1
```

Rationale:

- Under classic LL(1) the optimisation was safe because alternate FIRSTs were disjoint as sets.
- Under multi-lex, distinct terminal IDs can co-match the same input position (literal-prefix overlap, regex vs. literal overlap, identical regex sources). `handleAlternatesAmbiguity` already caught the *static* form of this and zeroed `isLocallyLL1` accordingly, and Step 3's head-alignment guard handled the *dynamic* form. Both remain in place.
- The looming Phase B Step 3 plan (multi-match `lex` returning several `LexMatch.end` positions per terminal) and the eventual Phase C/D/E moves will make exploration of every selectable alternate semantically necessary. Disabling the shortcut now keeps later steps from accidentally relying on early-termination behaviour that will have to be retracted anyway.
- Keeping the variable and the surrounding infrastructure (rather than deleting them) avoids re-doing the static analysis when we eventually re-enable the optimisation after Phase F's `lexLKH` predicate pruning is in place.

What was *not* changed:

- `GrammarNode.isLocallyLL1` still computed in `GrammarDiagnostics.handleAlternatesAmbiguity()`.
- `hasLiteralPrefixOverlapAcrossAlternates()` and its three conflict-pattern checks (literal-prefix, regex/literal overlap, identical regex sources) still execute during grammar load.
- The Step 3 head-alignment guard (`alt.firstBS.contains(headKindID)`) is untouched. Once we flip the gate back on it remains the correctness anchor.

**Validation:** Patterns + RegexLookbehind + SpecialTokens + Core suites — **190 pass / 12 fail of 202**. Identical to Step 3's headline number. The 12 failures are the same baseline:

- 5 `PatternSyntaxTests/unambiguous` (testNonBinding1/2/3/4/6 — residual ambiguity in matchPattern alternates).
- 6 `PatternSyntaxTests/treesMatch` (testNonBinding1–6 — failed parses producing `MissingExpr` placeholders).
- 1 `RegexLookbehindIntegration/adventAccepts` (`ternary-with-spaces` — drift within the Schrödinger non-determinism band).

That parity is unsurprising: the early-termination path was already rare in practice after Step 3's head-alignment guard tightened it, and the grammars that would have hit it now simply walk a couple of extra alternates per slot before producing the same descriptor set.

**Carryover:** see `TODO.md` item 5 ("LL(1) early-termination re-enable evaluation").

#### Phase B — Step 3 plan (remaining)

Build a real on-demand `LCNPLexer` that reads `input` directly per query rather than indexing into the pre-baked `tokens` array. Multiple match-end positions for the same terminal then become possible, enabling the doc's motivating case:

- `lex(pos, terminalID(">>"))` returns `[pos+2]` when input is `>>…`
- `lex(pos, terminalID(">"))` returns `[pos+1]` at the same position
- The parser forks descriptors over both extents where the grammar predicts them

Open design points to resolve before writing the new lexer:

1. **Trivia handling.** Without consulting `tokens`, the lexer needs the grammar's `isSkip` patterns and a `skipTrivia(from:)` step before pattern matching, so cursor positions don't accumulate trivia drift across forks.
2. **Cursor invariant.** Step 1 keeps `cI` at a visible-token boundary so the legacy `tokens[tokenIdx(at: cI)]` lookups in `testSelect` etc. work. A true on-demand lexer breaks that invariant for split extents. Either we (a) preserve the invariant by having the lexer return next-visible-token-start, which gives up the `>>` → `>` `>` fork (current Step 1 behavior, just wired through the API), or (b) drop the invariant and migrate `testSelect` / `followCheck` / `continuationViable` to also operate through the lexer instead of `tokens[…]`. (b) is the real LCNP move.
3. **Multi-match fork in `tokenMatch`.** When the lexer returns multiple `LexMatch`es, the GLL inner loop needs to fork descriptors:
   ```swift
   if matches.count == 1 { /* in-place continue */ }
   else { for m in matches { addDescriptor(L: cL.seq!, k: cU, i: m.end) ; addYield(…) } ; continue nextDescriptor }
   ```
   The infrastructure already supports this — descriptors are arbitrary `(L, k, i)` triples.
4. **Same-span ambiguity.** With per-terminal lex, the parser asks for `if` keyword AND `identifier` regex at the same position independently. Both can match. The Schrödinger dual chain becomes redundant for these terminals — but the eager scanner still produces it. `Token.dual` retirement is staged in Phase D.

Introduce the real `LCNPLexer` path for literal and operator terminals by integer terminal ID. Terminal consumption calls `lex(at: cI, terminalID: cL.nameID)` and forks one descriptor per returned `LexMatch.end`.

For the motivating case:
- `lex(pos, terminalID(">>"))` returns `[pos+2]` when the input has `>>`
- `lex(pos, terminalID(">"))` returns `[pos+1]` at the same source position
- The parser forks descriptors for both terminal extents where the grammar predicts them

This removes the special `≋` / `~~~` path first, before taking on same-span token ambiguity, regex islands, or lookbehind cleanup.

Touch list:
- `Scanner.swift` / new `LCNPLexer` — answer literal/operator `lex` queries from the original input
- `MessageParser.swift:tokenMatch()` — return `[LexMatch]` / `[CharPosition]` and fork descriptors for multiple terminal ends
- `Grammar.frankensteinID`, `≋` sentinel handling, and Frankenstein prefix-split code in `tokenMatch()` retire in this phase
- Swift/operator grammar rules that currently depend on `~~~` are rewritten to use ordinary literal terminals

**Validation:** all Phase A cases remain stable, and targeted `>>` / nested generic cases parse without Frankenstein machinery.

### Phase C — General parser-driven terminal matching

Broaden `lex(at:terminalID:)` to all ordinary literal and regex terminals. Preserve integer terminal IDs and `BitSet` FIRST/FOLLOW checks. At this point terminal matching no longer depends on a linear current token except when explicitly running through the legacy adapter.

Touch list:
- `Scanner.swift` / `LCNPLexer` — reusable per-terminal recognizers for literals and regex terminals
- `MessageParser.swift` — remove dependence on `[Token]` for normal terminal matching
- Test infrastructure — construct parser input from source text plus `LCNPLexer`

**Validation:** all Phase A/B cases remain stable. No broad disambiguation retirements happen until the LCNP path is the normal path.

#### Phase C — Step 1 landed (Jun 10, 2026)

`OnDemandLiteralLexer` now answers **pure regex terminals** directly from `input` via `Substring.prefixMatch(of:)`, alongside the existing literal-terminal path. The eager scanner's pre-baked `tokens` array is consulted only as a fallback for regex terminals that carry filtering metadata (lookbehind specs / gated scanner-mode transitions) that the on-demand path doesn't yet understand.

Definition of "pure regex terminal" at the construction site (`MessageParser.parse(...)`):

```swift
for (name, pat) in grammar.terminals {
    guard let id = grammar.symbolToID[name] else { continue }
    if pat.isLiteral {
        literalSourceByID[id] = pat.source
    } else if !pat.isSkip, pat.transitions.isEmpty, pat.lookbehind.isEmpty {
        // Pure regex terminal: no scanner-mode filtering, no
        // position-gated suppression. Safe to answer from input directly.
        regexByID[id] = pat.regex
    }
    if pat.isSkip {
        triviaRegexes.append(pat.regex)
    }
}
```

`OnDemandLiteralLexer.lex(at:terminalID:)` adds the regex arm:

```swift
if let regex = regexByID[terminalID] {
    let scanStart = skipTrivia(from: pos)
    guard scanStart < input.endIndex else { return [] }
    guard let m = input[scanStart...].prefixMatch(of: regex),
          m.0.endIndex > scanStart else { return [] }
    let cursorEnd = skipTrivia(from: m.0.endIndex)
    return [LexMatch(terminalID: terminalID, end: cursorEnd)]
}
return fallback.lex(at: pos, terminalID: terminalID)
```

What this changes:

- Regex terminal queries no longer require the eager scanner to have pre-committed a token at this position. `lex(pos, identifier)` matches `input[scanStart...]` against the identifier regex directly, regardless of whether the scanner's longest-match policy chose `if` as a keyword or identifier here.
- For terminals participating in Schrödinger dual chains, the on-demand path and the legacy-adapter dual walk both yield matches independently — the parser already enumerates terminal IDs per alternate (after Step 4's LL(1) shortcut disable), so each terminal gets queried directly and the dual chain becomes redundant in this path.
- Terminals with `<<1` / `<<2` / `++1` / `--1` / `++2` / `--2` lookbehind annotations, or gated-transition triples like `=== "X" >>> "Y"`, still go through the legacy adapter. Phase E covers their migration to on-demand equivalents.

What this doesn't change yet:

- `tokenMatch()` still picks `matches[0].end` — the multi-match fork (forking descriptors over multiple `LexMatch.end` values for the same terminal) is the immediate follow-up. With the regex path returning at most one match today this is a no-op, but variable-length regex matches and same-position alternatives over different terminals are the structural cases the fork unlocks.
- The Schrödinger `---()` exclude check in `tokenMatch` / `testSelect` / `addDecscriptorsForAlternates` still reads `tokens[tokenIdx(at: cI)].kindID` for the head token. These are the residual eager-scanner consumers Phase D retires.
- `LegacyScannerLexAdapter` is still constructed every parse — it's just the fallback now, not the regex backbone.

**Validation:** Patterns + RegexLookbehind + SpecialTokens + Core suites — **190 pass / 12 fail of 202**. Bit-for-bit identical to Step 4's headline. Same 12 failures (5 `PatternSyntaxTests/unambiguous`, 6 `PatternSyntaxTests/treesMatch`, 1 `RegexLookbehindIntegration/adventAccepts ternary-with-spaces`). Schrödinger, lookbehind annotation, exclusion-set, and core-grammar tests all still pass — including the regex-vs-operator lookbehind cases, which validates that the fallback gate (terminals with non-empty `lookbehind` keep going through the legacy adapter) is doing its job.

That the regex hot path's underlying implementation has changed (raw `prefixMatch(of:)` against `input` instead of `tokens[idx].kindID` lookup) without moving any test result is the meaningful signal — for the terminals we now own, the on-demand path agrees with what the eager scanner had pre-baked.

What's still routed through `LegacyScannerLexAdapter.lex`:

- Regex terminals with `lookbehind.isEmpty == false` (e.g. `plainRegularExpressionLiteral` with `<<1` / `<<2` annotations).
- Regex terminals with `transitions.isEmpty == false` (gated scanner-mode triples).
- Terminals not present in either `literalSourceByID` or `regexByID` for any other reason (e.g. failed grammar lookup).

These are the targets for Phase E (regex island & lookbehind migration). Once they move, `LegacyScannerLexAdapter` and the entire `tokens: [Token]` field can be retired alongside `Token.dual` (Phase D).

**Next step (queued):** the doc's "multi-match fork in `tokenMatch`" plan from the Phase B Step 3 remaining-plan section. It's now structurally interesting because the regex on-demand path lets us return multiple match ends per terminal (e.g. a regex matching `\d+` against input `123` could return positions 1, 2, 3). The current implementation still returns at most one match per terminal — that ceiling is what the fork lifts.

#### Phase C — Step 2 landed (Jun 10, 2026)

The "multi-match fork in `tokenMatch`" plan from the Phase B Step 3 remaining-plan section has landed. `tokenMatch()` now returns `[CharPosition]` (deduped end positions, first-seen order) rather than a single `CharPosition?`. The main parse loop forks descriptors when more than one distinct end comes back.

Changes:

- `MessageParser.tokenMatch()` signature is now `() -> [CharPosition]`. The body keeps the two parser-level filters (`---()` exclusion via head kindID, `>>1()` followAhead lookahead) unchanged — they're global gates that fire before the fork. After filtering, the function dedupes match ends with a `Set<CharPosition>` insert guard while appending to a result vector, so callers see distinct ends in first-seen order regardless of how many lex sources reported them.
- The main parse loop's `.T, .TI, .C` arm now dispatches three ways:
  ```swift
  let ends = tokenMatch()
  if ends.isEmpty {
      recordMismatch(expected: cL.name)
      continue nextDescriptor
  }
  if ends.count == 1 {
      // hot path: continue in place
      let next = ends[0]
      addYield(L: cL, i: cU, k: cI, j: next)
      cI = next
      cL = cL.seq!
  } else {
      // fork: one continuation descriptor per distinct end
      for end in ends {
          addYield(L: cL, i: cU, k: cI, j: end)
          addDescriptor(L: cL.seq!, k: cU, i: end)
      }
      continue nextDescriptor
  }
  ```

Behavioural reality today:

- `OnDemandLiteralLexer` returns at most one match per terminal: the literal arm checks `hasPrefix` once, the regex arm calls `prefixMatch(of:)` which gives the engine's chosen (typically longest) match, both wrapped in a single-element array.
- `LegacyScannerLexAdapter` walks the Schrödinger dual chain on `kindID == terminalID` equality. Duals at a position share the same end (the eager scanner's longest-match policy guarantees same-extent equal-length alternatives), so the chain produces matches that collapse to one distinct end under the dedupe.

So the fork branch doesn't fire on the current test inputs. The change is structural: it gives the GLL inner loop a place to receive variable-length match sets when later phases add lexers that produce them (e.g. greedy/non-greedy regex variants returning multiple legal extents, or future PEG-style ordered alternatives broadcasting all viable cuts).

**Validation:** Patterns + RegexLookbehind + SpecialTokens + Core suites — **191 pass / 11 fail of 202**, a one-test improvement vs. the Step 4 / Phase C Step 1 baseline of 190/12. The previously-flaky `RegexLookbehindIntegration/adventAccepts ternary-with-spaces` landed on the pass side this run; that case has been drifting in and out of the Schrödinger non-determinism band across every Phase A/B run, so the swing is consistent with normal variance rather than a real Step 2 effect. The 11 remaining failures are the same testNonBinding `unambiguous`/`treesMatch` cases the doc has tracked since Phase 0.

Treating the result as "no change" is the safe read: the multi-match fork has the infrastructure in place but isn't exercised by today's lex sources.

**What this unlocks:**

- Regex terminals that surface multiple legitimate extents (greedy + non-greedy, or alternation operators that all match a prefix) can now be returned from `lex` as separate `LexMatch` values with distinct `end` positions and the parser will explore each branch.
- The motivating `>>` vs `>` `>` case from the doc — at one input position the parser asks for `>>` (one terminal) and `>` (a different terminal) — was already handled correctly by Phase B Step 3's `testSelect` migration + Step 4's LL(1) shortcut disable: those are *separate* lex queries from *different alternates*, not multi-match within a single query. Step 2 here addresses the *intra-terminal* multi-match shape, which is orthogonal and lands ahead of demand.

**What's still wired to the eager scanner** (unchanged since Phase C Step 1):

- `LegacyScannerLexAdapter` fallback in `OnDemandLiteralLexer` for regex terminals with `lookbehind` annotations or gated `transitions`.
- `tokens[tokenIdx(at: cI)].kindID` lookup in `tokenMatch` / `testSelect` / `addDecscriptorsForAlternates` for the Schrödinger `---()` exclude gate.
- `tokens[nextIdx]` lookup in `tokenMatch` for the `>>1()` followAhead lookahead.

These are Phase D/E retirement targets.

**Phase B/C cumulative state:** Phase B is done end-to-end (LCNPLexer protocol + cache + literal on-demand + parser-side predicates + LL(1) gate disabled). Phase C Step 1 (regex on-demand) and Step 2 (multi-match fork) are done. The next architectural move is Phase D (retire `Token.dual` / `propagateExcludeSets` / `excludeBS` once same-span ambiguity is handled by independent per-terminal lex queries everywhere) or Phase E (move filtered regex/lookbehind terminals into the on-demand path, retiring `LegacyScannerLexAdapter`).

### Phase D — Retire same-span Schrödinger plumbing

Once all terminal matches are queried independently by terminal ID from source position, same-span ambiguity no longer needs `Token.dual`. A keyword and an identifier can both return the same end position from the same start; the grammar slot determines which terminal is being requested.

Remove or replace:
- `Token.dual`, all Schrödinger walking in `tokenMatch()`, `testSelect()`, and `followCheck()`
- `Grammar.propagateExcludeSets`, `GrammarNode.exclude` / `excludeBS`, and `---()` parsing, after former exclusion cases are covered by terminal-specific keyword/identifier recognition

**Validation:** keyword/identifier and soft-keyword tests retain the same accepted parses, with descriptor counts measured before and after.

#### Phase D — Step 1 landed (Jun 10, 2026)

The `>>1(…)` followAhead check inside `tokenMatch()` was the last place in the parser hot path that walked the `Token.dual` chain. It's now migrated to a per-end LCNP lex query, mirroring the Phase B Step 3 migration of `testSelect` / `followCheck` / `continuationViable`.

Before:

```swift
if cL.followAheadBS.count > 0 {
    let nextIdx = idx + 1
    var ok = false
    if nextIdx < tokens.count {
        var probe: Token? = tokens[nextIdx]
        while let p = probe {
            if p.kindID == grammar.eosID || cL.followAheadBS.contains(p.kindID) {
                ok = true
                break
            }
            probe = p.dual
        }
    } else {
        ok = true
    }
    if !ok { return [] }
}
```

After:

```swift
if cL.followAheadBS.count > 0 {
    matches = matches.filter { m in
        // Past the end of input acts as EOS — always allowed.
        if m.end >= input.endIndex { return true }
        for fID in cL.followAheadBS where fID != grammar.epsilonID {
            if !cachedLex(at: m.end, terminalID: fID).isEmpty { return true }
        }
        return false
    }
    if matches.isEmpty { return [] }
}
```

Semantic equivalence:

- The eager scanner's EOS token always sits at `input.endIndex` (image is `input[end..<end]`); under LCNP the equivalent "we're past the visible input" condition is `m.end >= input.endIndex`. That branch unconditionally accepts, matching the original `p.kindID == grammar.eosID` short-circuit.
- The dual walk was: "any token in the dual chain at the next position with a kindID in `followAheadBS`". The LCNP query is: "any terminal in `followAheadBS` whose lex returns a non-empty result at `m.end`". Under same-span ambiguity those are the same set — `Token.dual` was constructed precisely from terminals whose regexes matched equal-length input at that position, so a dual-chain kindID match corresponds 1:1 to an LCNP lex match.
- The per-end filter integrates naturally with Step 2's multi-match shape: each candidate end gets validated independently. With today's single-end lex sources, the filter just keeps or drops the single match — same behaviour as the original boolean.

Other consequences:

- The `idx`/`nextIdx`/`tokens[…]` lookups in the followAhead block are gone — only the `idx`/`headKindID` lookup for the `---()` exclude gate remains in `tokenMatch`. Phase D Step 2 will be retiring that one.
- The function-level `let` on `matches` became `var` to support the filter. No allocation savings, no extra cost — the filter rebuilds the array but today there's only one element in it.

**Validation:** Patterns + RegexLookbehind + SpecialTokens + Core suites — **190 pass / 12 fail of 202**, bit-for-bit identical to the Step 4 / Phase C Step 1 baseline. Same 12 failures (5 `PatternSyntaxTests/unambiguous`, 6 `PatternSyntaxTests/treesMatch`, 1 `RegexLookbehindIntegration/adventAccepts ternary-with-spaces`). The `ternary-with-spaces` test landed on the fail side this run, reverting from Step 2's pass — confirming this is the documented Schrödinger non-determinism band swinging, not a Step 1 regression.

**What's left of `Token.dual` in the codebase:**

- `LegacyScannerLexAdapter.lex` still walks the dual chain when answering fallback queries for filtered regex terminals (with `lookbehind` or `transitions`). Retired by Phase E when those terminals move into the on-demand path.
- Nothing else. The parser hot path is now free of `Token.dual` walks.

**Remaining eager-scanner consumers in the parser:**

1. `tokens[tokenIdx(at: cI)].kindID` head lookup in `tokenMatch` / `testSelect` / `addDecscriptorsForAlternates` — feeds the `---()` exclude gate.
2. `LegacyScannerLexAdapter.lex` fallback for filtered regex terminals.

Phase D Step 2 will tackle (1) — migrate the `---()` exclude semantic so it doesn't need a single canonical "head" token to compare against. The natural shape: per-alternate, query `lex(cI, excluded-terminalID)`; if any excluded terminal lexes at `cI` and we're trying to match a different terminal, suppress this match. That's the LCNP-faithful version of the head-dependent gate, and it retires the last `tokens[…]` consumer in the parser. After that, (2) is the only remaining eager-scanner dependency and Phase E owns it.

#### Phase D — Step 2 landed (Jun 10, 2026)

The `---()` exclude check in `tokenMatch` is now a per-end LCNP query. The `tokens[tokenIdx(at: cI)].kindID` head lookup is gone from `tokenMatch` entirely.

Change:

```swift
// Before — head-based exclude
let idx = tokenIdx(at: cI)
let headKindID = tokens[idx].kindID!
if cL.nameID != headKindID && cL.excludeBS.contains(headKindID) {
    return []
}

// After — per-end LCNP exclude
if !cL.excludeBS.isEmpty {
    matches = matches.filter { m in
        for eID in cL.excludeBS where eID != cL.nameID && eID != grammar.epsilonID {
            for em in cachedLex(at: cI, terminalID: eID) where em.end == m.end {
                return false
            }
        }
        return true
    }
    if matches.isEmpty { return [] }
}
```

Semantic equivalence — match-end is the key:

- Original: "if the eager scanner committed to terminal H at this position, and H is in our exclude set, suppress any non-H interpretation". That fires when the scanner's longest-match policy + dual-chain construction puts the excluded terminal at the same span.
- New: "for each candidate end of our terminal T, if any excluded terminal E ≠ T also lexes at this position with the *same end*, suppress this candidate". That fires when the two terminals genuinely consume the same input span.

Walking the canonical cases:

| Input | Slot | Exclude | Original | LCNP per-end |
|---|---|---|---|---|
| `if` | identifier | `{if}` | identifier suppressed (head=`if`) | `lex(0, if)=[end=2]`, `lex(0, identifier)=[end=2]` — same end → suppress identifier |
| `iffy` | identifier | `{if}` | identifier kept (head=identifier — longer) | `lex(0, if)=[end=2]`, `lex(0, identifier)=[end=4]` — different ends → keep identifier |
| `for` | identifier | `{for}` | identifier suppressed (head=`for`) | `lex(0, for)=[end=3]`, `lex(0, identifier)=[end=3]` — same end → suppress |
| `forx` | identifier | `{for}` | identifier kept (head=identifier) | `lex(0, for)=[end=3]`, `lex(0, identifier)=[end=4]` — different ends → keep |

The crucial insight: under LCNP we don't need a global "head" — *match-end equality* is the property that captures "same-span ambiguity", which is what the eager scanner's longest-match + dual-chain machinery was encoding all along. Each terminal's lex returns its own best end against `input` directly; the literal arm's `hasPrefix` will return a 2-char match for `if` against `iffy`, while the identifier-regex arm's `prefixMatch` returns a 4-char match. The exclude check sees them as covering different spans and lets the identifier through.

False-start note: the first attempt added a "keyword-boundary guard" to `OnDemandLiteralLexer` — suppress `lex(pos, literal)` when the literal starts with an identifier-start character and is followed by an identifier-continue character. That broke 95 CoreGrammarTests because grammars like `S = "a" "b" .` use single-letter alphabetic literals with no identifier-class regex in scope. Reverted immediately: the guard hardcoded Unicode identifier conventions that don't generalise across grammars, and it turned out the per-end exclude check doesn't need it. The lex API correctly returns "literal `if` matches the first 2 chars of `iffy`"; the parser's match-end comparison handles the rest.

For the doc's stalking-horse example `S = "x" | "xx" | "xxx" .` on input `"xx"`:
- `lex(0, "x") = [end=1]`, `lex(0, "xx") = [end=2]`, `lex(0, "xxx") = []`
- With LL(1) early-term disabled (Phase B Step 4), all three alternates get tried via per-terminal lex queries.
- Alternate `"x"` enters, descriptor advances to position 1, fails to reach EOS.
- Alternate `"xx"` enters, descriptor advances to position 2 == `input.endIndex`, succeeds.
- Alternate `"xxx"` doesn't enter (empty lex result).
- **One successful parse**, generated by the `"xx"` alternate. The other two paths die on continuation mismatches without affecting the result.

**Validation:** Patterns + RegexLookbehind + SpecialTokens + Core suites — **191 pass / 11 fail of 202**. Same 11 failures as the prior baselines (5 `unambiguous`, 6 `treesMatch` — the testNonBinding cases that have been there since Phase 0). The `ternary-with-spaces` test landed on the pass side this run — within the documented Schrödinger non-determinism band. Every Schrödinger, lookbehind annotation, and exclusion-set test still passes; ExclusionSets' 11-case suite continues to fully pass, validating that the per-end LCNP exclude check behaves identically to the head-based original across the existing test bed.

**Remaining eager-scanner consumers in the parser** (down from three to two):

1. `tokens[tokenIdx(at: cI)].kindID` head lookup in `testSelect` / `addDecscriptorsForAlternates` — same `---()` exclude pattern but at a different filter point. Phase D Step 3 target.
2. `LegacyScannerLexAdapter.lex` fallback for filtered regex terminals (lookbehind/transitions). Phase E target.

`tokenMatch` itself no longer touches `tokens[…]` or `Token.dual` at all.

**Phase D progress:** Step 1 retired the followAhead dual walk; Step 2 retired the exclude head lookup in `tokenMatch`. The next move is `testSelect` and `addDecscriptorsForAlternates` (both still consult `tokens[idx].kindID` for the same exclude semantic). After that, only the legacy adapter remains as an eager-scanner consumer, and Phase D wraps up alongside `Token.dual`'s last user retiring in Phase E.

#### Phase D — Step 3 landed (Jun 10, 2026)

`testSelect` is the only remaining `tokens[…].kindID` consumer in the parser hot path (`addDecscriptorsForAlternates` reaches it transitively via the `testSelect` call on each alternate). Migrating `testSelect`'s exclude semantic to the same per-end LCNP filter used in `tokenMatch` retires both at once.

Change:

```swift
// Before — head-based prediction filter
let headKindID = tokens[tokenIdx(at: cI)].kindID!
let excludeFiresOnDuals = slot.excludeBS.contains(headKindID)

func anyTerminalMatches(in bs: BitSet) -> Bool {
    for kID in bs {
        if kID == grammar.epsilonID { continue }
        if excludeFiresOnDuals && kID != headKindID { continue }
        if !cachedLex(at: cI, terminalID: kID).isEmpty { return true }
    }
    return false
}

// After — per-end LCNP filter
func anyTerminalMatches(in bs: BitSet) -> Bool {
    for kID in bs {
        if kID == grammar.epsilonID { continue }
        let matches = cachedLex(at: cI, terminalID: kID)
        if matches.isEmpty { continue }
        if slot.excludeBS.isEmpty { return true }
        let survives = matches.contains { m in
            for eID in slot.excludeBS where eID != kID && eID != grammar.epsilonID {
                for em in cachedLex(at: cI, terminalID: eID) where em.end == m.end {
                    return false
                }
            }
            return true
        }
        if survives { return true }
    }
    return false
}
```

Semantic equivalence:

- The original "if head's kindID is in `slot.excludeBS`, only count predict-set entries whose terminalID equals the head's" amounts to: "consider only the canonical (head) interpretation, suppress dual interpretations". That fires when the eager scanner committed to an excluded terminal at this position.
- The LCNP version asks the same question per terminal: "does this terminal lex here, and does its match end disagree with every excluded terminal's match end here?" When excluded terminal E lexes at the same end as candidate T, T's interpretation is the "dual" of E and gets suppressed. Same predicate, different mechanism, no head needed.

The fast-path `if slot.excludeBS.isEmpty { return true }` preserves the original's behaviour for the vast majority of slots that don't have `---()` — no per-end work, single lex call, identical to today.

**Cost picture:** For slots with non-empty `excludeBS`, each candidate terminal in the predict set may now trigger up to `|excludeBS|` extra `cachedLex` calls. The lex cache memoizes by `(pos, terminalID)`, so repeated queries during a `testSelect` for the same `cI` reuse results — the worst case is the first call for each excluded terminal at this position. The `ExclusionSets/testDescriptorReduction` test (which expects `descWith < descWithout`) still passes, so the per-end filter doesn't lose its descriptor-saving property in practice.

**Validation:** Patterns + RegexLookbehind + SpecialTokens + Core suites — **191 pass / 11 fail of 202**, identical to Step 2. Same 11 failures (5 `unambiguous`, 6 `treesMatch` — the testNonBinding cases). All ExclusionSets tests pass, including `testDescriptorReduction` which expects exclude to provably reduce descriptor count. Every Schrödinger and lookbehind test passes too.

**Parser hot path is now eager-scanner-free.** The `tokens[…]` and `Token.dual` references that remain in the codebase are:

- `LegacyScannerLexAdapter.lex` — walks the dual chain when answering fallback queries for filtered regex terminals (with `lookbehind` or `transitions`). Phase E.
- `parse(tokens:trivia:input:)` setup — assigns `kindID` to each token (including duals) from `grammar.symbolToID`. Not in the parser hot path; retires when the eager scanner itself does.
- `nextTokenStart(after:)` / `tokenIdx(at:)` / `tokenIndexByStart` — still used for diagnostics (the `recordMismatch` path, trace output), not for parsing decisions.

`tokenMatch`, `testSelect`, `followCheck`, `continuationViable`, `addDecscriptorsForAlternates`, and the main parse loop's `.T/.TI/.C` arm all run purely off `cachedLex` results. The eager scanner is now an implementation detail of the legacy fallback adapter, not a participant in parser logic.

**Phase D status:** Done for the parser. Full retirement of `---()` (alternative grammar mechanism for keyword-vs-identifier disambiguation) is `TODO.md` item 8.

**Next move:** Phase E — migrate filtered regex terminals (`<<1`/`<<2`/`++1`/`--1` lookbehind, gated `=== ">>>"` transitions) into the on-demand path, retiring `LegacyScannerLexAdapter` and the eager scanner end-to-end.

#### Post-Phase F review TODO — exclude semantics and annotations

Carried forward to `TODO.md` items 6 and 7 (exclude correctness/effectiveness audit; sweep of every APUS annotation against multi-lex).

### Phase E - Lookbehind migration, retire LegacyScannerLexAdapter

#### Phase E — Step 1 landed (Jun 11, 2026)

`++N(…)` / `--N(…)` lookbehind annotations now evaluate parser-side from the GLL commit log, with no grammar changes required. Lookbehind-annotated regex terminals route through the on-demand path; the eager scanner emits all syntactically-possible matches and the parser suppresses ones that fail the annotation.

**Constraint that shaped the design.** Lookbehind is a property of the terminal that real language grammars rely on, and APUS aims to use language grammars (Swift, Python, etc.) as-is without substantial rewrites. That ruled out "rewrite the grammar so the annotation is no longer needed" (option 3 from the design discussion). It also ruled out "keep `LegacyScannerLexAdapter` as a permanent lookbehind backend" (the user explicitly didn't want a dual scanner model). The viable shape is: lookbehind stays *as written in the grammar*, the *implementation* migrates from scanner-side to parser-side, using GLL state rather than the eager scanner's committed-token stream.

**Implementation:**

New parser-side types (`MessageParser.swift`):

```swift
struct ResolvedLookbehindRule {
    let polarity: LookbehindPolarity
    let distance: Int
    let kindsBitSet: BitSet  // resolved from kinds: [String] via grammar.symbolToID
}
struct ResolvedLookbehindLine { let rules: [ResolvedLookbehindRule] }
struct ResolvedLookbehindSpec {
    let positiveLines: [ResolvedLookbehindLine]
    let negativeLines: [ResolvedLookbehindLine]
    var isEmpty: Bool { positiveLines.isEmpty && negativeLines.isEmpty }
}
struct TerminalCommit { let kindID: Int; let start: CharPosition }
```

Per-parse state:

```swift
var lookbehindByTerminalID: [Int: ResolvedLookbehindSpec] = [:]
var terminalCommitsByEnd: [CharPosition: [TerminalCommit]] = [:]
```

The `.T`/`.TI`/`.C` arm in the main parse loop records each terminal commit:

```swift
addYield(L: cL, i: cU, k: cI, j: next)
terminalCommitsByEnd[next, default: []].append(
    TerminalCommit(kindID: cL.nameID, start: cI))
```

`tokenMatch` evaluates the lookbehind gate between `cachedLex` and the `---()` exclude check:

```swift
if let lookbehind = lookbehindByTerminalID[cL.nameID],
   !lookbehindAllows(lookbehind, at: cI) {
    return []
}
```

The evaluator mirrors `Scanner.lookbehindAllows` exactly: positives OR'd (any match → allow, overriding negatives); negatives OR'd (any match → block); whitelist mode (positives-only, no match) → block; default allow. Each rule's "N visible terminals back from `pos`" is implemented as a walk through `terminalCommitsByEnd`, taking set-unions when multiple histories arrive at the same position:

```swift
func previousKindIDs(at pos: CharPosition, distance: Int) -> BitSet {
    var endPositions: Set<CharPosition> = [pos]
    for _ in 1..<distance {
        var next: Set<CharPosition> = []
        for p in endPositions {
            if let commits = terminalCommitsByEnd[p] {
                for c in commits { next.insert(c.start) }
            }
        }
        if next.isEmpty { return BitSet() }
        endPositions = next
    }
    var result = BitSet()
    for p in endPositions {
        if let commits = terminalCommitsByEnd[p] {
            for c in commits { result.insert(c.kindID) }
        }
    }
    return result
}
```

This is the LCNP-multi-history equivalent of the original Schrödinger-dual chain walk in `Scanner.matchesLine`: the original walked `cur.dual` chains because multiple terminals could share the same span; the new code walks the union of kindIDs that committed to ending at the same position via different parse paths.

Routing changes in `MessageParser.parse(...)`:

```swift
// Before — lookbehind-annotated regex routed through LegacyScannerLexAdapter
} else if !pat.isSkip, pat.transitions.isEmpty, pat.lookbehind.isEmpty {
    regexByID[id] = pat.regex
}

// After — lookbehind-annotated regex routed through on-demand; gate fires
// parser-side in tokenMatch.
} else if !pat.isSkip, pat.transitions.isEmpty {
    regexByID[id] = pat.regex
}
if !pat.lookbehind.isEmpty {
    lookbehindByTerminalID[id] = resolveLookbehindSpec(pat.lookbehind)
}
```

The two `guard lookbehindAllows(...)` guards in `Scanner.swift`'s scan loop are retired — the scanner now emits all syntactically-possible matches; the parser does the filtering. The `LookbehindSpec` / `LookbehindRule` / `LookbehindLine` types stay where they are (on `TokenPattern`) — they're the grammar-level representation; the parser-side `Resolved…Spec` types are the BitSet-based runtime form, built at parse setup.

**Validation:** `SpecialTokenTests/RegexLookbehind` — **11 / 11 pass**. `RegexLookbehindIntegration` — **11 / 12 pass**, with the flaky `ternary-with-spaces` failing within the documented Schrödinger non-determinism band (it's been swinging between pass and fail across every phase). Patterns + RegexLookbehind + SpecialTokens + Core — **191 / 11**, identical to the Phase D Step 3 baseline. All Schrödinger / ExclusionSets / Core / lookbehind tests pass; same 11 testNonBinding pattern failures as Phase 0.

**What this changes architecturally:**

- Lookbehind no longer requires the eager scanner. The scanner still produces tokens (used by `LegacyScannerLexAdapter` fallback for terminals with `transitions`, and by diagnostics paths), but lookbehind is now an LCNP concept evaluated against parser state.
- Lookbehind-annotated regex terminals join literals and pure regex terminals on the on-demand path. The only routing distinction left at construction time is `transitions.isEmpty` — scanner-mode gating, still in the fallback adapter.
- The semantic for Schrödinger duals at the "N tokens back" position falls out for free: the eager scanner's dual-chain OR-walk becomes a BitSet-union of every kindID committed at that position by any GLL path.

**Multi-history semantic.** Under GLL multi-history, "the previous terminal" isn't a single answer — different descriptor paths may have arrived at `cI` by committing different terminals. The new `previousKindIDs(at: pos, distance: N)` returns the *union* across all paths. The lookbehind evaluator then asks each line "does any rule's kinds set intersect this position's union?" which is *permissive*: if any path's previous-terminal satisfies a `++N` line, allow; if any path's previous-terminal satisfies a `--N` line, block. The same intersection-with-set check the original scanner did across `Token.dual` chains.

This is intentionally permissive in the ambiguous case — under GLL, both interpretations should be explored, and the Oracle / further continuation filtering breaks ties. If a future workload reveals cases where descriptor-encoded "exact previous terminal" semantics are needed, that's a Phase G escalation (descriptor identity carries lexical state); for now the union semantic preserves all the test grammar behaviour.

**Remaining `LegacyScannerLexAdapter` users:**

- Terminals with non-empty `transitions` (gated scanner-mode triples `=== "X" >>> "Y"`). Still need state-aware backing.

That's the only category left. Phase E Step 2 will tackle gated transitions; once done, `LegacyScannerLexAdapter` retires and the eager scanner can be deleted (or kept only as a diagnostics-feed).

#### Phase E — Step 2 design: structured `:` non-terminal trivia + outer-grammar interpolation (Jun 13, 2026)

Working through Swift.apus's three remaining scanner-mode uses (`multiline-comment`, `string-interpolation`, `inside-parentheses`), the design converged on **two complementary moves** that together retire `LegacyScannerLexAdapter` and the entire `GatedTransition` machinery, with one small new operator and zero scanner-mode infrastructure.

##### Move 1: string interpolation, mode-stack annotations, and most "modes" → outer grammar productions

The eager scanner needed modes because it committed once per position (longest match). Under LCNP, the parser asks per-slot — different slots receive different terminal sets in their FIRST — so the choice between e.g. "string opener" and "string closer" at a `"` is decided by which grammar slot is active, not by a mode stack.

Swift string interpolation collapses to ordinary outer productions:

```apus
stringLiteral      = stringOpen stringContents stringClose .
stringContents     = ( stringText | interpolation )* .
interpolation      = interpolationStart expression ")" .

stringOpen        - "\"" .
stringClose       - "\"" .
interpolationStart - "\\(" .
stringText        - /(?:[^"\\]|\\(?!\())+/ .   // stops before " or \(
```

`stringText`'s negative-lookahead regex does the work the `===`/`>>>`/`<<<` mode machinery used to do. Python f-strings work identically with one extra recursion level for the format spec (`fSpec` contains `( fSpecText | nestedFExpr )*` where `nestedFExpr = "{" expression "}"`). The `inside-parentheses` mode in Swift.apus was disambiguating ternary `:` vs dictionary `:` — that disambiguation was always parser-level (different grammar slots accept `:` in different contexts), so its mode annotation was carrying nothing the LCNP slot context doesn't already carry.

##### Move 2: new operator structured `:` for non-terminal-shaped trivia

The remaining hard case — Swift's *nested* `/* … */` block comments — can't be regular (regexes don't count) and the body shouldn't appear in the outer BSR (it's trivia). The fit is a new production operator:

| | Terminal | Non-terminal |
|---|---|---|
| Emit | `-` | `=` |
| Skip | `:` | structured `:` (new) |

structured `:` is a non-terminal production whose recognised extent is consumed as trivia rather than emitted to the outer BSR. The existing `:` regex/literal trivia is the trivial case — a single-factor structured `:` production.

Swift.apus's three multilineComment* terminals + six `===`/`>>>` annotations become:

```apus
multilineComment structured : "/*" multilineCommentBody "*/" .
multilineCommentBody = ( multilineCommentText | multilineComment )* .
multilineCommentText - /[^*\/]|\*(?!\/)|\/(?!\*)/ .
```

(or inlined into one production). Recursion in the grammar replaces mode-stacking; full GLL handles nesting naturally; the sub-parse's BSR is internal to the recogniser, never reaches the outer BSR.

##### Semantic rules for structured `:`

1. structured `:` body can reference: `-` terminals, `:` terminals, other structured `:` non-terminals, plus `=` helper non-terminals that are reachable only via structured `:` (so factoring helper productions like `multilineCommentBody = …` works whether you mark them `=` or structured `:`).
2. `=` (outer) non-terminals must not reference structured `:` non-terminals (trivia shouldn't leak into structure). Enforced at grammar load.
3. Identifier references inside any `:`/`-`/structured `:` body resolve against the *union* of terminal symbols (`:` and `-`) and structured `:` non-terminals. The `:`/`-` flag only controls outer-grammar treatment (skip vs emit), not what gets recognised.

##### Implementation outline

Each structured `:` non-terminal becomes a recogniser at grammar load: a `MessageParser` sub-instance whose root is that structured `:` node. At trivia-skip time, `OnDemandLiteralLexer.skipTrivia` tries structured `:` recognisers alongside `triviaRegexes`. The sub-parser shares the grammar but has its own descriptor/CRF/BSR state; only accepting end-positions propagate back to the outer parse. Cached in the outer `lexCache` like any other lex query.

##### Architectural payoff

When this lands:
- `Scanner.swift`'s `GatedTransition` struct, mode stack, `===`/`>>>`/`<<<` parsing, and all related machinery: **deleted**.
- `TokenPattern.transitions`: deleted.
- `LegacyScannerLexAdapter`: **deleted** — no remaining users.
- The eager scanner becomes optional (kept only if any diagnostics path still needs it).
- The grammar language gains exactly one new operator (structured `:`) and **loses** an entire mechanism (scanner modes).

##### Scope and cost

| Step | LoC | Purpose |
|---|---|---|
| 2a | ~100 | Add structured `:` operator: parse, grammar-load classification, `OnDemandLiteralLexer` trivia-recogniser dispatch, Swift.apus nested-comment migration |
| 2b | ~20 grammar | Refactor Swift.apus string-interpolation terminals to outer productions; delete mode annotations |
| 2c | ~10 grammar | Same for `inside-parentheses` mode (confirm it was always parser-context anyway) |
| 2d | ~−200 | Delete `GatedTransition` machinery, `LegacyScannerLexAdapter`, `Scanner.swift` mode parsing |

Net code change: roughly break-even, with the language surface getting smaller (one operator added, one whole mechanism removed) and the architecture becoming strictly cleaner.

##### Pre-Step 2 baseline gap: `LanguageGrammarTests` Python + Swift regressions

Discovered 2026-06-13 when checking layout-sensitive parsing status. `LanguageGrammarTests/PythonGrammar/parseMessagesSequentially` fails on every message (32 / 32 fail, starting with the simplest case `x = 42`); `LanguageGrammarTests/SwiftGrammar/parseMessagesSequentially` fails on several messages. APUS-grammar tests still pass. The focused suite (Patterns + RegexLookbehind + SpecialTokens + Core) doesn't catch this — these tests use simple grammars without scanner-mode trivia or synthetic layout tokens, and the LCNP migration has not been validated against the language-grammar suite until now.

Root-causing exposed two distinct issues. **Both have minimal patches available, both were tried, and both were reverted** because each fix patches a symptom of architecture Step 2 deletes.

**Issue 1 — Conditional skip patterns over-eat in `skipTrivia`.**

Python.apus defines `bracketNewline : /\r?\n/ . === "bracket-mode"` — a trivia regex that should only fire inside parens/brackets. The LCNP construction in `MessageParser.parse(...)` adds *every* skip pattern to `triviaRegexes` unconditionally:

```swift
if pat.isSkip {
    triviaRegexes.append(pat.regex)
}
```

So `bracketNewline`'s regex eagerly consumes every `\n` during `skipTrivia`, including the trailing `\n` of `x = 42\n` that should match `NEWLINE`. The parser asks `lex(7, NEWLINE)` after the regex has already advanced past the newline → empty result → parse fails.

*Minimal patch (reverted):* gate the `triviaRegexes.append` on `pat.transitions.isEmpty`. Tried and verified: Python tests 1–17 recover (simple/expression cases); the Swift `parseMessagesSequentially` regression also clears. Tests 18+ (multi-line with `INDENT`/`DEDENT`) remain failing because of Issue 2.

*Why reverted:* this gate is a symptom-fix. The architectural cause is "the on-demand trivia pipeline has no mode state, but it's being asked to honour mode-gated patterns". Step 2's outer-grammar move for string-interpolation and the structured `:` operator for nested comments retire the mode mechanism entirely; `pat.transitions` becomes empty for every terminal once `Scanner.swift`'s `GatedTransition` machinery is deleted. The gate then trivially holds — no special case needed.

**Issue 2 — `LegacyScannerLexAdapter` finds only one token at a position.**

`injectLayoutTokens` inserts virtual `>>|` / `|<<` / `○` tokens with zero-length image (`image.startIndex == image.endIndex == X`) at positions where a real token also starts. So after the inject, the `tokens` array has multiple consecutive entries with the same `startIndex == X` — the synthetic token first, then the real one.

`LegacyScannerLexAdapter.firstTokenIndex(at: pos)` is a binary search returning the leftmost match. That always lands on the synthetic token. The adapter then walks `Token.dual` to find the requested `terminalID` — but injected tokens don't have duals (Schrödinger duals link same-span lex alternatives, which `>>|` isn't). So when the parser asks `lex(pos_after_indent, NAME)` after consuming the synthetic `>>|`, the adapter still finds the `>>|` first, dual-walks empty, returns `[]`. `NAME` never matches, parsing stalls.

*Minimal patch (reverted):* extend the adapter's lex loop to step forward through `tokens` while `startIndex[i] == pos`, walking each token's dual chain in turn. Tried and verified to build cleanly; would have fixed the layout-injection cases for Python tests 18+.

*Why reverted:* `LegacyScannerLexAdapter` itself disappears in Step 2 — once gated transitions retire (no remaining users) the adapter has no purpose and gets deleted. Synthetic layout tokens then need a new home; the natural one is a parser-side virtual-token table populated by `injectLayoutTokens` and consulted directly by `tokenMatch` before falling through to the lex layer. Forward-scanning the legacy adapter is wasted work toward an architecture that's about to vanish.

**Net effect:** `LanguageGrammarTests` is a known-broken baseline going into Step 2. The fixes will fall out of the Step 2 architecture rather than being added on top of the current one. Tracked as the Step 2 acceptance criterion: PythonGrammar + SwiftGrammar `parseMessagesSequentially` both pass when Step 2 lands.

**Process note:** these two tests should have been in the focused suite all along. Adding them now (or at the start of Step 2) prevents the same kind of silent regression next time.

#### Phase E — Step 2 landed (Jun 13–14, 2026)

All four sub-steps landed in sequence; Swift is fully migrated, the legacy lex backend is gone, and Python is on the documented "needs its own design" track.

**Step 2a — structured `:` operator + recursive `MessageParser` infrastructure.**

`ApusTerminals` registers structured `:` as a new operator token. `ApusParser.production()` accepts structured `:` alongside `=`, flagging the LHS as `isTrivia = true`. `GrammarNode` gains an `isTrivia: Bool` field; `MessageParser.parse(...)` accepts optional `root:` / `start:` parameters so a sub-parser can run from any non-terminal at any position.

For each structured `:` non-terminal in the grammar, the outer parser builds a sub-`MessageParser` instance and a recogniser closure. `OnDemandLiteralLexer.skipTrivia` tries those recognisers alongside `triviaRegexes`. Validated on a new `CoreGrammarTests/TriviaNonTerminal` case with grammar `nested structured : "<" { /[^<>]/ | nested } ">" . S = "x" .` — accepts `<<<a>>>x`, rejects `<x`, `<a>`.

**Crucial structural fix during Step 2a:** the naive sub-parser invocation looped horribly under Swift.apus because `parse()` rebuilds the entire per-input setup on every call. Split `parse()` into:

- `prepareInput(tokens:trivia:input:isSubParser:)` — per-input setup (`kindID`s, `tokenIndexByStart`, `literalSourceByID`, `regexByID`, `triviaRegexes`, `lookbehindByTerminalID`, sub-parser construction). Runs once per input.
- `runGLL(root:start:)` — per-call: resets descriptor/CRF/yields state, seeds the root cluster, runs the GLL loop. Cheap; called many times against the prepared input.

`parse()` is now `prepareInput + runGLL`. Sub-parsers get `prepareInput` once during outer-parse setup; their recogniser closures call only `runGLL`. A no-match structured `:` recogniser call is now O(state-reset + one lex query) instead of O(grammar size). `lexCache` survives across `runGLL` calls within the same prepared input, so repeated queries at the same position become hits.

**Sub-parser semantics:** when a sub-parser is set up (`isSubParser: true`), `triviaRegexes` stays empty and `triviaRecognisers` stays empty. Inside a structured `:` body, what would otherwise be outer trivia (whitespace, line comments) is actual content. This matches the grammar author's intent — `multilineComment` body chars include literal whitespace.

**Step 2b — string interpolation: scanner-mode annotations retired.**

`interpolatedStringLiteralHead` / `Part` / `Tail` lost their `=== "string-interpolation"` / `>>>` / `<<<` annotations. Under LCNP these terminals are queried per-slot — the parser only asks for them inside the `interpolatedStringLiteral` production, so the spurious matches their regexes would otherwise produce elsewhere are simply never queried. The mode mechanism was carrying nothing the slot context didn't already carry.

**Step 2c — `inside-parentheses` mode: also retired.**

`leftParenthesis` / `rightParenthesis` lost their `=== "inside-parentheses"` annotations. The mode existed only to gate `interpolatedStringLiteralHead` (now slot-gated, Step 2b) and itself. Zero remaining users in Swift.apus.

**Step 2d — `LegacyScannerLexAdapter` deleted.**

Once Steps 2b/2c emptied every `transitions` annotation in Swift.apus, the legacy adapter's only remaining users were Python's `bracketNewline` (a single grammar). The user explicitly asked to remove the legacy stuff anyway and accept that Python becomes a documented gap.

Deletions:
- `LegacyScannerLexAdapter` struct in `Descriptor.swift` (the entire ~50-line type).
- `fallback: LegacyScannerLexAdapter` field on `OnDemandLiteralLexer`.
- The `return fallback.lex(...)` fall-through in `OnDemandLiteralLexer.lex` (now returns `[]` for unknown terminals).
- `pat.transitions.isEmpty` predicate in `MessageParser.prepareInput` — all non-skip regex terminals now route through `regexByID`.

**EOS handling added** to `OnDemandLiteralLexer`: the synthetic `"○"` sentinel isn't in `grammar.terminals` so isn't in `literalSourceByID` or `regexByID`. Previously the legacy adapter served it from the augmented tokens array. Now the lexer takes `eosID: Int` at construction and matches EOS directly when `skipTrivia(from: pos) == input.endIndex`. The earlier set of CoreGrammar test failures (everything returning "no parse found" because root NT `followCheck` couldn't see EOS) was caused by missing this; the fix recovered them all.

**Validation at the end of Step 2:**

| Suite | Result |
|---|---|
| `CoreGrammarTests` (incl. new `TriviaNonTerminal`) | all pass |
| `SpecialTokenTests` | all pass |
| `RegexLookbehindIntegration` | 11/12 (flaky `ternary-with-spaces`) |
| `LanguageGrammarTests/SwiftGrammar` | **2/2 pass** (was 1/2 before) |
| `LanguageGrammarTests/APUSGrammar` | 2/2 pass |
| Combined focused | **182/183**, baseline-or-better |

**What's left for `Token.dual`:** Still produced by the eager scanner for Schrödinger same-span ambiguity, but no parser-side code walks it any more after Phase D Step 1. The dual chain survives because the scanner builds it; it's unused downstream. Retiring it would require removing same-span ambiguity construction from the scanner itself, which is straightforward but separate.

**Python regression — documented status.**

`LanguageGrammarTests/PythonGrammar/parseMessagesSequentially` remains broken; all 32 messages fail. Two reasons:

1. **`bracketNewline` conditional trivia.** Python.apus has `bracketNewline : /\r?\n/ . === "bracket-mode"` — newline-as-trivia only inside `(`/`[`/`{`. With `transitions` ignored (Step 2d), `bracketNewline` is now added to `triviaRegexes` unconditionally (it's still a skip pattern). It over-eats *every* `\n`, swallowing the trailing `\n` that should match `NEWLINE`. Simple statements like `x = 42\n` fail because the parser can't find the trailing NEWLINE.
2. **Layout-injection tokens.** The `>>|` / `|<<` / `○` synthetic tokens injected by `injectLayoutTokens` aren't in `grammar.terminals`; `OnDemandLiteralLexer` can't find them. Previously the legacy adapter served them from the augmented tokens array. Now they're invisible to the parser. (`○` (EOS) is now handled explicitly; `>>|` and `|<<` are not.)

**Both gaps closed:** synthetic layout tokens via `virtualTokensAt` (Phase G Step 1) and `bracketNewline` via grammar refactor (Phase G Step 2). Python parses 32/32.

**Cumulative state at Step 2 close:**

- `OnDemandLiteralLexer` is the sole lex backend. ~250 lines of `LegacyScannerLexAdapter` deleted.
- `GatedTransition` machinery in `Scanner.swift` still alive for the eager scanner's own scan loop (used by `bracketNewline`-style annotated terminals); the parser no longer consults `pat.transitions`. Full removal of the `===`/`>>>`/`<<<` grammar syntax + scanner mode stack is feasible but waits on Python.
- `Token.dual` still produced; unused by parser hot path.
- Swift parses fully (192/193 tests if you include `TriviaNonTerminal`); Python remains a documented gap.

#### Phase E close — `boundaryMatches` retired the scanner-tokens dependency (Jun 14, 2026)

After Step 2d, `ternary-with-spaces` (`let r = b ? /1/ : /2/`) still failed. Debugging traced it to the SCANNER producing one giant token for the entire input (matched by the anonymous inline regex inside `multilineComment structured :`), which then broke `<s>`/`>s<` boundary checks: the old `boundaryMatches` indexed into `parser.tokens[]` and the giant token gave hasInterTokenGap nonsense answers.

Root cause: `boundaryMatches` had no business reading scanner tokens at all under LCNP. The lex queries that actually drive the parse are per-terminal and predict-set-bounded, so they never spuriously match an anonymous interior regex (it's not in the FIRST set of any outer-grammar slot). Only the eager scanner — pattern-blind — would match it. The fix moved boundary semantics off `parser.tokens[]` entirely.

**Rewrite of `boundaryMatches`:**

- `LexMatch` gained `rawEnd: CharPosition` — position right after the literal/regex content, before trailing trivia skipping. `end` (already present) is the cursor position after trivia skipping.
- `TerminalCommit` gained `rawEnd: CharPosition`. The parse loop's `.T/.TI/.C` arm logs `rawEnd` into `terminalCommitsByEnd[end]` for every consumed terminal.
- `boundaryMatches(_:at:)` now reads `terminalCommitsByEnd[position]` directly: for each commit ending at `position`, the gap `input[commit.rawEnd..<position]` is the exact trivia text the lexer skipped. Predicates are pure functions of that slice (`<s>` = non-empty; `>s<` = empty; `<n>` = contains a line break; `>n<` = doesn't). Multi-history GLL produces several commits at one position; we require unanimity across them.

Consequence: the scanner's eager tokenization no longer affects parse decisions, only diagnostics. The grammar-cache deferred work (below) follows from this.

**Test infrastructure: cached Swift grammar.**

`SwiftSyntaxTests.swift`'s `loadFreshSwiftGrammar()` reloaded Swift.apus per snippet — historically required by Phase A's exclude/Schrödinger order-dependence. Phase D retired the order-dependent code paths (exclude is now a per-end LCNP filter, `yields` moved off `GrammarNode`), so the grammar is load-time immutable and shareable across snippets.

Replaced fresh-load with a lazy-initialised `cachedSwiftGrammar` constant. Measured wall-clock improvements:

| Suite | Before | After | Speedup |
|---|---|---|---|
| RegexLookbehind (12) | 57.4 s | 8.0 s | 7.2× |
| PatternSyntax (6) | ~29 s | 7.2 s | ~4× |
| ExpressionSyntax (184) | ~15 min (projected) | 101 s | ~9× |

Equivalence evidence: 12/12 RegexLookbehind pass identically with cache; 39/39 CoreGrammar+SpecialToken pass identically; the 39 ExpressionSyntax failures cluster on `testKeypathExpression`/`testCollectionLiterals`/`testInterpolatedStringLiterals` — grammar-feature signature, not order-dependence (which would scatter failures randomly).

**Phase E housekeeping (same commit):**

- Deleted `MessageParser.hasInterTokenGap` / `lineBreakCountBetweenTokens` (now-dead boundary helpers).
- Deleted `MessageParser.nextTokenStart(after:)` (Phase A bridging artifact).
- Deleted `MessageParser.testRepeat` (orphaned; TODO marked it).
- Deleted `Descriptor.swift`'s `TokenPosition` struct + `TokenPosition.charPosition(in:input:)` (Phase A bridge, no live callers). Kept `CharPosition.tokenIndex(in:input:)` — still used by `tokenIdx` fallback and diagram/AST builders for diagnostic lookup.
- Updated the `OnDemandLiteralLexer` / Phase A foundation comments in `MessageParser.swift` and `Descriptor.swift` to reflect current architecture.

**What stays for Phase F or later:**

- LL(1) early-termination skeleton (`false && X.isLocallyLL1` in `addDecscriptorsForAlternates`) — Phase F to evaluate under LCNP whether the optimisation is still worthwhile.
- `LookbehindSpec` (string-keyed grammar DSL) vs `ResolvedLookbehindSpec` (BitSet-keyed parser-internal) — clean grammar↔parser boundary, not duplication.
- `Token.dual`, `GatedTransition` machinery — kept for the scanner; the parser ignores them. Full retirement waits on the Python-specific design.
- `parser.tokens` array — diagnostic-only now; harmless.

#### Phase E (original) - Regex island, trivia, and lookbehind migration

Move plain regex literals back to a single terminal backed by a lex-side recognizer. Keep ordinary slash/operator alternatives available through LCNP terminal queries. Add the minimal trivia/layout summary needed for `>s<`, `<s>`, `<n>`, and `>n<` before deleting scanner lookbehind.

Remove or replace:
- The regex-CFG productions in `Swift.apus` (revert to single `plainRegularExpressionLiteral` terminal, now backed by a lex-side recognizer)
- `LookbehindSpec`, `LookbehindRule`, `LookbehindLine`, and `Scanner.lookbehindAllows`, once regex-vs-operator cases are covered by LCNP alternatives and/or the regex recognizer

**Validation:** regex overclaim cases such as `(/E.e).foo(/0)` reject the regex edge, valid regex literals still parse, slash/operator expressions remain available, and whitespace-sensitive tests retain behavior.

### Phase F — Apply `lexLKH` predict-set lookahead

Optimisation and selective pruning. Replace raw `lex(pos, terminalID)` calls with `lexLKH(pos, terminalID, β, X)` where the paper's `valid(end, predict(β, X))` predicate is implemented as: there exists at least one predicted terminal whose `lex(end, terminalID)` result is non-empty.

Do not retire `>>1(...)` until each existing `followAhead` use is proven equivalent to the computed LCNP `predict(β, X)` at that grammar slot.

Measures: descriptor count reduction, BSR yield count reduction, wall-clock improvement.

#### Phase F landed (Jun 14, 2026)

**Realisation:** the predict set the paper calls `predict(β, X)` (FIRST of the suffix after this slot, with epsilon look-through to enclosing FOLLOW) is already computed and stored per node by `Grammar.populateFirstFollowSets`'s `updateFollow`. `node.followBS` *is* the predict set — no new computation needed.

**Implementation:** unified the existing `followAheadBS` filter in `MessageParser.tokenMatch` with a new predict filter:

```swift
let predictBS = cL.followAheadBS.isEmpty ? cL.followBS : cL.followAheadBS
if !predictBS.isEmpty && !predictBS.contains(grammar.epsilonID) {
    matches = matches.filter { m in
        if m.end >= input.endIndex { return true }    // EOS always allowed
        for fID in predictBS where fID != grammar.epsilonID {
            if !cachedLex(at: m.end, terminalID: fID).isEmpty { return true }
        }
        return false
    }
}
```

`followAheadBS` (manual `>>1(…)` annotation) is a *stricter* override and wins when present; otherwise the computed `followBS` is used. The filter is skipped when the predict set is empty or contains ε (fully-nullable suffix — any continuation is valid).

**Measurements:**

| Suite | Pass/Fail | Descriptor change | Wall-clock change |
|---|---|---|---|
| CoreGrammarTests + SpecialTokenTests (21) | unchanged | n/a | unchanged |
| RegexLookbehind (12) | 12/12 pass | -1% to -3% on heavier snippets | unchanged (8.0 s) |
| PatternSyntax (6) | 6/6 pass | ~0% | unchanged (7.1 s) |
| ExpressionSyntax (184) | 145/184 pass (identical 39 failures, same cluster) | n/a measured | unchanged (101.5 s) |

**Why the gain is small:** Phase D already pushed exclusion/followAhead/Schrödinger checks down to per-end LCNP filters, and `continuationViable` (in `rtn` / `bracketRtn`'s pop replay) prunes dead-end descriptors before they enter the queue. By Phase F the remaining dead-end terminals were already being suppressed one slot later by `testSelect`'s per-terminal lex. Phase F formally closes the LCNP migration by making the prediction happen *at lex time* (matching the paper's semantics), but the operational headline-win that motivated `lexLKH` in classical implementations was already captured by Phase D's piecemeal filters. TODO: is the lexer filter more efficient than the parser?

**Token.dual + GatedTransition retirement:** completed in Phase H.

**`>>1(…)` audit:** carried to `TODO.md` item 7 (annotation sweep).

**Cumulative state at Phase F close:**

- All paper-defined LCNP API surfaces live and exercised: `lex`, `lexLKH` (via the unified `tokenMatch` filter), per-terminal cached queries, per-end exclusion / followAhead / lookbehind filters, and parser-side `terminalCommitsByEnd`-driven boundary checks.
- `OnDemandLiteralLexer` is the sole lex backend.
- Grammar load-time-immutable; safely cached across snippets in tests.
- ~50 lines of dead Phase-A/E scaffolding removed (`TokenPosition`, `hasInterTokenGap`, `lineBreakCountBetweenTokens`, `nextTokenStart`, `testRepeat`).

### Phase G — Lexical state only if forced

Do not carry today's mutable scanner mode stack into LCNP by default. First try pure terminal recognizers, trivia/layout summaries, or grammar-encoded islands. If a concrete construct cannot be represented that way, then extend descriptor identity with lexical state, e.g. `lex(pos, terminalID, state) -> Set<(endPos, stateAfter)>`, understanding that this grows descriptor/CRF keys and reduces sharing.

#### Phase G — Step 1 landed (Jun 14, 2026)

Synthetic layout tokens (Python's `>>|` INDENT and `|<<` DEDENT) routed through `OnDemandLiteralLexer` via a gated source-position table — closes the second of the two known Python regressions (#2 synthetic layout tokens). The first regression (#1 `bracketNewline` mode-gating) remains and is the sole blocker for Python parses.

**Mechanism.** `OnDemandLiteralLexer` gains a `virtualTokensAt: [CharPosition: [Int]]` field — zero-length synthetic terminals keyed by source position. The `lex` path checks `virtualTokensAt[skipTrivia(from: pos)]` for the requested terminalID before falling through to EOS/literal/regex matching. Multiple synthetics at one position (e.g. two DEDENTs at the same column) appear as multiple entries in the value array; each parser slot asking for the terminal at that position gets a successful match (grammar structure controls how many ask — Python.apus's `block = … |<<` is one per block end).

**Precompute.** `computeVirtualLayoutTokens(tokens:input:indentKindID:dedentKindID:bracketPairs:)` in `LayoutTokenInjection.swift` mirrors the algorithm of `injectLayoutTokens` exactly — same indent-stack walk, same bracket-depth counter, same blank-line / NEWLINE-token treatment — but writes its output to a `[CharPosition: [Int]]` table instead of mutating `tokens[]`. Called from `MessageParser.prepareInput`, gated on `grammar.usesInjectedLayoutTokens` and `!isSubParser`. Sub-parsers (structured `:` bodies) skip the precompute; synthetic tokens live at the outer parse level only.

**Gating.** Existing `grammar.usesInjectedLayoutTokens` flag (set by `ApusParser` when `>>|` / `|<<` appear unquoted in grammar structure) reused unchanged — non-layout grammars allocate an empty dictionary and pay nothing. Verified: SwiftGrammar full-message suite, CoreGrammarTests, SpecialTokenTests, RegexLookbehindIntegration — all pass identically; no overhead measured on non-layout grammars.

**Coexistence with `injectLayoutTokens`:** retired in Phase I; mutating variant deleted, only the pure `computeVirtualLayoutTokens` survives.

**`bracketNewline` regression:** fixed in Phase G Step 2 via grammar refactor (Python.apus uses `<n>` boundary + global newline-trivia instead of NEWLINE-as-token).

#### Phase G — Step 2 landed (Jun 14, 2026)

`bracketNewline` and the scanner mode-stack apparatus retired *via grammar refactor*, not via a new APUS primitive. The class of problems "trivia behaviour depends on lexical context" turned out to be cleanly expressible with what was already in the toolbox once `NEWLINE`-as-token was let go.

**The architectural insight.** The bracket-newline regression and the "newline as statement terminator" requirement both stem from the same modelling choice: representing line breaks as a *token* (`NEWLINE - /\r?\n/`). That choice creates the conflict — `\n` cannot simultaneously be trivia (inside brackets, where Python's implicit line continuation lives) and an emit token (between statements). Scanner modes were band-aiding the conflict.

Drop the choice and the conflict dissolves: `\r?\n` becomes *global trivia*, and statement boundaries are asserted by the `<n>` boundary predicate ("a line break appears in the trivia gap between the previous emit and the cursor"). Implicit line continuation inside brackets falls out for free — the cursor's trivia just includes the newline. Blank lines vanish as trivia. No predicates, no contexts, no frame stack.

**Two small bits of infrastructure required to make the swap clean:**

1. **`<n>` at end-of-input is satisfied unconditionally.** Files without a trailing `\n` need to parse; CPython's tokenizer emits a synthetic NEWLINE before EOF for exactly this reason. Implemented as a one-line special case in `MessageParser.boundaryMatches`: `if boundary == "<n>", position == input.endIndex { return true }`. Holds for any grammar that uses `<n>` as a terminator — same problem any line-based language has (JS ASI, Go, etc.).

2. **`>n<` boundary for single-line vs multi-line disambiguation.** Python's `block` rule has two shapes — one-liner (`if x: return 1`) and indented (`if x:<n>    return 1`). Without disambiguation, both alternatives match either input via GLL ambiguity. Adding `>n<` to the one-liner alternative (`block = >n< simple_stmts | <n> >>| <statement> |<<`) forces same-line. Reuses the existing `>n<` boundary primitive; no new mechanism.

**Python.apus diff in concrete terms:**

- Lexical section: `hspace : /[ \t\f]+/` broadened to `whitespace : /[ \t\f\r\n]+/`. `NEWLINE`, `bracketNewline`, and all six `pyLP/pyRP/pyLS/pyRS/pyLC/pyRC` mode-pumping terminals deleted — they had no production-rule consumers, only existed to feed the scanner mode-stack.
- Five production-rule edits: `NEWLINE`-as-token replaced with `<n>` in `simple_stmts` / `decorator`; `<NEWLINE | …>` KLN alternatives collapsed to `<…>` in `file` / `block` / `match_stmt` (blank lines are now trivia); `>n<` added to `block`'s one-liner alternative.
- Header comments updated; deviations #2 (blank-line handling) and #6 (bracket-newline suppression) merged into one deviation describing the unified `<n>` approach.

**Validation:**

| Suite | Result |
|---|---|
| `LanguageGrammarTests/PythonGrammar/parseMessagesSequentially` (32 messages) | 32/32 pass (was 0/32) |
| `LanguageGrammarTests/SwiftGrammar/parseMessagesSequentially` | identical (no regression from `<n>` EOS rule) |
| `LanguageGrammarTests/APUSGrammar/parseMessagesSequentially` | identical |
| `CoreGrammarTests` + `SpecialTokenTests` + `RegexLookbehindIntegration` + `TriviaNonTerminal` | all pass |

**What this closes.** Python regression #1 (`bracketNewline` mode-gating) and regression #2 (synthetic layout tokens) are both fixed. Python is now a working language target alongside Swift. The eager scanner has no remaining parser-side consumer that uses scanner modes — `Token.dual`, `GatedTransition`, `modeStack`, all six `pyL*`/`pyR*` mode-pumping declarations, and the `bracketNewline` scanner-mode terminal are all officially dead weight ready for the next retirement commit.

**What didn't need to happen.** No grammar-level predicate DSL (`when bracketDepth > 0`). No trivia-frame stack on descriptors. No new APUS primitive. The "general mechanism for this class of problems" turned out to be: *don't model a piece of layout as a token if it can be modelled as a trivia-gap predicate*. The existing `<n>` / `>n<` / `<s>` / `>s<` boundary set was sufficient.

### Phase H — Eager scanner machinery retirement (Jun 15, 2026)

With Python parsing and the bracket-newline mode-gating dependency gone, every scanner-internal mechanism that the parser hot path stopped consulting in earlier phases became deletable. Phase H is a single cleanup sweep, ~250 lines removed, no behavioural change.

**Retired:**

| Construct | File | Reason it's gone |
|---|---|---|
| `Scanner.matchesLine` + `Scanner.lookbehindAllows` | `Scanner.swift` | Dead since Phase E Step 1 (parser-side `MessageParser.lookbehindAllows` took over) |
| `Token.dual` field + chain construction | `Scanner.swift` | Schrödinger same-span ties no longer tracked; Phase D's per-end LCNP exclusion filter handles disambiguation |
| `MessageParser.prepareInput` dual-chain walk | `MessageParser.swift` | One-line `kindID` assignment now |
| `Scanner.modeStack` / `scannerMode` / mode-gate prefilters / transition execute | `Scanner.swift` | Scanner mode-stack entirely gone; the parser stopped consulting `pat.transitions` in Phase E Step 2d |
| `GatedTransition` struct | `Scanner.swift` | |
| `TokenPattern.transitions` field | `Scanner.swift` | |
| `while token.kind == "==="` annotation block | `ApusParser.production()` | Mode-annotation parser; no longer wires anything anywhere |
| `===` / `<<<` / `>>>` token registrations | `ApusTerminals.swift` | Grammar syntax for the retired feature |
| `mode = …`, `context = mode \| follow`, `name = …` productions | `apus.apus` | Meta-grammar productions describing the retired syntax. `context` callsites collapsed to inline `[ follow ]` to preserve nullability. |
| `attributeHunt.apus`, `apusAmbiguous.apus` | `apus grammars/` | Test fixtures exercising the retired feature; no test referenced them. (`ScanModeTest.apus` deleted by the user in the same window.) |
| `mode:` / `modeBeforeTransition:` parameters; `recordTransition` method | `ScannerTelemetry.swift` | Telemetry hooks for the retired mode transitions |

**What still uses the eager scanner.** It still produces `tokens[]` / `trivia[][]` for:
- `MessageParser.prepareInput` — `kindID` assignment, `tokenIndexByStart` sidecar (latter used only by `tokenIdx(at:)` for diagnostics).
- `DerivationBuilder` / `SwiftSyntaxGenerator` — read `tokens[idx].image` by index when emitting AST/derivation nodes.
- `recordMismatch` trace output.
- `LayoutTokenInjection` mutating `tokens[]` in place — kept to feed the above readers. The *parser* now uses `virtualTokensAt` (Phase G Step 1); the *diagnostic* readers still read the augmented token stream.

Replacing the diagnostic readers with parser-side scans of `input` is the remaining work to fully retire the eager scanner. None of it is on the hot path, and the diagnostic users are well-isolated.

**Validation.** All focused suites (Python full grammar, Swift full grammar, APUS full grammar, APUS self-parse, CoreGrammar, SpecialToken, RegexLookbehindIntegration, TriviaNonTerminal) — 47/47 pass, identical to pre-Phase-H. Schrödinger duals continue to disambiguate correctly through the parser-side per-end LCNP filter alone.

**Architectural state at Phase H close.**

- LCNP per-terminal lex (`OnDemandLiteralLexer`) is the sole parsing lex backend.
- `boundaryMatches` is parser-side, reading `terminalCommitsByEnd[].rawEnd`.
- Layout tokens (INDENT/DEDENT/EOS) served via parser-side `virtualTokensAt` table.
- Lookbehind, exclusion, predict-set (`lexLKH`) filters all parser-side.
- The eager scanner is now a thin tokenization pass with no parser-state feedback loop, kept only for diagnostic readers.
- Two working language targets (Swift, Python) plus APUS self-hosting; one synthesis test (`TriviaNonTerminal`).

**Carryover work:** completed in Phase I (diagnostic readers migrated off `tokens[]`; mutating `injectLayoutTokens` deleted).

### Phase I — Retire `Scanner` from the message-parsing pipeline (Jun 16, 2026)

After Phase H the eager `Scanner` was kept alive only to feed diagnostic readers (`DerivationBuilder`, `SwiftSyntaxGenerator`, `recordMismatch`, derivation diagram). Phase I migrates those readers to walk `input` and the parser's own commit log directly, then removes `Scanner` from every message-parsing call site. `Scanner` survives in the codebase only for `ApusParser` (which uses it to tokenize `.apus` grammar sources via the fixed `ApusTerminals` set).

**Architectural insight that drove the migration.** The parser already records, for every committed terminal, an exact `(start, rawEnd, kindID)` triple in `terminalCommitsByEnd`. That's grammar-authoritative boundary information — *no* whitespace heuristic, *no* language-specific assumption. Phase I exposed it as the source of truth: the parser dual-indexes commits as `terminalCommitsByStart` and offers `parser.terminalImage(startingAt: CharPosition) -> Substring?` returning the literal source content of the terminal that committed at that position. Trivia falls out as "everything between consecutive commits" — also available by walking the same sidecar.

**`MessageParser` API simplified.** `parse(tokens:trivia:input:…)` → `parse(input:…)`. `prepareInput(tokens:trivia:input:isSubParser:)` → `prepareInput(input:isSubParser:)`. The `tokens: [Token]`, `trivia: [[Token]]`, `tokenIndexByStart` fields and the `tokenIdx(at:)` helper are gone. Sub-parsers (structured `:` bodies) share the simplified API.

**Mini-scanner for layout precompute.** `computeVirtualLayoutTokens` previously walked the scanner's `tokens[]`. It now walks `input` char-by-char with hardcoded Python-shaped string and comment delimiters (`"`, `'`, `"""`, `'''`, `#`). 80 lines, language-parameterisable when a second grammar needs different delimiters (Haskell, F#, YAML); no per-language hack today. Gating on `grammar.usesInjectedLayoutTokens` unchanged; non-layout grammars allocate nothing.

**Diagnostic readers migrated.**
- `DerivationBuilder`: `ParseTreeNode.token: Token?` → `image: Substring?`. Leaves get their image from `parser.terminalImage(startingAt: from)` — exact boundaries, falls back to `input[from..<to]` only if no commit recorded.
- `SwiftSyntaxGenerator`: `tokenText(at:)` and `collectTerminalText(from:to:)` walk `terminalCommitsByStart` for grammar-defined boundaries. No more whitespace-stop heuristics that would have broken on languages with non-standard separator conventions.
- `SPPFExtractor`: never actually read `tokens[]`; just dropped the dead parameter.
- `Oracle`: dead `tokens:` parameter dropped.
- `recordMismatch`: shows a `sourceSnippet(at:)` slice of `input` instead of `tokens[idx].image`. The heuristic (Unicode whitespace stop, 30-char cap) is intentionally limited to this *failure-report* path; everything that runs on a *successful* parse uses `terminalImage(startingAt:)`.

**Call sites swept.** `main.swift`, `TestInfrastructure.swift` (3 sites), `SwiftSyntaxTests.swift`, `SpecialTokenTests.swift`, `PerformanceTests.swift`. No `Scanner(...)` invocation remains for message parsing. The mutating `injectLayoutTokens(tokens:trivia:input:…)` has been deleted entirely; only the pure `computeVirtualLayoutTokens(input:…)` survives.

**`Token.kindID`** is now used by no parser-hot-path code. `ApusParser` reads `Token.kind` (string) but never `kindID`. Field removal pending audit — `TODO.md` item 9.

**Validation.** 132 / 132 in the focused suite (CoreGrammar across 9 sub-suites, SpecialToken across 3, RegexLookbehindIntegration, TriviaNonTerminal, APUS self-parse, all three LanguageGrammar full-message suites for Python / Swift / APUS). Schrödinger duals still disambiguate, lookbehind still fires, Python's 32 messages still parse, Swift unchanged, APUS self-parse unchanged.

**Architectural state at Phase I close.**

- The message-parsing pipeline is `MessageParser.parse(input:)` + `Oracle(parser:input:)`. `Scanner` no longer appears in any signature or call site for message parsing.
- `Scanner` survives as a *grammar-loader* dependency: `ApusParser` uses it to tokenize `.apus` files via the fixed `ApusTerminals` set. Quarantined.
- `Token.kindID`, `Token` itself, `TokenPattern.lookbehind`, `LookbehindSpec/Rule/Line` (string-keyed) — all retained as grammar metadata, consumed by `MessageParser.prepareInput` via `grammar.terminals`. They're not "scanner machinery"; they're grammar metadata that happens to live in `Scanner.swift`. Move-or-rename can wait.

**Open follow-ups:** see `TODO.md` items 10 (consolidate `terminalCommits*` indexes) and 14 (mini-scanner parameterisation for non-Python layout-sensitive grammars).

## Open Questions

The §A–§H open-question outline that opened this section has been resolved or moved:

| § | Topic | Outcome |
|---|---|---|
| §A | Lexical state / scanner modes | Phase H deleted the scanner mode-stack entirely; no language has so far needed descriptor-encoded lexical state. |
| §B | Whitespace / trivia / layout | Phase E close moved boundary evaluation to parser-side `terminalCommitsByEnd[].rawEnd`. |
| §C | Performance on Swift workloads | Profiling carried to `TODO.md` item 13. |
| §D | `lexLKH` and existing FIRST/FOLLOW | Phase F implemented using `cL.followBS` as the predict set. |
| §E | Memoisation of lex results | `lexCache: [LexCacheKey: [LexMatch]]` in `MessageParser`. |
| §F | `Token.image` / `Token.kindID` | `image` migrated to `parser.terminalImage(startingAt:)`; `kindID` removal carried to `TODO.md` item 9. |
| §G | Test infrastructure | Migrated in Phase I. |
| §H | Generated parser code (`GenerateParser.swift`) | Carried to `TODO.md` item 12. |

## What This Does Not Address

- **Parser-level ambiguity** (`Array<Array<Int>>`, all `canParseAsXxx` decisions) — addressed by the grammar-predicate lookahead family (`Grammar Predicate Lookahead Design`).
- **Oracle dead-wood propagation** — orthogonal; LCNP doesn't touch it.
- **Performance on long inputs** generally — `pruneUnproductive` is already O(n²) per call; LCNP doesn't fix that.

## Per-File Change Inventory

Phase A (source positions + legacy adapter):
| File | Change | Size |
|---|---|---|
| `BinarySubtreeRepresentation.swift` | `BinarySpan` field types | small |
| `Descriptor.swift` | replace `TokenPosition` with `CharPosition`; keep local alias | small |
| `CallReturnForest.swift` | `ParsePosition` and pop set key types | small |
| `MessageParser.swift` | replace `cI`/`cU` mechanics; consume legacy adapter matches by source span | medium/large |
| `Oracle.swift` | `pruneUnproductive`, `endPositions`, span comparisons | medium |
| `DerivationBuilder.swift` | label generation from source extents | small |
| `SPPFExtractor.swift` / derivation builder | character extents | small/medium |
| `AdventTests/TestInfrastructure.swift` | helper comparisons and baseline capture | small |

Phase B (literal/operator LCNP + Frankenstein removal):
| File | Change | Size |
|---|---|---|
| `Scanner.swift` / new `LCNPLexer` | pure literal/operator `lex(pos, terminalID)` queries | medium |
| `MessageParser.swift:tokenMatch` | return `[LexMatch]` / `[CharPosition]`, fork descriptors | medium |
| `Grammar.swift` | drop `frankensteinID` / `≋` sentinel once tests pass | small |
| `ApusParser.swift` | drop `~~~` parsing once grammar no longer uses it | small |
| Swift/operator `.apus` rules | remove Frankenstein annotations | small per file |
| `Advent/Frankenstein Tokens.md` | mark superseded by LCNP Phase B | small |

Phase C (general parser-driven terminal path):
| File | Change | Size |
|---|---|---|
| `Scanner.swift` / `LCNPLexer` | reusable per-terminal recognizers for literals and regex terminals by terminal ID | **large** |
| `MessageParser.swift` | normal terminal matching no longer depends on linear `[Token]` | medium |
| `LexMatch` / parser input types | introduce LCNP lex-result shape; keep `Token` in legacy adapter | small |
| Test infrastructure | construct parser input from source text plus `LCNPLexer` | small |

Phase D/E retirements:
| File | Change |
|---|---|
| `Scanner.swift` | drop `Token.dual`, then scanner lookbehind support after LCNP equivalence is proven |
| `Grammar.swift` | drop `propagateExcludeSets`; retain integer terminal IDs and `BitSet` setup |
| `GrammarNode.swift` | drop `exclude`/`excludeBS`; defer `followAheadBS` until `lexLKH` equivalence is proven |
| `ApusParser.swift` | drop `---()`, `++N/--N`; defer `>>1` parsing until Phase F proof |
| `Swift.apus` | regex CFG -> regex terminal with lex-side recognizer in Phase E |
| `Advent/Schrodinger Tokens.md`, `Advent/Regex Lookbehind Design.md` | mark superseded only after corresponding retirement phase |

Total estimated effort: **2-4 weeks of focused work**, dominated by Phase A's source-position migration and Phase C's scanner/lexer API redesign. The old implementation should remain available only through the legacy adapter and baseline results so failures can be analysed or rolled back without keeping duplicate active architecture.

## References

In-tree:
- Scott & Johnstone, *Multiple Lexicalisation — A Java Based Study*, SLE 2019 — `articles/raw/Multiple Lexicalisation - A Java Based Study.txt`
- Scott & Johnstone, *GLL Syntax Analysers for EBNF Grammars*, SLE 2016 — `articles/raw/GLL Syntax Analysers For EBNF Grammars.txt`
- Afroozeh, *Practical General Top-Down Parsers*, PhD 2018 — `articles/raw/Practical general top-down parsers.txt`

Project docs (will be superseded or cross-referenced):
- `Advent/Schrodinger Tokens.md`
- `Advent/Frankenstein Tokens.md`
- `Advent/Regex Lookbehind Design.md`
- `Advent/Structured Lookahead Design.md`
- `Advent/Regex CFG Discussion.md`
- `Advent/Scanner Mode Design.md`

External (cited in paper):
- Aycock & Horspool — Schrödinger token approach
- Visser — SDF/SGLR scannerless GLR (compared as related work)
- Ford — PEG (compared as related work)

## Adoption Decision

Recommended: proceed with Phase 0 (capture baseline) immediately, then Phase A using `String.Index` / `CharPosition` as the first source-position type. Keep integer terminal IDs and `BitSet` FIRST/FOLLOW/select sets as the parser hot path. Keep the old scanner only as a legacy adapter for baseline comparison and rollback; the final architecture is source text plus parser-driven `lex(pos, terminalID)` calls. The structural cost is real, but five accumulating mechanisms collapsing into one principled interface — backed by Scott & Johnstone's measured implementation — is a positive ratio.

# Lexer V3: per-position terminal sets for lexing on demand

Goal: give `viable` and `continuationViable` back the bit-set test that lexing on demand lost,
without lexing up front, and make the lexer itself cheap per question. Same answers as today.

Ground rules:
- One step at a time, each with before/after numbers: `tools/run_tests.sh` (full suite),
  `BendCheck` (`TEST_RUNNER_APUS_BEND=1`), the lex report and timings of the decision
  statistics suite (`TEST_RUNNER_APUS_DECISION_STATS=1`, `DecisionStatisticsTests`), and a
  profile (`profileTarget()`, attach `sample`).
- These are engine changes: each step is agreed before it is made.

## Background: two formulations by Scott et al.

- **MGLL** (*Multiple input parsing and lexical analysis*, Scott, Johnstone, Walsh) lexes up
  front into a TWE set Σ and keeps, per position, the set of terminals starting there,
  `tΣᵢ = {b | (b, i, j) ∈ Σ}`. Selection is `testSelect(i, β, X, Σ) = predict(β, X) ∩ tΣᵢ ≠ ∅`:
  a bit-set intersection.
- **LCNP** (*Multiple Lexicalisation – A Java Based Study*), which ApusApus follows, lexes on
  demand: `valid(i, T) = ∃ t ∈ T: lex(i, t) ≠ ∅`. The paper "makes no assumptions about how
  lex() is implemented", calls its own implementation "not optimised", and points at "more
  efficient lexer implementations, such as linear time finite state automata".

ApusApus implements `valid` literally: `viable` walks FIRST (and FOLLOW) terminal by terminal
and asks the lex cache about each one. The comment at the END case in `MessageParser.swift`
already notes "ApusApus has no precomputed tΣᵢ".

## Measurements (2026-11-04, Swift grammar on `Oracle.swift`, 5,322 positions)

Profile of 10 parses (`sample`, about 2,800 samples on the parsing thread):

| What | Share of parse time |
|---|---|
| `viable` (in `addDescriptorsForAlternates`) | 59% |
| `OnDemandLiteralLexer.lex`, all callers | 44% |
| of which `Regex.prefixMatch` | 35% |
| `continuationViable` | 19% |
| exclusion check inside `viable` (`---( … )`) | 14% |
| `suppressesLeadingTriviaForPrediction` (array allocation) | 13% |
| `tokenMatch` | 7% |
| lex-cache dictionary probes | ≈ 5% |
| descriptors (`addDescriptor` + set insert) | ≈ 1.5% |

Lex questions, by terminal kind:

| Kind | In grammar | Questions | Per position | Matched |
|---|---|---|---|---|
| literal | 223 | 284,255 | 53.4 | 1.1% |
| regex | 35 | 54,896 | 10.3 | 5.1% |
| recogniser (GLL sub-parse) | 5 | 6,456 | 1.2 | 0.7% |

Matches per position: one terminal at 87–89% of positions, two at 10–12%, three or more at
≤ 0.5%. Almost all multiple matches are the same text under two names (`"let" | identifier`,
`nonArrowOperatorToken | postfixOperatorToken`). Different lengths: 3–24 positions per file
(`"-" | "->"`, `#`/`poundName`, `<`, regex literals). No terminal ever had two ends.

With the APUS grammar on `Swift.apus`: 99% of positions have one terminal; 17 questions per
position.

## Findings

1. Cost is per question, not per match: every question is a lex-cache probe (keyed on a
   `String.Index`) and, inside `lex()`, four more dictionary lookups (`virtualTokensAt`,
   `lexicalTokenRecognisers`, `literalSourceByID`, `regexByID`) before a `hasPrefix` or a
   regex `prefixMatch`.
2. Regex terminals run where they cannot start (numeric literals at a letter, `identifier`
   at an operator). Swift's `Regex.prefixMatch` has a large fixed cost per call.
3. Literal munch: each matching literal runs the 3 `@literalMunch` regexes again.
4. Exclusion `---( … )` probes every excluded keyword one at a time.
5. `suppressesLeadingTriviaForPrediction` builds `bodySymbols` arrays on every call, but
   depends only on (slot, terminal).
6. Trailing trivia is skipped once per match, not once per distinct end.

## Design: a lazy tΣᵢ

On the first visit to position `i`, compute once:
- `tΣᵢ`: a `BitSet` of the cheap terminals that match at `i`, with their ends grouped as
  `end → BitSet`;
  - literals: one walk of a trie over all literals gives every literal that matches;
  - regexes: only those whose precomputed first-character set admits the next character
    (from the leading atom of the regex; "any character" when the analysis is unsure, so the
    filter is always safe);
  - virtual tokens from their table; EOS at the end of input;
- recognisers stay lazy, run only when one is in the predict set (each is a GLL sub-parse).

Then:
- `viable(slot)` = leading gates hold ∧ `predictBS(slot) ∩ tΣᵢ ≠ ∅`, where `predictBS` =
  FIRST(slot) ∪ (FOLLOW(owner) if nullable), precomputed per slot. `continuationViable` is
  the same intersection.
- Exclusion: for some end `e` of `t`, `excludeBS ∩ terminalsEndingAt(i, e) = ∅`.
- Literal munch: a literal is suppressed when a munch terminal in `tΣᵢ` has a longer end.
- Trailing trivia: skipped once per distinct end.
- Rare context-dependent questions keep today's uncached path: slots that suppress leading
  trivia, recogniser sub-parses (`usesRecognizerLexBoundaries`), `@preempt` split choices.

Exactness: `tΣᵢ = {t | lex(i, t) ≠ ∅}` by construction, so `T ∩ tΣᵢ ≠ ∅` is LCNP's
`valid(i, T)`. The existing cache, keyed on (position, terminal) only, already relies on lex
being independent of context. The Bend twin treats `lex` abstractly, so its proofs are not
affected.

Care point: `hasPrefix` compares `Character`s (`"e"` does not match the start of a
decomposed `"é"`). A byte-level trie must check that a match ends on a character boundary.

## Plan

1. **Cheap fixes.** Precompute `suppressesLeadingTriviaForPrediction` per slot (a `BitSet`
   of terminals whose first occurrence suppresses leading trivia, usually empty). Replace the
   four dictionary lookups in `lex()` by one array indexed by terminal ID (kind + payload).
   Expected ≈ 15%.
2. **tΣᵢ.** Literal trie, first-character sets for regexes, per-position entry with ends.
   Switch `viable` and `continuationViable` to `predictBS ∩ tΣᵢ`.
3. **Move the rest onto the per-position entry:** exclusion, literal munch, trailing trivia,
   and `tokenMatch`.
4. **Retire** `lexCache` for ordinary questions once nothing reads it (the lex report in
   `DecisionStatisticsTests` must then read the per-position entries instead).

None of these steps has been made yet. Step 1's precomputed `BitSet` is withdrawn: see
"Revised proposals" below, which removes the cost without precomputing anything.

## Re-measurement (2026-11-17, Swift grammar on `GenerateSwiftSyntaxAST.swift`)

Input: 544 KB, 9,801 lines, one parse from the CLI (`^^^#GenerateSwiftSyntaxAST.swift`).
About 11 s and almost 2 million descriptors. Instruments Time Profiler, Release build,
37,000 samples, symbolicated with `atos` (trace: `~/Desktop/apus.trace`).

| What (inclusive) | Share |
|---|---|
| `MessageParser.parse` | 92.5% |
| `addDescriptorsForAlternates` → `viable` → `anyTerminalMatches` | 58% / 52% / 51% |
| `cachedLex` | 51% |
| `OnDemandLiteralLexer.lex` (cache misses) | 35% |
| Swift `Regex` engine (`prefixMatch` → `Executor._run`) | 28% |
| of which `Processor.signalFailure` (failing matches) | 10% |
| `continuationViable` (mostly from `leave`) | 17% |
| lex-cache dictionary probes (`Dictionary.subscript.getter` in `cachedLex`) | 10% |
| `suppressesLeadingTriviaForPrediction` | 12% |
| of which `bodySymbols` (array building) | 5.6% |
| `tokenMatch` (almost all of it the `---( )` exclusion) | 6% |
| descriptors and yields (`addDescriptor`, `addYield`, set inserts) | ≈ 4.5% |
| `swift_retain` + `swift_release` (self) | 14.5% |

Hottest functions by self time: `__RawDictionaryStorage.find` 11%, `swift_release` 7.8%,
`swift_retain` 6.7%, `Hasher._finalize` + `_combine` 6.9%, `Processor.cycle` 3.6%.

Compared with 2026-11-04 the picture is the same: GLL itself is cheap, and answering "can
terminal t start here?" one terminal at a time costs most of the time.

## Findings (2026-11-17)

7. **The lexer runs about 1,000× slower than a lexer should.** Lexing a 544 KB file once,
   byte by byte, takes a few milliseconds (≥ 100 MB/s). Here `lex` takes about a third of
   11 s, roughly 3.5–4 s. The target of being 10–100× faster is conservative. The cost is
   not the number of tokens. It comes from the work done for each of the ~60 questions asked
   at every position (finding 1), and from each question going through the general Swift
   `Regex` engine or a `Character`-level comparison.
8. **Every regex question pays the full `Regex` setup cost, even when it fails on the first
   character.** `prefixMatch` builds a `Processor` (registers, save points, a retained
   program), runs it, and tears it down: `Processor.cycle`, `signalFailure`,
   `destroy for Processor.SavePoint`, `initializeWithCopy for MEProgram`. All regexes are
   stored as `Regex<AnyRegexOutput>`, so a match also builds a type-erased output.
   `CharacterClass` members built from closures
   (`DSLTree.CustomCharacterClass.Member.generateConsumer`) show up on their own (0.9%).
9. **Literal tests compare `Character`s.** `Substring.hasPrefix` walks grapheme clusters
   (`String.Iterator.next`, `_StringGuts.validateScalarIndex`, `_quickASCIICharacter`), and
   `index(offsetBy: literal.count)` walks them again. Most of the 223 literals fail on the
   first byte.
10. **The lexer struct is copied on every call (part of the retain/release cost).**
    `MessageParser.lexer` is `var lexer: OnDemandLiteralLexer!`: an implicitly unwrapped
    optional STRUCT stored in a class, holding about 12 reference-counted fields (`input`,
    six dictionaries, arrays, closures). The profile shows `initializeWithCopy for
    OnDemandLiteralLexer` and `destroy for OnDemandLiteralLexer`. Each `lexer.lex(…)` copies
    the whole struct out of the optional (one retain per field) and destroys it afterwards
    (one release per field). The rest of the retain/release traffic is the `Regex` engine
    (finding 8) and the `input[scanStart...]` substrings (each retains the string's
    storage).
11. **Hashing positions costs about 10%.** `LexCacheKey` is (`String.Index`, `Int`), and every
    probe runs SipHash (`Hasher._combine`, `_finalize`). An integer key would hash no faster.
    The cost goes away only when a table indexed by position replaces the dictionary.
12. **`bodySymbols` allocates a new array on every call.** It collects the `seq` chain of an
    alternative up to its `END` (`GrammarNode.swift:297`). `suppressesLeadingTriviaForPrediction`
    calls it for every candidate terminal and stops at the first symbol it looks at. The
    array is not needed: walking `seq` in place gives the same answer.
13. **`tokenMatch` pays for cases that are rare, on every token.** Three filters are layered on
    the lex result: the `@preempt` split commit, the `---( )` exclusion, and a dedupe by
    `triviaEnd`. The common case has one match, no preempt and no exclusion, but still
    builds a `Set<String.Index>` and a new array. When a slot has an exclusion
    (`identifier ---( lexerClassifiedKeyword )`), every excluded keyword is lexed separately
    (`exclusionLex`, each a cache probe), although the question is just "is this text one of
    those keywords?".

## Revised proposals (2026-11-17)

Analysis only; each item is an engine change to be agreed first. The aim is to remove work,
not to cache or precompute it.

A. **Store the lexer by reference.** Make `OnDemandLiteralLexer` a `final class`, or store it
   non-optional. One reference instead of twelve per call. Trivial, and it should remove the
   copy/destroy traffic of finding 10.
B. **Compare literals on bytes.** Compare `input.utf8` against the literal's UTF-8 bytes;
   the first byte rejects almost every literal immediately. This is the "first-character
   filter" for literals, and it needs no analysis. Care point: a match must end on a
   `Character` boundary (see the `"é"` note above).
C. **Hand-written scanners for the hot regex terminals.** `identifier`, the operator
   terminals, the numeric literals and `poundName` are simple, and most regex questions are
   about them. Each becomes a small scanner over UTF-8 / unicode scalars, as the string
   literals already are (`ApusTokenScanner`, `SwiftStringLiteralTokens`). A hand-written
   scanner fails on the first byte in nanoseconds, so no first-character analysis is
   needed. The `Regex` stays as the specification, and a differential test checks that each
   scanner agrees with its regex over the test corpus.
D. **First-character sets for the remaining regexes: declared, not extracted.** RegexBuilder
   regexes cannot be analysed through public API. The builder tree (`DSLTree`) is internal.
   `Regex._literalPattern` (underscored, Swift 6) prints a builder as a pattern when it can,
   but whether it covers our patterns is still to be checked, and it would mean parsing
   regex syntax. The builders are already made of named heads (`identifierHead`,
   `operatorHead`, …), so each library entry can declare its head next to its builder,
   reusing the same named `CharacterClass`. A missing declaration means "any character", so
   the filter stays safe. The differential test of C checks soundness on the corpus. After
   C this matters only for the few rare regexes left.
E. **Integer positions inside the parser.** `CharPosition` becomes a UTF-8 offset (`Int`).
   `String.Index` appears only where a `Regex` still runs (conversion is O(1) on native
   strings). Integer positions make the tables of F possible and remove `String.Index` from
   every hashed key.
F. **Answer each position once (the lazy tΣᵢ above).** Once B–D make the matching cheap,
   compute what is at a position the first time that position is visited, in an array
   indexed by offset. That replaces the per-question dictionary probe (finding 11).
G. **`suppressesLeadingTriviaForPrediction` without `bodySymbols`.** Walk `slot.seq` up to
   `END` in place, with the same early exits. No allocation and no precomputed table.
H. **`tokenMatch` fast path, and exclusion by text.** Return immediately when there is one
   match, no `@preempt` and no exclusion. When every excluded terminal is a literal (the
   keyword case), exclusion becomes one question: is the matched text one of those
   literals? That needs no lex call per keyword.

Expected order of gains: A, G and H are small and local. B and C remove most of the 35% lex
time and most of the retain/release traffic. E and F remove the remaining probe and hashing
cost.

## Results (2026-11-18, same input, Release CLI, CPU time, mean of 3 runs)

| Step | CPU time | Change |
|---|---|---|
| Baseline | 11.16 s | |
| A: `OnDemandLiteralLexer` is a `final class` | 10.80 s | −3.2% |
| H1: `tokenMatch` returns early (one match, no exclusion) | 10.70 s | −1.0% |
| H2: an excluded literal is checked against the candidate's text | 10.46 s | −2.3% |
| G: `suppressesLeadingTriviaForPrediction` walks `seq` in place | 9.09 s | −13% |
| Lazy per-position bits (`lexAsked`/`lexMatched`, two `BitArray`s) in front of `lexCache` | 8.1 s | −11% |
| C: hand-written matchers for `identifier`, `poundName`, `propertyWrapperProjection` and the four operator terminals | 5.15 s | −36% |
| Total | 5.15 s | −54% |

C: `ApusRegexLibrary.matchers` (end of `SwiftGrammarRegexLibrary.swift`), bound by builder key
through `TokenPattern.matcherKey` and run by `OnDemandLiteralLexer.patternEnd` in the regex path,
literal munch and `@preempt` splits. ASCII is decided by hand. A non-ASCII scalar is decided by a
one-scalar regex over the same library class, so the Unicode ranges stay written once. The
regexes remain the specification: `HandMatcherTests` compares each matcher with its regex at every
scalar position of a corpus (1.25 million checks, 0 differences when written).

Tried and reverted: remembering the longest `@literalMunch` end for the last position
(no gain: at 87–89% of positions only one literal matches, so there was nothing to share).

Profile after the lazy bits (2026-11-18, `xctrace` Time Profiler, 9,000 samples):
`OnDemandLiteralLexer.lex` 44%, the Swift `Regex` engine 37%, `Set.insert` 12% (yields,
descriptors, `enter`), `lexCache` stores 9%, `hasPrefix` only 4.7%. The regex time splits into
literal munch, `Lexer.swift` munch loop (13%), and regex terminals asked where they cannot start
(20%). Both are mostly the `identifier` and operator regexes, so C (hand-written scanners for
them) is now the step with the largest gain. B is worth at most ≈ 5%.

## Finding 14: why our regexes are slow (micro-benchmark, 2026-11-18)

`swiftc -O`, the real `SwiftGrammarRegexLibrary.swift`, one `prefixMatch` per call:

| Per call | Fails at `+` | Matches `barBaz123` |
|---|---|---|
| library `identifier` (what `lex` runs) | 3,541 ns | 6,247 ns |
| the same, typed instead of `AnyRegexOutput` | 3,472 ns | 6,252 ns |
| ASCII pattern `[A-Za-z_][A-Za-z0-9_]*` | 271 ns | 589 ns |
| library `nonArrowOperatorToken` | 7,911 ns | 9,147 ns |
| loop over `utf8` | 3 ns | 18 ns |

The API is used correctly. Type erasure, `Substring` and matching semantics make no
difference. The cost is in the character classes. Swift `Regex` turns a class into a bitmap
only when all its members are ASCII. A class that mixes ASCII and Unicode ranges is tested
member by member, at ≈ 65 ns per range, and a character that fails pays for every range.
`identifierHead` has 48 ranges, and a pattern string with the same ranges costs the same
(3,193 ns).

Splitting each class into its ASCII part (a bitmap) and the rest, tried only after a
one-range "not ASCII" check, gives the same ends on a mixed sample. It costs 636 ns when
failing at `+` (5.6×) and 2,645 ns when matching `barBaz123` (2.4×). About 270 ns per call is
the engine's floor, so even a perfect regex stays ≈ 100× slower than a hand-written scanner.

## Profile after C (2026-11-18, 5.15 s)

| What (inclusive) | Share |
|---|---|
| `viable` | 41% |
| `cachedLex` | 36% |
| `OnDemandLiteralLexer.lex` | 19% |
| `Set.insert` (`addYield` 4.4%, `addDescriptor` 4.3%, `Grammar.updateFollow` 2.6%, `enter` 2.4%, …) | 18% |
| `lexCache` stores (`Dictionary` setter) | 12.5% |
| hashing (`Hashable._rawHashValue`) | 10.5% |
| `skipTrivia` | 7.9% |
| `Regex` engine (other regex terminals, trivia) | 7.5% |
| `hasPrefix` (literals) | 6.9% |

Not part of the measured parse time: `ApusMarkdownConverter` (6.4% of the trace) runs at grammar
load.

## Step 1a: `CharPosition = Int` (2026-11-18)

`CharPosition` is a UTF-8 offset. `prepareInput` calls `makeContiguousUTF8()`, so the helpers next
to the `typealias` in `Lexer.swift` (`index(at:)`, `position(of:)`, `endPosition`,
`[positions:]`, `[from:]`, `[characterAt:]`, `position(afterCharacterAt:)`) are O(1). This step is
purely mechanical. `String.Index` remains wherever a `String` API needs one (regexes, matchers,
scanners, slicing text, `LayoutTokenInjection`'s `Character` walk). `Character` semantics are kept
everywhere, including in reports that print character offsets.

Exactness check: the old and the new build parsed the same frozen input. Their dumps of every lex
answer, yield and descriptor (7.6 million lines, in UTF-8 offsets) are identical, and so are the
counts. `tools/run_tests.sh`, `HandMatcherTests`, `TriviaRoundTripTests`, `SpecialTokenTests`,
`OracleDisambiguationTests`, `CoreGrammarTests` and `BendExport` pass. CPU time on the same input:
5.04 s → 4.96 s. The gains come from what `Int` makes possible next (1b, then the packed descriptor
and the tables indexed by position).

Measurement trap: the benchmark input is `GenerateSwiftSyntaxAST.swift`, a source file that changes
with the code. Editing it changes the counts (1,897,690 → 1,898,316 descriptors after 1a). Compare
counts only on the same input. Since 2026-11-18 the benchmark is a frozen copy,
`grammars/sampleLargeFile.swift` (outside every target, so it is not compiled), referenced from
`Swift.apus` as `^^^#../grammars/sampleLargeFile.swift`. That spelling resolves for the CLI
(relative to `ApusApus/`) and for the tests (relative to `grammars/`). Baseline on it: 4.96 s,
1,898,316 descriptors.

## Step 1b: the lexer on bytes (2026-11-18)

Literals are compared as UTF-8 bytes (`literalBytesByID`, `bytesMatch`), like swiftc's lexer, no
longer as `Character`s. A complete UTF-8 literal always ends on a scalar boundary. `@preempt` split
points step by scalar (`scalarEnd`). The `---( )` text check compares bytes. The hand-written
matchers take a `MatcherInput` (the bytes plus the `String` for the one-scalar regex slow path) and
`Int` positions, so the conversion wrappers are gone. The counts on `sampleLargeFile.swift` are
unchanged. `tools/run_tests.sh`, `HandMatcherTests` and the related suites pass.
**4.96 s → 4.59 s (−7.5%).**

## Step 2: one-word `Descriptor` (2026-11-18)

`Descriptor` is a `UInt64`: slot number (16 bits) | k (24) | i (24). `Grammar.nodes` maps a number
back to its node. `prepareInput` checks the limits: at most 65,536 nodes, inputs below 16 MiB. A
TODO notes per-parse widths. Counts unchanged, tests pass. **No measurable gain**
(4.59 s → 4.65 s, within noise). Descriptor bookkeeping was only ≈ 4% of the time, and
`Set<Descriptor>` still runs SipHash on the one word.

Profile after step 2 (4.65 s): `lexCache` stores 13.6% (nearly all of them non-matches, which the
bits already record), `Set.insert` 18.8% (`addYield` 4.5%, `addDescriptor` 3.7%, `enter` 3.2%,
`recordMismatch` 1.6%), `skipTrivia` 8.2% with trivia regexes 8%, the per-terminal dictionaries in
`lex` 4.8%, `probe` 6.5%. Outside the measured time: `ApusMarkdownConverter` 7.3% at grammar load.

## Clean-up: keep only what pays (2026-11-18)

Step 2 was reverted (`Descriptor` is three fields again; a note at its TODO records the attempt).
Each earlier change was then taken out on its own and measured on the current code (median of
5 runs; baseline 4.58 s):

| Taken out | CPU time | Verdict |
|---|---|---|
| A: lexer back to a `struct` | 5.08 s | keep (+11%) |
| H1: `tokenMatch` early return | 4.60 s | removed (noise) |
| H2: excluded literal checked against the text | +11% | keep |
| G: walk `seq` in place | +25% | keep |
| lazy per-position bits | +17% | keep |

(H2, G and the bits were measured with H1 already out, against 4.60 s and then 5.13 s.)

Proposal 1, done so that the code gets simpler. Since ≈ 98% of the answers are non-matches, ONE
bit array, `lexNoMatch`, replaces `lexAsked` + `lexMatched`, and `lexCache` holds only matches.
`cachedLex` returns `[]` for a known non-match without hashing or allocating, so the separate
yes/no function `lexes(at:entry:…)` and the `entry` hoisted in `viable` / `continuationViable` are
gone. `forEachLexAnswer` reports both kinds of answer to `DecisionStatisticsTests`.
**4.62 s → 3.81 s (−18%).**

`exclusionLexCache` was removed too: since H2, only excluded terminals that are not literals reach
`exclusionLex`, and calling the lexer directly costs nothing measurable (3.81 s → 3.84 s, noise).

State: ≈ 3.85 s on `sampleLargeFile.swift`, 1,898,316 descriptors. `tools/run_tests.sh`,
`HandMatcherTests`, `TriviaRoundTripTests`, `SpecialTokenTests`, `OracleDisambiguationTests`,
`CoreGrammarTests`, `LanguageGrammarTests`, `BendExport` and `DecisionStatisticsTests` pass.

The descriptor, CRF, set and yield counts are unchanged at every step (1,897,690 descriptors),
and `tools/run_tests.sh` passes after H2 and after G. G gained more than its 5.6% profile share,
probably because removing the allocations also took malloc and retain/release work off the
hot loop.

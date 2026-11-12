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

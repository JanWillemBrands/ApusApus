# Testing

How the Advent / APUS GLL parser is tested, how to run the suites, how to read
their (sometimes misleading) output, and the pitfalls that have cost real time.

This doc consolidates hard-won workflow knowledge. When you change any of it,
update this file — it is meant to be the single home for "how we test."

---

## 1. Test harnesses (and which one is the source of truth)

There are **two** ways a Swift snippet gets fed to the grammar. They disagree on
identical input, and only one is authoritative.

### 1a. SwiftSyntax Swift Testing suites — THE SOURCE OF TRUTH

`AdventTests/SwiftSyntax*.swift` — parametrized `swift-testing` suites over
`SwiftSnippet` arrays, driven through `adventParse` →
`runAdventOnce` → the shared `cachedSwiftGrammar`. The snippet source is the
byte-exact `SwiftSnippet.source` (a Swift `"""…"""` literal, so the compiler has
already unescaped it).

Suites (one `@Suite` each, struct in parens):

| File | Suite struct | Origin | ~count |
|------|--------------|--------|--------|
| `SwiftSyntaxDeclarations.swift` | `DeclarationSyntaxTests` | DeclarationTests | 173 |
| `SwiftSyntaxExpressions.swift` | `ExpressionSyntaxTests` | ExpressionTests | 184 |
| `SwiftSyntaxStatements.swift` | `StatementSyntaxTests` | StatementTests | 52 |
| `SwiftSyntaxTypes.swift` | `TypeSyntaxTests` | TypeTests | 71 |
| `SwiftSyntaxPatterns.swift` | `PatternSyntaxTests` | PatternTests | 6 |
| `SwiftSyntaxAttributes.swift` | `AttributeSyntaxTests` | AttributeTests | 104 |
| `SwiftSyntaxTranslated.swift` | `TranslatedSyntaxTests` | 79 translated files | 1263 |
| `SwiftSyntaxTests.swift` | shared infra (`SwiftSnippet`, `adventParse`, `ParserProbe`) | — | — |

### 1b. `^^^` messages in `Swift.apus` — NOT a truth signal

`Swift.apus` embeds ~840 snippets as `^^^ … ^^^` blocks, parsed by
`main.swift` and by `LanguageGrammarTests / SwiftGrammar / parseMessagesSequentially`
(→ `parseLanguageMessage`). **Do not use this path to judge whether Advent accepts
a snippet.** It is retained only because `main.swift` and `harvest_ambiguity.py`
still drive off it.

**Why they disagree (this has caused weeks of phantom debugging, twice):**
1. `^^^` blocks re-add leading/trailing whitespace that single-line `"""` sources
   don't have, and are stored **escaped** (`\"`, `\n`, `\t`) — see the escaping bug
   in §7.
2. `parseLanguageMessage` checks only `parser.currentParseRoot` with a **strict
   `j == endIndex`**; `adventParse` requires a `grammar.root` yield via `buildAST`
   with **EOS-trivia tolerance**. Different root + different criterion.

Concrete: `func square(_ x: Int) -> Int { return x*x }` "passes" the `^^^` path but
genuinely **fails** `adventParse`. Conversely (2026-07-28) the four top-level
bodiless-func snippets (`@objc(_:)⏎func f(_: Int)`, `@abi(func fn()) func fn()`, …)
**pass** as `^^^` messages — because that path checks acceptance only — while the
Swift Testing cases still show red, because they *also* run `treesMatch`
(the acceptance is fine; the tree comparison is the frontier — see §7).

**Rule of thumb:** "passes as a message but fails as a test case" almost always
means *acceptance passes, `treesMatch` fails*. Check the `@Test` name before
concluding anything is broken.

---

## 2. The four `@Test`s per suite — what each one signals

Each SwiftSyntax suite runs the same snippet array through four checks. They are
NOT equal in authority:

| `@Test` | Question | Authority |
|--------|----------|-----------|
| **`swiftSyntaxAccepts`** | does swift-syntax `Parser.parse(source:).hasError == false`? | baseline — confirms the snippet is valid input |
| **`Advent accepts`** | does the grammar produce a full-span root yield? | **correctness signal** — a failure is a real accept regression |
| **`no residual ambiguity`** | after the Oracle, is the parse unambiguous? | **correctness signal** — a failure is a real ambiguity |
| **`trees match`** | does Advent's derivation dump byte-match swift-syntax's tree dump? | **aspirational frontier** — most failures here are expected, not regressions |

`accepts` is computed **pre-Oracle** (raw yields), so Oracle rules like
`@longest`/`@prefer` cannot cause an accept failure. `unambiguous` and `treesMatch`
are post-Oracle.

**`treesMatch` is the current frontier.** ~1660 of the Translated cases fail it —
that is the baseline, not a regression. When triaging a run, always split issues by
`@Test`: only `accepts` / `no residual ambiguity` failures are actionable
correctness signals. A `treesMatch` count that is *stable vs baseline* means "no
regression" even though the run is red.

---

## 3. Running the suites

### Full sweep — `tools/run_tests.sh` (use this)

```bash
tools/run_tests.sh                 # all correctness suites
tools/run_tests.sh Rejects         # only suites matching a name (grep -i)
tools/run_tests.sh Expressions Types
```

This script is the authoritative runner and folds in every workflow safeguard, so
you never have to reconstruct them by hand. It:
- **always builds fresh** (no stale DerivedData binary),
- leaves **hashing non-deterministic on purpose** — the GLL algorithm does not depend
  on `Dictionary`/`Set` order, so a random seed acts as a fuzzer that surfaces
  order-dependent bugs (see the dollar-closure story in §7). Do **not** set
  `SWIFT_DETERMINISTIC_HASHING`.
- runs the **full** suite set every time (no MCP "smart re-run" narrowing),
- reads the **complete** log (no 100-row truncation) and prints clean per-category
  counts by matching the exact `#expect` messages,
- **flags `Crash: … <deduplicated_symbol>` loudly as a real fault**, and
- exits non-zero only on crashes or correctness failures — `Trees differ` (the
  frontier, §2) is reported but never fails the run.

The counts it prints map to these messages, if you ever need to grep a log yourself:

| Category | Message grepped | Actionable? |
|----------|-----------------|-------------|
| reject failure | `Advent wrongly accepted invalid input` | yes — accepted invalid input |
| accept failure | `Advent failed to parse:` | yes — rejected valid input |
| residual ambiguity | `Residual ambiguity in` | yes |
| trees differ | `Trees differ for` | no — frontier |

### Iterating on the grammar — use the probe

For fast single-snippet iteration use the non-parametric `SwiftSyntaxTests / ParserProbe`
`@Test` calling `adventParse` on exact strings. `.apus` edits are read at runtime via
`#filePath`, so a grammar-only change needs **no recompile** — but that also means
MCP `RunSomeTests` sees "no changed input" and may re-run only a stale set of args;
for any real count use `tools/run_tests.sh`.

---

## 4. Reading output — the traps

### `main.swift` / CLI logs are invisible on stdout

`Logger.*` (OSLog) messages go to the unified log, **not** stdout/stderr. Worse, the
console app's logs are effectively **not captured** at all when run headless — a
grammar-load failure exits `1` with **completely empty stdout** (all diagnostics
went to `Logger.ui.error` then `exit(1)`). Don't assume "no output" means "no run."

Read OSLog explicitly (note: full path `/usr/bin/log` — zsh has a `log` builtin):
```bash
/usr/bin/log show --last 30s --info --debug --no-pager \
  --predicate 's="com.magenta.apusParser"' 2>&1 | head -100
```
Subsystem `com.magenta.apusParser`; categories `ui`/`scan`/`parse`/`grammar`/`generate`.
OSLog **redacts** `\(interpolated)` values as `<private>` outside the debugger — for
content, temporarily `fputs(…, stderr)` or read them in Xcode's console.

### Probe swift-syntax truth with `hasError`, not `swiftc`

Ground truth for "is this valid Swift?" is swift-syntax
`Parser.parse(source:).hasError` (what `swiftSyntaxAccepts` uses). `swiftc -parse`
is a *different* parser and diverges on trivia (it accepts `@available (*)`,
`nonisolated ()->` with a space, that `hasError` rejects). To probe fast, add a temp
`@Test` in `SwiftSyntaxTests.ParserProbe`, `print("PROBE …")`, run with
`RunSomeTests`, grep `PROBE`, remove it. (`RunCodeSnippet` needs `-Onone`; the main
target is `-O`.)

---

## 5. Parallel execution (2026-07-27)

The SwiftSyntax comparison suites run **in parallel**. This is safe because the
parser was made reentrant:

- **Shared immutable grammar.** `cachedSwiftGrammar` loads `Swift.apus` **once**
  (lazy `let`, thread-safe init) and shares it; it is load-time immutable
  (yields moved off `GrammarNode` into `MessageParser.yields[node.number]`).
- **Per-parse instances, no static state.** `MessageParser`, `Grammar`, `Scanner`,
  `CallReturnForest`, `Descriptor`, BSR carry **no** `static var`. Each parse builds
  its own `MessageParser`.
- **Per-source memoization.** `parseCache` parses each unique source once; the three
  post-parse `@Test`s share that result.

### What had to change to go parallel
1. **`ebnfDot()`/`emit()` made static-free** (GrammarNode.swift). They used four
   process-global statics (`dottedEBNF`/`dottedSlot`/`containingNonterminal`/
   `toplevelAlternate`) as recursion scratch — a data race in diagnostics. State is
   now threaded as `inout`/params.
2. **Dropped the global lock from the hot path.** `withParserIsolation`
   (an `NSRecursiveLock` in `TestInfrastructure.swift`) previously serialized *every*
   parse. It was removed from `runAdventOnce` (which uses the pre-built cached grammar
   and touches no statics). It is **kept** around the small-grammar helpers
   (`parseMatches`/`parseGrammar`/`loadGrammarFile`, and Performance/ParserGenerator/
   SpecialToken suites) which *build* grammars and touch `GrammarNode.sizeofSets`.
3. **Un-`.serialized`ed the 7 SwiftSyntax comparison suites** so their parametrized
   cases (e.g. the 1263-case `treesMatch`) fan out across cores. The grammar-building
   suites stay `.serialized`.
4. **Gated the baseline CSV.** `runAdventOnce` only writes `baseline-phase0.csv` when
   `APUS_BASELINE_CSV=1` — otherwise parallel row order churns that tracked file.

### Results / verification
- Test-run phase **~43s → ~16s** on the 7 suites (~2.6×); `user ≈ 2×real` confirms
  real multicore use. Wall time is now dominated by the build (see §7 stale builds).
- **No data race (one-time check):** pinning the seed with
  `SWIFT_DETERMINISTIC_HASHING=1` for this verification gave identical issue counts and
  failing snippets across repeated runs. That was a *methodology to prove reentrancy* —
  normal runs stay non-deterministic (§7).
- **ThreadSanitizer: 0 data-race warnings** on a high-concurrency subset
  (`-enableThreadSanitizer YES` on Expressions+Attributes). TSan exits non-zero
  simply because `treesMatch` fails — that is not a race; grep for
  `WARNING: ThreadSanitizer`.

---

## 6. The test corpus / extraction pipeline

Snippets are extracted from the `swift-syntax` repo by `tools/extract_snippets.py`.
The Advent test target currently keeps two corpora side by side:

- `swift-syntax 603`: the pre-6.4 baseline corpus, with child suites such as
  `Declarations`, `Expressions`, and `Rejects`.
- `swift-syntax 604`: the 6.4 migration corpus, imported from
  `604.0.0-prerelease-2026-06-05`, with the same child-suite names.

The raw 604 SwiftSyntax parser tests are copied under `tools/swiftsyntax_tests_604`
for provenance; `tools/swiftsyntax_tests` remains the older corpus source.

Extraction rules:
1. Parse `assertParse(...)` calls; **skip** those with a `diagnostics:` arg
   (error-recovery tests).
2. Strip diagnostic markers (1️⃣, ℹ️).
3. Tag `@_`-underscored attributes → `disabledReason: "underscore attribute"`.
4. Emit `SwiftSnippet` arrays.

`disabledReason` values: `"underscore attribute"`, `"experimental feature"`
(features swift-syntax 603.0.1 itself rejects), `"compiler error — <ref>"`
(cases where Advent deliberately follows the **compiler**, which is stricter than
swift-syntax's permissive parser — see the acceptance-policy note in `TODO.md`).

**Limitation:** the script can't expand `assertParse` sources that use string
interpolation with loop variables — expand those into concrete snippets by hand.

**On a swift-syntax version bump:** re-download test files, re-run the extractor with
the new version string, diff against existing snippet files, and re-check the
experimental-feature disables (features may have graduated).

---

## 7. Known problems, gotchas & stale-test hazards

*Build staleness, smart-rerun narrowing, log truncation, and mixed crash/grammar
counts are all handled by `tools/run_tests.sh` (§3) — use it and none of those bite.
The items below are the residual knowledge a script can't remove.*

- **A wall of `Crash: … <deduplicated_symbol>` is a REAL fault, not runner noise.**
  When every case in a suite reports that identical crash, the parser is trapping at
  runtime. The classic cause is a **canonically-decomposable scalar used as a
  `CharacterClass` range bound** (see the U+F900 / U+2000 note in
  `SwiftGrammarRegexLibrary.swift`): Swift's regex engine traps at *match time*, so it
  crashes every parse reaching that terminal — which looks like mass runner failure.
  (This once masqueraded as "122 pre-existing crashes"; it was one bad bound.)
  Check a bound with
  `python3 -c "import unicodedata; d=unicodedata.decomposition(chr(0xNNNN)); print(d and not d.startswith('<'))"`
  — `True` = unsafe as a bound; give it via `.anyOf` instead.

- **`^^^` fixtures are stored escaped.** The `^^^` blocks contain literal `\"`,`\n`,
  `\t`. `harvest_ambiguity.py` **unescapes** before running; `loadLanguageFixture`
  and `accept_dump.py` do **not** → they feed malformed Swift → **false rejections**.
  The `LanguageGrammarTests / SwiftGrammar` "104 issues" baseline is exactly this
  artifact, **not** a grammar bug. Don't chase it.

- **Message-path vs test-path (see §1b).** "Passes as a message, fails as a test" =
  acceptance passes, `treesMatch` fails. Always split by `@Test`.

- **`treesMatch` is red by design.** ~1660 Translated cases fail it. Track the count
  vs baseline; a *stable* count = no regression.

- **Load-time non-confluence → per-process flakes.** The old
  `testClosureWithDollarIdentifier#1/#2` "flake" (~50%) was NOT a parser race — it
  was a **non-confluent exclude-set fixpoint at grammar load**
  (`Grammar.propagateExcludeSets` used a `formUnion` *least* fixpoint for
  intersection semantics; the result depended on hash-seeded `Dictionary` order).
  Because the grammar is loaded once and **cached/shared**, the wrong-or-right set was
  baked in per process → looked flaky. Fixed as a **greatest** fixpoint (start at TOP,
  shrink by intersection). **Lesson:** a shared cached grammar makes *any* load-time
  order-dependence a per-process flake — this is exactly why we keep hashing
  **non-deterministic**: the random seed is what exposes such bugs. When one surfaces,
  audit load-time set computations for order-independence; to study a specific case you
  can temporarily set `SWIFT_DETERMINISTIC_HASHING=1` to reproduce one seed and diff
  descriptors/yields between a PASS and a FAIL run — but never leave it set for normal runs.

---

## 8. Debugging workflow (grammar vs swift-syntax failures)

1. **Fix by root cause, not by test.** Cluster failures by shared cause (same as the
   ambiguity-signature workflow) — one grammar change usually clears a whole cluster.
2. **Probe swift-syntax truth (`hasError`) before every faithfulness claim** (§4).
3. **Prefer structural grammar fixes over `@prefer`/oracle hacks** — only `.apus`
   declarations, no custom Swift disambiguation. `@prefer` is single-level (no 3-way
   priority) and can create *new* ambiguities; re-harvest after.
4. **Measure with the right yardstick.** `Advent accepts` (decoded `source`) is ground
   truth for acceptance; `harvest_ambiguity.py ALL` for ambiguity. The `^^^` /
   `accept_dump.py` paths are unreliable (escaping).
5. **After every change:** re-harvest (ambiguity unchanged or down) **and** run the
   affected suite (no acceptance regression).
6. **Distinguish "compiler-invalid but swift-syntax-permissive."** Many disabled
   snippets are cases where Advent correctly follows the *compiler* and rejects —
   those are policy, not gaps (see `TODO.md` acceptance-policy note).

---

*Testing improvement options live in `TODO.md` under "Testing infrastructure & speed."*

---

## 8b. Diagnosing an Oracle prune — `APUS_TRACE_ORACLE=1`

When a parse reports `matched: 1` (a full-span parse EXISTS) but `adventParse` returns nil, the
disambiguator removed the last reading and nothing says which rule did it. Do not theorise — trace:

```sh
TEST_RUNNER_APUS_TRACE_ORACLE=1 xcodebuild test -scheme Advent \
  -destination "platform=macOS,arch=arm64" -project Advent.xcodeproj \
  -only-testing:"AdventTests/SwiftSyntaxTests/ParserProbe/<yourProbe>()" 2>&1 \
  | grep oracle-trace
```

Emits one line per pruned yield — rule type, anchor node, span with source text — plus a
root-full-span ALIVE/GONE checkpoint after each of the four phases (phase-1 dead-wood,
hard-constraint pass, inter-pass dead-wood, preference pass, phase-2 dead-wood). The phase where
the root goes GONE localises the fault immediately.

Costs nothing when the variable is unset. Implemented in `Oracle.swift` (`traceRulePrunes`,
`logRulePrune`, `logRootStatus`). This is what finally explained the accessor-block gap after three
wrong inferences — see REJECTS.md C7.

## 8b-lex. Which lexicalisation won? — `APUS_TRACE_LEX=1`

`explainNoMatch` (§8b) is SLOT-oriented: "why did THIS terminal fail here?". With on-demand lexing
you usually need the POSITION-oriented question instead — *what can be lexed here at all, how far
does each reading reach, and which one did the parse commit to?* Several terminals of different
extents match one position, and a parse can fail because the wrong-length reading survived. That fan
is invisible in a slot-local report.

`APUS_TRACE_LEX=1` fires on a FAILED parse, independently of `APUS_PARSE_REPORTS`, and dumps the fan
plus the parse state at the furthest position reached:

```sh
TEST_RUNNER_APUS_TRACE_LEX=1 xcodebuild test-without-building -project Advent.xcodeproj \
  -scheme Advent -destination 'platform=macOS,arch=arm64' -parallel-testing-enabled NO \
  -only-testing:AdventTests/<YourProbe>
```

Three methods on `MessageParser`, all callable directly from a probe when you want a position other
than the failure site:

| method | answers |
|---|---|
| `dumpLexicalisations(at:label:)` | every terminal matching here, longest first, with extents |
| `dumpParsePosition(_:label:)` | commits arriving/departing here, and which nonterminal yields cover it |
| `dumpFailureDiagnostics()` | both, at `furthestMismatchIndex` (the automatic hook) |

**Worked example — its first use.** `ApusToHTML.swift` fails to parse. Ten guesses at a minimal
construct all PASSED (line continuations, closer indentation, nested funcs, embedded quotes, blank
lines, and combinations); bisection narrowed to "statement 8 of `renderDocument` flips it" but
statement 8 accepts alone, so there was no construct to blame. One `APUS_TRACE_LEX` run gave:

```
commit ENDING here: singleLineStringLiteral '""'
```

The opening `"""` had been committed as an EMPTY single-line string, eating two of three quotes;
`multilineStringLiteral` produced no commit. That is a diagnosis — the wrong lexicalisation won —
and no amount of construct bisection would have shown it.

**Lesson:** when a large input fails and small reproductions pass, stop guessing at constructs and
ask which lexicalisation was committed.

## 8c. Bulk runs are quiet — `APUS_PARSE_REPORTS=1`, `APUS_TREE_DUMPS=1`

Two output sources were written for the single-message CLI in `main.swift` and were never gated,
so under the suites they fired on *every* parse and *every* failure. Both now default to OFF and
are opt-in per run. Nothing about the failure signal changed — the same 1028 issues and the same
`Trees differ` / `Residual ambiguity` / accept / reject counts, at a quarter of the volume:

| Run | Log lines | Issues |
|---|---|---|
| both sources ungated | 127,827 | 1028 |
| both gated (current default) | 30,966 | 1028 |

**`APUS_PARSE_REPORTS=1`** — the engine's own per-parse console output: the
`matched/failed/crf size/descriptors` summary `MessageParser.parse` emits on completion, the
`no parse found at …` block plus `explainNoMatch` / `dumpRecentCommits` on failure, and Oracle's
`oracle: removed …` line. That was ~9k lines per full run (4.1k summaries, 2.4k oracle lines,
1.3k failure blocks and their commit dumps). Flag lives in `OutputTools.swift` (`parseReports`);
`main.swift` sets it to `true` because the CLI parses one message, where the report is the point.

**`APUS_TREE_DUMPS=1`** — the full `refDump` / `adventDump` SwiftSyntax trees that Swift Testing
prints automatically under a failing `#expect(refDump == adventDump, …)`. That was ~96k of the
128k log lines. `TreeDump` (in `SwiftSyntaxTests.swift`) caps the framework's capture to a
one-line shape summary; suites that interpolate `\(refDump)` into their own message still print
the whole tree, because there a human asked for it. Set this when narrowing in on one snippet
whose suite passes only the snippet ID as its message.

Both need the **`TEST_RUNNER_` prefix** to reach the test process (same trap as
`SWIFT_DETERMINISTIC_HASHING` — see "Reading the numbers"):

```sh
TEST_RUNNER_APUS_TREE_DUMPS=1 TEST_RUNNER_APUS_PARSE_REPORTS=1 \
  xcodebuild test -scheme Advent -destination "platform=macOS,arch=arm64" \
  -project Advent.xcodeproj -only-testing:AdventTests/SwiftSyntax603Tests/TypeSyntaxTests
```

Related: a failing `#expect` also made the framework `Mirror`-walk whatever the condition named.
`#expect(result == nil, …)` therefore dumped the entire engine — every `TokenPattern` with its
compiled `Regex`, the `nonTerminals` table, the `GrammarNode` graph — 100 times per run, with a
**6.98 s stall** inside one such walk that made the run look hung mid-suite. `DerivationBuilder`,
`MessageParser` and `Grammar` now conform to `CustomTestReflectable` with a childless `Mirror`
(bottom of `TestInfrastructure.swift`), which caps the descent at the engine boundary.

## 9. Efficient testing workflow — recommendations

### Tier 1: single-snippet iteration (fastest, seconds)

Use `SwiftSyntaxTests / ParserProbe` with a temporary inline `adventParse` call.
`RunSomeTests` runs it instantly with no smart-rerun collapse (it is not
parametrized). Best for: confirming a single snippet accepts/rejects before
touching the grammar.

### `-only-testing` silently runs ZERO tests when the path is wrong

`xcodebuild ... -only-testing:'AdventTests/Oracle Disambiguation/Parse predicates'` exits **rc=0**
having run nothing. A non-matching filter is not an error, and a suite `@Suite("…")` display name
with spaces is not the identifier `-only-testing` wants. So a green targeted run proves nothing until
you confirm the count:

```sh
grep -E "Test run with|Executed [0-9]+ tests" run.log
# "Executed 0 tests, with 0 failures" ← the filter matched nothing
```

swift-testing also needs the trailing parens on a function (`…/myProbe()`). When in doubt, filter to
the FILE-level suite (`-only-testing:AdventTests/SwiftSyntax603Tests/ExpressionSyntaxTests`) or just
run the full set — it is 80s.

### Tier 2: targeted suite run (seconds to ~1 min)

Use `RunSomeTests` on a single suite (e.g. `RejectSyntaxTests/adventRejects(_:)`)
**immediately after** starting a fresh session (or after verifying the smart-rerun
cache is pointing at the right suite). Best for: confirming that a specific
category of failing tests passes after a fix. **Do not trust this after a session
reset without checking which test case it intends to run** (smart-rerun caveat above).

### Tier 3: reject-count sweep (the real correctness signal)

The definitive metric for "how many snippets does Advent wrongly accept?" is
a `RunAllTests` followed by a grep:
```bash
grep -c "Advent wrongly accepted" "$full_console_log"
```
This number is **immune to crash-count noise**. Run it:
- Before starting a new fix (establish baseline)
- After applying a fix (confirm it went down)
- Before closing a session (record final count in `REJECTS.md`)

Use `xcodebuild` (§3) for the authoritative command-line equivalent.

### Tier 4: full regression check (5–10 min)

Run `RunAllTests` (or `xcodebuild test`) targeting all suites. Then check:
1. `grep -c "Advent wrongly accepted"` — should be ≤ baseline
2. `grep -c "Advent wrongly rejected"` — must be 0 (no accept regressions)
3. Crash count in the `failed` total is expected to be 50–150 (pre-existing parallel noise)

The `treesMatch` suite failure count (~1660 baseline) is separately tracked and
not a correctness signal by itself.

### Interpreting a `RunAllTests` result quickly

| Observation | Meaning |
|-------------|---------|
| `failed` jumps by 20–40 with all-crash error messages | Pre-existing parallel noise, not a regression |
| `grep "wrongly accepted" log` goes up | Real regression — a previously-rejected snippet now accepts |
| `grep "wrongly rejected" log` > 0 | Accept regression — fix narrowed the grammar too much |
| `testEscapedIdentifiers16#1` STATE: Passed in `fullSummaryPath` | C11 fix is live |
| `fullSummaryPath` missing a test you expect | The test ran in a process that crashed — not a grammar signal |

## Reading the numbers (settled 2026-08-30)

**`trees differ` wobbles by design.** `run_tests.sh` deliberately does NOT set
`SWIFT_DETERMINISTIC_HASHING` (see the comment at the top of the script): a non-deterministic hash
seed is a cheap fuzzer for order-dependence. Consequence: the `trees differ` count moves between runs
(observed 1614–1630 in one session) and a handful of labels FLAP — `testForwardSlashRegex71#1`, `#78`,
`testIdentifiers10#1`, `testNonisolatedSpecifier#12` appeared as "fixed" in one run and "broken" in
the next.

Pinning the seed narrows this but does NOT close it — **corrected Sep 2 2026**, see
"AST converter work" below for the measurements. Two consecutive pinned PARALLEL runs of
identical code still differed by 2 labels; only adding `-parallel-testing-enabled NO` gave
byte-identical label sets. The earlier "exactly reproducible" reading came from a single
matching pair, which the wider sample did not hold up.
```
TEST_RUNNER_SWIFT_DETERMINISTIC_HASHING=1 xcodebuild test -scheme Advent \
  -destination 'platform=macOS,arch=arm64' -parallel-testing-enabled NO …
```
So:
- Never read a single-run tree diff as signal — only large moves, or a pinned-seed A/B.
- `accept` and `ambiguity` have been 0 across every seed, so those ARE stable invariants.
- The flapping labels are real order-dependence in the Oracle / AST tiling, i.e. the fuzzer working.
  Worth fixing eventually, but they are not regressions.

**Compare reject label SETS, not counts.** The harness count can differ by one from the number of
distinct labels (a log line can be truncated mid-label). `comm -23` on sorted label lists is reliable;
a count delta of ±1 is not.

## Fixture trap: invisible characters

`testIdentifiers6#1` reads as `()` in an editor, a terminal, `grep`, and `sed`. Its actual bytes are
`EF A3 BF 28 29` — **U+F8FF** (the Apple-logo Private Use Area character) followed by `()`. Retyping
such a snippet into a probe or a scratch `.swift` file silently drops the invisible scalar and the
probe then measures a DIFFERENT input. That cost real time: standalone probes and `swiftc -parse` both
said "valid", while the in-process test correctly said invalid, and the contradiction looked like a
harness or toolchain-version bug.

When a fixture and a hand-written probe disagree, print the bytes first:
```swift
print(Array(snippet.source.utf8))
```
A temporary `@Test` inside the suite is the reliable way to observe what the test process actually
sees; filter it with `-only-testing:'AdventTests/<Suite>/<testName>()'` (swift-testing needs the
trailing parentheses, or zero tests run).


## AST converter work (`GenerateSwiftSyntaxAST.swift`)

**Rule comments are copy-paste, never paraphrase.** Every generator bug found so far has
the same root cause: a comment above a `convert*` asserting a grammar rule that isn't what
`Swift.apus` says. `// optionalType = type "?" .` versus the real
`optionalType = simpleType >s< optionalMark .` produced a silent `MissingType` for `Int?`;
`// postfixExpression = primaryExpression postfixOperation* .` describes a rule that does not
exist. `find(name:)` deliberately digs through brackets (OPT/DO/KLN/POS) but NOT through
non-matching nonterminals, so an inaccurate rule comment translates directly into a silent
`MissingX`. Grep the grammar before writing or trusting one.

**A fallback must say which kind it is.** `SwiftSyntaxGenerator.diagnostics` records every
site where the converter gave up, tagged `.unhandled` (construct not implemented yet — the
phase work queue) or `.lookupFailed` (a rule we CLAIM to handle didn't yield its expected
child — a bug). Without the split, a `MissingType` means either "not yet" or "wrong", and the
~1617 `trees differ` labels can only be triaged by eyeball. `adventGeneratorDiagnostics(snippet)`
exposes the list to tests; `treesMatch` failures print it under `--- converter fallbacks ---`.

**Phase suites must be green, unlike the extracted corpus.** `Phase1TreeTests` asserts three
things per source: Advent accepts, trees match EXACTLY, and the converter reports NO fallbacks.
A red row there is a regression, not frontier movement.

**A reproducible tree-diff A/B needs pinned seed AND serial execution.** Measured Sep 2 2026,
two consecutive runs each, identical code:

| configuration | run-to-run delta |
|---|---|
| `SWIFT_DETERMINISTIC_HASHING=1` (no `TEST_RUNNER_` prefix) | not pinned at all — the variable never reaches the test process |
| `TEST_RUNNER_SWIFT_DETERMINISTIC_HASHING=1`, parallel | **±2 labels** — pinning the seed is NOT sufficient |
| `TEST_RUNNER_SWIFT_DETERMINISTIC_HASHING=1 -parallel-testing-enabled NO` | **identical label sets** |

The residual parallel noise is the order-dependence in the Oracle / AST tiling noted above: with
the suites no longer `.serialized`, thread interleaving varies even with the hash seed fixed. The
flapping labels are not a fixed set (`testOptional1#1` and `testTypeExpr10#4` flapped in one pair,
neither of which is in the previously-recorded flap list).

So the only trustworthy A/B is:
```
TEST_RUNNER_SWIFT_DETERMINISTIC_HASHING=1 xcodebuild test -project Advent.xcodeproj \
  -scheme Advent -destination 'platform=macOS,arch=arm64' -parallel-testing-enabled NO
grep -o "Trees differ for '[^']*'" /tmp/run.log | sort -u > /tmp/after.txt
comm -13 /tmp/before.txt /tmp/after.txt   # newly broken
comm -23 /tmp/before.txt /tmp/after.txt   # newly fixed
```
Roughly 90s per serial run — cheaper than the parallel run it replaces, so there is no reason
to accept the noisy version.

**Get the "before" side from a worktree, not a stash.** Other agents may be working in the
repo; `git worktree add /tmp/advent-head HEAD --detach`, run there, then
`git worktree remove --force`. On Sep 2 2026 a post-change count was initially compared against a
number recalled from a previous session rather than a run against HEAD. It happened to land
inside the recorded band — luck, not evidence. Redone properly, the same change measured
1610 → 1607 with zero newly-broken labels.

### Tooling facts for this work

- **`RunCodeSnippet` does not work in this project at all.** The Advent target builds `-O` and
  previews require `-Onone` ("Not built with -Onone"). Do not reach for it to probe converter
  behaviour — add a focused `@Test` instead.
- Inner loop is `xcodebuild test -only-testing:AdventTests/<Suite>` — roughly 10s for a focused
  suite, ~4 minutes for the whole of AdventTests.
- Parallel test output interleaves. Redirect to a log and grep it; line numbers shift between
  runs, so never `sed -n '<range>p'` against a freshly re-run invocation.

## Sleep, not flakiness — diagnosing a "hung" run

A run that exceeds its timeout is almost always the LAPTOP SLEEPING, not a hang, a regression or
build contention. Diagnosed Sep 7 2026 after repeatedly misattributing it.

The two clocks in the log disagree in a way only suspension produces:

```
$ grep -o "IDETestOperationsObserverDebug: [0-9.]* elapsed" run.log
IDETestOperationsObserverDebug: 465.547 elapsed        # xcodebuild: WALL clock
$ grep -o "Test run with .* seconds" run.log
Test run with 178 tests in 70 suites failed after 67.896 seconds   # swift-testing: does NOT
                                                                   # advance while suspended
```

465 − 68 ≈ 400s unaccounted for. To confirm, find the gaps between timestamped log lines:

```sh
python3 - <<'EOF'
import re, datetime
pat = re.compile(r'^(20\d\d-\d\d-\d\d \d\d:\d\d:\d\d\.\d+)')
prev = None
for line in open('run.log', encoding='utf-8', errors='replace'):
    m = pat.match(line)
    if not m: continue
    t = datetime.datetime.strptime(m.group(1)[:26].split('+')[0], '%Y-%m-%d %H:%M:%S.%f')
    if prev and (t - prev).total_seconds() > 3:
        print(round((t - prev).total_seconds(), 1), 's before:', line[:100])
    prev = t
EOF
```

A sleep shows up as ONE large gap, and the tests either side of it are unrelated and trivial —
in the diagnosed case a 388s gap fell between `final-class` and `public-final`, two Phase4
one-liners that take milliseconds. A REAL hang looks different: the gap lands inside a single
expensive test, and the reported swift-testing duration grows to match the wall clock.

`tools/run_tests.sh` now wraps `xcodebuild` in `caffeinate -i` to prevent this. When invoking
`xcodebuild` by hand, do the same:

```sh
caffeinate -i xcodebuild test-without-building -project Advent.xcodeproj -scheme Advent \
    -destination "platform=macOS,arch=arm64" -parallel-testing-enabled NO
```

**Never read a timeout as a regression without checking the two clocks first.** The tests took
~68s on every one of ~40 consecutive runs, including every run that appeared to fail.

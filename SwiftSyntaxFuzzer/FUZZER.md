# Advent Fuzzer

This folder contains a first Advent-vs-swift-syntax differential fuzzer kept outside the Advent source tree.

## Shape

- `Sources/AdventFuzzRunner/main.swift` is the long-running supervisor.
- `Sources/AdventProbe/ProbeMain.swift` is a one-input probe compiled together with Advent source files.
- `bin/build.sh` builds the Advent target with Xcode, then compiles:
  - `.build/advent-fuzz-probe`
  - `.build/advent-fuzz-runner`
- `runs/<timestamp>/events.jsonl` records probe outcomes.
- `runs/<timestamp>/artifacts/*.json` stores selected non-matching inputs, probe output, stderr, and tree dumps.

By default, the runner keeps one persistent probe process alive. The probe loads the immutable Swift grammar once, then creates a fresh `MessageParser` for every input, matching the SwiftSyntax test-suite strategy. Use `--isolated-probe` to return to the older one-process-per-input mode when debugging crashes or timeout containment.

## Build

From repository root:

```sh
AdventFuzzer/bin/build.sh
```

By default, the script asks Xcode to build the Advent scheme into fuzzer-local DerivedData under `AdventFuzzer/.build/DerivedData`, then compiles the probe and runner against those products.

Inside this agent/Xcode environment, the reliable path is to build Advent with Xcode first, then rebuild only the fuzzer binaries:

```sh
ADVENT_FUZZER_SKIP_XCODEBUILD=1 AdventFuzzer/bin/build.sh
```

The fuzzer keeps Swift/Clang module-cache output under `AdventFuzzer/.build/module-cache`. The build script discovers usable Release products automatically; if needed, override discovery with `ADVENT_FUZZER_PRODUCTS=/path/to/Build/Products/Release`. Other escape hatches are `ADVENT_FUZZER_DERIVED_DATA`, `ADVENT_FUZZER_SOURCE_PACKAGES`, `ADVENT_FUZZER_SWIFT_SYNTAX_SHIMS`, and `ADVENT_FUZZER_XCODE_LOG`.

## Run

```sh
AdventFuzzer/.build/advent-fuzz-runner --iterations 1000 --timeout 10
```

Useful options:

```sh
AdventFuzzer/.build/advent-fuzz-runner \
  --iterations 100000 \
  --timeout 10 \
  --seed 0xA0C2021 \
  --output AdventFuzzer/runs \
  --seed-corpus AdventFuzzer/seeds/known-problems.txt \
  --heartbeat-every 25 \
  --max-artifacts 10000 \
  --max-artifact-mb 1024

# Crash-isolating fallback:
AdventFuzzer/.build/advent-fuzz-runner \
  --iterations 1000 \
  --timeout 10 \
  --isolated-probe
```

For quieter long runs:

```sh
AdventFuzzer/.build/advent-fuzz-runner --iterations 100000 --quiet-passes
```

By default, full artifacts are written for Advent correctness statuses, tree differences, residual ambiguity, timeouts, crashes, and harness errors. Compiler-only telemetry statuses are still counted and written to `events.jsonl`, but they do not write full artifacts unless requested. Use `--all-artifacts` or an explicit `--artifact-statuses` list when you want those telemetry artifacts too.

For accept/reject-focused harvesting, keep full artifacts for correctness statuses and let tree differences remain as event telemetry:

```sh
AdventFuzzer/.build/advent-fuzz-runner \
  --iterations 100000 \
  --timeout 15 \
  --quiet-passes \
  --artifact-statuses advent-underaccept,advent-overaccept,timeout,crash,invalid-probe-output,probe-error \
  --max-artifacts-per-status 200 \
  --dedupe-by-signal
```

In this Xcode agent environment, the reliable long-run launch is a direct attached TTY run. Detached
`nohup`, `screen`, and piped `tee` launches have been temperamental here and should not be used as the
canonical path.

```sh
AdventFuzzer/.build/advent-fuzz-runner \
  --iterations 1000000 \
  --timeout 15 \
  --seed 0xA0C2021 \
  --heartbeat-every 250 \
  --quiet-passes \
  --max-artifacts-per-status 500 \
  --dedupe-by-signal
```

During a run, inspect:

- `heartbeat.json` for counts and rate
- `state.json` for next index and stop status
- `events.jsonl` for event records
- `artifacts/` for unique non-`same` cases

## Outcome Classes

For status classification, Advent accepts only when the post-Oracle `DerivationBuilder` produces a tree.
The JSON `adventMatched` field is raw pre-Oracle root-yield telemetry.

- `same`: swift-syntax and Advent agree for the selected checks.
- `advent-underaccept`: swift-syntax and the compiler accept, but Advent does not produce a full parse.
- `advent-overaccept`: swift-syntax has an error, but Advent produces a post-Oracle tree.
- `compiler-rejects-swiftsyntax-accepts`: swift-syntax accepts and Advent rejects, but `swiftc -parse` rejects too. Treat this as compiler-wins, not an Advent underacceptance.
- `compiler-typecheck-rejects-swiftsyntax-accepts`: swift-syntax and `swiftc -parse` accept and Advent rejects, but `swiftc -typecheck` rejects. Treat this as compiler-wins telemetry: Advent agrees with the compiler, while swift-syntax is more accepting.
- `residual-ambiguity`: Advent produces a post-Oracle tree, but the post-Oracle derivation still has ambiguity.
- `advent-no-generated-tree`: Advent produces a post-Oracle tree, but the SwiftSyntax generator did not produce a source-file tree.
- `tree-difference`: both sides accept, but normalized SwiftSyntax dumps differ.
- `timeout`: the probe exceeded the per-input timeout and was killed.
- `crash` / `invalid-probe-output` / `probe-error`: harness or Advent process failure; keep the artifact.

## First Generator

The current generator is deliberately simple. It samples Swift fragments around the choice points that have historically mattered in Advent:

- generic angle brackets vs operators
- `?` / `!` token boundaries
- tight `try`, `try?`, and `try!` token boundaries
- cast operators followed by optional, force, generic, or prefix-operator-looking types
- trailing closures
- regex literals and regex-vs-division boundaries
- conditional compilation expressions
- dotted keyword case/member names
- key-path component and member-name boundaries
- string interpolation around regex, casts, and `try`
- closure labels and call/trailing-closure boundaries
- optional, tuple, and nested binding patterns
- attributes and generic declarations
- generic `where` clauses
- extension type grammar edges
- ownership modifiers and `consume` / `copy` expressions
- effectful accessors and effectful function types
- macro and pound-directive boundaries
- modifier stacks such as `public private(set)` and `nonisolated(unsafe)`
- collection type spelling around arrays, dictionaries, tuples, and function types
- member-list separators across structs, conditionals, attributes, subscripts, and initializers
- protocol requirements, operator declarations, async/throwing initializers, and effectful subscripts
- nested `#if` / `#sourceLocation` / macro-ish directive combinations
- regex bodies with interior spaces and tabs
- dense cast / `try` / operator clusters
- larger optional-case and cast-pattern matrices
- `#if` in member and expression-leading-dot contexts
- key-path optional, force, subscript, and dynamic-member components
- slash-heavy regex, ternary, and division boundaries
- wider member-list containers, including class, actor, extension, protocol, and enum bodies
- composed existential, opaque, pack, isolated, sending, and effectful function types
- contextual-keyword declaration/member/call-label positions
- import declarations with attributes, kinds, and operators
- closure/result-builder-ish bodies with conditional compilation
- statement control-flow edges around typed throws, availability, pattern conditions, and `for try await`
- macro declaration, attribute, and source-location directive boundaries
- labeled seed-corpus snippets, both raw and structurally mutated

It then embeds those fragments in small source-file templates. This is the LegoFuzz/Grammarinator idea in miniature: generate reusable structured fragments, compose them cheaply, and keep the expensive oracle deterministic.

## Seed Corpus

`AdventFuzzer/seeds/known-problems.txt` is loaded by default. Each seed starts with a label line:

```text
### short-label
swift source goes here
```

The runner mixes these seeds into the generated stream in four forms:

- raw replay,
- structural mutation,
- wrapping inside a function, type, `do`, or `#if`,
- crossover with another seed.

Use `--seed-corpus PATH` to point at a different corpus. If the file is missing, the runner prints a warning and disables only the seed-corpus lane.

## Triage

For any artifact:

1. Read `source`.
2. Check `probe.status`.
3. For `tree-difference`, compare `probe.referenceDump` and `probe.adventDump`.
4. For `residual-ambiguity`, inspect `probe.residualAmbiguities`.
5. For accept/reject mismatches, minimize the `source` manually or with a later reducer.

The artifact filename includes the iteration, status, and stable source hash.

Each non-`same` event includes `signalHash` and `signalSummary`. The signal is a normalized failure-shape fingerprint: tree differences use the first normalized dump divergence, accept/reject mismatches use normalized SwiftSyntax tree shape plus compiler verdicts, and harness failures use the compact diagnostic or generator family. Use this to group many surface variants of the same underlying problem.

The runner deduplicates artifact files by `(status, sourceHash)` by default. Duplicate events still appear in `events.jsonl` with `note: "duplicate-artifact"`, but they do not write another full artifact. Add `--dedupe-by-signal` to deduplicate artifact writes by `(status, signalHash)` instead; this is usually better for long campaigns once exact source duplicates are rare. Artifact writes also stop after `--max-artifacts`, `--max-artifact-mb`, `--max-artifacts-per-status`, or the artifact-status filter. The default filter skips full artifacts for `compiler-rejects-swiftsyntax-accepts` and `compiler-typecheck-rejects-swiftsyntax-accepts`, because those are compiler-wins telemetry rather than Advent correctness failures.

`SIGINT` and `SIGTERM` request a graceful stop between probes. The current probe is allowed to finish or hit its timeout, then `summary.txt`, `heartbeat.json`, and `state.json` are flushed.

In persistent mode, each request is a JSON line sent to the probe and each response is one JSON line back. If a request times out, the runner kills that persistent child, records the timeout, and starts a fresh child for the next input. If probe launching or probe output becomes harness-broken repeatedly, for example empty stdout from otherwise successful probes or runner-side file descriptor failures, the runner stops after a short consecutive-failure threshold instead of flooding artifacts.

## Next Work

- Add a reducer that preserves the same status.
- Add a seed-corpus mode that mutates existing SwiftSyntax/Advent snippets.
- Persist interesting passing inputs that increase Advent metrics such as `yieldCount` or `oraclePruned`.
- Add a tree/fragments corpus and structure-aware crossover.
- Add a worker pool of persistent probes to multiply the single-probe speedup toward the 100x target.

## Smoke Result

Initial smoke run:

```sh
AdventFuzzer/.build/advent-fuzz-runner --iterations 5 --timeout 15
```

Recent smoke run:

```sh
AdventFuzzer/.build/advent-fuzz-runner --iterations 8 --timeout 15 --quiet-passes --output /tmp/advent-fuzzer-smoke
```

Result after compiler parse and type-check tie-breaks: 7 `same`, 1 `compiler-typecheck-rejects-swiftsyntax-accepts`.

The telemetry artifact was:

```swift
struct Fuzz<T: any P> { var value: T }
```

That confirms the runner can persist divergences for offline triage without counting compiler-rejected generic constraints as Advent underacceptance bugs.

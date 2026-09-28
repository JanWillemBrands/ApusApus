# ApusApus SwiftSyntax Fuzzer

Differential fuzzer for `Swift.apus` against `swiftc -parse`. The fuzzer generates or mutates
Swift source, sends each input to `advent-fuzz-probe`, and records compiler/ApusApus mismatches,
residual ambiguity, tree-conversion gaps, telemetry, and novelty. SwiftSyntax is an instrument for
reference trees and corpus material; it is not the validity oracle.

## Components

- `Sources/AdventProbe/ProbeMain.swift`: one-input probe. It loads `Swift.apus`, compares
  `swiftc -parse` and ApusApus, and emits one JSON response.
- `Sources/AdventFuzzRunner/main.swift`: run supervisor, generator, artifact writer, telemetry,
  novelty retention, and persistent-probe driver.
- `Sources/AdventFuzzRunner/Widening.swift`: token mutator, wide real-source contexts, and artifact
  reducer.
- `bin/build.sh`: builds `.build/advent-fuzz-probe` and `.build/advent-fuzz-runner`.
- `bin/run-night.sh`: launches a multi-worker campaign.
- `tools/cluster_ambiguities.py`: clusters residual-ambiguity artifacts by grammar signature.
- `tools/replay_fuzz_sources.py`: replays saved artifacts or telemetry after grammar changes.

## Build

From the repository root:

```sh
SwiftSyntaxFuzzer/bin/build.sh
```

In this Xcode agent environment, build ApusApus with Xcode first, then rebuild only the fuzzer
binaries:

```sh
ADVENT_FUZZER_SKIP_XCODEBUILD=1 SwiftSyntaxFuzzer/bin/build.sh
```

If the full build is killed by resource pressure while compiling the probe, validate runner-only
changes with:

```sh
xcrun swiftc -swift-version 5 -O -parse-as-library \
  -module-cache-path SwiftSyntaxFuzzer/.build/module-cache \
  SwiftSyntaxFuzzer/Sources/AdventFuzzRunner/Widening.swift \
  SwiftSyntaxFuzzer/Sources/AdventFuzzRunner/main.swift \
  -o /tmp/advent-fuzz-runner-check
```

## Run

Single-worker smoke:

```sh
SwiftSyntaxFuzzer/.build/advent-fuzz-runner \
  --iterations 2000 \
  --timeout 10 \
  --quiet-passes \
  --dedupe-by-signal \
  --reduce-artifacts 30 \
  --output /tmp/apus-fuzzer-smoke
```

Full-core campaign in this environment:

```sh
SWIFT_DETERMINISTIC_HASHING=1 \
FOREGROUND=1 \
WORKERS=10 \
ITERATIONS=1000000 \
TIMEOUT=10 \
HEARTBEAT_EVERY=250 \
MAX_ARTIFACTS_PER_STATUS=500 \
DEDUPE_BY_SIGNAL=1 \
REDUCE_ARTIFACTS=50 \
SwiftSyntaxFuzzer/bin/run-night.sh
```

Use `FOREGROUND=1` here. Detached `nohup` workers have been unreliable in this managed Xcode
environment.

## Important Runner Options

- `--wide-corpus PATHS`: comma-separated labeled corpora for the wide real-source lanes.
  Default: `SwiftSyntaxFuzzer/seeds/swift-syntax-corpus.txt,SwiftSyntaxFuzzer/seeds/real-source.txt`.
  Pass `--wide-corpus ""` to disable.
- `--wide-percent N`: percentage of generated inputs drawn from wide real-code lanes. Default: `50`.
- `--seed-corpus PATH`: labeled known-problem corpus. Default:
  `SwiftSyntaxFuzzer/seeds/known-problems.txt`.
- `--interesting-corpus PATHS`: comma-separated `interesting.jsonl` files from earlier runs. These
  passing sources are sampled, mutated, wrapped, and crossed over as a coverage corpus.
- `--interesting-percent N`: percentage of generated inputs drawn from `--interesting-corpus` when
  provided. Default: `15`.
- `--dedupe-by-signal`: deduplicate artifacts by failure shape instead of exact source hash.
- `--reduce-artifacts N`: run up to `N` reducer probes before writing each reducible artifact.
- `--interesting-passes` / `--no-interesting-passes`: retain passing sources that add cheap novelty.
  Enabled by default.
- `--max-interesting-passes N`: cap retained passing sources. Default: `2000`.
- `--artifact-statuses LIST`: restrict full artifact writes. Counts and events are still recorded.
- `--all-artifacts`: write full artifacts for every non-`same` status.

## Outputs

Each run directory contains:

- `events.jsonl`: event records for non-`same` inputs, plus passing inputs unless `--quiet-passes`.
- `telemetry.jsonl`: compact source records for status-filtered events, usually compiler-only
  telemetry.
- `interesting.jsonl`: passing sources retained because they reached new novelty: generator lane,
  bucketed probe metric, or post-Oracle grammar alternate coverage.
- `artifacts/*.json`: full artifacts for selected non-`same` statuses.
- `heartbeat.json`: current counts, rate, artifact bytes, and freshness.
- `state.json`: resumable run state information.
- `summary.txt`: final status counts plus interesting-pass and reduced-duplicate counts.

Artifact JSON includes:

- `source`: reduced source when reduction succeeded, otherwise original generated source.
- `originalSource`: unreduced source when `source` was reduced.
- `reductionProbes`: reducer probe count when applicable.
- `probe`: decoded probe output, including dumps, metrics, residual ambiguity fingerprints, and
  post-Oracle grammar coverage fingerprints.

Reduction preserves the compiler-first status. For reduced artifacts, `source` should keep the same
compiler parse result and ApusApus failure class as `originalSource`.

## Outcome Classes

- `same`: `swiftc -parse` and ApusApus agree on syntax acceptance.
- `advent-underaccept`: `swiftc -parse` accepts, but ApusApus does not build a tree.
- `advent-overaccept`: `swiftc -parse` rejects, but ApusApus builds a tree.
- `residual-ambiguity`: compiler and ApusApus accept, but the post-Oracle derivation is still
  ambiguous.
- `tree-difference`: compiler, ApusApus, and SwiftSyntax accept, but normalized tree dumps differ.
- `advent-no-generated-tree`: compiler and ApusApus accept, but the SwiftSyntax generator does not.
- `timeout`, `crash`, `invalid-probe-output`, `probe-error`: harness or probe failures.

`swiftc -parse` is the validity oracle. SwiftSyntax parse results are reference-tree telemetry only.

## Generator Lanes

Current lanes are:

- Curated fragment lanes for known sharp edges: generics, regex, key paths, conditional
  compilation, attributes, interpolation, member lists, declarations, statements, operators, and
  contextual keywords.
- Known-problem seed lanes: raw replay, mutation, wrapping, structural splicing, and crossover.
- Wide real-source lanes: snippets from swift-syntax and real-source corpora, optionally token
  mutated, then placed in source, function, member, closure, interpolation, and `#if` contexts.
- Interesting corpus lane: retained passing sources from previous `interesting.jsonl` files,
  replayed, mutated, context-wrapped, `#if`-wrapped, and crossed over.
- Interesting-pass retention: passing inputs that hit a new generator, bucketed probe metric, or
  post-Oracle grammar alternate are written to `interesting.jsonl`.

Wide lanes are intentionally approximate. They are expected to produce many `same` rejections while
occasionally reaching parser states that curated local fragments miss.

## Triage Workflow

Cluster residual ambiguity first:

```sh
tools/cluster_ambiguities.py SwiftSyntaxFuzzer/runs/worker-*/<run>/artifacts/*.json --top 30
```

Replay after a grammar or converter change:

```sh
tools/replay_fuzz_sources.py --only-changed SwiftSyntaxFuzzer/runs/<run>/artifacts/*.json
tools/replay_fuzz_sources.py SwiftSyntaxFuzzer/runs/<run>/telemetry.jsonl
```

For a long run:

1. Read `summary.txt`.
2. Group artifacts by status and signal.
3. For `residual-ambiguity`, use `cluster_ambiguities.py`.
4. For reduced artifacts, inspect `originalSource` before deciding compiler validity.
5. Replay fixed artifacts with the rebuilt probe.
6. Run a bounded smoke with `--dedupe-by-signal --reduce-artifacts`.

## Phased Roadmap

Phase 1 is implemented:

- full-core worker launcher,
- signal dedupe,
- bounded artifact reduction,
- residual-ambiguity clustering,
- wide real-source lanes,
- cheap novelty retention in `interesting.jsonl`.

Phase 2 is partially implemented:

- record grammar alternates reached by final derivations,

Phase 2 should next make novelty broader:

- replace name/body alternate fingerprints with explicit stable alternate IDs,
- record SwiftSyntax node kinds and converter fallback diagnostics,
- retain sources that cover a new node kind, Oracle prune kind, or converter diagnostic.

Phase 3 should add structure-aware mutation:

- parse retained sources into SwiftSyntax trees,
- delete, duplicate, swap, and wrap same-kind nodes,
- splice expressions/types/patterns only into compatible contexts,
- use `interesting.jsonl` as the evolving corpus.

Phase 4 should add grammar-directed generation:

- generate from `Swift.apus` with depth limits,
- bias alternatives by inverse hit count,
- validate generated sources against swift-syntax,
- feed accepted or novel rejected sources back into the retained corpus.

Phase 5 should run separate campaigns for converter parity:

- artifact and signal policy optimized for `tree-difference`,
- passing-source retention based on new SwiftSyntax dump shapes,
- tree-difference clustering by first normalized dump divergence.

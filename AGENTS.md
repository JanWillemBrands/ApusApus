## Default Working Mode

- This project/repository originated as Advent / AOC2021.  It is now called ApusApus, but references to the old names may persist.
- Use fast mode by default.
- Keep file reads minimal and targeted.
- Make only targeted edits for the requested task.
- Always run full builds and full test suites, unless it's very low risk to run a limited one.
- If any command runs longer than 120 seconds, stop and replan with a lighter approach.

## Tool Selection (Critical)

- In this Xcode environment, prefer `mcp__xcode-tools__*` commands for project file reads/edits/build/diagnostics.
- Use shell commands only when Xcode tools cannot do the task; keep shell commands short and narrowly scoped.
- Avoid long chained shell edits; prefer small atomic edits to reduce interruption risk.
- If a shell command is blocked/rejected, report it immediately and switch to an Xcode-tools path when possible.

## Collaboration Preferences (Learned)

- Ask before exploring newly added directories or broad workspace areas (example: `grammars/`).
- When discussing grammar details, verify claims against the local reference grammar file before finalizing conclusions.
- If the user asks for design discussion only, do not modify code; produce a concrete, resumable design note instead.
- For regex performance work, preserve longest-token correctness first: alternation is first-successful-branch, not automatic longest-branch.
- For mixed ASCII/Unicode identifiers, prefer scanner-level ASCII fast paths; if regex alternation is used, guard the ASCII branch with a negative lookahead so it cannot steal shorter matches (e.g. before trailing Unicode-continue characters).
- For feature activation driven by grammar syntax (e.g. layout injection), distinguish declaration from use: terminal existence in `symbolToID` is not enough when the symbol can appear quoted in the meta-grammar.
- Prefer parser-level `usesX` flags when activation depends on unquoted grammar constructs actually used by a specific grammar.
- For broad replacement requests ("all source files, documentation, and grammars"), scan and verify the whole repository scope, not only files currently visible in the Xcode project navigator.
- After bulk replacements, run a full-repo verification grep and report any remaining out-of-scope matches explicitly.
- Treat pasted project structure as session context; do not require repeated full listings for follow-up edits unless scope actually changes.

## Merged From codex.md and claude.md

- If a required tool is missing (example: `pdftotext`), ask the user first before installing it, and ask before switching to a fallback workflow.
- Keep users informed during long operations with periodic status updates.
- Prefer diagnosing root causes over patching symptoms; avoid adding flags unless required.
- Keep structural reorganization separate from parser behavior changes.

### TODO Source Of Truth

- Read and update markdown TODOs only in `TODO.md`.
- Do not duplicate TODO lists across assistant notes.

### Project Context (GLL/APUS)

- Project implements a GLL parser with CRF/BSR-related structures.
- `ApusParser` parses .apus grammars into `GrammarNode` graphs.
- `MessageParser` runs GLL descriptor processing and parse forest and BSR construction.
- Scanner performance and correctness are critical; preserve longest-token correctness in regex/scanner work.
- Prefer parser-owned mutable state over shared static state for reentrancy/concurrency safety.

### Testing & Execution Workflow

See `TESTING.md` for the full approach. Non-negotiable rules distilled from prior sessions:

- **Source of truth for "does Advent accept X?"** is the SwiftSyntax Swift Testing
  suites (`AdventTests/SwiftSyntax*.swift`, `adventParse`), NOT the `^^^`-messages
  path in `Swift.apus` — the two disagree on identical input.
- **Split test results by `@Test`.** Only `Advent accepts` and `no residual ambiguity`
  failures are correctness signals; `trees match` is an aspirational frontier (~1660
  Translated cases fail it by design — not regressions). "Passes as a message but fails
  as a test" = acceptance passes, `treesMatch` fails.
- **Always set `SWIFT_DETERMINISTIC_HASHING=1`** on test runs — the grammar is loaded
  once and cached/shared, so any load-time hash-order dependence becomes a per-process
  flake. Pin flakes with it, then diff descriptors/yields PASS vs FAIL.
- **Always build before running a DerivedData binary** (stale products persist);
  `main.swift`/CLI diagnostics go to OSLog (`com.magenta.apusParser`), not stdout — an
  empty stdout with exit 1 is usually a grammar-load failure.
- **Probe swift-syntax truth with `Parser.parse(source:).hasError`**, not `swiftc -parse`
  (they diverge on trivia).
- **MCP `RunSomeTests` smart-reruns** only previously-failing args after the first call
  (and a `.apus` edit isn't a "changed input"); use `xcodebuild` directly for true
  full-parameter counts.
- **Fix by root cause, not per-test**; prefer structural `.apus` fixes over
  `@prefer`/oracle hacks; re-harvest ambiguity + run the affected suite after each change.


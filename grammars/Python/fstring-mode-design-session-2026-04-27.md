# F-String + Scanner Mode Design Notes (Session 2026-04-27)

## Goal

Find an elegant, general scanner-mode model for Apus that goes beyond Swift and works for Python f-strings plus other popular language constructs (C++, Rust, JS templates, etc.), while preserving the pre-scan + GLL architecture.

## What We Confirmed

- Python grammar in this repo currently marks f-strings as not covered (`Python.apus` comment).
- Python formal grammar reference (`Python3.14.4.txt`) uses replacement fields that end with plain `}`.
- There is no formal `f}"` closing construct; `f` is a string literal prefix.
- Current scanner model has:
  - stack-based modes,
  - one mode record per terminal,
  - push/check/pop behavior (`>>>`, `===`, `<<<`),
  - eligibility gate by current mode.
- Current Apus parser reads only one optional mode annotation after terminal definitions.

## Problem We Are Solving

Support constructs that have **structure inside a lexical token** (interpolation/raw delimiter constructs), while keeping pre-scan + GLL architecture.

Primary target: Python f-strings.  
Secondary/general target: C++ raw strings, Rust raw strings, Swift `#`-delimited strings, JS template interpolation.

## Key Design Decisions Reached

### 1. Keep Only Three Operators

- Keep `===`, `>>>`, `<<<`.
- Remove `!!!`.
- Allow **lists** of annotations per terminal.
- Execute annotation lists **atomically** (all-or-nothing).
- Failure should be **silent candidate rejection** (no side effects applied).

Equivalent of mode-replace becomes ordered atomic sequence:

- `<<< "fExpr" >>> "fSpec"`

instead of a dedicated `!!!`.

### 2. Dynamic Mode Values Are Required

Static mode names (`"inside-bracket"`) are insufficient for constructs like C++ raw strings where the delimiter is runtime text.

Agreed syntax direction:

- annotation operands are either:
  - mode literal (`"inside-bracket"`), or
  - mode identifier (`tag`).
- mode identifier must correspond to a **named capture** in the immediately preceding token regex.

Conceptual shape:

- `rawHead - /R"(?<tag>[A-Za-z0-9_]*)\(/ . >>> tag`
- `rawTail - /\)(?<tag>[A-Za-z0-9_]*)"/ . <<< tag`

### 3. Multiple Behaviors for Same Token Form

Same token text may trigger different actions depending on top-of-stack mode.

Example:

- `}` can close `fExpr` or `fSpec`, depending on current mode.

## Scanner-Level Constraints and Feasibility

With current scanner architecture, full declarative support requires:

1. Parser support for multiple annotations per terminal (ordered list).
2. Scanner support for atomic annotation transaction per candidate.
3. Dynamic binding source from matched token data (named captures from regex re-match).

Without those, fallback is scanner-specialized handling for specific token classes (e.g. C++ raw string opener/closer logic).

## Major Discussion: Where Bindings Live

This was a key unresolved design decision.

### Position A: Global Dictionary (simplicity/perf oriented)

- Keep mode stack logic out of the hot path as much as possible.
- Re-match only when annotations exist.
- If capture names are distinct by convention (`rawTag`, `fmtTag`, etc.), many collisions are avoided.

### Position B: Stack-Scoped Bindings (safety/correctness oriented)

- Store identifier bindings in mode stack scope (frame-local or equivalent).
- Nesting naturally restores previous values on pop.
- Prevents leakage during silent-fail candidate trials.

### Synthesis

- A plain global dictionary is only safe with explicit scoping semantics:
  - per-identifier stacks, or
  - transactional rollback per candidate.
- Since scanner already has a stack, stack-scoped binding is the least surprising correctness model.

## Named Regex Capture + Annotation Matching

Agreed addition to the model:

- For identifier operands (`tag`), scanner must resolve value from named capture of the preceding regex token.
- Resolution mechanism discussed:
  - re-match previous `token.image` against `grammar.tokens[token.kind]` to recover named capture values.
- This keeps Apus syntax clean (no `@1`-style capture-index API in grammar text).

## Example Constructs Discussed

### Python f-string format transition

For `f"{value:{width}.{prec}f}"`:

- `{` opens expression mode.
- `:` transitions expression -> format-spec mode.
- nested `{width}` and `{prec}` temporarily open expression mode again.
- final `}` closes format-spec mode.

Why multi-annotation atomicity matters:

- transitions may require ordered checks/pops/pushes;
- if one step fails, the entire token candidate must fail silently.

### C++ raw string

`R"tag( ... )tag"`

- requires runtime delimiter capture (`tag`) on open,
- requires matching same captured value on close.

## Current Limitations

1. **ApusParser reads only one mode annotation per terminal.** The `if/else-if` chain at ApusParser.swift:216–239 consumes a single `>>>`, `===`, or `<<<` and returns. Multi-annotation terminals (e.g., `=== "mode" <<<` sequences) require a loop.
2. **`<<<` always requires an operand.** `ScanModeTest.apus` lines 14–15 and 37–39 use bare `<<<` without a mode name — these are outdated and will cause a parse error. All three operators take a literal operand; `<<<` pops and verifies it matches the stack top.
3. **`Mode` struct is flat.** It holds one `modeName` and three booleans. The proposed ordered action lists require replacing it with `[ModeAction]` and migrating the `TokenPattern` tuple to a struct.
4. **No dynamic (capture-bound) mode operands.** All operands are currently string literals. No mechanism to bind regex capture groups to mode names.
5. **Mode annotations don't interact with layout injection.** `LayoutTokenInjection.swift` is unaware of scanner modes; f-string content inside a Python source could generate spurious indent/dedent tokens.

## Stack Trace Walkthroughs

### Python f-string: `f"{value:{width}.{prec}f}"`

Token stream after scanning (simplified):

| # | Token           | Action              | Stack after         |
|---|-----------------|----------------------|---------------------|
| 1 | `f"`            | `>>> "fExpr"`        | `[fExpr]`           |
| 2 | `{`             | (grammar-level)      | `[fExpr]`           |
| 3 | `value`         | —                    | `[fExpr]`           |
| 4 | `:`             | `<<< "fExpr" >>> "fSpec"` | `[fSpec]`      |
| 5 | `{`             | `>>> "fExpr"`        | `[fSpec, fExpr]`    |
| 6 | `width`         | —                    | `[fSpec, fExpr]`    |
| 7 | `}`             | `<<< "fExpr"`        | `[fSpec]`           |
| 8 | `.`             | —                    | `[fSpec]`           |
| 9 | `{`             | `>>> "fExpr"`        | `[fSpec, fExpr]`    |
| 10| `prec`          | —                    | `[fSpec, fExpr]`    |
| 11| `}`             | `<<< "fExpr"`        | `[fSpec]`           |
| 12| `f`             | —                    | `[fSpec]`           |
| 13| `}`             | `<<< "fSpec"`        | `[]`                |
| 14| `"`             | (closing)            | `[]`                |

Key observations:
- The `:` token is the tricky one — it must atomically pop `fExpr` and push `fSpec`. If the pop fails (not in `fExpr` mode), the entire candidate is rejected silently.
- `}` is ambiguous: it can close either `fExpr` or `fSpec`. The `<<<` operand disambiguates — the scanner checks the stack top against the operand before popping.
- Nested `{width}` and `{prec}` push/pop `fExpr` on top of `fSpec`, and the stack depth handles nesting correctly.

Nested f-string: `f"{f'{x}'}"`

| # | Token           | Action              | Stack after              |
|---|-----------------|----------------------|--------------------------|
| 1 | `f"`            | `>>> "fExpr"`        | `[fExpr]`                |
| 2 | `f'`            | `>>> "fExpr"`        | `[fExpr, fExpr]`         |
| 3 | `x`             | —                    | `[fExpr, fExpr]`         |
| 4 | `}`             | `<<< "fExpr"`        | `[fExpr]`                |
| 5 | `'`             | (closing inner)      | `[fExpr]`                |
| 6 | `}`             | `<<< "fExpr"`        | `[]`                     |
| 7 | `"`             | (closing outer)      | `[]`                     |

Stack depth alone disambiguates which `}` closes which f-string level.

### C++ raw string: `R"tag(hello world)tag"`

| # | Token           | Action              | Stack after | Bindings       |
|---|-----------------|----------------------|-------------|----------------|
| 1 | `R"tag(`        | regex captures `tag="tag"`, `>>> tag` | `["tag"]` | `tag → "tag"` |
| 2 | `hello world`   | `=== tag`            | `["tag"]`   |                |
| 3 | `)tag"`         | regex captures `tag="tag"`, `<<< tag` | `[]` | cleared |

The `<<<` verifies the captured delimiter matches the stack top. If the raw string used a different delimiter (e.g., `R"delim(...)delim"`), `tag` binds to `"delim"` and the stack holds `"delim"`.

Mismatched close `R"abc(...)xyz"` — the closing regex matches `tag="xyz"`, but `<<< tag` tries to pop `"abc"` and finds `"xyz" ≠ "abc"` → candidate rejected silently.

### C# interpolated string: `$"Hello {name}, you have {count:N0} items"`

C# uses `$"..."` with `{expr}` and `{expr:format}` — structurally identical to Python f-strings.

| # | Token           | Action              | Stack after         |
|---|-----------------|----------------------|---------------------|
| 1 | `$"`            | `>>> "csExpr"`       | `[csExpr]`          |
| 2 | `Hello `        | `=== "csExpr"`       | `[csExpr]`          |
| 3 | `{`             | (grammar-level)      | `[csExpr]`          |
| 4 | `name`          | —                    | `[csExpr]`          |
| 5 | `}`             | —                    | `[csExpr]`          |
| 6 | `, you have `   | `=== "csExpr"`       | `[csExpr]`          |
| 7 | `{`             | (grammar-level)      | `[csExpr]`          |
| 8 | `count`         | —                    | `[csExpr]`          |
| 9 | `:`             | `<<< "csExpr" >>> "csFmt"` | `[csFmt]`    |
| 10| `N0`            | `=== "csFmt"`        | `[csFmt]`           |
| 11| `}`             | `<<< "csFmt"`        | `[]`                |
| 12| ` items"`       | (closing)            | `[]`                |

C# also supports `$@"..."` (verbatim interpolated) and raw `$"""..."""` — the model handles them identically, only the opening/closing terminal regexes differ.

C# nesting: `$"outer {$"inner {x}"}"` works by stacking `csExpr` levels, same mechanism as Python.

## Atomicity: Failure Semantics

An annotation list `[a₁, a₂, ..., aₙ]` executes as a transaction:

1. **Snapshot** the mode stack before evaluating `a₁`.
2. **Evaluate each action in order.** An action fails if:
   - `===` operand ≠ stack top (literal) or resolved binding (identifier).
   - `<<<` operand ≠ stack top, or stack is empty.
   - `>>>` identifier operand has no binding (named capture didn't match).
3. **On any failure:** restore the snapshot. The token candidate is rejected silently — no diagnostics by default.
4. **On success of all actions:** commit the final stack state. Discard the snapshot.

Ordering rules:
- Any permutation of operators is syntactically valid. Semantic validity is determined by the stack state at each step.
- `<<< "X" >>> "Y"` (mode replace) is the canonical pattern — pop then push.
- `>>> "X" === "X"` is technically valid (push then check) but pointless.
- A single `>>>` without any check is valid — it pushes unconditionally.

## Named-Capture Resolution Strategy

For dynamic (identifier) operands, the scanner must resolve the identifier against a named regex capture. Two approaches were evaluated:

**Retain match object for all tokens** — rejected. The scanner processes every token on the hot path. Holding `Regex.Match` objects for all tokens penalizes the common case (no annotations) with allocation/lifetime overhead.

**Selective re-match** — preferred. The scanner re-runs the regex only for tokens whose annotation list contains identifier operands. Since mode annotations are rare (a handful of terminals per grammar), the cost is negligible. Implementation:
- During grammar loading, flag terminals that have identifier operands (`hasCaptureBoundAnnotation`).
- In candidate resolution, when a flagged terminal wins, re-match `token.image` against `grammar.terminals[token.kind].regex` with capture extraction.
- Bind captured names into the stack-scoped environment for the duration of the annotation transaction.

Risk: if a regex has non-deterministic captures (alternations where different branches bind the same name), the re-match could bind differently from the original. Mitigation: document that capture names in mode-annotated terminals must be unambiguous (each name bound by exactly one branch).

## Layout Token Interaction

Python is the primary target. Python uses layout-sensitive parsing with `>>|`/`|<<` indent/dedent tokens injected by `injectLayoutTokens()`. Scanner modes must compose correctly with layout injection:

**Bracket-mode already suppresses layout.** The existing `bracket-mode` annotation on `(`, `[`, `{` suppresses NEWLINE tokens inside brackets. This is the right mechanism — f-string modes should extend it.

**Required analysis:** Every mode annotation that pushes or replaces a mode must declare whether layout injection is suppressed in that mode. Options:
1. **Implicit suppression when any mode is active.** Simple, but wrong — some modes might want layout (e.g., a hypothetical block-string mode).
2. **Per-mode suppression flag.** Each `>>>` push can optionally carry a `nolayout` annotation. `injectLayoutTokens()` checks the mode stack and skips injection when the top mode has this flag.
3. **Compose with bracket-mode.** If f-string `{` pushes `bracket-mode` (or a sub-mode of it), the existing suppression mechanism applies without changes.

Option 3 is the least invasive for the Python case: f-string `{` already pushes a mode, and that mode can inherit bracket-mode's NEWLINE suppression. But this conflates two concerns (bracket-level line joining and f-string expression parsing). A clean design should keep them separate (option 2), with the Python grammar stacking both modes when needed.

## Open Questions for Next Session

1. Binding storage implementation:
   - stack-frame environment vs global+rollback transaction.
   - Agreed direction: stack-scoped, but exact data structure TBD.
2. Silent-fail diagnostics:
   - Default is silent. Add optional debug logging gated on a grammar annotation or Logger level.
3. Parser grammar updates:
   - Replace `if/else-if` chain with a loop to parse `scanmode+` list.
   - Backward compatible: single-annotation grammars remain valid.
4. `TokenPattern` migration:
   - Migrate from tuple to struct. Replace `mode: Mode` with `annotations: [ModeAction]`.
5. Layout interaction for Python:
   - Decide between per-mode suppression flag vs. composing with bracket-mode.
6. Update `ScanModeTest.apus`:
   - All bare `<<<` must get an operand to match the operand-required design.

## Suggested Incremental Implementation Plan

1. Migrate `TokenPattern` from tuple to struct; replace `Mode` with `[ModeAction]`.
2. Extend Apus grammar/parser to parse `scanmode+` list (loop instead of if/else-if).
3. Apply action list transactionally in scanner candidate resolution (snapshot/rollback).
4. Add named-capture identifier resolution via selective re-match for flagged terminals.
5. Add per-mode layout suppression flag; wire into `injectLayoutTokens()`.
6. Prototype on C++ raw string first (best delimiter-capture test).
7. Model Python f-string transitions using `===`, `>>>`, `<<<`.
8. Model C# interpolated strings to validate generality.
9. Update `ScanModeTest.apus` to use operand-bearing `<<<` throughout.

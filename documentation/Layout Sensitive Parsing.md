# Layout-Sensitive Parsing in APUS

## Problem

Some languages encode syntactic structure through whitespace: Python uses indentation for blocks, Haskell has the offside rule, Go and JavaScript have automatic semicolon insertion, Swift distinguishes prefix/postfix operators by adjacency. A general parser framework needs to handle these without language-specific hacks in the parser core.

## Design Criteria

1. **Parser-agnostic** — The GLL algorithm and its data structures (descriptors, CRF, BSR) must not change. Layout sensitivity is handled entirely outside the parser.
2. **Grammar-driven** — Whether and how layout applies is determined by the grammar file (presence of `>>|` or `|<<` terminals, future annotation syntax), not by code changes.
3. **Lazy and lightweight** — Spatial facts are computed on demand from existing data (token positions in the input string). No additional scanning pass, no auxiliary arrays.
4. **General** — The same mechanism should cover indentation (Python, Haskell), adjacency (Swift operators), and line-break sensitivity (ASI in Go/JS). Language-specific details are parameters, not code.

## Options Considered

### Option A: Adams-style IS-CFG (2013)

Embed column constraints directly into grammar symbols and check them during parsing. Each grammar position carries an indentation predicate; the parser evaluates it at every step.

**Rejected because**: Requires deep modifications to the parser core (violates criterion 1). Column predicates in every grammar symbol add complexity to the grammar representation. The approach is theoretically cleaner but not worth the implementation cost when the parser already handles ambiguity naturally.

### Option B: TeX-style preprocessing

A standalone pass that reads raw characters, tracks indentation, and emits a transformed character stream with explicit block delimiters (like TeX's `\begin` and `\end`). The scanner then tokenizes the transformed stream.

**Rejected because**: Operates below the token level, complicating error recovery and position tracking. The transformation must understand enough about tokenization to avoid injecting delimiters inside strings, comments, or multi-line tokens — essentially reimplementing parts of the scanner.

### Option C: Lazy spatial computation + token injection (chosen)

A two-layer architecture where spatial facts are computed lazily from token positions, and synthetic tokens are injected pre-parse. The parser runs unchanged on an augmented token stream.

**Chosen because**: Clean separation of concerns. Each layer is independently testable. The parser sees `>>|` and `|<<` as ordinary terminals — no special cases. GLL's ambiguity handling naturally accommodates the additional tokens. Position recovery works because synthetic tokens use zero-length Substrings anchored in the original input.

## Architecture

```
Layer 1:  injectLayoutTokens  — injects >>| and |<< tokens pre-parse
Layer 2:  (future)            — checks >s< <s> >n< <n> constraints during parse
```

### Spatial computation

All spatial facts are computed lazily from token `image.startIndex` and `endIndex` positions in the original input string — no auxiliary data structures needed.

**Adjacency**: Two tokens are touching when `prevToken.image.endIndex == currToken.image.startIndex`.

**Line breaks**: Count newlines in the span from the previous token's *start* (not end) to the current token's start. Scanning from the previous token's start ensures newlines consumed by visible tokens (e.g. Python's NEWLINE) are still detected. The sequence `\r\n` counts as one line break, not two (the `prevWasCR` guard).

**Column**: `String.columnOf(_:tabWidth:)` in `StringExtensions.swift`. Scans forward from the line start to the target index, counting Characters (grapheme clusters) with tab expansion. This matches what language specifications mean by "column."

**`linePosition(of:)`**: Also in `StringExtensions.swift`. Returns `"L{line}P{position}"` for diagnostics. Handles `\n`, `\r`, and `\r\n` as line endings.

### Layer 1: Token injection

A free function that computes spatial facts inline and modifies the token/trivia arrays in place:

```swift
func injectLayoutTokens(
    tokens: inout [Token],
    trivia: inout [[Token]],
    input: String,
    tabWidth: Int = 8,
    bracketPairs: [(open: String, close: String)]
)
```

**Algorithm**:
- Maintain an indent stack (initially `[0]`) and a bracket depth counter.
- For each token, if a line break occurred and we're outside brackets:
  - Column increased → push indent, emit `>>|`
  - Column decreased → pop indent(s), emit `|<<` for each level
- At end-of-string (`○`), emit `|<<` for each remaining indent level.
- Newline-only tokens (visible NEWLINE terminals) are passed through without triggering indent/dedent, preventing blank lines at column 0 from causing false dedents.

**Synthetic tokens** use zero-length Substrings (`input[idx..<idx]`) so that `token.image.base` remains the original input string. This preserves position recovery for error messages.

**Bracket suppression**: Languages specify which token pairs suspend indent tracking. Python uses `[("(", ")"), ("[", "]"), ("{", "}")]`. A language without bracket exemption passes `[]`.

**Lives in**: `LayoutTokenInjection.swift`. Called from `main.swift` between scanning and parsing, gated on `grammar.usesInjectedLayoutTokens`.

### Layer 2: Constraint annotations (future)

Four spatial constraint annotations for grammar rules:

| Annotation | Meaning | Check |
|------------|---------|-------|
| `>s<` | Tokens must be adjacent (no gap) | `prevToken.image.endIndex == currToken.image.startIndex` |
| `<s>` | Tokens must not be adjacent | `prevToken.image.endIndex != currToken.image.startIndex` |
| `>n<` | Tokens must be on the same line | no `\n`/`\r` in gap between tokens |
| `<n>` | Tokens must be on different lines | has `\n`/`\r` in gap between tokens |

Not yet implemented. Design direction: model constraints as a new `GrammarNodeKind` (a pass-through node in the grammar graph, like `.EPS`). The parser checks the constraint when it reaches the node and either advances or abandons the descriptor. This is during-parse checking, analogous to how exclusion sets are checked in `testSelect`/`tokenMatch`.

## Implementation Learnings (May 2026)

1. `>>|` and `|<<` are synthetic layout tokens and should be handled as normal `.T` terminals in grammar matching.
2. Boundary operators (`<s>`, `>s<`, `<n>`, `>n<`) are semantic boundary predicates (`.B`), not scanner tokens.
3. Boundary predicates are evaluated between the previous and current parser token position.
   Example: in `a <s> b`, the check is on the boundary between `a` and `b`.
4. `<s>` and `>s<` must use source span geometry, not trivia buckets:
   - `<s>`: `leftToken.endIndex < rightToken.startIndex`
   - `>s<`: `leftToken.endIndex == rightToken.startIndex`
   This is required because synthetic layout tokens intentionally carry empty trivia.
5. `<n>` and `>n<` continue to use line-break counting over the source span between token starts.
6. `.B` nodes should be excluded from FIRST/FOLLOW and LL(1) diagnostics because they are predicates and do not consume input.
7. EOS should be represented as a zero-width token at end-of-input (not a detached `"$"` literal image), otherwise span-based boundary checks can hit invalid ranges.
8. Diagram rendering should map `>>|` and `|<<` to `⇥` and `⇤` for readability; this is presentation only and must not change parser semantics.

## Implementation Learnings (June 2026)

1. Injection activation must be based on **grammar use**, not **terminal declaration**.
2. `grammar.symbolToID[">>|"] != nil` is insufficient because grammars like `apus.apus` may define layout token terminals as literals but never use layout-sensitive constructs.
3. APUS parsing now sets `grammar.usesInjectedLayoutTokens = true` only when unquoted layout operators are parsed in grammar structure (for example in sequence/layout positions), and injection is gated on that flag.
4. Practical rule: quoted literals such as `">>|"` in grammar meta-syntax do not imply layout-sensitive parsing is enabled for that grammar.

## Language Coverage

| Language | Mechanism | Spatial facts used |
|----------|-----------|-------------------|
| Python | INDENT/DEDENT | line breaks + column |
| Haskell | Offside rule | line breaks + column |
| F#, Nim | Indent blocks | line breaks + column |
| Swift | Operator adjacency | adjacency |
| Go, JS | Automatic semicolons | line breaks |
| YAML | Block styles | line breaks + column |
| Markdown | Blank-line paragraphs | line break count > 1 |

## Files

| File | Role |
|------|------|
| `StringExtensions.swift` | `columnOf(_:tabWidth:)`, `linePosition(of:)` |
| `LayoutTokenInjection.swift` | `injectLayoutTokens()` free function |
| `main.swift` | Wiring: calls injection between scan and parse |
| `*.apus` grammar files | Use `>>|` and `|<<` terminals to define indented blocks |

## References

- Adams, M.D. (2013). "Principled parsing for indentation-sensitive languages." *POPL 2013.* — The IS-CFG approach we considered and deferred.
- Scott, E. and Johnstone, A. — GLL papers (see CLAUDE.md for full references).
- CPython Grammar/python.gram — Reference for Python's INDENT/DEDENT semantics.

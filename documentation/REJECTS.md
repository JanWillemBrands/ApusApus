# Reject Test Failures: Inventory

## Purpose

Inventory of all known failures in the `adventRejects` / `swiftSyntaxRejects` test suites.
Each entry records the root cause, current status, and preferred fix approach.

The broader goal is to identify issues that expose gaps in the APUS annotation vocabulary,
and to design new general-purpose APUS tools — reusable across grammars, not Swift-specific.
"Structural lookahead" (peering through the content of a non-terminal before deciding to
match it) is one such candidate.

---

## Resolved

### R1 — `testNonBreakingSpace#1`

**Source:** `a \u{00A0}+ 2`
**Origin:** `ExpressionTests.testNonBreakingSpace`

Swift-syntax emits only a `.warning`-severity diagnostic for a non-breaking space (U+00A0),
not an `.error`. Since `swiftSyntaxAccepts` is keyed on `!parsed.hasError` (not `hasWarning`),
this snippet is syntactically valid and belongs in the accepts suite.

**Resolution:** Moved from `expressionRejectSnippets` to `expressionSnippets` in
`SwiftSyntaxExpressions.swift`. ✓

**Accept-side grammar fix (2026-08-05):** moving it to the accepts suite exposed that the
`whitespace` terminal (reject-era) had dropped U+00A0, so Advent couldn't parse `a<NBSP>+ 2`.
Added `\u{00A0}` back to the `whitespace` regex (swift-syntax lexes NBSP as trivia + a
`.nonBreakingSpace` warning; it is the only non-ASCII whitespace so treated). Accept now passes. ✓

---

### Resolved: B1 — Trailing Closure on Literal Expressions *(partial)*

**Test cases:** `testLiteralWithTrailingClosure#1` – `#9`

| # | Source | Status |
|---|--------|--------|
| 1 | `_ = true { return true }` | ✓ fixed (`disabledReason` on accept-side, compiler rejects) |
| 2 | `_ = nil { return nil }` | ✓ |
| 3 | `_ = 1 { return 1 }` | ✓ |
| 4 | `_ = 1.0 { return 1.0 }` | ✓ |
| 5 | `_ = "foo" { return "foo" }` | ✓ |
| 6 | `_ = /foo/ { return /foo/ }` | **still open** (see below) |
| 7 | `_ = [1] { return [1] }` | ✓ |
| 8 | `_ = [1: 1] { return [1: 1] }` | ✓ |
| 9 | `_ = 1 + 1 { return 1 }` | ✓ |

**Root cause:** The grammar rule `functionCallExpression = postfixExpression trailingClosures`
placed no restriction on what `postfixExpression` reduces to. A bare integer, boolean, nil,
string, regex, array, or dictionary literal is a valid `postfixExpression`, so the grammar
accepted `1 { }`, `[1] { }`, etc.

**Fix implemented (2026-08-01):** Introduced two new non-terminals:

- `nonLiteralPrimary` — all 20 `primaryExpression` alternatives **except** `literalExpression`
  (keeps `@prefer parenthesizedExpression` for the `(…)`-vs-functionType disambiguation)
- `nonLiteralPostfix` — `nonLiteralPrimary` plus all 8 postfix-chain alternatives:
  postfixOperator, postfixOperatorToken, dotOperator, functionCallExpression,
  initializerExpression, explicitMemberExpression, subscriptExpression, forcedValueExpression,
  optionalChainingExpression

Changed `functionCallExpression` to:
```
functionCallExpression = @prefer postfixExpression functionCallArgumentClause trailingClosures
                       | nonLiteralPostfix trailingClosures .
```

The second alternative covers trailing-closure-only calls (`f{}`). `nonLiteralPostfix`
ensures the callee is either a non-literal primary or has at least one postfix operation
applied (so `1!`, `[1][0]`, `1.description` are all callable — matching swift-syntax's
`!leadingExpr.raw.kind.isLiteral` check which applies at postfix level, not primary level).

**Residual: test #6** — `_ = /foo/ { return /foo/ }` — regex literals are not in
`literalExpression` in the grammar; they have their own scanner mode and production path.
The B1 exclusion therefore doesn't apply. Filed as C3 (forward slash regex issues) below.

**Net improvement:** 8 tests fixed, 107 → 99 effective adventRejects once C3 is addressed.

---

### Resolved: B3 — Guard without Required Clause

**Test cases:**

| Label | Source |
|-------|--------|
| `testGuard1#1` | `func noConditionNoElse() { guard {} }` |
| `testGuard2#1` | `func noCondition() { guard else {} }` |

**Root cause (investigated):** Both tests are already passing. `guard {}` — the `>->("{")` gate
on `"guard"` was preventing the rule when the next token was `{`, but even after those gates were
removed the tests still pass: swift-syntax's `parseConditionList` consumes the `{}` as a closure
condition, and the missing `else` means `hasError` is set. Advent rejects correctly because
`conditionList` parsing of a bare closure followed by no `else` fails. `guard else {}` — `else`
is excluded from `hardIdentifier` so `conditionList` finds no valid condition and Advent rejects.

**Status:** Tests confirmed passing. The `>->("{")` annotations on `if`/`switch`/`while`/`guard`
were briefly **removed** (2026-08-01) in anticipation of a different fix, then **re-added** as B2
discriminator 2 (see B2 above) — a condition/subject may never open with `{`. ✓

**Side effect (historical, now resolved):** while the gates were removed, `testRecovery28#1`
(`repeat {} while { true }()`) failed adventRejects. With the `>->("{")` gates restored under B2,
Advent rejects it again; the only remaining wrinkle is on the swiftSyntax-reference side (see the
B2 caveat).

---

### Resolved: B4 — if-Expression with Multiple / Invalid Type Operations

**Test cases:**

| Label | Source summary |
|-------|---------------|
| `testIfExprMultipleCoerce#1` | `if .random() { 0 } else { 1 } as Int as Int` |
| `testIfExprIs#1` | `if .random() { 0 } else { 1 } is Int` |

**Root cause:** An if-expression used as the left operand of `as`/`is` in a sequence
expression. Swift-syntax's `parseSingleValueStmt` handles if/switch and returns *without*
trying to parse infix operators — so no `as`/`is`/`+` etc. can follow an if/switch expression.
The grammar was allowing it because `conditionalExpression` was reachable via
`primaryExpression → postfixExpression → prefixExpression`, putting it in the same
sequence-element position as any other expression.

**What swift-syntax actually does:** If/switch are parsed inside `parseUnaryExpression`
as ordinary sequence elements — there is NO grammar-level gate. The sequence loop can
append `as Int`, `is Int`, `as Int as Int`, etc. Swift-syntax builds a `SequenceExprSyntax`
and sets `hasError` **post-parse** during operator-precedence folding/validation, not
during parsing.

**Fix (implemented 2026-08-01, grammar-level):**
- Removed `primaryExpression = conditionalExpression .`, so if/switch can no longer be
  a `prefixExpression` (sequence operand or infix LHS).
- Added `expression = tryOperator? awaitOperator? conditionalExpression coercingOperator? .`
  where `coercingOperator` covers `as`/`as?`/`as!` but NOT `is`.
- Added a separate `coercingOperator` non-terminal (subset of `typeCastingOperator`,
  excluding `"is" type`).
- Assignment (`=`) and ternary false-branch use `expression` (not `prefixExpression`)
  so `x = if...` and `a ? b : if...` remain valid.

**Verified:** `adventAccepts` and `swiftSyntaxAccepts` for ExpressionSyntaxTests: 0 failures.
`RejectSyntaxTests`: 118 (down from 121; B4's 2 tests × 2 facets = 4 fewer). ✓

---

### Resolved: B5 — Member Access with String Interpolation

**Test case:** `testMissing#1`
**Source:** `` someVar.\(trailing) ``

**Root cause:** `\(...)` is a string-interpolation escape sequence valid only inside a
string literal. Using it in member-access position (`someVar.\(...)`) is syntactically
invalid, but the GLL grammar may scan the `\(` as a valid token and admit it as a member
name.

**Status:** Confirmed passing (2026-08-01 test run). ✓

---

### Resolved: B6 — Xcode Placeholder Token

**Test case:** `testTrailingClosures13b#1`
**Source:** `fn {} g: <#T##() -> Void#>`

**Root cause:** `<#T##() -> Void#>` is an Xcode editor placeholder. Swift-syntax handles
it as an `editorPlaceholderExpr` and sets `hasError`. Advent's scanner does not recognise
the `<#…#>` syntax, so this should fail at scan time and `adventRejects` should pass.
Verify: the `swiftSyntaxRejects` check (`parsed.hasError`) should also pass since
swift-syntax sets `hasError` for placeholders.

**Status:** Confirmed passing (2026-08-01 test run). ✓

---

### Resolved: C13a — Missing Space Around `=` in Declarations

**Test cases:** `testRecovery163#1`, `testRecovery164#1`

| Label | Source |
|-------|--------|
| `testRecovery163#1` | `let _= 5` and `let _ =5` |
| `testRecovery164#1` | `let _: Int= 5` and `let _: Array<Int>= []` |

**Root cause:** Swift's lexer (`classifyOperatorToken` in `Cursor.swift`) rejects `=` with
inconsistent surrounding whitespace universally — in declarations and expressions alike.
Advent had no spacing enforcement on declaration-initializer `=`.

**Fix (2026-08-02):** Introduced `assignmentOperator` nonterminal with symmetric spacing:
```
assignmentOperator = <s> "=" <s> | >s< "=" >s< .
```
All production-rule `"="` tokens replaced: `initializer`, `infixExpression`, `captureListItem`,
`typealiasAssignment`, `defaultArgumentClause`, `enumCaseRawValueInitializer`, `macroDefinition`. ✓

---

### Resolved: C13b — Invalid Unicode in identifiers

**Test cases:** `testRecovery160#1`

| Label | Source |
|-------|--------|
| `testRecovery160#1` | `let ￼tryx = 123` (U+FFFC Object Replacement Character before identifier) |

**Root cause:** The `identifierHead` / `identifierCharacter` regex classes in
`SwiftGrammarRegexLibrary.swift` used `FE47–FFFD` as the upper Unicode range, but
swift-syntax (`UnicodeScalarExtensions.swift`) uses `FE47–FFF8` — U+FFF9–FFFD are excluded
(FFF9 = Interlinear Annotation Anchor, FFFC = Object Replacement Character, FFFD = Replacement
Character).

**Fix (2026-08-02):** Changed both `identifierHead` and `identifierCharacter` upper bounds from
`\u{FFFD}` to `\u{FFF8}` in `SwiftGrammarRegexLibrary.swift`. ✓

---

### Resolved: C13b — Consecutive member declarations without separator

**Test cases (9):** `testConsecutiveStatements4a/4b`, `5a/5b`, `6a/6b`, `8`, `testTrailingSemi4a/4b`

**Root cause:** All 6 member list types (`enumMembers`, `structMembers`, `classMembers`,
`actorMembers`, `protocolMembers`, `extensionMembers`) used `xMembers = xMember xMembers?` —
no separator required between consecutive members. The `statements` grammar already enforced
this correctly via `statementSeparator = <n> | ";"`.

**Fix (2026-08-03):** Mirrored the `statements` pattern for all 6 member list types.
Removed `";"?` from each `xMember` definition; replaced `xMembers = xMember xMembers?` with:
```
xMembers = xMember ";"? .
xMembers = xMember statementSeparator xMembers .
```
Reuses the existing `statementSeparator` non-terminal — no new rules needed. ✓

---

### Resolved: C13c — Assignment expression in condition position

**Test cases:** `testRecovery153#1`

| Label | Source |
|-------|--------|
| `testRecovery153#1` | `if var y = x, z = x { z = y; y = z }` |

**Root cause:** `condition = expression` allowed any `expression` in condition position,
including assignment expressions (`z = x` via `infixExpression = assignmentOperator ...`).
Swift assignment returns `Void` — it is never a valid condition expression — but Advent's grammar
accepted it without error.

**Fix (2026-08-03):** Introduced `conditionExpression` and `conditionInfixExpression` in
`Swift.apus`. `conditionInfixExpression` mirrors `infixExpression` but omits the
`assignmentOperator` alternative. Three usage sites updated to use `conditionExpression`:
`condition`, `repeatWhileStatement`, and `whereExpression`. ✓

**Permissive counterpart disabled (2026-08-05):** swift-syntax *accepts* `if _ = 42 {}` syntactically
(`testMissingIfClauseIntroducer#1`), but this same rule (correctly) rejects it as an assignment in
condition position. Per the follow-the-compiler policy we keep our interpretation and marked that
accept snippet `disabledReason: "compiler error — …(we follow compiler)"` rather than loosen the rule.

---

### Resolved: C11 (partial) — Invalid Backtick-Escaped Identifiers: Null Byte and Backslash

**Test cases:** `testEscapedIdentifiers18#1`, `testEscapedIdentifiers21#1`

| Label | Source | Violation |
|-------|--------|-----------|
| `testEscapedIdentifiers18#1` | `` `null\u{0000}is not allowed` `` | Null byte inside backtick identifier |
| `testEscapedIdentifiers21#1` | `` `\\starting` ``, `` `mid\\dle` `` | Backslash inside backtick identifier |

**Fix (2026-08-02):** The `escapedIdentifier` regex was corrected to exclude control characters
(`\u{0000}-\u{001F}`) and backslash (`\\`). Also fixed `\u{2000}-\u{200A}` range (invalid as
Swift regex range bounds) → `\u{2000}\u{2001}\u{2002}-\u{200A}`. ✓

**Residual:** `testEscapedIdentifiers16#1` (operators inside backticks) remains open — see C11 below.

---

### Resolved: B7 — Reserved Keyword as Trailing Closure Label

**Test cases:** `testTrailingClosures14a#1`, `testTrailingClosures14b#1`

**Source (both, appears duplicated):**
```swift
func produce(fn: () -> Int?, default d: () -> Int) -> Int {
    return fn() ?? d()
}
_ = produce { 0 } default: { 1 }
_ = produce { 2 } `default`: { 3 }
```

**Root cause:** Bare `default:` as a labeled trailing closure label. Swift-syntax's
`atStartOfLabelledTrailingClosure()` explicitly checks `self.at(.keyword(.default))`
and returns `false` — with comment: "But 'default:' is ambiguous with switch cases and
we disallow it (unless escaped) even outside of switches." All other keywords (including
`case`, `return`, etc.) ARE valid trailing closure labels per `atArgumentLabel()` /
`isArgumentLabel()`.

The duplicate source in 14a vs 14b is a harvesting artefact.

**Fix (2026-08-01):** Added `trailingClosureLabel` non-terminal used in
`labeledTrailingClosure` — mirrors `argumentLabel` (`softIdentifier | "_"`) but also
excludes `default`. The exclusion set is `---("_" "let" "var" "inout" "default")`.

**Status:** Both tests passing. ✓

---

## Resolved: B2 — Trailing Closure / Closure Expression in Condition or Subject Position

**Test cases:**

| Label | Actual source (verbatim; newlines matter) |
|-------|---------------|
| `testTrailingClosureInIfCondition#1` | `if test {⏎  $0⏎} {}` |
| `testClosureAtStartOfIfCondition#1` | `if {x}() {}` |
| `testClosureAtStartOfIfCondition#2` | `if {⏎  x⏎}() {}` |
| `testClosureAtStartOfIfCondition#3` | `if { x⏎}() {}` |
| `testClosureAtStartOfIfCondition#4` | `if { a in⏎  x + a⏎}(1) {}` |
| `testTrailingClosureInGuard#1` | `guard test { $0 } else {}` |
| `testTrailingClosureInGuard#2` | `guard test {⏎  $0⏎} else {}` |
| `testTrailingClosureInGuard#3` | `guard test { $0⏎} else {}` |
| `testTrailingClosureInGuard#4` | `guard test { x in⏎  x⏎} else {}` |
| `testRecovery17#1` | `if { true } {}` |
| `testRecovery18#1` | `if { true }() {}` |
| `testRecovery23#1` | `while { true } {}` |
| `testRecovery24#1` | `while { true }() {}` |
| `testRecovery28#1` | `repeat {} while { true }()` |
| `testRecovery50#1` | `switch { 42 } { case _: return }` — closure as switch subject |
| `testRecovery51a#1` | `switch { 42 }() { case _: return }` — called-closure as switch subject |
| `testRecovery51b#1` | (same source, duplicate) |

**Provenance / methodology note (2026-08-19):** an earlier pass hand-typed *single-line*
approximations of these sources from this table's summaries and mis-concluded that
swift-syntax now accepts them ("stale rejects"). That was a probe error, not a swift-syntax
change: `atValidTrailingClosure` keys on `isAtStartOfLine`, so flattening the newline flips the
verdict. Re-probed against the **verbatim** sources (`Parser.parse(source:).hasError`), **all
entries above are genuine rejects.** Always probe the literal snippet, never a paraphrase.

**Root cause (measured).** The rejects come from three *distinct* discriminators in
swift-syntax's `atValidTrailingClosure(flavor:)` (Expressions.swift:2263), all active only in
**`.stmtCondition`** flavor (in `.basic` flavor the function returns `true` at line 2284, so a
multiline `foo {⏎ bar⏎}` at statement level stays valid — any Advent gate MUST be scoped to the
condition path or it breaks accept-side statement closures):

1. **Newline after the closure's opening `{`** (`if test {⏎ $0⏎} {}`, and the multiline
   Recovery variants). `!self.peek().isAtStartOfLine` (line 2296): if the body's first token is
   at start of line, the `{…}` is not a condition trailing closure, so the enclosing structure
   breaks → reject. Largest sub-cluster.
2. **Condition begins with `{`** (`if {x}() {}`, `while { true } {}`, `switch { 42 } …`). The
   leading `{` is always taken as the statement body (condition = `MissingExpr`) → reject.
   Independent of newlines.
3. **Disqualifying follow token after the closing `}`** (`guard test { $0 } else {}`, single-line
   — not a newline case). The token after `}` is `else`, which is not in the follow true-set
   (`{ where , [ ( . is as ? ! : =` + operators, the operator/bracket group additionally
   requiring `!lookahead.atStartOfLine`) → closure refused → reject.

**Resolution (2026-08-23) — all three discriminators, fully declarative** (no procedural filter,
no Oracle input re-read; see `Grammar Predicate Lookahead Design.md`):

- **disc-1 — newline after `{`.** Folded the layout into a real nonterminal
  `newlineOpenedClosure = "{" <n> closureSignature? statements? "}" .` (the `<n>` fires at parse
  time), and excluded it from both condition and trailing-closure position:
  `closureExpression = @excludedFrom(conditionExpression) @excludedFrom(trailingClosures) newlineOpenedClosure .`
  `@excludedFrom` is a `ContainmentRule` BSR query — it prunes the newline-opened reading only where
  it is contained in a `conditionExpression`/`trailingClosures` yield, so statement-level multiline
  closures stay valid.
- **disc-2 — condition/subject begins with `{`.** `>->("{")` on the
  `if`/`while`/`switch`/`guard`/`repeat`-`while` keyword slots (existing terminal-anchored gate).
  Re-fixes `testRecovery28` on the Advent side.
- **disc-3 — `}` followed by `else`.** The genuinely-new primitive: the token-set `>->`/`>+>`
  forward gate now fires at **nonterminal completion**, not just after a terminal, via the shared
  `MessageParser.forwardGateAllows()` helper wired at the four CRF continuation sites (`call`
  pop-replay, `rtn`, `bracketCall`, `bracketRtn`). `trailingClosures` partitions into two disjoint
  alternates, and `@excludedFrom` prunes the `else`-following one inside a condition:
  ```apus
  trailingClosures = closureExpression >-> ("else") labeledTrailingClosures? .                              // not before else — always OK
  trailingClosures = @excludedFrom(conditionExpression) closureExpression >+> ("else") labeledTrailingClosures? .  // before else — pruned in a condition
  ```

The `@within`/`WithinRule` procedural filter that previously carried disc-1/disc-3 was deleted.

**Validation:** probe of the **verbatim** sources matches swift-syntax `hasError` on every case
(`testTrailingClosureInIfCondition#1`, `testTrailingClosureInGuard#1–4` REJECT; statement-level
`foo {⏎ bar⏎}` ACCEPTs). Full sweep: 0 accept-regressions, and no B2 label among `adventRejects`
failures. ✓

**Caveat (test data, not Advent):** `testRecovery28#1` (`repeat {} while { true }()`) now fails on
the *`swiftSyntaxRejects`* side — the current swift-syntax parses it without `hasError`, so the
snippet is miscategorised and should move to the accepts suite (same pattern as R1/B1). Advent's
own verdict is not at issue.

---

## Resolved: C1 — Key Path Expression Extensions *(one case parked)*

**Test cases:**

| Label | Source | Status |
|-------|--------|--------|
| `testKeypathExpression#2` | `\String?.!.count.?` | ✓ rejects |
| `testKeypathExpression#3` | `\Optional.?!?!?!?.??!` | ✓ rejects |
| `testKeyPathMethodAndInitializers#3` | `\Foo.method<Int>()` | ✓ rejects |
| `testKeyPathSubscript#1` | `\Foo.Bar.[2].[1]` | ✓ rejects |
| `testKeyPathSubscript#2` | `\Foo.Bar.?.[1]` | **disabled/parked** (see below) |
| `testChainedOptionalUnwrapsWithDot#1` | `\T.?.!` | ✓ rejects |
| `testChainedOptionalUnwrapsAfterSubscript#1` | `\T.abc[2].?` | ✓ rejects |

**Root cause (was):** the `keyPathExpression` grammar admitted some but not all of the postfix
operations Swift accepts inside key paths — consecutive `?.!` chains, bare subscript `.[n]`,
optional chain `.?` as a key-path postfix, generic method calls `method<T>()`.

**Status:** confirmed rejecting on the 2026-08-23 sweep (none appear among `adventRejects`
failures) — the grammar was extended to match swift-syntax's key-path postfix set. ✓

**Parked residual — `testKeyPathSubscript#2`** (`\Foo.Bar.?.[1]`), disabled in
`SwiftSyntaxRejects.swift`: swift-syntax *commits* to the key path and errors on the missing
member after `.?` (`.[` is not `.member`). Advent (GLL) also finds the valid-shaped reading
`\Foo.Bar` + infix `.?.` + `[1]`, and nothing prunes it — the greedy alternative doesn't
complete, so `@longest` can't see it. Needs a key-path-commit / structural-lookahead primitive,
not a lexical fix.

---

## Open: C2 — Malformed String / Multiline String Literals

12 labels, classified 2026-08-29 by probing `Parser.parse` + `ParseDiagnosticsGenerator` for the exact
rule and its boundary (valid near-misses probed alongside each invalid case). **11 are string issues in
4 groups; 1 is misfiled.** Each group needs a DIFFERENT mechanism, which is why they never fell to one
fix.

### Group A — multiline delimiter shape *(4)* — ✓ RESOLVED 2026-08-29
`testStringLiterals#5` (`""""""`), `testMultilineString47#1` (`_ = """"""`),
`testMultilineString48#1` (`_ = """A"""`), `testWhitespaceAfterOpenQuote#1`.

**Sweep 39 → 34, accept 0, ambiguity 0** — all four, plus `testPostProcessMultilineStringLiteral#1`
from Group D as a bonus (see below). Implemented as RegexBuilder terminals in
`SwiftGrammarRegexLibrary.swift` (`multilineStringLiteral`, `extendedMultilineStringLiteral`,
`multilineInterpolatedStringLiteralHead`, `multilineInterpolatedStringLiteralTail` — all now
`- @builder .`). `…Part` stays a plain regex: it touches no delimiter, so the shape rule cannot apply
to it. RegexBuilder earns its place here for three reasons, not as a style preference:
- the raw form needs a BACKREFERENCE for the `#` count (`Reference` + `Capture(_:as:)`);
- line breaks must be CRLF-correct, and under the default GRAPHEME semantics `\r\n` is ONE
  `Character`, so a component matching `"\n"` would not match the `\n` of a CRLF pair — hence
  `.matchingSemantics(.unicodeScalar)` and an explicit CRLF-first `lineBreak` rather than
  `CharacterClass.newlineSequence` (which wrongly also matches U+000B/U+000C/U+0085/U+2028/U+2029);
- the body-item components are now SHARED between the static and interpolated forms instead of being
  copy-pasted across four regexes.

The disjoint-on-first-character body alternation is preserved deliberately — an earlier overlapping
version caused catastrophic backtracking on large inputs.

**Follow-up: ALL TEN string terminals are now `@builder`** (2026-08-29) — the remaining six
(`singleLineStringLiteral`, `extendedSinglelineStringLiteral`, the three single-line
`interpolatedStringLiteral{Head,Part,Tail}`, and `multilineInterpolatedStringLiteralPart`) were
converted mechanically. **Sweep 34/0/0 with a byte-identical reject set** — behaviour-neutral, as a
mechanical conversion should be. Duration 14.29s → 14.47s (~1%, within single-run noise).

One hazard worth recording, since a naive conversion would have introduced a silent bug: the
single-line regexes used `\\(?!\().` and a regex `.` does NOT match a newline, whereas
`CharacterClass.any` DOES. Translating `.` as `.any` would have started accepting `\`+newline inside a
single-line string. The two families genuinely differ — multiline uses `[\s\S]`/`.any` on purpose,
because there `\`+newline is a legal line continuation — so the catch-alls are separate components
(`singleLineEscapeCatchAll` uses `.anyNonNewline`).

The escape alternatives (`unicodeScalarEscape`, `simpleEscape`) are subsumed by the catch-alls and so
are redundant for MATCHING, but they are written out as named components on purpose: Group B1 is
exactly "delete the catch-all and keep these".

Only one literal-terminal regex is left inline, `extendedRegularExpressionLiteral` — regex, not string,
so out of scope here.

Two diagnostics, both structural:
- *"content must begin on a new line"* — after the opening `"""` the rest of the line must be EMPTY.
  Not even a space or tab: `"""  ⏎"""` and `"""⇥⏎"""` both error, only `"""⏎` is legal.
- *"closing delimiter must begin on a new line"* — the closing `"""` may be preceded on its line by
  horizontal whitespace only.

`multilineStringLiteral`'s regex requires neither, so `""""""` lexes as a valid empty multiline string.
**Approach: tighten the regex** — `"""\r?\n` … `\r?\n[ \t]*"""`, keeping the `(?![\s\S]*\\\()`
interpolation guard. Scanner-only, no engine change. Must sweep: multiline strings are everywhere in
the accept corpus.

**Latent bug found while probing (untested, no failing case yet):** `extendedMultilineStringLiteral`
allows `[ \t]*\r?\n` after the opener, but `#"""  ⏎"""#` errors in swift exactly as the plain form
does — that `[ \t]*` should not be there. Note this does NOT apply to `#"""A"""#` or `#""""""#`, which
are hasError=FALSE: with content on the opener line they are SINGLE-line raw strings holding `"`
characters ("false delimiters"), which is what the existing comment on that terminal already records.

### Group B — `#`-count coupling between delimiter and escape *(2)*
`testPoundsInStringInterpolationWhereNotNecessary#1` (`"\#(1)"` → *"invalid escape sequence in
literal"*), `testRawStringErrors2#1` (`#"\##("invalid")"#` → *"too many '#' characters to start string
interpolation"*).

The rule: in a string opened with N `#`s, interpolation is `\` + exactly N `#`s + `(`. Fewer or more is
an error, and N=0 means `\#(` is simply an invalid escape. Our `extendedSinglelineStringLiteral` treats
the raw body as opaque, so `\##(` is just content.

**Not expressible as one regex.** The body constraint is "no `\` followed by a `#`-run LONGER than
backreference `\1`", and a backreference cannot parameterise a quantifier. → needs Group B/D's shared
mechanism below.

### Group C — interpolation must not span a newline *(3 of 3 RESOLVED)*

**✓ PARTIAL FIX 2026-08-29: reject 30 → 28.** `testUnterminatedString4#1` and `testUnterminatedString5#1`
fixed with two `>n<` gates on the boundaries the `interpolatedStringLiteral` production OWNS
(after Head, before Tail, and around each Part). Grammar-only, accept 0, ambiguity 0, trees unchanged.

**THE EXACT RULE, found in swift-syntax.** It is not a check — it is a per-lexer-state TRIVIA MODE.
`Cursor.swift`:
```swift
func leadingTriviaLexingMode(cursor:) -> TriviaLexingMode? {
  case .inStringInterpolation(let stringLiteralKind, _):
    switch stringLiteralKind {
    case .singleLine, .singleQuote: return .noNewlines
    case .multiLine:                return .normal
    }
```
and in `lexInStringInterpolation`:
```swift
case "\r", "\n":
  precondition(stringLiteralKind != .multiLine)
  return Lexer.Result(.stringSegment, stateTransition: .pop)   // literal simply ENDS here
```
So: while in `inStringInterpolation`, a newline is NOT trivia; it emits an empty `.stringSegment` and
pops the state, i.e. the literal ends — which is why the diagnostic is the parser's "expected ')'"
rather than an "illegal newline". Multiline gets `.normal`, so our multiline production is correctly
left ungated. Nested string literals are exempt because entering one PUSHES a different state.

**Why `>n<` cannot finish the job.** The state persists at ANY paren depth (`parenCount` is tracked in
the same enum), so swift's rule covers gaps we do not own. `testNewlineInInterpolationOfSingleLineString#1`
(`"test \(label:⏎foo)"`) puts the newline between two tokens of the shared
`functionCallArgumentList`. Gating that needs a trivia policy that INHERITS into shared nonterminals.

**Design note for whoever picks this up:** the mechanism sketched earlier in this file as
"region-scoped trivia policy" is exactly what swift implements — a small `TriviaLexingMode` enum
(`.normal` / `.noNewlines` / nil) selected by a STACK of lexer states. That is a strong argument that
the abandoned scanner-mode system was the right shape, and that the missing piece is per-state trivia
modes rather than per-terminal ones. The GLL obstacle stands: the state must be derivable from the
grammar slot or the sub-parse identity, not from mutable parser state.

**✓ ALL THREE RESOLVED 2026-08-30 with `@sameLine`: reject 28 → 27, accept 0, ambiguity 0.**
The four `>n<` gates were REMOVED in the same change — `@sameLine` subsumes them. Verified by
instrumenting the rule: it prunes exactly the three offending literals (`"abc\(<NL>def)"`,
`"abc\(def<NL>)"`, `"test \(label:<NL>foo)"`) and nothing else.

Three things had to be right, and each was wrong first:

1. **Annotation home.** `@sameLine` is a whole-nonterminal span property, so it belongs at the
   production start beside `@longest`/`@shortest`, NOT after the `=`. It was initially parsed in
   `sequence()` (alternate level) purely because that was convenient; that placement is misleading
   once the prune anchors on the LHS. Now parsed in `production()`.
2. **Anchor.** The prune must attach to the LHS, whose completion yields have `i == k` and `j` = the
   true end — the exact span. Body-symbol anchors give
   `(i = production start, k = symbol start, j = SYMBOL end)`: the first symbol sees too little
   (nothing fired), the last mis-measures (6 valid inputs pruned). Because pruning LHS yields would
   also take sibling alternates' yields, the grammar had to be SPLIT:
   `interpolatedStringLiteral = singleLineInterpolatedStringLiteral | multilineInterpolatedStringLiteral`.
   That split is a faithfulness win in its own right — swift returns `.normal` for the multiline kind,
   so only the single-line form should ever carry the rule.
3. **Trailing trivia.** A yield's `j` is `triviaEnd`, so EVERY span includes the trivia that followed
   it. `"\(unsafe)"<NL>` and `"a\(maybeThrow())b"<NL>` were pruned as if they crossed a newline. The
   fix distinguishes crossing from trailing: require a committed token to START after the newline and
   still inside the span. That also handles a trailing comment (`"…"<NL>// c`), where a
   "followed by non-whitespace" test would have failed.

Also note the token cover only needs the tokens that may legitimately CONTAIN a newline (nested
multiline strings, block comments), which keeps it tiny and states the intent directly: a newline is
legal only inside such a token.

**Superseded design note — kept because the reasoning still applies elsewhere.** The containment machinery
(`@confinedTo`/`@excludedFrom`) turns out to be the right family to reuse: a `DisambiguationRule`
registered per-alternate whose closure CAPTURES THE PARSER, so it can query anything the parser knows.
That corrects an earlier claim in this file — the committed-token cover IS reachable post-parse, via
`parser.commits` (`TerminalCommit` carries `[start, end)`).

Implemented: `GrammarNode.requiresSameLine`, an `@sameLine` production pragma in `ApusParser`, and
`SameLineSpanRule` in `Oracle.swift` — prune a yield whose span contains a newline NOT covered by any
committed token. Newlines inside a token stay legal, which is what keeps the nested-multiline case
parseable. The cover over-approximates (the log includes commits from derivations that later died), so
the rule can only MISS a prune, never remove a legitimate parse.

NOT applied to the grammar, because anchoring is wrong: rules attach to a BODY SYMBOL, whose yield is
`(i = production start, k = symbol start, j = SYMBOL end)`. Anchoring on the FIRST symbol inspects only
`[literal start, Head end)` — never contains the newline, so nothing fired (28/0/0 unchanged). Anchoring
on the LAST symbol over-fires: **reject 27 but accept 6** — `testTry24#1` (three single-line
interpolations on separate lines), `testUnsafeExpr#16` (`func f() { "\(unsafe)" }`, function spans
lines), `testMultilineString46#1`. None has a newline inside the literal, so the inspected span is
larger than the literal.

What it needs: split `interpolatedStringLiteral` into `interpolatedStringLiteral =
singleLineInterpolatedStringLiteral | multilineInterpolatedStringLiteral`, put `@sameLine` on the
single-line nonterminal, and anchor the prune on its LHS COMPLETION yields (`i == k`, `j` = true end).
That gives an exact span AND the right scope — the current shared LHS makes per-alternate scoping
impossible. Once it works, the `>n<` gates in that production become redundant and should be removed:
`@sameLine` subsumes them.

### Group C — original analysis *(kept for the reasoning)*
`testNewlineInInterpolationOfSingleLineString#1`, `testUnterminatedString4#1` (`"abc\(def⏎)"`),
`testUnterminatedString5#1` (`"abc\(⏎def)"`). Diagnostic *"expected ')' in string literal"*.
Probed boundary: this holds for MULTILINE strings too (`"""⏎\(b⏎c)⏎"""` errors with *"unexpected code
'c'"*), so it is a general rule about interpolation contents, not a single-line-string rule.

**Structurally different from A/B/D, and unfixable in the scanner.** Interpolation is the split-token
hybrid: `interpolatedStringLiteralHead` ends at `\(`, the CFG then parses `functionCallArgumentList`,
and `Part`/`Tail` resume at `)`. The offending newline is not inside any token — it is in a TRIVIA GAP
between tokens of the argument list, where the CFG skips it freely. The Head/Part/Tail regexes already
ban newlines and are not the problem.

`>n<` cannot express it either: `boundaryMatches(cL.name, at: cI)` tests ONE position (the gap
`triviaStart..<start` of a single `TerminalCommit`), while the requirement covers every boundary in the
extent. Nor can it be placed at the use site: the interpolation's contents are `functionCallArgumentList`,
shared with ordinary calls, which legitimately span lines.

**The constraint's exact shape, probed 2026-08-29 — and it is NOT "the extent contains no newline":**

| input | `hasError` | consequence |
|---|---|---|
| `_ = "a\("""⏎x⏎""")"` | **false** | a nested MULTILINE string inside a single-line interpolation is LEGAL, newlines and all |
| `_ = "a\(f(⏎b))"` | true | the rule reaches into NESTED trivia gaps, not just the argument list's top level |
| `_ = "a\(  b  )"` | false | horizontal whitespace in the gaps is fine |

So the rule is: **no newline in any TRIVIA GAP within the interpolation; newlines inside tokens are
fine.** A raw span scan would wrongly reject the first row. And the cheap encoding — "Head and Tail on
the same line" — is also wrong, because in that same legal case the Tail sits three lines below the Head.

**Why this is hard in a GENERAL parser, which is the real obstacle.** The natural formulation is a
region-scoped trivia policy: on entering the interpolation, newlines stop counting as trivia; on
leaving, they resume. That is the `Scanner Mode Design.md` concept — but note the live `Scanner.swift`
has NO mode machinery, and `Swift.apus` uses no mode annotations at all. Reviving it as parser STATE will not
work: GLL processes descriptors from an unordered worklist, so "currently inside the region" is not a
well-defined global during the parse — it would have to become part of the descriptor/CRF identity, or
be derived from the input position alone. That is very likely why the mode system was dropped.

Sound alternatives, both non-trivial:
- **Position-derived table.** Precompute per input position whether a newline is trivia or inside a
  literal, by scanning nested delimiters — exactly what `LayoutTokenInjection.swift`'s
  `skipPythonStringLiteral` already does for Python. Language-specific, but GLL-safe because it is a
  pure function of the input.
- **Completion-time check over committed tokens.** Test at the completion of the single-line
  `interpolatedStringLiteral` production (a dedicated production, so no shared nonterminal is
  affected) whether any newline in the extent falls outside every committed token. Needs the token
  cover for the derivation, which the BSR does not currently expose at that point.

**What the swift-syntax TREE SHAPE suggests — the most promising direction.** For `_ = "abc\(def⏎ghi)"`
swift records NO "illegal newline" node. It CLOSES THE LITERAL at the newline:
```
├─[1]: ExpressionSegmentSyntax
│ ├─expressions: … identifier("def")
│ ╰─rightParen: rightParen MISSING
╰─closingQuote: stringQuote MISSING
├─[1]: CodeBlockItemSyntax ╰─ identifier("ghi")        ← separate TOP-LEVEL statement
╰─[2]: UnexpectedCodeDeclSyntax ╰─ rightParen, stringQuote
```
So the model is not "a newline is illegal inside interpolation" but "the single-line literal's TOKEN
STREAM is bounded, and the newline ends it". The legal nested case confirms the exemption mechanism:
the nested multiline string appears as a COMPLETE token pair (`multilineStringQuote … multilineStringQuote`),
so no newline is ever taken as whitespace.

**Region = SUB-PARSE.** This dissolves the GLL objection above. "Inside the region" cannot be parser
STATE (unordered worklist), but a sub-parse is a separate `MessageParser` instance, so the region
becomes that instance's identity. The seam already exists and already varies policy per instance:
`isSubParser` switches off the FOLLOW obligation and the predict filter, and `@preempt` constructs
sub-parsers exactly this way. "Newlines are not trivia in this sub-parse" is the same kind of
per-instance policy and needs no descriptor/CRF identity change. Mechanically: make the single-line
interpolated string a structured `-` lexical nonterminal — one token spanning the literal, body recognised by a
newline-free sub-parse — which mirrors swift emitting it as one bounded token stream.

Caveats to weigh first:
- The structured `-` attempt earlier in this session failed (76/26/1), for an unrelated cause since fixed
  (`prepareInput` skipped lookbehind resolution for lexical tokens). Less proven than it looks.
- If the literal becomes ONE token, the interpolation's expressions leave the main forest — moving
  `trees differ` and affecting AST generation. That trades a reject fix against tree fidelity, which
  is the current frontier, so it is not free.

**PARKED** at 3 tests. The "not expressible" claim is recorded WITH its probe evidence so it can be
re-challenged: what is actually ruled out is a raw-span constraint and a Head/Tail same-line
constraint, both by the legal nested-multiline row — not the sub-parse route above.

### Group D — multiline post-process rules *(2 → 1 remaining)*
`testPostProcessMultilineStringLiteral#1` — ✓ **RESOLVED as a side effect of Group A**, and
structurally rather than by luck. swift's rule is *"escaped newline at the last line of a multi-line
string literal is not allowed"*; in our grammar the body ends `line 2 \` + newline, the `\`-escape
CONSUMES that newline, and the closing delimiter now requires a line break before it — so no match
remains. The rule is IMPLIED by the delimiter shape and needs no post-lex check.

Still open: `testUnderIndentedWhitespaceonlyLineInMultilineStringLiteral#1` — *"insufficient
indentation of line in multi-line string literal"*. Probed: applies to whitespace-only AND text lines;
a whitespace-only line aligned with the closing delimiter is fine (`#"""⏎A⏎␠␠␠"""#` fails on this rule,
which incidentally confirms horizontal whitespace before the closer is shape-legal).

This one is a property of the matched token's TEXT, decidable from that text alone since the closing
delimiter's indentation is inside the token. swift applies it as a post-lex pass. It is column-relative,
so it is not expressible as a regex over the token.

### ✓ Groups B and D RESOLVED 2026-08-29 — and `@check` turned out to be UNNECESSARY

Sweep **34 → 30, accept 0, ambiguity 0**. Fixed: `testPoundsInStringInterpolationWhereNotNecessary#1`,
`testStringLiterals#10`, `testRawStringErrors2#1`, `testUnderIndentedWhitespaceonlyLineInMultilineStringLiteral#1`.
All four fell to DECLARATIVE RegexBuilder — no new annotation, no `ApusParser` change, no engine hook.
The plan below (a named Swift predicate over the token text) was written before trying harder on the
regex side, and each of its three justifications dissolved:

**B1 — escape set (2 tests, not 1).** Deleting the `\` + anything catch-alls leaves swift's closed
escape set (`\0 \\ \t \n \r \" \'`, `\u{…}`, `\(`), so `"\#("` and `"\1"` become unmatchable. This is
why the escape alternatives were written out as named components during the `@builder` conversion.
It also fixed `testStringLiterals#10` (`""\1 \1""`), which § C2 had filed as "misfiled / keypath" —
that call was wrong, or at least the fix landed here. No verified account of the exact derivation.

**B2 — `#`-count coupling (1 test).** Claimed "not expressible as one regex" because a backreference
cannot parameterise a quantifier. True but irrelevant: the rule is expressible by putting the
backreference INSIDE A NEGATIVE LOOKAHEAD — a `\` is body content only if not followed by the
delimiter's pound run PLUS at least one further `#`:
```swift
Regex { "\\"; NegativeLookahead { extendedSinglelinePoundDelimiter; OneOrMore { "#" } } }
```
With N=1, `\##` trips it and `\#(` does not.

**D — indentation (1 test).** Claimed "column-relative, so not expressible as a regex". Wrong on the
premise: `StringLiterals.swift` `visitTokenNode` does
`SyntaxText(rebasing: leadingTrivia[indentationStartIndex...]).hasPrefix(expectedIndentation)` — a
PREFIX test, not column arithmetic. Tabs/spaces must match literally, and a line indented deeper than
the closer passes because the closer's whitespace is still a prefix of it. So it IS regular, given the
closer's indentation as a backreference.

**The line-partition model** (suggested in review) is what makes it declarative: model the body as a
sequence of lines each carrying a layout prefix, and require every line to begin with `closerIndent`.
The obstacle was DIRECTION — the closer is at the end, and per the `Reference` docs an unbound
reference "will not match until it has previously been captured", so a forward reference silently never
matches. Resolved with a zero-width `Lookahead` that scans to the closer and captures its indentation
BEFORE the body is matched. **Verified empirically: captures made inside a `Lookahead` DO persist for
later backreference matching in Swift's engine** — undocumented, and the reason to be sure is that the
failure mode is silent (every multiline string becomes unmatchable, a mass accept regression, rather
than an error). Two facts made it correct:
- Empty lines are EXEMPT — swift-syntax's `testEmptyLineInMultilineStringLiteral` parses a
  zero-character line as `.stringSegment("\n")` with no leading trivia, while a whitespace-only line
  with 7 of 8 spaces IS an error. Hence the bare-`lineBreak` alternative.
- The lookahead must bind the indentation BEFORE the opener's line break is consumed. Placing it after
  demands a second line break, which an EMPTY literal (`_ = """⏎␠␠␠␠"""`) does not have — that cost 2
  accept failures (`testMultilineString41#1`, `testStringLiterals#3`) until moved.

**Standing lesson:** "not expressible as a regex" was asserted three times here and was wrong three
times — twice because the rule was prefix/lookahead-shaped rather than arithmetic, once because a
backreference can appear inside a lookahead. Push on the declarative encoding before reaching for an
escape hatch into Swift code.

### The mechanism that was PLANNED for B and D — kept for the record, not implemented
A **named predicate over a terminal's matched text**, resolved from Swift code by name — exactly
mirroring how `@builder` already resolves a named regex out of `SwiftGrammarRegexLibrary.swift`:

```apus
extendedSinglelineStringLiteral - /(#+)"(?:[^"\n\r]|"(?!\1))*?"\1/ @check(poundEscapeCount) .
multilineStringLiteral          - /…/ @check(multilineIndentation) .
```

It is a lex-match veto, so it drops straight into the existing filter chain in `tokenMatch` alongside
the lookbehind, forward-gate and `@preempt` steps — `TokenPattern.validator: String?` plus a
`[String: (Substring) -> Bool]` library. This is also the faithful shape: these rules are post-lex
validation in swift, not grammar.

### Misfiled
`testStringLiterals#10` (`""\1 \1""`) is **not a string problem**. Probed: swift's error is
*"consecutive statements on a line must be separated by newline or ';'"*, and `_ = \1` alone gives
*"expected root in key path"*. So `\1` lexes as a keypath expression and the violation is statement
separation. Belongs with C13 (error recovery), not here.

### Status
1. ~~**A**~~ — ✓ done. 5 tests (4 A + 1 D), reject 39 → 34. Includes the latent
   `extendedMultilineStringLiteral` `[ \t]*` over-acceptance.
2. ~~**B + D**~~ — ✓ done. 4 tests, reject 34 → 30. All declarative RegexBuilder; **`@check` was not
   needed and was not built.**
3. **C** — the only string group left (3 tests): an interpolation may not span a newline. Still needs
   a span-level constraint, because the offending newline sits in a TRIVIA GAP between tokens of the
   CFG-parsed argument list, not inside any token — so no scanner-level encoding can reach it. Given
   the three wrong "not expressible" calls above, re-examine that claim before building anything.

**String rejects: 12 → 0.** Reject total 39 → 27, accept 0, ambiguity 0 throughout.

---

## Resolved: C3 — Forward-Slash Regex vs Operator *(7 of 7)*

Swift decides regex-vs-operator in the LEXER (`lexOperatorIdentifier` → `tryLexOperatorAsRegexLiteral`
→ `tryScanOperatorAsRegexLiteral`, `RegexLiteralLexer.swift`). The real rule, in order:
1. `guard !isLeftBound` — a `/` tight against the previous CHARACTER is a postfix operator, never a
   regex start (adjacency, not a token-kind test).
2. `previousKeyword ∈ {func, operator}` → never a regex (`operator /^/`).
3. **Only when `isLeftBound == isRightBound`** (the slash "looks like a binary operator") consult
   `isInRegexLiteralPosition()` — the previous-*token-kind* operand-ender test.
4. `scanRegexLiteral(mustBeRegex:)`; `mustBeRegex` stays false in argument-list context
   (`( [ , : ::`), where an unapplied operator is legal.

Naming note: **`preferRegexOverBinaryOperator` is NOT this rule.** It is a narrow flag, set only after
`try?`/`try!`, meaning "prefer a regex even though a postfix `?`/`!` would normally imply a BINARY
operator follows". Advent's `regexOpenSlash` `<-<` operand-ender list is the analog of
`isInRegexLiteralPosition()`, and the docs/comments that called it the `preferRegexOverBinaryOperator`
analog were mis-citing it.

**Resolved (2026-08-24):**

- `testLiteralWithTrailingClosure#6` (`_ = /foo/ { … }`) and `testForwardSlashRegex116#1`
  (`qux(/, "(")/2`). ONE declarative rule on `operator` now covers every operator use — prefix,
  operator-as-argument, infix, operator-as-value:
  ```apus
  operator = >->( regularExpressionLiteral ) operatorToken .
  ```
  `regexOpenSlash`'s `<-<` gates WHERE a regex may start; this predicate adds WHETHER one completes,
  which only the CFG-modelled regex can know. It snapshots the RAW forest (swift's `canParseAsXxx`), so
  a viable regex counts even when the enclosing parse fails, and the prune cascades through the
  Oracle's greatest-fixpoint `pruneUnsupported`. Readings with no viable regex keep the operator:
  `_ = /x` (never closes), `qux(/, 1)` (unbalanced `)` fails the regex CFG), any infix `/` (blocked by
  the `<-<` gate). This REPLACED a narrower `prefixOperator`-only version — one rule in one place.

- **Operand-ender faithfulness.** The predicate exposed real gaps in the `<-<` list. `_ = /x/??/x/`
  regressed because postfix `?` was missing: swift blocks a regex after `.postfixQuestionMark` but
  ALLOWS one after `.infixQuestionMark`, so only the postfix spelling may be listed — Advent
  distinguishes them naturally (`optionalMark` terminal vs the ternary literal `"?"`), so
  `b ? /1/ : /2/` still parses. Also, entries must name the terminal that actually COMMITS: postfix
  `?`/`!`/`>` commit as the munch-exempt REGEX terminals `optionalMark`/`forceMark`/`closeAngle`
  (operator dev 6), so the pre-existing bare `"!"`/`">"` literal entries were **inert**
  (probe-confirmed: `!` commits as `forceMark`, never as literal `"!"`). Terminal names added alongside.

**Also resolved (2026-08-24) — `142` was never a regex problem:**

`_ = /\()/` was Advent reading prefix `/` + `keyPathExpression` (`\` with an empty-tuple root `()`) +
postfix `/`. swift's only diagnostic is "unexpected code '/' in source file" on the TRAILING slash, so
swift parses `_ = /\()` happily and merely won't attach the last `/`. Probed down to a minimal pair:

| source | swift | note |
|---|---|---|
| `_ = \.foo` | accept | keypath alone is fine |
| `_ = x/` | accept | postfix `/` on an ordinary operand is fine |
| `_ = \.foo/` | **reject** | **a postfix OPERATOR may not follow a key-path expression** |
| `_ = \().foo` | accept | `.member` after a keypath is a keypath COMPONENT, not outer postfix |

**Fix:** a leading `>->( keyPathExpression )` on the three postfix-OPERATOR alternates of
`postfixExpression`. The gate is exact because a `keyPathExpression` yield can only start at a `\`, and
a `postfixExpression` starting at `\` can only be that keypath. `?`/`!`/`.member`/subscript after a
keypath are handled inside `keyPathExpression`, so C1's keypath cases are untouched.
(Annotation order matters: `@prefer` must precede `>->` — `sequence()` consumes `@prefer`/`@avoid`,
then `@confinedTo`/`@excludedFrom`, then `>->`/`>+>`. Getting it wrong is a grammar LOAD failure, which
`tools/run_tests.sh` currently reports as "PASS" with all-zero counts — see the caveat below.)

**Still failing: NONE — all 7 resolved (`150a/b` and `151a/b` were the last).**

Positions in `_ = ^/"/"` — `^`=4, `/`=5, `"`=6, `/`=7, `"`=8. There are exactly two readings:

| | operator | then | leftover |
|---|---|---|---|
| **A** (swift) | `^` [4,5] | regex `/"/` [5,8] | `"` at 8 → unterminated string → **error** |
| **B** (Advent) | `^/` [4,6] (maximal munch) | string `"/"` [6,9] | nothing → **valid parse** |

1. swift's lexer, while lexing an operator, scans it for its FIRST internal `/` and tries a regex
   there. The scan of `/"/` succeeds, so it **commits**: the operator is truncated to `^`.
2. That commitment is irrevocable, so the stray `"` at 8 becomes an unterminated string → swift errors.
3. Advent explores both readings. A dies on the leftover `"`; B consumes everything, so Advent accepts.
4. To match swift, Advent must kill B — forbid the operator from spanning past position 5 *because a
   regex could start there*.

Crucially swift `break`s and KEEPS the whole operator when the regex scan fails
(`lexOperatorIdentifier`), so *viability* is the essential condition and no shortcut is faithful:
"an operator may not end in `/`" would wrongly reject a declared `prefix operator ^/` used as `^/x`.

Three findings, all measured:

1. **The geometry is a straddle, not containment.** The swallowed regex starts inside the operator and
   ends OUTSIDE it (`^/` = [4,6], regex `/"/` = [5,8]), so neither `>->` (start-anchored) nor
   `@confinedTo`/`@excludedFrom` can express it. Prototyped as `@excludesStartOf` + `StraddleRule`;
   it correctly subsumes the start-anchored case but changed nothing (see 2), so it was REVERTED.
2. **The target yield does not exist, and TWO gates suppress it.** Measured by disabling the Phase-F
   predict filter: with it OFF `regexCloseSlash` commits [7,8], but `regularExpressionLiteral` still
   yields NOTHING — `FOLLOW(plainRegularExpressionLiteral)` has no terminal that lexes at the trailing
   `"`, so `followCheck` independently refuses the completion. Both gates ask "can anything legal
   follow?" and the honest answer is no, which is *why* swift errors. **Removing `lexLKH` would not
   help**, and neither gate is wrong. (Contrast `/foo/{}` and `qux(/, "(")/2`, where the regex
   COMPLETED and only the enclosing expression failed — already handled by the RAW-forest snapshot.)
3. **structured `-` (lexical-token recogniser) is NOT a viable framing for regex.** Declaring
   `plainRegularExpressionLiteral structured - …` loads and runs, but: **reject 43 → 76, accept 0 → 26,
   ambiguity 0 → 1** (all 13 accept-failure labels regex-related). Cause: a recogniser sub-parse
   strips OUTER CONTEXT, and Advent's regex rules are built from outer-context gates — `<-<` on
   `regexOpenSlash` (evaluated against the commit log, which is empty at sub-parse start, while the
   outer `cL` is now the `plainRegularExpressionLiteral` terminal carrying no lookbehind) and the
   `>n<`/`<n>` newline split. Smoking gun: `testForwardSlashRegex41#1` (`/x/??/x/`), the case the
   `optionalMark` gate had just fixed, became an accept failure. Also `<-<` is currently parsed only
   in the TERMINAL branch of `production()`, so it cannot even be written on a structured `-` production
   (tracked as a TODO). Lesson: structured `-` suits self-contained bodies; it hides rather than solves context
   dependence, which is the whole substance of regex-vs-divide.

**Direction considered — lexicalisation-DAG framing, and its FALSIFICATION (2026-08-24).**
The idea: act at lexicalisation time rather than post-parse. A "straddle" is not a CFG notion at all
(GLL consumes a fixed token sequence, so overlapping tokens cannot arise); it is two **crossing edges**
in a lexicalisation DAG — the multiple-lexicalisation setting of `articles/Multiple input parsing and
lexical analysis.pdf`. That gives a well-formed side condition, the same shape as the maximal-munch
rule already in `Descriptor.swift`: *remove edge `(T,i,j)` if `T` carries `@splitBefore(X)` and an
`X`-edge starts at some `p`, `i < p < j`*. Prune the edge and the straddle never reaches the parser.

Prerequisite built (kept): `<-<`/`<+<` are now attachable to structured `-` productions
(`lookbehindAnnotations(attachingTo:)`, hoisted out of the terminal-only branch of `production()`) —
the TODO #19 unification in the "can *carry*" direction. It also exposed a real bug: `prepareInput`
`continue`d on `pat.isLexicalToken`, which skipped not just the regex/literal registration but the
**lookbehind resolution** at the bottom of the same loop, so a structured `-` terminal could never have a gate.
Both fixes are behaviour-neutral at 43/0/0 and currently UNEXERCISED (no grammar uses structured `-`).

**The test failed.** Prediction: with the gate attached outward, most accept failures recover and
`testForwardSlashRegex41#1` (`/x/??/x/`) passes.

| config | reject | accept | ambiguity |
|---|---|---|---|
| baseline | 43 | 0 | 0 |
| regex as structured `-`, no outward gate | 76 | 26 | 1 |
| structured `-` + outward gate, bug present | 76 | 26 | 1 (byte-identical — gate discarded) |
| structured `-` + outward gate, bug fixed | 73 | 24 | 1 |

Only 2 of 26 recovered and FSR41 still fails, with the gate demonstrably live (it moved 3 rejects /
2 accepts). So the *engineering* claim is disproven: pushing the regex into a structured `-` edge with the gate
moved outward does NOT restore correct behaviour. The 24 residual accept failures are all regex, with
`ForwardSlashRegexSkipping*` dominating, so the regex rules depend on more inner structure than the
two gates identified (`<-<`, `>n<`/`<n>`). The DAG *description* remains accurate and still explains
why the straddle feels alien; what is dead is this route to avoiding it. Grammar experiment reverted.

**Open.** No credible path yet that avoids the straddle. Speculative parsing is untouched by this
failure — the recogniser query is sound; it was the edge-pruning consumer that collapsed.

**OUTCOME — `@preempt` landed 2026-08-28 (`150a/b`, sweep 41/0/0); `151a/b` closed 2026-08-29
via the lexeme-shape viability test (sweep 39/0/0). No `ForwardSlashRegex` rejects remain.**

The straddle was avoided exactly as hoped: the decision sits at the operator's START, where every
candidate match shares the position, so it is a plain choice among sibling EXTENTS — no span geometry,
no Oracle rule. `@splitBefore` + `@yieldTo` were folded into ONE annotation, second operand optional:

```apus
@literalMunch @preempt(regexOpenSlash, plainRegularExpressionLiteral)   -- offer split + COMMIT
operatorToken - @builder .
@preempt(openAngle)                                                     -- offer only (generics)
operatorName  - @builder .
```

Two operands are irreducible: the first names the terminal whose `<-<` gate (swift's `isLeftBound`
analogue, checked at the operator's start) decides whether a split is offered; it cannot be derived
from `FIRST(N)`, whose members differ in gating (`regexOpenSlashNL` is ungated, so "some member
passes" would never block infix `x+/y/`). Viability comes from a MEMOISED speculative recogniser
sub-parse — the reuse the design doc prescribed.

Enablers found along the way:
- The `isSubParser` FOLLOW exemption covers only the sub-parse ROOT, so the target must be
  `plainRegularExpressionLiteral`, not `regularExpressionLiteral` (an inner nonterminal stays gated).
- The predict filter must be skipped for recognisers, else the query inherits an outer FOLLOW
  obligation and answers NO for a well-formed regex.
- **Regex boundary spaces, stated structurally.** swift bans an *unescaped* space/tab adjacent to a
  bare `/…/` delimiter but allows INTERIOR ones. `>s<` cannot express this — it measures the trivia
  GAP, while a boundary space is body CONTENT, so GLL always finds the atom derivation (probe-proved:
  even with trivia stripping enabled the space still matched as an atom). Encoded instead as
  `regexBody = regexItem | regexItem regexBodyTail` with `regexSpaceAtom` only interior; `/a b/` still
  parses and `/a\ /` (escaped) stays legal, matching swift's "unespaced". The `>s<` gates STAY — they
  block the trivia route, which the structural rule cannot see (removing them wrongly accepts `/ a/`).

**Latent bug found and FIXED: `boundaryMatches` was universally quantified.** Commits sharing a
`triviaEnd` are ALTERNATIVE lexicalisations, so requiring all to satisfy let one veto another — in
`_ = /\ /` the literal `"\\"[5,6]` (space as trailing trivia) vetoed `regexEscape[5,7]` (gap empty).
That broke MONOTONICITY: an extra surviving lexicalisation could REMOVE a parse. Now existential.
Behaviour-neutral today (41/0/0) because the predict filter happened to prune the loser — which is
precisely why it would have bitten later, blamed on whatever change exposed it.

**Predict filter: measured twice, now REMOVED (2026-08-29).** It was never the pure optimisation the
design doc claims. First measurement (2026-08-28) said KEEP: removing the FOLLOW-derived half (keeping
the grammar-authored `>+>`, which shares the block) gave reject 40 / accept 4 under the old boundary
semantics, and 41 / 14 / ambiguity 1 with the existential fix — the extra surviving derivations change
what `@prefer`/`@longest` see and they mis-prune. Both causes were then fixed independently (existential
`boundaryMatches`; the `@preempt` viability cut), and re-measurement over **three hash seeds** gives
39 / 0 / 0 either way — the half is now behaviourally INERT, and marginally *costly* (13.76s with vs
13.31s without; it spends a `cachedLex` per candidate match). Deleted, with the history kept in the
comment because it has been reinstated once already. Also DEAD CODE REMOVED earlier: the `lexLKH`
protocol method (no overrides, no call sites) and the whole `LCNPLexer` protocol (one conformer, one
use site — an existential on the hot path).

**Open lead CLOSED.** The "one over-accept failing only because of the filter" (41 → 40) evaporated:
it was a C3 regex case, now fixed properly by the viability cut rather than accidentally by the filter.
Removal holds at 39, not 38. The deeper thread — *why* a pruning filter could interact with
`@prefer`/`@longest` at all — is answered by the monotonicity analysis above and is no longer live.

**`151a/b` (`_ = ^/"[/"`) — RESOLVED (2026-08-29), grammar-only, via a lexeme-shape viability test.**
Advent's body `"[` is genuinely malformed (`regexCharacterClass` needs a closing `]`, and `[` is not a
plain atom), so a CFG-level viability test says "no regex" and `@preempt` never commits — leaving the
`^/` + string `"[/"` reading to win. swift instead commits to a regex-shaped LEXEME (its scan does not
require a well-formed body) and then errors on it.

Admitting `[` as a plain regex atom was TRIED and REJECTED: reject 41 → 39 (both fixed), accept 0, but
**ambiguity 2** — `/([)])/` gains a second reading, and `@avoid` cannot resolve it because the contest
is body-TILING (one 3-char character class vs atom-by-atom), not same-span. Beyond the ambiguity it
degrades the balance-aware regex CFG toward "scan to the next `/`", which is what that CFG exists to
prevent, with no principled floor.

The fix instead keeps the strict grammar untouched and adds `regexLexemeShape` — a deliberately WEAKER
model of `scanRegexLiteral`, referenced by NO production, existing solely as `@preempt`'s viability
target. **Sweep: 39 / 0 / 0**, and the ambiguity-0 result is the discriminator that was written into the
design doc as a falsifiable prediction *before* measuring: the grammar-loosening version also reaches
39, but at ambiguity 2. `148` (`_ = (^/x)/`) and `152` (`_ = (^/)("/")`) regressed on the first attempt
and were fixed by transcribing swift's group tracking rather than guessing at it.

**Shape is correct on the suite but MIS-FACTORED — one known latent gap.** Grounded in
`RegexLiteralLexer.swift`:
- `groupDepth` is never checked at end of scan, so the rule is not "parens balance" but the weaker
  Dyck-PREFIX condition *"no `)` at depth 0"*; a trailing unclosed `(` still lexes.
- `customCharacterClassDepth` exists ONLY to stop parens inside `[…]` counting as groups — nothing
  bails on an unbalanced `[`. The asymmetry `151` relies on is genuine, not curve-fitted.
- The `)` bail sits under `!mustBeRegex`. Confidence is decided in `tryScanOperatorAsRegexLiteral` by
  an OUTER guard and then a previous-token switch:
  ```swift
  if isLeftBound == isRightBound {                      // ← outer guard; if unequal, stays FALSE
    if preferRegexOverBinaryOperator { mustBeRegex = true }        // only after try? / try!
    if !mustBeRegex && !operatorStart.isInRegexLiteralPosition() { return nil }
    switch previousTokenKind {
    case .leftParen, .leftSquare, .comma, .colon, .colonColon: break   // unapplied op legal → FALSE
    default: mustBeRegex = true
    }
  }
  ```
  **Confident is the RARE mode.** For the ordinary shape `_ = /abc/` the slash is space-preceded (not
  left-bound) but letter-followed (right-bound) → guard unequal → block skipped → `mustBeRegex` FALSE.
  So nearly every real regex is scanned NON-confidently and the `)`-at-depth-0 bail DOES apply.

**Confirmed by experiment: FLATTENING THE STRICT BODY IS WRONG.** `hasError` is false for `/(/` `/[/`
`/]/` `/a]b/` `/(]/` `/((/` `/()/` `/[[]/` `/[(]/` `/[)]/` `/)/`, which looks like "swift has no balance
rule". Deleting `regexGroup`/`regexCharacterClass`/`regexClassBody`/`regexClassItem` and admitting
`( ) [ ]` as plain atoms gave **43 reject / 12 accept / 0 ambiguity** (from 39/0/0). Lost: `_ = (/x)/`,
`_ = (/[(0)])/`, `foo(/E.e, /E.e)`, `baz(^^/, /)` — all non-confident positions where a depth-0 `)`
must ABORT the regex. `/[(0)])` additionally proves the class exemption is real (the `)`s inside `[…]`
must not balance the trailing one). Reverted. **Always-balance is the correct default**; the whole
"swift's body is unbalanced" family lives in the rare confident mode. Termination, separately, IS flat:
`/[/]/` and `/(/)/` both error, so the closing `/` is the first unescaped one and the balance rule never
affects where the literal ends.

So the real discriminator for `148`/`152` is the **confidence flag**, not `groupDepth`; both those
tests sit after `(`. Our shape applies the bail UNCONDITIONALLY, which is right almost everywhere but
wrong in confident mode — `_ = ^/)/` and `_ = /)/` are valid Swift (probe: `hasError=false`,
tokens `regexSlash | regexLiteralPattern(")") | regexSlash`) which advent cannot parse at all, since
`)` is not reachable as a plain `regexAtom`. **Two missing accept tests, worth adding.**

The fix is NOT a new annotation kit but ONE conditional variant: a second, flat body selected by the
same confidence predicate. The anchor needed already exists and is already wired — `MessageParser.swift`
evaluates a `@preempt` gate terminal's `<-<` at `cI`, the operator's START, so a lookbehind on the token
preceding the whole operator IS expressible (an earlier note here claiming otherwise was wrong). What is
missing is only ARITY: `preemptStart`/`preemptConstruct` are one gate and one target per terminal, so a
terminal cannot carry two `(condition → viability)` pairs. Making that a list, first passing gate wins,
is ~4 sites and needs no new syntax. Deferred: it buys two edge-case inputs at the cost of a duplicated
body, so it should wait until a second call site justifies it.

Also removed: the `<n> regexOpenSlashNL` shape alternate, provably dead because `@preempt` only queries
viability at a split point strictly inside an operator token, so a newline can never immediately precede.

This is one instance of a general problem — see
**`Grammar Predicate Lookahead Design.md` § "Mimicking a deterministic parser: cuts with local
viability tests"**, which reframes C1, C3 and the B2 family as a single phenomenon (swift's language is
defined by an algorithm, not a grammar) and records why every survivor-filtering annotation we have is
structurally unable to express it.



**Test-harness caveat:** a grammar LOAD failure makes every suite abort before running, and
`tools/run_tests.sh` then prints `PASS` with `reject 0 / accept 0 / ambiguity 0 / trees differ 0`.
All-zero counts (especially `trees differ: 0`) mean "nothing ran", not "everything passed" — the
`xcodebuild rc=65` in the same line is the tell. Worth making the script fail loudly on this.

**Separate latent bug found:** `---( namedTerminal )` crashes at grammar load. The `---(…)` operand
parser (`ApusParser`, `while token.kind == "literal"`) accepts ONLY quoted literals, not named
terminals (unlike `>+>`/`>->`/`<-<`), so a named-terminal operand isn't consumed, `expect(")")` fails,
and the load error surfaces as a crash. Should accept named terminals (or error cleanly).

---

## Resolved: C4 — Module Selector (SE-0491 `Module::name`) Invalid Forms *(11 of 11)*

Grounded in swift-syntax's `Names.swift` — `isAtModuleSelector` / `consumeModuleSelectorTokensIfPresent`
/ `parseModuleSelectorIfPresent` / `parseDeclReferenceBase`. A valid selector is
`identifier "::" baseName`: the module name must be a **plain identifier**, there is **no valid
chaining** (`A::B::c`), no leading `::`, and the base name must be on the **same line** as `::`.

- `testModuleSelectorImports#3`, `#4` — SE-0491 import-path / module-selector grammar work.
- **Same-line rule** — `testModuleSelectorWhitespace#1/#2/#3`, `testModuleSelectorExpr#1`.
  `consumeModuleSelectorTokensIfPresent` sets `skipQualifiedName = afterContainsAnyNewline`
  (Names.swift:117): a newline between `::` and the base name → missing base name → `hasError`.
  **Fix:** `moduleSelector = hardIdentifier "::" >n< .` (the `>n<` forbids a newline before the base name).
- **Binding-pattern rule** — `testModuleSelectorIncorrectBindingDecls#7/#8/#9`
  (`case let Optional.some(Swift::decl)`, `case let Swift::decl?`). Inside a `let`/`var` binding
  pattern a name is *introduced*; swift-syntax parses it as a plain identifier and leaves `::decl` as
  unexpected code → `hasError`. Advent leaked it in via `matchPattern → expressionPattern`.
  **Fix:** `moduleSelector = @excludedFrom(valueBindingPattern) hardIdentifier "::" >n< .` — the
  Oracle prunes any module selector whose span lies inside a value-binding pattern.
- **Attribute-name rule** — `testModuleSelectorIncorrectAttrNames#1` (`@main::available(macOS 10.15, *)`).
  A module-qualified attribute name is a *custom* attribute, so its args are an expression argument
  list, not the balanced-token soup builtins allow — `(macOS 10.15, *)` (an availability spec) is not
  a valid expression list. **Fix:** the general balanced-token rule's `attributeName` is now
  module-free (`attributeHeadName = hardIdentifier | selfType`); a dedicated rule
  `attribute = "@" … moduleSelector attributeName attributeArgumentExprClause?` gives module-qualified
  attributes a strict `functionCallArgumentList` argument clause. `@main::available(foo: bar)` still
  accepts.
- **`@isolated(x)` rule** — `testModuleSelectorAttrs#2` (`@isolated(Swift::any)`). SE-0431 `@isolated`
  takes a plain identifier argument (swift-syntax's parser accepts any identifier and defers the
  `any`-only check to sema, so `@isolated(sdfhsdfi)` parses). **Fix:** a dedicated rule
  `attribute = "@" "isolated" "(" identifier ")"` (and `isolated` added to the general rule's
  `>->` exclusion). A module selector leaves `::any` unconsumed → reject; `@isolated(any)` /
  `@isolated(sdfhsdfi)` accept. (`identifier`, not `hardIdentifier | "any"`, to avoid a double-match
  on `any`.)

All probe-verified against swift-syntax `hasError`; full sweep **reject 57 → 46, accept 0,
residual ambiguity 0** (matching the last commit). ✓

---

## Resolved: C5 — Invalid Access Level Modifier Combinations

**Test cases:** `testAccessLevelModifier#1`–`#11` (all confirmed rejecting, 2026-08-23 sweep)

**Source (representative):**
```swift
open open(set) var openProp = 0
public public(set) var publicProp = 0
...
```

**Root cause (corrected):** the failing cases are all `open(set)` — either bare `open(set) var`
or `open open(set) var`. This is NOT a "duplicate modifier" counting problem: `open` is simply
never a *setter* access level. Swift-syntax only tolerates a leading `open(set)` by reading it as
a call; the compiler rejects it.

**Fix:** `accessLevelModifier` offers the `X | X "(" "set" ")"` pair for
`private`/`fileprivate`/`internal`/`package`/`public`, but `open` has **no `(set)` alternate**
(`accessLevelModifier = "open" .`). Dropping that one alternate makes `open(set)` unparseable, so
both `open(set) var` and `open open(set) var` reject. The other `X(set)` forms remain valid. ✓

---

## Open: C6 — Coroutine Accessors and Init Accessor with Default Values

**Test cases:** `testCoroutineAccessors#1`, `testCoroutineAccessors#2`,
`testInitAccessorsWithDefaultValues#1`

**Coroutine accessor sources:**
```swift
// #1: _read + modify
var i_rm: Int { _read { yield _i }  modify { yield &_i } }
// #2: _modify + read
var ir_m: Int { _modify { yield &_i }  read { yield _i } }
```

**Root cause:** The coroutine accessor blocks `_read { yield }`, `_modify { yield }`,
`read { yield }`, `modify { yield }` use `yield` as a statement. Advent may be accepting
these because `yield` inside an accessor is parsed as an expression call `yield(...)` rather
than a statement. The combination `_read + modify` or `_modify + read` in one `var` block
is flagged by swift-syntax as an invalid accessor combination.

For `testInitAccessorsWithDefaultValues#1`: init accessors with default values on the same
binding are invalid in Swift but may be accepted by Advent.

### Measured 2026-09-02 — the three split into two DIFFERENT causes

`buildAllTrees` on each (all three: `trees=1`, so one surviving reading):

| test | winning reading | cause |
|---|---|---|
| `testCoroutineAccessors#1/#2` | `{accessorClauseList, coroutineAccessorClause}` | accessor block, as designed |
| `testInitAccessorsWithDefaultValues#1` | `{trailingClosures}` | the forest gap below |

**#1/#2 are a deliberate design tradeoff, not a bug.** They parse *as accessor blocks* because
`coroutineSpecifier` intentionally keeps the modern `read`/`modify`/`mutate` spellings, which
`Parser.parse(source:)` gates behind experimental features and the corpus was therefore harvested
without. See the note at `coroutineSpecifier` (`Swift.apus:~2205`): dropping the modern spellings
was already tried and reverted — it fixed nothing (advent still finds the getter-body reading) and
lost real language coverage. So these two are a corpus artifact of the harvest configuration.
Rejecting them faithfully requires either gating the spellings behind a grammar-level feature flag
matching the harvest, or accepting them as known-divergent.

**`testInitAccessorsWithDefaultValues#1` is blocked by the same forest gap as `testUsing#1`** (see
C7): `(42, 0) { … }` after an initializer has only the trailing-closure reading, so the accessor
block — which is where an `init` accessor could be forbidden alongside a default value — is never
built. Fix the gap first.

---

## Open: C7 — Recently-Added / Evolving Language Keywords

**Test cases:**

| Label | Source | Keyword / Feature |
|-------|--------|-------------------|
| `testUsing#1` | `@MainActor\nusing` | `using` keyword (Swift 6.2+) |
| `testInverseTypesInParameter#1` | `func f(_: any borrowing ~Copyable) {}` | `~T` inverse type in parameter |
| `testNonisolatedSpecifier#2` | `func foo(test: nonisolated () async -> Void)` | `nonisolated` as type modifier |
| ~~`testAsync11d#1`~~ | `let _ = [() -> async ()]()` | ✓ RESOLVED 2026-09-02 |

**Root cause:** Syntax added after the grammar was last updated:
- `using` is not a keyword in the grammar.
- `~Copyable` in parameter position (the `~` before a type name) may not be handled.
- `nonisolated` as a standalone type modifier (not a declaration modifier) — `nonisolated` in
  type position means the function type is not isolated, but the grammar may only handle it in
  declaration-modifier position.

### ✓ RESOLVED 2026-09-02 — `testUsing#1`, and the accessor-block gap behind it

`var x: T = foo() { <accessors> }` now binds the block as an ACCESSOR BLOCK, not as a trailing
closure on the initializer, so `>->(declaration attributes)` on `statement` could finally go in and
reject `@MainActor⏎using`.

**What swift-syntax does.** SwiftParser is deterministic recursive descent and decides once, at
parse time: `parsePatternBinding` parses `= parseExpression(flavor: .basic, pattern: .none)`, then
takes a following `{` via `parseAccessorBlock`. Inside the initializer,
`parsePostfixExpressionSuffix` only accepts `{` as a trailing closure if
`withLookahead { $0.atValidTrailingClosure(flavor:) }` approves, and that refuses the brace when it
opens an accessor block (`atStartOfGetSetAccessor`, Lookahead.swift:252). So swift never constructs
the competing reading.

**The grammar half** (`trailingClosures`, both alternates):
`>->(willSetDidSetBlock accessorBlockBrace)` is that lookahead. `accessorBlockBrace` is factored out
as a named nonterminal precisely so the lookahead can anchor on the opening `{` — anchoring on
`accessorClauseList` fails because that is the block CONTENT and derives one token later, and
`getterSetterBlock` is unusable because its `codeBlock` alternate matches ANY block. The target appears in real productions, and GLL only creates its yields where a rule
calls it, so the gate fires only where an accessor block is grammatically possible — inside an
ordinary closure (`foo { get { 1 } }`) there is no such slot and trailing closures are unaffected.

**The engine half — this was the actual blocker, and it was a rule-ORDERING bug.** Adding the gate
alone turned valid input into a reject. `APUS_TRACE_ORACLE=1` on
`var x: Int = foo()⏎{ didSet {} }` showed why:

    after phase 1 dead-wood: root ALIVE
    PreferRule             pruned trailingClosures#3179  [13..34]'foo()⏎{⏎  didSet {}⏎}'
    LongestMatchRule       pruned prefixExpression#1273  [13..16]'foo'
    LongestMatchRule       pruned prefixExpression#1273  [13..19]'foo()⏎'
    LookaheadPredicateRule pruned closureExpression#490  [19..34]'{⏎  didSet {}⏎}'
    after rule pass: root ALIVE
    after phase 2 dead-wood: root *** GONE ***

`LongestMatchRule` deleted the short `prefixExpression` `foo()` — the reading the accessor block
needs — in favour of the maximal `foo() { … }`. The lookahead then deleted the closure. Prunes are
irreversible, so between them nothing survived.

Fix: `DisambiguationRule.isHardConstraint` splits the rule pass in two. HARD CONSTRAINTS
(`LookaheadPredicateRule`, `ContainmentRule`, `SameLineSpanRule` — what the LANGUAGE permits) run to
a fixpoint first, then a dead-wood sweep propagates their kills, then PREFERENCES
(`@longest`/`@shortest`/`@prefer`/`@avoid`, associativity — choices among readings that are all
legal) run over the survivors. Now the constraint removes the closure, dead-wood removes the long
`prefixExpression`, and `LongestMatchRule` correctly keeps `foo()`.

This also retires several wrong claims previously recorded here: the accessor tiling was never
"absent from the forest", and the `>->` anchor granularity was never too coarse (anchors are
per-reference-site and `span.i` is already the alternate start). Both were inferences that
measurement contradicted. **Reach for `APUS_TRACE_ORACLE=1` before theorising about a prune.**

### ✓ RESOLVED 2026-09-02 — `testInitAccessorsWithDefaultValues#1`

**With an initializer present, an `init` accessor may appear only FIRST.** Probed truth table
(swift-syntax 603.0.1) — every subset is legal, only the combination fails:

| default value | accessor order | swift `hasError` |
|---|---|---|
| yes | `init` FIRST, then get/set | false |
| yes | get, set, then `init` | **true** |
| yes | get, then `init` | **true** |
| yes | set, then `init` | **true** |
| yes | get, set (no `init`) | false |
| no | get, set, then `init` | false |

The corpus tests BOTH directions — `testInitAccessorsWithDefaultValues` is an ACCEPTING fixture with
`init` first (`SwiftSyntaxDeclarations.swift`) and a REJECTING one with `init` last — so this is the
deliberate point of the test, not error-recovery noise. The last row is why the restriction cannot
live on `accessorClauseList`: without an initializer `init` goes anywhere.

Encoding: `variableDeclaration = … typeAnnotation initializer initializedAccessorBlock`, where

    initializedAccessorBlock = >->(accessorBlockBrace) codeBlock .
    initializedAccessorBlock = "{" accessorClauseListNoInit "}" .
    initializedAccessorBlock = "{" initAccessorClause accessorClauseList? "}" .
    initializedAccessorBlock = @excludedFrom(variableDeclaration) accessorBlockBrace .

**The fourth alternate is a RECOGNIZER, and it is the whole trick.** The first attempt at this split
failed because swapping the alternate to a restricted block removed the only production calling the
UNRESTRICTED block at that `{`; the accessor-commitment lookahead on `trailingClosures` then had no
target yield, silently no-opped, and the block reverted to a trailing closure on `(42, 0)` — traced
as `INITTRACE accept trailingClosures,patternInitializerList`. The recognizer restores reachability
**without** admitting the bad shape, because `LookaheadPredicateRule` snapshots the RAW forest at
Oracle registration (`canParseAsXxx`, before any pruning): a doomed alternate still supplies the
yield the lookahead needs. `@excludedFrom(variableDeclaration)` then prunes it unconditionally — it
is always inside one — and reads as the truth it encodes: an unrestricted accessor list is never
valid in a variable declaration that has a default value.

`codeBlock` carries the same commitment negatively (`>->(accessorBlockBrace)`): a plain block body
is available only where the brace does not open an accessor list. `@prefer` cannot do this job — it
prunes codeBlock only where an accessor alternate covers the SAME span, and for the invalid ordering
none does, so `{ get {…} set {} init(…) {} }` would be re-accepted as statements.

**Reusable pattern:** when a lookahead target is only reachable from the alternates a restriction
removes, add a recognizer alternate for reachability and prune it with a containment rule. This is
the general escape from the "target reachable only from an annotation is snapshot-empty" trap.

---|---|---|
| yes | `init` FIRST, then get/set | false |
| yes | get, set, then `init` | **true** |
| yes | get, then `init` | **true** |
| yes | set, then `init` | **true** |
| yes | get, set (no `init`) | false |
| no | get, set, then `init` | false |

So: **with an initializer present, an `init` accessor may appear only FIRST**; without one it goes
anywhere.

**Attempted and reverted — the structural split is circular.** Swapping
`variableDeclaration = … typeAnnotation initializer getterSetterBlock` to a restricted
`initializedAccessorBlock` (no `init`, or `init` first) removes the only production that calls the
UNRESTRICTED accessor block at that `{`. The accessor-commitment lookahead
(`>->(willSetDidSetBlock accessorBlockBrace)` on `trailingClosures`) then has no target yield there
and silently no-ops, so the block goes back to being a trailing closure on `(42, 0)` and the input
is accepted anyway. Traced: `INITTRACE accept trailingClosures,patternInitializerList`. This is the
documented "target reachable only from an annotation is snapshot-empty" trap.

Encoding it needs one of:
- an **ordering predicate over a list** (`init` may not follow another entry) — a new apus primitive;
- or the unrestricted block kept **reachable** for the lookahead while a hard constraint prunes the
  bad ordering — i.e. both blocks offered, one killed by a constraint.

Confirm the restriction against a newer swift-syntax first: order-sensitive *and* conditional on the
default value smells like SE-0400 error recovery rather than settled language, in which case
disabling the fixture (as with the coroutine accessors) is the better call.

---|---|---|
| yes | `init` FIRST, then get/set | false |
| yes | get, set, then `init` | **true** |
| yes | get, then `init` | **true** |
| yes | set, then `init` | **true** |
| yes | get, set (no `init`) | false |
| no | get, set, then `init` | false |

So the rule is: **when a default value is present, an `init` accessor may appear only as the FIRST
entry of the accessor list.** Without a default, `init` may appear anywhere.

Encoding it needs a with-initializer accessor-list variant (`init` first, or no `init` at all) used
by `variableDeclaration = … typeAnnotation initializer getterSetterBlock`, AND suppression of the
`getterSetterBlock = codeBlock` reading, which otherwise re-accepts the invalid form as statements
(`get {…}` = call + trailing closure). The oddness of the restriction — order-sensitive, and only
with a default — suggests it may be SE-0400 error-recovery behaviour rather than a settled language
rule, so confirm against a newer swift-syntax before encoding it.

---

## Open: C8 — Multiline Generic Arguments Containing `of` Keyword

**Test cases:** `testMultiline#1`, `testMultiline#2`, `testMultiline#3`

**Sources:**
```swift
S<[
    3
    of      // ← 'of' at start of line inside array-in-generic
    Int
]>()
```
```swift
S<[3
   of Int]>()
```

**Root cause:** The word `of` appears at the start of a line inside a generic argument that
is itself an array type `[...]`. The layout-sensitive scanner may be treating `of` as a
keyword (statement separator or similar) rather than as an identifier in this context, causing
the generic argument to be mis-parsed. Swift-syntax rejects these forms (sets `hasError`).

---

## Resolved: C9 — `@abi` Attribute and Macro Role Name Violations

**Test cases (all resolved 2026-08-04):**

| Label | Source | Violation |
|-------|--------|-----------|
| `testMacroRoleNames#1` | `@attached(member, names: named(class))\nmacro m()` | `class` used as a macro role name |
| `testABIAttribute#1` | `@abi(<#fnord#>)\nfunc placeholder() {}` | Placeholder inside `@abi` |
| `testABIAttribute#2` | `@abi(import Fnord)\nfunc invalidDecl() {}` | `import` inside `@abi` |
| `testABIAttribute#3` | `@abi(var )\nvar v1` | Trailing space / empty decl in `@abi` |
| `testABIAttribute#5` | `@abi()\nfunc fn2() {}` | Empty `@abi` arg list |
| `testABIAttribute#6` | `@abi\nfunc fn3() {}` | `@abi` with no argument at all |

**Fix (2026-08-04):** Added dedicated `attribute` rules in `Swift.apus`, with the general rule
using `>->("abi" "attached" "freestanding")` to skip the three names that have dedicated rules.

**Accept-regression + hybrid repair (2026-08-05):** The first cut over-tightened both arms and
**wrongly rejected 34 valid attribute snippets** (ACCEPT suite was at 0 before this work). Fixed by
making each arm cover exactly what swift-syntax accepts — a hybrid of specific + token-soup:
- **`@abi`** stays a *specific* declaration check (token-soup can't reject `@abi(import Fnord)`), but
  `abiDeclaration` was **widened** to the bodyless/accessor/constant forms swift-syntax allows:
  `constantDeclaration` (`let c1, c2`), `bodylessInitializerDeclaration` (`init()`),
  `abiSubscriptDeclaration` (bodyless `subscript(…) -> …`), `abiVariableDeclaration`
  (`var v { get set }` with no type annotation).
- **`@attached`/`@freestanding`** replaced `functionCallArgumentList?` (too narrow — rejected
  `named(deinit)`, `named(subscript)`, `named(init(a:b:))`, module selectors) with a faithful
  token-soup `macroRoleArguments`, whose identifier atom excludes exactly the keywords
  swift-syntax's `parseDeclReferenceBase` rejects as decl-reference names (everything except
  `init`/`deinit`/`subscript`/`self`/`Self`, plus role `extension`). `named(class)` still fails
  (`testMacroRoleNames#1` preserved); `literal` omitted so `named(true)`/`named(nil)` still fail.
  A stray `"::"` atom was dropped — it duplicated the scanner's `:`/`::` Schrödinger reading and
  caused 2 pivot ambiguities (`testModuleSelectorExpr#8/#9`).

All C9 rejects preserved; all 34 attribute accepts restored; 0 residual ambiguity. ✓

---

## Open: C10 — Spacing-Sensitive Postfix Operator Parsing

**Test cases:**

| Label | Source | Issue |
|-------|--------|-------|
| `testOperators34a#1` | `foo!!foo` | `!!` treated as custom operator |
| `testOperators34b#1` | `foo!!foo` | (duplicate) |
| `testOperators35a#1` | `foo??bar` | `??` without surrounding spaces parsed as operator |
| `testOperators35b#1` | `foo??bar` | (duplicate) |

**Root cause:** Swift requires that `!!` is parsed as `foo!` (postfix force-unwrap) followed by
`!foo` (prefix logical-not), and `??` without spaces is ambiguous. The expected parse of
`foo!!foo` is invalid Swift. Advent's postfix operator scanner may be accepting `!!` or `??`
as a single compound postfix operator, allowing `foo!!foo` to parse without error.

---

## Resolved: C11 — Invalid Backtick-Escaped Identifiers (residual)

**Test cases:**

| Label | Source | Violation |
|-------|--------|-----------|
| `` testEscapedIdentifiers16#1 `` | `` let `+` = 0 ``, `` let `.` = 0 `` | Pure-operator sequence inside backticks |

**Fix (2026-08-04):** Converted `escapedIdentifier` from a raw `/regex/` terminal in
`Swift.apus` to a `@builder` terminal backed by `ApusRegexLibrary.escapedIdentifier` in
`SwiftGrammarRegexLibrary.swift`.

The authoritative rule (from `lexEscapedIdentifier` in swift-syntax's `Cursor.swift`) is:
a backtick identifier is rejected if ALL of its characters form a pure operator sequence
— i.e., the first character is an `isOperatorStartCodePoint` and every subsequent
character is an `isOperatorContinuationCodePoint`.

The fix encodes this with a `NegativeLookahead`:
```swift
NegativeLookahead {
    One(operatorHead)           // first char ∈ isOperatorStartCodePoint
    ZeroOrMore { operatorCharacter }  // all remaining ∈ isOperatorContinuationCodePoint
    "`"
}
```
Both ASCII and Unicode operator ranges are covered via the existing `operatorHead`/
`operatorCharacter` constants (which already back `operatorToken`). A second lookahead
rejects all-whitespace identifiers (permittedRawIdentifierWhitespace). The `validRawIdentifierContent`
class (built from the three new named constants — `unprintableASCII`, `forbiddenRawIdentifierWhitespace`,
`permittedRawIdentifierWhitespace`) replaces the former ad-hoc exclusion list. ✓

*(Null byte and backslash cases fixed — see Resolved: C11 partial above.)*

---

## Parked: C12 — `@available` argument string literal kind

**Test cases:** `testDiagnoseAvailability17a#1`, `testDiagnoseAvailability17b#1`,
`testDiagnoseAvailability20#1`, `testDiagnoseAvailability21#1`

**Root cause:** `@available` attribute arguments are parsed via `balancedTokens`, which accepts
any string literal form. Swift-syntax parses the same input but emits a diagnostic based on the
*kind* of string literal found:

| Test | Diagnostic |
|------|------------|
| 17a/17b | "argument cannot be an **interpolated** string literal" (`"\(...)"`) |
| 20 | "argument cannot be an **extended escaping** string literal" (`#"""..."""#`) |
| 21 | "argument cannot be an **extended escaping** string literal" (`#"..."#`) |

Plain string literals (`"…"`, `"""…"""`) are accepted; only `#`-delimited and `\()`-interpolated
forms are rejected. The check is a property of the *parsed token kind*, not the token stream
shape — a post-parse predicate on `stringLiteralExpression` kind, not a grammar production split.

**Parked:** waiting for the Oracle Filter / Post-Parse Predicate mechanism (see APUS Extension
Candidates §1 below). The predicate would inspect the string literal's token type and prune
the derivation for those two disallowed forms.

---

## Open: C13 — Error Recovery: Miscellaneous

Tests where swift-syntax performs error recovery (`hasError = true`) but Advent accepts cleanly.
Require individual source inspection to determine root cause:

**Still failing:** `testSwitch64#1`, `testSwitch67#1`, `testSelfRebinding2#1`,
`testRegexParseError17#1`, `testIdentifiers6#1`, `testInitDeinit11#1`

**Resolved 2026-09-02 — `testIfconfigExpr8#1`, `testIfconfigExpr9#1`.** The postfix machinery
(`postfixConditionalCompilationBlock`) already excluded infix operators and statements by
construction, but both inputs still parsed by falling through to the **statement-level** block,
where `.methodOne() + 12` / `return` were accepted as ordinary statements. Two changes:

1. `>->( "." )` on `compilationCondition` in `ifDirectiveClause` / `elseifDirectiveClause`
   (and after `elseDirective`) — a statement-level clause body may not begin with a leading dot,
   since a bare `.member` is never a valid statement. Where one does, the block is a postfix
   continuation and must route through the postfix form.
2. `postfixIfBody` gained a nested-block RUN (`postfixNestedBlocks`) — required by
   `testIfconfigExpr11` (`nestedIfConfig`), whose `#if` clause holds two nested blocks
   back-to-back. Without it those clauses had no postfix reading and change 1 rejected them.

Note the mid-body `>->` form attaches to the **preceding symbol** (`node.followAhead`,
`ApusParser.swift:831`) and takes **literal** operands; the sequence-start form takes identifiers
and attaches to the alternate (`:493`). A `>->` after a `<n>` boundary node fails to parse — the
boundary is consumed by `layout()` before the lookahead site is reached.

Do NOT add a `postfixExpression postfixNestedBlocks?` alternate: `explicitMemberExpression =
postfixExpression postfixConditionalCompilationBlock` already absorbs trailing blocks, and
spelling it out again makes `.unknownMethod1() #if … #endif` derivable two ways (ambiguous pivot).

**Resolved (2026-08-23 sweep):**
- `testEnum11#1` — a top-level `case` is not a declaration; fixed by
  `declaration = @confinedTo(memberDeclaration) enumCaseDeclaration .` (see
  `Grammar Predicate Lookahead Design.md`). ✓
- `testInvalid17#1`, `testInvalid21#1` — confirmed rejecting. ✓

---

## APUS Extension Candidates

The patterns above suggest two high-value additions to the APUS annotation vocabulary:

### 1. Oracle Filter / Post-Parse Predicate

**Motivation:** B1 (literal trailing closure) and C12 (`@available` string literal kind).
Both restrictions are properties of the *parsed result*, not the token stream — B1 checks
`leadingExpr.isLiteral`; C12 checks `stringLiteral.isInterpolated || stringLiteral.isExtended`.
Encoding either as a grammar production split creates combinatorial duplication. An Oracle-level
hook is the natural home for such post-parse structural predicates.

**Proposed form:** A declarative annotation on a production rule (or a named Oracle rule)
that can inspect the sub-tree of one of the rule's components and prune the derivation if
a predicate fails. General enough to cover any "based-on-what-parsed" disambiguation.

**Reuse:** Any grammar where an alternative is valid only when a sub-expression has a
particular syntactic shape (e.g., lvalue restrictions, callable/non-callable distinctions).

### 2. Structural Lookahead — ✓ DELIVERED (2026-08-23)

**Motivation:** B2 (condition trailing closure). The `atValidTrailingClosure` check fires
at the *end of a sub-parse* (the end of `closureExpression`) and inspects the token that
follows. Existing `>>N` lookaheads anchor on a terminal; `>+>` / `>->` annotations anchored
only on a terminal-use. Neither covered "inspect what follows the close of an embedded
non-terminal."

**Delivered form:** no new syntax was needed — the existing `>+>` / `>->` token-set forward
gate simply became live **after a nonterminal / bracket completion** as well as after a
terminal. The gate is evaluated by one shared helper `MessageParser.forwardGateAllows(slot:at:)`
at the four CRF continuation sites, alongside `continuationViable`. So the proposed
`>>end+>(…)` is spelled with the ordinary gate on a nonterminal-use:
```apus
trailingClosures = closureExpression >-> ("else") labeledTrailingClosures? .
```
This honours the invariant *the Oracle never re-reads input* — a token-set lookahead is a
scanner query and stays at parse time. See `Grammar Predicate Lookahead Design.md` and the
`@within`/`WithinRule` retirement note in `The rise and fall of … dead-ends.md`.

**Reuse:** Any grammar with context-sensitive continuation requirements after a sub-parse —
layout-sensitive languages, operator precedence disambiguation, statement/expression
boundary detection.

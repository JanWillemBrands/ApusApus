# Regex Lookbehind Design

Scanner-level token lookbehind annotations (`++1`/`++2` positive, `--1`/`--2` negative) for disambiguating regex literals from division operators. Designed as a general APUS mechanism, with Swift as the primary use case.

> **Status (Jul 1 2026).** The `<<1`/`<<2` naming used in some older notes is **superseded** by `--1`/`++1`/`--2`/`++2`; the resolved spec is stored **per-terminal** in `MessageParser.swift`.
> The **plain** `/…/ ` regex is now a parser-level CFG (`plainRegularExpressionLiteral`, no annotations) — the previous-token disambiguation these annotations provided is subsumed by grammatical reachability + GLL parse viability. Only the **extended** `#/…/#` terminal still carries a `--1(...)` position guard (it's still a single scanner token).
> **Do not re-add these annotations to the plain-regex CFG to fix residual ambiguity** — measured net-negative (fixes ~1, breaks 3 multiline-skipping acceptances). See `TODO.md` item 19 for the experiment and the reasoning: the residual regex ambiguity is *structural*, not previous-token, so it belongs to the Oracle.

## Problem

Languages that use `/` both as a division operator and as regex literal delimiters (`/pattern/`) create a scanner-level ambiguity. The scanner's longest-match rule causes a regex pattern to greedily consume characters that may be intended as division:

```swift
let x = 1 / 2 ; let y = 3 / 4    // scanner sees / 2 ; let y = 3 / as one regex
```

This cannot be resolved at the parser level — once the scanner commits to a regex token, the consumed characters are unavailable for alternative interpretations.

## Swift's Lexer: Four Disambiguation Layers

Swift's lexer (SwiftSyntax `RegexLiteralLexer.swift` + `Cursor.swift`) applies four checks in order. Each is a hard gate — if it rejects, later layers are not consulted.

### Layer 1: Left-bound check (`isLeftBound`)

Checks the raw character immediately before `/` in the source text. If `/` is physically glued to a non-whitespace, non-opener character, it is "left-bound" and cannot be a regex.

Characters that make `/` NOT left-bound (regex possible):
- Whitespace: space, `\t`, `\n`, `\r`
- Opening delimiters: `(`, `[`, `{`
- Separators: `,`, `;`, `:`
- Comment end: `*/`
- NUL byte

Everything else (letters, digits, `)`, `]`, `}`, `>`, `!`, `?`, etc.) → left-bound → NOT regex.

```swift
foo/bar/baz              // NOT regex — 'o' before /, left-bound
b?/1/:/2/                // NOT regex — '?' before /, left-bound
foo!/regex/              // NOT regex — '!' before /, left-bound
42/7                     // NOT regex — '2' before /, left-bound
f()/2                    // NOT regex — ')' before /, left-bound
```

### Layer 2: `func`/`operator` keyword rejection

If the previous keyword was `func` or `operator`, `/` is always an operator (used in operator declarations), never a regex.

```swift
func /^/ (x: Int) {}     // NOT regex — operator declaration
operator /^/             // NOT regex — operator declaration
prefix func /(x: Int){}  // NOT regex — func before /
```

### Layer 3: `preferRegexOverBinaryOperator` hack (try?/try! only)

After `try?` or `try!`, the previous token is `.postfixQuestionMark` or `.exclamationMark`, which would normally reject regex (layer 4). A special lexer state overrides this.

From Cursor.swift line 69: `/// NOTE: This is a complete hack, do not add new uses of this.`

```swift
try? /^x/.wholeMatch(in: s)   // REGEX via hack — try? pushes special state
try! /^x/.wholeMatch(in: s)   // REGEX via hack — try! pushes special state
```

The hack is needed because `try` cannot appear on the LHS of a binary operator, so the `/` after `try?` must start a regex, not a division.

### Layer 4: `isInRegexLiteralPosition()` — previous token kind

A heuristic that checks the previous token to determine whether we are expecting an expression (regex OK) or a binary operator (not regex).

**Returns TRUE (regex allowed) after:**

| Token kind | Examples | Rationale |
|------------|----------|-----------|
| nil (start of buffer) | `/regex/` | First token |
| `.leftAngle`, `.leftBrace`, `.leftParen`, `.leftSquare` | `(/regex/)`, `[/regex/]` | Opening delimiters |
| `.prefixOperator`, `.prefixAmpersand` | `-/regex/`, `&/regex/` | Prefix grammar |
| `.binaryOperator`, `.equal` | `x + /regex/`, `x = /regex/` | Binary operators |
| `.semicolon`, `.comma`, `.colon` | `x; /regex/`, `f(a, /regex/)` | Separators |
| `.infixQuestionMark` | `a ? /regex/ : b` | Ternary ? |
| `.keyword` (most) | `return /regex/`, `if /regex/` | Keywords |
| `.poundIf/Else/Elseif/Endif` | `#if true; /regex/` | Conditional compilation |

**Returns FALSE (not regex, expect binary operator) after:**

| Token kind | Examples | Rationale |
|------------|----------|-----------|
| `.postfixOperator`, `.exclamationMark`, `.postfixQuestionMark` | `foo! / 2`, `foo? / 2` | Postfix = value produced |
| `.rightAngle`, `.rightBrace`, `.rightParen`, `.rightSquare` | `f() / 2`, `a[0] / 2` | Closing delimiters = value |
| `.identifier`, `.dollarIdentifier`, `.wildcard` | `foo / bar` | Identifiers = values |
| `.floatLiteral`, `.integerLiteral` | `42 / 7` | Literals = values |
| `.keyword` (`true`, `false`, `nil`, `self`, `Self`, `super`, `Any`) | `true / x` | Expression-keywords = values |
| `.arrow`, `.ellipsis`, `.period`, `.atSign`, etc. | `-> /x/` | Non-sequencing punctuation |
| string/regex tokens | `"s" / 2` | Already in literal context |

## APUS Design: `++` and `--` Lookbehind

Instead of four separate layers, APUS uses two composable scanner annotations that subsume all four Swift checks.

### Syntax

```
++1("token" ...)                   — positive lookbehind: allow if previous token matches
--1("token" ...)                   — negative lookbehind: block if previous token matches
++2("token"), ++1("token")         — compound positive (AND within line, OR between lines)
```

- `--1(...)`: regex is **blocked** if the previous token is any of the listed tokens. Quoted items are literal token values; unquoted items are named terminal references.
- `++N(...)`: regex is **allowed** if the lookbehind matches. Overrides `--1`.
- Compound `++2(...), ++1(...)`: AND within a line (both must match), OR between lines.
- Default (token in neither list): **allowed**. This makes `--1` the primary mechanism — enumerate what to block, not what to allow.

### Evaluation order

1. Check compound `++` rules first. If any compound matches → **allow** (hard override).
2. Check `--1`. If the previous token is in the deny list → **block**.
3. Default → **allow**.

This means `++` overrides `--`, which is essential for `try!`: `"!"` is in `--1`, but `++2("try"), ++1("!")` overrides it.

### Why `--1` (blacklist) instead of `++1` (whitelist)

Swift has ~50 hard keywords that allow regex and only 9 that don't. A positive-only `++1` list requires 74 entries. A `--1` deny list requires ~25. The blacklist is three times shorter and more maintainable — adding a new keyword to Swift doesn't require updating the annotation.

### Why left-bound check is not needed

Swift's left-bound check prevents regex when `/` is physically adjacent to a non-whitespace character. In APUS with `--1`, this check is redundant:

**For tokens IN the `--1` list** (identifiers, literals, closing delimiters): `--1` already blocks regex. Left-bound adds no protection.

**For tokens NOT in `--1`** (keywords, openers, operators, separators): these tokens always precede expressions, never binary operators. Regex after them is correct regardless of spacing:
- `return/regex/` → scanned as `return <regex>` → valid parse (return a regex value)
- `(/regex/)` → scanned correctly
- `if/regex/` → scanned correctly

The GLL parser benefits from this leniency. Swift's left-bound check is a heuristic needed by a single-pass lexer; our GLL parser explores both interpretations and picks the correct one. This enables `b?/1/:/2/` to parse correctly as a ternary — something Swift's lexer rejects.

### Why `func`/`operator` falls out of `--1`

Include `"func"` and `"operator"` in the `--1` deny list. After these keywords, regex is blocked → `/^/` remains an operator name. No separate check needed.

### Why the try?/try! hack is eliminated

In Swift, `try?` produces `.postfixQuestionMark` which normally blocks regex. The hack overrides this.

In APUS, `"?"` is NOT in `--1`. After `try?`, the previous token is `?`, which is not denied. Default = allow. Regex is enabled automatically.

This works because postfix `?` in Swift (optional chaining) always requires `.`, `[`, or `(` to follow — never `/`. So `?` followed by `/` is always ternary context, never optional chaining + division.

For `try!`, postfix `!` (force unwrap) CAN be followed by `/` as division (`foo! / 2`), so `"!"` must be in `--1`. The compound rule `++2("try"), ++1("!")` overrides this: regex is allowed after `!` when `try` is two tokens back.

## Concrete Examples

### Regex IS allowed (scanner produces regex token)

```swift
// After opening delimiters — not in --1, default allow
(/regex/)                 // "(" not denied → allowed
[/regex/]                 // "[" not denied → allowed
{/regex/}                 // "{" not denied → allowed

// After assignment — not in --1
let x = /regex/           // "=" not denied → allowed

// After binary operators — not in --1
x + /regex/               // "+" not denied → allowed
x ?? /regex/              // rawOperator not denied → allowed
x == /regex/              // rawOperator not denied → allowed

// After separators — not in --1
foo(a, /regex/)           // "," not denied → allowed
foo(a: /regex/)           // ":" not denied → allowed
x; /regex/                // ";" not denied → allowed

// After ternary ? — not in --1
a ? /regex/ : b           // "?" not denied → allowed
b?/1/:/2/                 // "?" not denied → allowed — GLL finds ternary parse

// After keywords — not in --1
return /regex/            // "return" not denied → allowed
if /regex/.test(s) {}     // "if" not denied → allowed
case /regex/:             // "case" not denied → allowed

// After try?/try! — compound override or default
try? /regex/.match(s)     // "?" not denied → allowed (no override needed)
try! /regex/.match(s)     // "!" IS denied, BUT ++2("try"),++1("!") overrides → allowed

// After conditional compilation — not in --1
#if DEBUG
/regex/.match(s)          // "#if" not denied → allowed
#endif
```

### Regex is NOT allowed (scanner produces operator token)

```swift
// After identifiers — in --1
a / b / c                 // --1(rawIdentifier) → blocked → operator
foo / bar                 // --1(rawIdentifier) → blocked → operator

// After numeric literals — in --1
42 / 7                    // --1(decimalLiteral) → blocked → operator
3.14 / 2.0                // --1(decimalFloat) → blocked → operator

// After expression-keywords — in --1
true / x                  // --1("true") → blocked → operator
self / x                  // --1("self") → blocked → operator
nil / x                   // --1("nil") → blocked → operator

// After force unwrap — in --1
foo! / 2                  // --1("!") → blocked → operator
                          // ++2: prev-2 is "foo", not "try" → no override

// After closing delimiters — in --1
f() / 2                   // --1(")") → blocked → operator
arr[0] / 2                // --1("]") → blocked → operator

// After func/operator — in --1
func /^/ (x: Int) {}      // --1("func") → blocked → operator
operator /^/              // --1("operator") → blocked → operator

// After closing > — in --1 (could be generic close)
Array<Int> / 2            // --1(">") → blocked → operator
```

## Complete Scanner Annotation for Swift.apus

```apus
plainRegularExpressionLiteral - /\/(?:[^\/\\\n]|\\.)+\// .

    // ── deny list ─────────────────────────────────────────────────
    // Regex is blocked if the immediately preceding token is any of
    // the following.  Everything else defaults to allow.

    --1(
        // expression-value keywords (produce values, expect operator)
        "true" "false" "nil" "self" "Self" "super" "Any"

        // operator-declarator keywords (/^/ is an operator name)
        "func" "operator"

        // identifiers and identifier-like tokens
        rawIdentifier              // covers all identifiers and contextual keywords
        escapedIdentifier          // `keyword` used as identifier
        implicitParameterName      // $0, $1, ...
        propertyWrapperProjection  // $foo

        // numeric literals
        decimalLiteral binaryLiteral octalLiteral hexadecimalLiteral
        decimalFloat hexadecimalFloat

        // string and regex literals (value produced, expect operator)
        plainRegularExpressionLiteral extendedRegularExpressionLiteral
        // TODO: add string-closing terminals once string scanner modes are implemented

        // closing delimiters (value produced, expect operator)
        ")" "]" "}" ">"

        // postfix ! (foo!/2 is force-unwrap then divide)
        "!"

        // non-sequencing punctuation (never precede expressions)
        "->" "..." "." "@"
    )

    // ── positive override ─────────────────────────────────────────
    // Overrides --1("!") when "try" is two tokens back.
    // Needed because try! /regex/ is valid but foo! / 2 is division.
    ++2("try"), ++1("!")
```

### Token counts

| Category | Count | Tokens |
|----------|-------|--------|
| Expression-value keywords | 7 | `true` `false` `nil` `self` `Self` `super` `Any` |
| Operator-declarator keywords | 2 | `func` `operator` |
| Identifier terminals | 4 | `rawIdentifier` `escapedIdentifier` `implicitParameterName` `propertyWrapperProjection` |
| Numeric literal terminals | 6 | `decimalLiteral` `binaryLiteral` `octalLiteral` `hexadecimalLiteral` `decimalFloat` `hexadecimalFloat` |
| Regex literal terminals | 2 | `plainRegularExpressionLiteral` `extendedRegularExpressionLiteral` |
| Closing delimiters | 4 | `)` `]` `}` `>` |
| Postfix `!` | 1 | `!` |
| Punctuation | 4 | `->` `...` `.` `@` |
| **Total --1 entries** | **30** | |
| Compound override | 1 | `++2("try"), ++1("!")` |

Compared to 74 entries in a positive-only `++1` approach. The `--1` blacklist is more than twice as compact and doesn't need updating when new keywords are added to Swift.

### Implicitly allowed tokens (not in `--1`, regex enabled by default)

| Category | Examples |
|----------|----------|
| Opening delimiters | `(` `[` `{` |
| Assignment, ternary, separators | `=` `?` `,` `;` `:` |
| All single-char operators except `!` | `+` `-` `*` `/` `%` `&` `\|` `^` `~` `<` |
| Multi-char operators | `rawOperator` (`==` `!=` `&&` `\|\|` `??` ...), `dotOperator` (`.+` `.==` ...) |
| Conditional compilation | `#if` `#elseif` `#else` `#endif` |
| All hard keywords not in --1 | `return` `if` `while` `for` `case` `let` `var` `class` `struct` ... (50 keywords) |

## Comparison with Swift's Lexer

| Swift layer | Mechanism | APUS equivalent | Status |
|-------------|-----------|-----------------|--------|
| 1. Left-bound | `isLeftBound()` | Not needed | `--1` subsumes; GLL handles `b?/1/:/2/` |
| 2. func/operator | Hard-coded check | `--1("func" "operator")` | Falls out naturally |
| 3. try?/try! hack | `preferRegexOverBinaryOperator` state | `++2("try"), ++1("!")` overrides `--1("!")` | Eliminated — clean override replaces hack |
| 4. Token position | `isInRegexLiteralPosition()` switch | `--1(...)` deny list | Inverted but equivalent |

## General `++`/`--` Annotation Semantics

The `++`/`--` lookbehind system is general-purpose — not limited to regex disambiguation.

### When to use which

| Situation | Annotation | Example |
|-----------|------------|---------|
| Few tokens allow the terminal | `++1(...)` whitelist | Hypothetical: regex only after `=` and `return` |
| Few tokens block the terminal | `--1(...)` blacklist | Swift regex: block after identifiers, literals, closers |
| Exception within a block | `++N` compound override | `try!` carved out of `--1("!")` |

### Composability

- `--1` and `++` on the same terminal: `++` overrides `--1`.
- Multiple `--1` lines: OR'd (any match blocks).
- Multiple `++` compound lines: OR'd (any match allows).
- `++1(...)` without `--1`: pure whitelist (default = block).
- `--1(...)` without `++`: pure blacklist (default = allow).
- Both present: `++` checked first, then `--1`, then default allow.

## APUS Grammar Changes Required

### apus.apus meta-grammar

The `context` production after terminal definitions needs to support `++`/`--` annotations:

```apus
context     = mode | lookbehind .

lookbehind  = < lookbehindRule > .

lookbehindRule = ( "++" | "--" ) /[1-9]/ "(" < literal | identifier > ")"
              | ( "++" | "--" ) /[1-9]/ "(" < literal | identifier > ")" ","
                ( "++" | "--" ) /[1-9]/ "(" < literal | identifier > ")" .
```

### Implementation touches

| File | Change |
|------|--------|
| `ApusParser.swift` | Parse `++N(...)` and `--N(...)` annotations on terminals |
| `Grammar.swift` / `TokenPattern` | Store deny list and override list on terminal patterns |
| `Scanner.swift` | Before trying a candidate, evaluate `++`/`--` against previous token(s) |
| `Swift.apus` | Add annotations to `plainRegularExpressionLiteral` |
| `apus.apus` | Update meta-grammar for new annotation syntax |

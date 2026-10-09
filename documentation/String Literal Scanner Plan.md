# String Literal Scanner Plan

Status: implemented (2026-10-09). See "As built" at the end for the differences from the plan.

## Problem

A Swift string literal is one lexical unit: its pound count N, its form (single-line or multiline)
and its closer's indentation decide how every part of its body is lexed. APUS lexes an interpolated
literal as separate tokens instead (a Head, Parts and a Tail, with the interpolated expressions
parsed by the grammar between them). Only the Head can see N (a regex backreference inside its own
match); Parts and Tails fall back to "any number of `#`", and nothing checks indentation after the
first interpolation.

Measured holes (swiftc `-swift-version 6 -parse` and swift-syntax agree on every row):

| Rule | Example | APUS |
| --- | --- | --- |
| closer needs exactly N `#` | `##"\##(x) "#"##` (valid) | rejects: `"#` ends the body |
| closer needs exactly N `#` | `##"\##(x)"#`, `#"\#(x)"##`, `#"""⏎\#(x)⏎"""##` | accepts |
| interpolation needs exactly N `#` | `##"\##(x)\#(y)"##` | wrong tree: `\#(y)` read as interpolation |
| multiline indentation after an interpolation | `"""⏎  a \(x)⏎ b⏎  """` | accepts |
| raw escape `\#q` is invalid | `#"\#q"#` | accepts |
| `\u{…}` must be a valid scalar | `"\u{110000}"` | accepts |

Real-world reproducer: `swiftlang__swift-package-manager/Sources/Workspace/InitPackage.swift`, line
868 (an outer `##"""` literal with `\##(moduleName)` and inner `"""#` lines). TODO #1 (residual
ambiguity `interpolatedStringLiteral` vs `staticStringLiteral` in `MultilineErrorsTests.swift`) is in
the same area: after this plan the grammar no longer chooses between those two.

## Design

One scanner owns all lexical rules of a literal; the grammar keeps parsing what is grammar (the
interpolated expressions).

### Scanner

`SwiftStringLiteralScanner`, a port of the compiler's string lexer (`swiftlang/swift`
`lib/Parse/Lexer.cpp`, main as of 2026-10-08):

| Step | Compiler source |
| --- | --- |
| opener: `#` run, `"` or `"""`, multiline mode | `advanceIfCustomDelimiter` :1333, `lexStringLiteral` :1943 |
| body characters and escapes (`\` + exactly N `#`; valid `\u{…}`) | `lexCharacter` :1421 |
| interpolation extent: balanced `( )`, nested string literals, no line break in a single-line literal | `skipToEndOfInterpolatedExpression` :1542 |
| closer: `"` / `"""` + exactly N `#` | `isStringLiteralEndDelimiter` |
| indentation of every line against the closer, including lines after interpolations | `diagnoseInvalidMultilineIndents` :1771 |

It scans a whole literal from its opener and returns a **layout**: form, N, closer indentation,
and the ranges of all pieces (static segments and interpolation spans). It is a pure function of
`(input, opener position)`; the converter uses the same function.

### Terminals and grammar

The 16 builder terminals (`{plain, raw} × {single-line, multiline} × {static, Head, Part, Tail}`)
and the rules `staticStringLiteral`, `interpolatedStringLiteral`, `singleLineInterpolatedStringLiteral`
and `multilineInterpolatedStringLiteral` are replaced by:

```apus
stringLiteralToken - @builder .   // whole literal without interpolation, any form
stringHead         - @builder .   // opener … first interpolation opener `\#(` (inclusive)
stringPart         - @builder .   // `)` … next interpolation opener (inclusive)
stringTail         - @builder .   // `)` … closer (inclusive)

stringLiteral = stringLiteralToken
              | stringHead functionCallArgumentList? { stringPart functionCallArgumentList? } stringTail .
```

- `stringLiteralToken` matches when the layout at this position has no interpolation.
- `stringHead` matches from an opener to the first interpolation opener.
- `stringPart` / `stringTail` match only at a position where a layout scanned earlier in this parse
  has a piece starting, and end exactly where that piece ends.
- `availabilityStringLiteral` (no raw forms, for `@available`) becomes `>->( "#" ) stringLiteralToken`
  or a fifth, plain-only terminal (decide in step 3).
- The `@sameLine` on `singleLineInterpolatedStringLiteral` goes: the scanner already refuses a line
  break inside an interpolation of a single-line literal, as the compiler does.

### Engine hook

Builders are global, stateless `Regex` values today. `stringPart` / `stringTail` need the layouts that
`stringHead` computed in the same parse. Hook: a builder registry entry may be a factory that makes a
per-parse matcher; `OnDemandLiteralLexer` creates one instance per parse (sub-parsers get their own).
The four string terminals share one instance and its layout cache, keyed by opener position. In GLL a
Part is only tried after its Head was scanned on that path, so the layout exists when it is needed.

The scanner is a `CustomConsumingRegexComponent` (verified: matched through
`Substring.prefixMatch`, it receives the whole base string, so it can also look before its start).

### Converter

`convertStringLiteral` / `convertInterpolatedStringLiteral` (around `GenerateSwiftSyntaxAST.swift:8456`,
about 450 lines) choose the form from which of 16 terminals matched and re-derive delimiters and
indentation from token texts. After the change they read the layout at the Head position (N, quotes,
closer indentation, segment texts) and only build the `StringLiteralExprSyntax` nodes.

## Steps

Each step ends with the full test suite green (except known unrelated failures) before the next starts.

1. **Fixture table.** Add accept/reject fixtures for every row of the table above, the
   `InitPackage.swift` reduction, and controls (each form, empty interpolation `"\()"`, nested string
   `"\("a")"`, escaped newline, CRLF, tabs in multiline, empty multiline). Record the current results as
   the baseline. No code change.
2. **Scanner as a library function.** `SwiftStringLiteralScanner.layout(in:at:)` plus unit tests
   against `swiftc -parse` on the fixture table. Not wired into the grammar.
3. **Engine hook.** Per-parse builder matchers (factory in the registry, instances in the lexer). Add a
   core-grammar test with a tiny two-terminal grammar that shares state. Decide the `@available` form.
4. **Cutover.** New terminals and the one `stringLiteral` rule in `Swift.apus`; the converter reads the
   layout. Keep the old builders in the library until step 6, so a revert is a grammar edit.
5. **Validation.** Full suite; corpus slice A/B against the pre-change probe
   (`~/Library/Caches/ApusApusCorpus/oracle-ab`, 1,593 files); full crawl; replay the string fuzzer
   artifacts; recheck TODO #1.
6. **Cleanup.** Delete the 16 old builders and their comments, `tookMultilineStringForm`, and the
   `@sameLine` annotation on strings. If nothing else uses the deep form of `@sameLine`, remove it from
   `SameLineSpanRule` and `apus.md` (only `@sameLineOutsideBrackets` would remain).

## Risks and open points

- **Interpolation extent.** The scanner decides where an interpolation ends; the grammar must parse
  exactly that span. This is the compiler's model, so a disagreement is also a disagreement with
  swiftc. Known consequence: the compiler's skip does not understand regex literals or comments
  inside an interpolation, so a `)` in a regex there ends the interpolation, in APUS as in swiftc.
- **Per-parse builder state** is a new engine concept. Keep it limited to builders that ask for it.
- **swift-syntax segments.** The converter must produce swift-syntax's segment split (for example where
  `\` line continuations and indentation are attached); check against `StringLiterals.swift` in
  swift-syntax while writing step 4.
- **Performance.** One layout scan per literal opener, cached; expect no slowdown, measure in step 5.

## As built

- **Scanner.** `SwiftStringLiteralScanner.layout(in:at:)` and `SwiftStringLiteralLayout` in
  `SwiftGrammarRegexLibrary.swift`. Rules found while porting, beyond the table above: a tab is
  invalid in a single-line literal; `\u{…}` takes 1–8 digits and no surrogates; every non-empty
  line after a line break must start with the closer's indent, including lines inside an
  interpolation and lines with only spaces; in an interpolation `'` also delimits a nested string.
- **Engine hook.** A `@builder` terminal listed in `ApusRegexLibrary.scannedTerminals` is matched
  by an `ApusTokenScanner` object. `MessageParser.prepareInput` makes one per factory key per input
  (sub-parsers included) and serves it through the lexer's one-token recogniser slot
  (`lexicalTokenRecognisers`), so the lexer itself did not change. A pure backward search from a
  part to its opener was rejected: in `"""⏎ say "\(x)" ⏎"""` the inner `"` is a valid single-line
  opener whose interpolation also closes at the same `)`.
- **Grammar.** Five terminals: `stringLiteralToken`, `plainStringLiteralToken` (the `@available`
  form), `stringHead`, `stringPart`, `stringTail`. The rules `staticStringLiteral =
  stringLiteralToken` and `interpolatedStringLiteral = stringHead … stringTail` stay, because
  attribute arguments and `filePath` accept only a static literal. `nonWordToken` now reads
  `"#" >-> ( "#" "\"" )`.
- **Converter.** `stringLiteralLayout(from:to:)` gives the form, the `#` count and the closer
  indent; `tookMultilineStringForm` is gone. The multiline helpers now test line breaks against
  `lineBreakCharacters` (`"\r\n"` is one `Character`, so tests for `"\n"` alone missed CRLF lines)
  and share `multilineContentText` / `strippingIndent`.
- **`@sameLine` removed.** The deep form had no other user. `@sameLineOutsideBrackets` remains.
- **Results.** All 51 fixtures agree with swiftc and swift-syntax's tree (`ApusApusTests`
  fuzz-harvest suites: 8 accepts and 10 rejects added). `MultilineErrorsTests.swift` (TODO #1)
  parses with no residual ambiguity and the same tree as swift-syntax. Corpus slice (1,593 files):
  no status change, same time.

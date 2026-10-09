//
//  SwiftGrammarRegexLibrary.swift
//  ApusApus
//
//  RegexBuilder definitions for `Swift.apus` regex terminals declared with `@builder`.
//
//  Naming convention: a terminal written in the grammar as
//
//      identifier - @builder .
//
//  resolves its scanner regex to `ApusRegexLibrary.patterns["identifier"]` — the
//  dictionary KEY equals the terminal name. (`@builder(otherKey)` overrides the key
//  when the Swift symbol should differ from the terminal name.)
//
//  Why this exists: flat `/…/` regex string literals in the apus grammar cannot reference each other,
//  so large Unicode character classes (the identifier / operator ranges) are
//  copy-pasted verbatim across several terminals. Defining them ONCE here as
//  reusable `CharacterClass` components and composing terminals from them removes
//  that duplication — and lets us state the (near-)exact TSPL code-point ranges.
//
//  Each composed terminal is matched under `.matchingSemantics(.unicodeScalar)` so
//  the code-point ranges compare per Unicode scalar, not per grapheme — the
//  faithful reading of TSPL's lexical structure (e.g. `⚽️` = U+26BD op-head +
//  U+FE0F op-continuation, two scalars, one operator token).
//
//  NOTE on `Character` range bounds: a range bound that is *canonically*
//  decomposable (e.g. U+F900 豈 → U+8C48) is rejected by Swift's regex engine as
//  an "invalid bound for character class range" in EVERY form (string, literal,
//  `CharacterClass` scalar or grapheme). The identifier ranges below work around
//  the one such bound (F900 → F8FF) plus carry two other deviations from
//  TSPL — all documented at `identifierHead`.
//

import RegexBuilder

enum ApusRegexLibrary {

    // ── Identifier code-point classes ───────────────────────────────────────────
    // Follows TSPL `identifier-head` / `identifier-character` with THREE deliberate
    // deviations (this is the tested-working set; the "faithful" variants either
    // crash or aren't expressible as regex character classes):
    //
    //   1. `F8FF` as the CJK-compat block's lower bound, with U+F8FF then SUBTRACTED.
    //      TSPL starts at U+F900, but U+F900 (豈) is canonically decomposable → an
    //      invalid range bound (the regex engine traps at match time), and so is every
    //      other scalar at the start of that block (the CJK compatibility ideographs
    //      decompose by design), so there is no safe bound to move the range to.
    //      U+F8FF (last Private-Use char) IS a valid bound, so the range starts there
    //      and the one over-included scalar is removed with `.subtracting(.anyOf(…))`
    //      — membership, not a range bound, the same trick
    //      `forbiddenRawIdentifierWhitespace` uses for U+2000/U+2001.
    //      This matters: `testIdentifiers6#1` is U+F8FF + `()`, which swift rejects.
    //   2. `1681…1DBF` (head) / `1681…1FFF` (continuation) merged across the TSPL
    //      gap `…180D` / `180F…`. Consequence: WRONGLY INCLUDES U+180E (Mongolian
    //      vowel separator), which TSPL excludes.
    //   3. Upper bound `FFF8` instead of TSPL's `FFFD`. swift-syntax
    //      (UnicodeScalarExtensions.swift) uses `FE47–FFF8` — U+FFF9–U+FFFD are
    //      excluded (FFF9 = Interlinear Annotation Anchor, FFFC = Object Replacement
    //      Character, FFFD = Replacement Character, etc.).
    //
    // `_` is folded into the head; bare `_` is the wildcard, excluded at
    // name-consuming sites in Swift.apus via `---("_")`. `$` is a swift-syntax/compiler
    // extension over TSPL: it is an ASCII continuation only, never a head. Unlike coarse `\p{So}`,
    // these do NOT sweep in arbitrary BMP symbols — U+26BD ⚽ (∈ 2500–2775) is an
    // operator-head, not an identifier char, which is what disjoins the two classes.
    static let identifierHead = CharacterClass(
        "A"..."Z", "a"..."z", "_"..."_",
        "\u{00A8}"..."\u{00A8}", "\u{00AA}"..."\u{00AA}", "\u{00AD}"..."\u{00AD}", "\u{00AF}"..."\u{00AF}",
        "\u{00B2}"..."\u{00B5}", "\u{00B7}"..."\u{00BA}", "\u{00BC}"..."\u{00BE}",
        "\u{00C0}"..."\u{00D6}", "\u{00D8}"..."\u{00F6}", "\u{00F8}"..."\u{02FF}",
        "\u{0370}"..."\u{167F}", "\u{1681}"..."\u{1DBF}", "\u{1E00}"..."\u{1FFF}",
        "\u{200B}"..."\u{200D}", "\u{202A}"..."\u{202E}", "\u{203F}"..."\u{2040}",
        "\u{2054}"..."\u{2054}", "\u{2060}"..."\u{20CF}", "\u{2100}"..."\u{218F}",
        "\u{2460}"..."\u{24FF}", "\u{2776}"..."\u{2793}", "\u{2C00}"..."\u{2DFF}",
        "\u{2E80}"..."\u{2FFF}", "\u{3004}"..."\u{3007}", "\u{3021}"..."\u{302F}",
        "\u{3031}"..."\u{D7FF}", "\u{F8FF}"..."\u{FD3D}", "\u{FD40}"..."\u{FDCF}",  // F8FF instead of F900 (an invalid range bound)
        "\u{FDF0}"..."\u{FE1F}", "\u{FE30}"..."\u{FE44}", "\u{FE47}"..."\u{FFF8}",  // swift-syntax uses FE47–FFF8 (TSPL says FE47–FFFD; FFF9–FFFD excluded)
        "\u{10000}"..."\u{1FFFD}", "\u{20000}"..."\u{2FFFD}", "\u{30000}"..."\u{3FFFD}",
        "\u{40000}"..."\u{4FFFD}", "\u{50000}"..."\u{5FFFD}", "\u{60000}"..."\u{6FFFD}",
        "\u{70000}"..."\u{7FFFD}", "\u{80000}"..."\u{8FFFD}", "\u{90000}"..."\u{9FFFD}",
        "\u{A0000}"..."\u{AFFFD}", "\u{B0000}"..."\u{BFFFD}", "\u{C0000}"..."\u{CFFFD}",
        "\u{D0000}"..."\u{DFFFD}", "\u{E0000}"..."\u{EFFFD}"
    ).subtracting(.anyOf("\u{F8FF}"))   // U+F8FF is a PUA code point, not an identifier char

    static let identifierCharacter = CharacterClass(
        "A"..."Z", "a"..."z", "0"..."9", "_"..."_", "$"..."$",
        "\u{00A8}"..."\u{00A8}", "\u{00AA}"..."\u{00AA}", "\u{00AD}"..."\u{00AD}", "\u{00AF}"..."\u{00AF}",
        "\u{00B2}"..."\u{00B5}", "\u{00B7}"..."\u{00BA}", "\u{00BC}"..."\u{00BE}",
        "\u{00C0}"..."\u{00D6}", "\u{00D8}"..."\u{00F6}", "\u{00F8}"..."\u{167F}",
        "\u{1681}"..."\u{1FFF}", "\u{200B}"..."\u{200D}", "\u{202A}"..."\u{202E}",
        "\u{203F}"..."\u{2040}", "\u{2054}"..."\u{2054}", "\u{2060}"..."\u{218F}",
        "\u{2460}"..."\u{24FF}", "\u{2776}"..."\u{2793}", "\u{2C00}"..."\u{2DFF}",
        "\u{2E80}"..."\u{2FFF}", "\u{3004}"..."\u{3007}", "\u{3021}"..."\u{302F}",
        "\u{3031}"..."\u{D7FF}", "\u{F8FF}"..."\u{FD3D}", "\u{FD40}"..."\u{FDCF}",  // F8FF instead of F900 (an invalid range bound)
        "\u{FDF0}"..."\u{FE44}", "\u{FE47}"..."\u{FFF8}",                           // swift-syntax uses FE47–FFF8
        "\u{10000}"..."\u{1FFFD}", "\u{20000}"..."\u{2FFFD}", "\u{30000}"..."\u{3FFFD}",
        "\u{40000}"..."\u{4FFFD}", "\u{50000}"..."\u{5FFFD}", "\u{60000}"..."\u{6FFFD}",
        "\u{70000}"..."\u{7FFFD}", "\u{80000}"..."\u{8FFFD}", "\u{90000}"..."\u{9FFFD}",
        "\u{A0000}"..."\u{AFFFD}", "\u{B0000}"..."\u{BFFFD}", "\u{C0000}"..."\u{CFFFD}",
        "\u{D0000}"..."\u{DFFFD}", "\u{E0000}"..."\u{EFFFD}"
    ).subtracting(.anyOf("\u{F8FF}"))   // U+F8FF is a PUA code point, not an identifier char

    // ── Operator code-point classes (exact TSPL) ────────────────────────────────
    // TSPL `operator-head` / `operator-character`, exact (no decomposable range
    // bounds here, so no workaround needed). Two subtleties:
    //  • `= ! ? &` ARE operator-heads in the grammar, but Swift reserves them when
    //    SOLO (`=` assign, `!`/`?` postfix, `&` inout/bitwise); they only form an
    //    operator WITH ≥1 continuation. So the "stands alone" head subtracts them
    //    (`operatorHeadStandalone`); they survive via `operatorSpecial` + continuation.
    //  • `3021–302F` is NOT in `operator-head` but IS kept in `operator-character` —
    //    a historical inclusion swift-syntax retains for source compatibility (those
    //    ideographs may CONTINUE but not START an operator).
    static let operatorHead = CharacterClass(
        "/"..."/", "="..."=", "-"..."-", "+"..."+", "!"..."!", "*"..."*", "%"..."%",
        "<"..."<", ">"...">", "&"..."&", "|"..."|", "^"..."^", "~"..."~", "?"..."?",
        "\u{00A1}"..."\u{00A7}", "\u{00A9}"..."\u{00A9}", "\u{00AB}"..."\u{00AC}",
        "\u{00AE}"..."\u{00AE}", "\u{00B0}"..."\u{00B1}", "\u{00B6}"..."\u{00B6}",
        "\u{00BB}"..."\u{00BB}", "\u{00BF}"..."\u{00BF}", "\u{00D7}"..."\u{00D7}",
        "\u{00F7}"..."\u{00F7}", "\u{2016}"..."\u{2017}", "\u{2020}"..."\u{2027}",
        "\u{2030}"..."\u{203E}", "\u{2041}"..."\u{2053}", "\u{2055}"..."\u{205E}",
        "\u{2190}"..."\u{23FF}", "\u{2500}"..."\u{2775}", "\u{2794}"..."\u{2BFF}",
        "\u{2E00}"..."\u{2E7F}", "\u{3001}"..."\u{3003}", "\u{3008}"..."\u{3020}",
        "\u{3030}"..."\u{3030}"
    )

    static let operatorCharacter = CharacterClass(
        "/"..."/", "="..."=", "-"..."-", "+"..."+", "!"..."!", "*"..."*", "%"..."%",
        "<"..."<", ">"...">", "&"..."&", "|"..."|", "^"..."^", "~"..."~", "?"..."?",
        "\u{00A1}"..."\u{00A7}", "\u{00A9}"..."\u{00A9}", "\u{00AB}"..."\u{00AC}",
        "\u{00AE}"..."\u{00AE}", "\u{00B0}"..."\u{00B1}", "\u{00B6}"..."\u{00B6}",
        "\u{00BB}"..."\u{00BB}", "\u{00BF}"..."\u{00BF}", "\u{00D7}"..."\u{00D7}",
        "\u{00F7}"..."\u{00F7}", "\u{2016}"..."\u{2017}", "\u{2020}"..."\u{2027}",
        "\u{2030}"..."\u{203E}", "\u{2041}"..."\u{2053}", "\u{2055}"..."\u{205E}",
        "\u{2190}"..."\u{23FF}", "\u{2500}"..."\u{2775}", "\u{2794}"..."\u{2BFF}",
        "\u{2E00}"..."\u{2E7F}", "\u{3001}"..."\u{3003}", "\u{3008}"..."\u{3020}",
        "\u{3021}"..."\u{302F}", "\u{3030}"..."\u{3030}",   // 3021–302F: swift-syntax compat (continuation only)
        "\u{0300}"..."\u{036F}", "\u{1DC0}"..."\u{1DFF}", "\u{20D0}"..."\u{20FF}",
        "\u{FE00}"..."\u{FE0F}", "\u{FE20}"..."\u{FE2F}", "\u{E0100}"..."\u{E01EF}"
    )

    /// Operator-head chars that may stand ALONE (= TSPL head minus the solo-reserved
    /// `= ! ? &`). Paired with `operatorSpecial` for the `special(cont)+` arm.
    static let operatorHeadStandalone = operatorHead.subtracting(.anyOf("=!?&"))
    static let operatorSpecial = CharacterClass.anyOf("=!?&")

    /// Dot-operator continuation = TSPL `dot-operator-character` (`. | operator-character`),
    /// which includes `!`/`?`. See Swift.apus operator dev 3 for why `?`/`!` are admitted and
    /// keypath dev 6 / `Ambiguity.md` §3.2 for the keyPathDot coexistence.
    static let dotOperatorCharacter = CharacterClass(operatorCharacter, .anyOf("."))

    // ── Raw-identifier scalar classes (mirrors swift-syntax UnicodeScalarExtensions) ──
    // Used to assemble `escapedIdentifier` from named building blocks instead of a
    // raw regex string literal.

    /// swift-syntax: `isForbiddenRawIdentifierWhitespace`
    /// These code points generate `.rawIdentifierCannotContainCharacter` — our scanner
    /// simply excludes them so the terminal never matches.
    ///
    /// NOTE: U+2000 and U+2001 are *canonically decomposable* (→ U+2002 / U+2003), so
    /// they trap Swift's regex engine at match time if used as RANGE BOUNDS (see the
    /// header note on `identifierHead`). They are given via `.anyOf` (membership, not a
    /// range bound) — the safe range starts at U+2002.
    static let forbiddenRawIdentifierWhitespace = CharacterClass(
        "\u{0009}"..."\u{000D}",   // HT, LF, VT, FF, CR
        "\u{0085}"..."\u{0085}",   // NEL
        "\u{00A0}"..."\u{00A0}",   // NBSP
        "\u{1680}"..."\u{1680}",
        .anyOf("\u{2000}\u{2001}"), // decomposable — NOT usable as range bounds
        "\u{2002}"..."\u{200A}",
        "\u{2028}"..."\u{2029}",
        "\u{202F}"..."\u{202F}",
        "\u{205F}"..."\u{205F}",
        "\u{3000}"..."\u{3000}"
    )

    /// swift-syntax: `isPermittedRawIdentifierWhitespace` — U+0020, U+200E, U+200F.
    /// Allowed individually, but an identifier whose ENTIRE content is these chars is
    /// rejected via `NegativeLookahead` in `escapedIdentifier`.
    static let permittedRawIdentifierWhitespace = CharacterClass(
        "\u{0020}"..."\u{0020}",
        "\u{200E}"..."\u{200F}"
    )

    /// swift-syntax: `!isPrintableASCII` — U+0000–001F (controls) + U+007F (DEL).
    /// Generates `.unprintableAsciiCharacter` → hasError = true.
    static let unprintableASCII = CharacterClass(
        "\u{0000}"..."\u{001F}",
        "\u{007F}"..."\u{007F}"
    )

    /// Valid backtick-identifier content: any code point that does NOT generate an
    /// immediate lexing error — not backtick, not backslash, not forbidden whitespace,
    /// not unprintable ASCII.
    static let validRawIdentifierContent = CharacterClass(
        .anyOf("`\\"),
        unprintableASCII,
        forbiddenRawIdentifierWhitespace
    ).inverted

    // ── Terminals ───────────────────────────────────────────────────────────────
    // `.matchingSemantics(.unicodeScalar)` applied directly on each composed regex.

    /// `identifier` — head then zero-or-more continuation chars.
    static let identifier = Regex {
        identifierHead
        ZeroOrMore { identifierCharacter }
    }.matchingSemantics(.unicodeScalar)

    /// Operator characters stop before Swift comment openers. `//` and `/*` are trivia starts even
    /// when a previous operator character was already scanned (`x*//` is `x*` + line comment, not a
    /// postfix operator named `*//`).
    static let operatorCharacterBeforeComment = Regex {
        NegativeLookahead {
            ChoiceOf {
                "//"
                "/*"
            }
        }
        operatorCharacter
    }

    static let dotOperatorCharacterBeforeComment = Regex {
        NegativeLookahead {
            ChoiceOf {
                "//"
                "/*"
            }
        }
        dotOperatorCharacter
    }

    /// Shared operator body — `(headStandalone)(char)* | special(char)+`. Carries
    /// `.unicodeScalar` semantics itself, so every consumer matches per scalar (the
    /// `⚽️` = U+26BD + U+FE0F case) without having to re-apply it.
    static let operatorBody = Regex {
        ChoiceOf {
            Regex {
                NegativeLookahead {
                    ChoiceOf {
                        "//"
                        "/*"
                    }
                }
                operatorHeadStandalone
                ZeroOrMore { operatorCharacterBeforeComment }
            }
            Regex {
                operatorSpecial
                OneOrMore { operatorCharacterBeforeComment }
            }
        }
    }.matchingSemantics(.unicodeScalar)

    /// `operatorToken` / `operatorName` — the operator body (already scalar-semantic)
    /// (Swift.apus operator dev 1: one greedy `@literalMunch` token).
    static let operatorToken = operatorBody

    /// `postfixOperatorToken` — operator body that may not BEGIN with `!`/`?`
    /// (Swift.apus operator dev 4: `x!!` is two force-unwraps, not a `!!` operator).
    static let postfixOperatorToken = Regex {
        NegativeLookahead { CharacterClass.anyOf("!?") }
        notExactlyArrow
        operatorBody
    }.matchingSemantics(.unicodeScalar)

    /// Rejects the EXACT token `->` while leaving longer operators that merely start with it
    /// (`-->`, `->>`) alone — the inner lookahead requires a further operator character.
    ///
    /// `->` is punctuation in swift, never an operator: it is reachable only through
    /// `ArrowExprSyntax` (`ExprNodes.swift:71`). Keeping it out of the operator terminals makes
    /// `arrowExpr` the single source of the arrow here too, which is what lets `typeEffectSpecifiers`
    /// be optional exactly as swift declares it.
    static let notExactlyArrow = NegativeLookahead {
        "->"
        NegativeLookahead { operatorCharacter }
    }

    /// Operator body that is not exactly `->`. Used for `operator` (prefix and spaced infix).
    static let nonArrowOperatorToken = Regex {
        notExactlyArrow
        operatorBody
    }.matchingSemantics(.unicodeScalar)

    /// `functionNameOperator` — same body as `nonArrowOperatorToken` (`func ->(a: Int, b: Int) {}`
    /// errors: "expected identifier in function"), but a DISTINCT terminal because it needs a
    /// different `@preempt`: the function-name position must yield the generic `<` back
    /// (`func %%%%<T, U>`), while the expression position must yield to a regex opener.
    /// `@preempt` takes ONE (start, construct) pair per terminal, so the two cannot share one.
    static let functionNameOperator = Regex {
        notExactlyArrow
        operatorBody
    }.matchingSemantics(.unicodeScalar)

    /// `dotOperator` — a `.`-led operator (`...`, `..<`, `.?.`, `.?`, `.!`, `.??`).
    ///
    /// A trailing `?`/`!` run is KEPT, not split off as postfix. The old rule ("may not END in
    /// `?`/`!`", via a `dotOperatorCharacterNoReserved` final character) was wrong in BOTH
    /// positions, measured 2026-09-23 against swift-syntax:
    ///
    ///     let v = x.?         →  PostfixOperatorExpr(operator: postfixOperator(".?"))
    ///     let v = x.!         →  postfixOperator(".!")
    ///     let v = x.??        →  postfixOperator(".??")
    ///     let v = x.?.        →  postfixOperator(".?.")
    ///     let v = a .? b      →  BinaryOperatorExpr(operator: binaryOperator(".?"))
    ///     let v = \Foo.?.?[0] →  …, binaryOperator(".?"), ArrayExpr
    ///
    /// so ApusApus rejected `x.?`, `f(x.?)` and `a .? b` alike. Relaxing the terminal itself (rather
    /// than adding a second one for the postfix position) keeps ONE operator token, which is what
    /// `@literalMunch` wants: two terminals matching the same span would be an ambiguity.
    ///
    /// Munch hazard this creates, worth knowing about: a LITERAL `"."` in a lookaround operand set
    /// is now suppressed wherever `.?` matches, because munch prefers the longer token. The
    /// munch-exempt regex `keyPathDot` is the antidote and is spelled beside `"."` where it matters
    /// (`genericArgumentClause`'s follow set).
    static let dotOperator = Regex {
        "."
        OneOrMore { dotOperatorCharacterBeforeComment }
    }.matchingSemantics(.unicodeScalar)

    /// `poundName` — `#` followed by an identifier (N1518 ranges, same as `identifier`).
    /// Swift-syntax lexes `#macroName` as two tokens (`.pound` + `.identifier`); we
    /// combine them into one scanner terminal. Character classes are identical to
    /// `identifierHead`/`identifierCharacter`.
    static let poundName = Regex {
        "#"
        identifierHead
        ZeroOrMore { identifierCharacter }
    }.matchingSemantics(.unicodeScalar)

    /// `propertyWrapperProjection` — `$` + digits* + one non-digit identChar + identChar*.
    /// Mirrors `lexDollarIdentifier` in swift-syntax: only the `!isAllDigits` path
    /// (i.e. at least one non-digit continuation char) yields a projection identifier.
    /// `$0`, `$1` etc (all-digit) are closure shorthand args, not projections.
    static let propertyWrapperProjection = Regex {
        "$"
        ZeroOrMore { CharacterClass("0"..."9") }
        identifierCharacter.subtracting(.anyOf("0123456789"))
        ZeroOrMore { identifierCharacter }
    }.matchingSemantics(.unicodeScalar)

    /// `escapedIdentifier` — backtick-delimited identifier.
    /// Rejects two cases that swift-syntax (lexEscapedIdentifier) marks hasError:
    ///   1. Pure-operator content: first char ∈ operatorHead, all remaining ∈ operatorCharacter
    ///   2. All-whitespace content: every char ∈ permittedRawIdentifierWhitespace
    static let escapedIdentifier = Regex {
        "`"
        NegativeLookahead {
            One(operatorHead)
            ZeroOrMore { operatorCharacter }
            "`"
        }
        NegativeLookahead {
            OneOrMore { permittedRawIdentifierWhitespace }
            "`"
        }
        OneOrMore { validRawIdentifierContent }
        "`"
    }.matchingSemantics(.unicodeScalar)

    // String literals are lexed by `SwiftStringLiteralScanner` (end of this file).

    // ── Extended regex literal `#/…/#` ──────────────────────────────────────────

    /// Swift's line terminators — CRLF first, so it is consumed as a unit. Deliberately
    /// NOT `CharacterClass.newlineSequence`, which also matches U+000B/U+000C/U+0085/
    /// U+2028/U+2029; those are not line terminators for Swift's lexer.
    static let lineBreak = ChoiceOf {
        "\r\n"
        "\n"
        "\r"
    }

    static let poundRun = OneOrMore { "#" }

    // TWO MODES, probe-confirmed (2026-08-30), exactly parallel to the multiline strings:
    //   `#/a/#`      → ok          `#/a⏎b/#`   → "expected '/#' to end regex literal"
    //   `#/⏎a⏎/#`    → ok          `#/\⏎/#`    → same error  (testRegexParseError17)
    //   `#/⏎␠␠a⏎␠␠/#` → ok
    // i.e. a line break IMMEDIATELY after `#/` selects the multi-line form (body may span lines);
    // otherwise the body may contain no newline at all. The previous flat regex allowed newlines
    // unconditionally, so it accepted the single-line form spread over two lines.
    //
    // Extended regexes do NOT process escapes — `\` is ordinary content and only `/` + the matching
    // pound run closes the literal, which is why the single-line body admits a `/` that is not
    // followed by the delimiter.
    static let extendedRegexPoundDelimiter = Reference(Substring.self)
    static let extendedRegularExpressionLiteral = Regex {
        Capture(poundRun, as: extendedRegexPoundDelimiter)
        "/"
        ChoiceOf {
            Regex {                                     // multi-line: `#/` then a line break
                lineBreak
                ZeroOrMore(.reluctant) { CharacterClass.any }
            }
            ZeroOrMore(.reluctant) {                    // single-line: no newline anywhere
                ChoiceOf {
                    CharacterClass.anyOf("/\r\n").inverted
                    Regex {
                        "/"
                        NegativeLookahead { extendedRegexPoundDelimiter }
                    }
                }
            }
        }
        "/"
        extendedRegexPoundDelimiter
    }.matchingSemantics(.unicodeScalar)

    /// `regexLiteralToken` — a plain slash-delimited regex literal.
    ///
    /// The slash/operator decision is still made by the grammar (`plainRegularExpressionLiteral`
    /// and operator preemption). Once a slash is known to open a regex, the lexer owns the rest of
    /// the literal: escapes, character classes and the first unescaped closing slash are lexical
    /// extent rules, not recursive grammar structure. That keeps unmatched regex parentheses such
    /// as `/)/` out of the parser's ambiguity machinery; the regex engine diagnoses body syntax
    /// later, just as the Swift compiler does.
    struct PlainRegexLiteral: CustomConsumingRegexComponent {
        typealias RegexOutput = Substring

        func consuming(_ input: String, startingAt index: String.Index, in bounds: Range<String.Index>) throws -> (upperBound: String.Index, output: Substring)? {
            guard bounds.contains(index), input[index] == "/" else { return nil }

            var i = input.index(after: index)
            guard i < bounds.upperBound else { return nil }
            guard input[i] != "/", input[i] != "*" else { return nil }
            guard input[i] != " ", input[i] != "\t", input[i] != "\n", input[i] != "\r" else { return nil }

            var lastWasSpace = false
            var sawBodyItem = false
            var parenDepth = 0
            while i < bounds.upperBound {
                switch input[i] {
                case "/":
                    guard !lastWasSpace else { return nil }
                    let end = input.index(after: i)
                    guard end == bounds.upperBound || (input[end] != "/" && input[end] != "*") else { return nil }
                    return (end, input[index..<end])

                case "\\":
                    i = input.index(after: i)
                    guard i < bounds.upperBound else { return nil }
                    guard input[i] != "\t", input[i] != "\n", input[i] != "\r" else { return nil }
                    i = input.index(after: i)
                    lastWasSpace = false
                    sawBodyItem = true

                case "[":
                    let next = input.index(after: i)
                    guard next < bounds.upperBound, input[next] != "]" else { return nil }
                    if let end = scanCharacterClass(input, from: i, in: bounds) {
                        i = end
                    } else {
                        i = next
                    }
                    lastWasSpace = false
                    sawBodyItem = true

                case "(":
                    i = input.index(after: i)
                    parenDepth += 1
                    lastWasSpace = false
                    sawBodyItem = true

                case ")":
                    if !sawBodyItem {
                        let next = input.index(after: i)
                        guard next < bounds.upperBound, input[next] == "/" else { return nil }
                    } else {
                        guard parenDepth > 0 else { return nil }
                        parenDepth -= 1
                    }
                    i = input.index(after: i)
                    lastWasSpace = false
                    sawBodyItem = true

                case " ":
                    i = input.index(after: i)
                    lastWasSpace = true
                    sawBodyItem = true

                case "\t", "\n", "\r":
                    return nil

                default:
                    i = input.index(after: i)
                    lastWasSpace = false
                    sawBodyItem = true
                }
            }
            return nil
        }

        private func scanCharacterClass(_ input: String, from start: String.Index, in bounds: Range<String.Index>) -> String.Index? {
            var i = input.index(after: start)
            guard i < bounds.upperBound, input[i] != "]" else { return nil }

            while i < bounds.upperBound {
                switch input[i] {
                case "]":
                    return input.index(after: i)

                case "\\":
                    i = input.index(after: i)
                    guard i < bounds.upperBound else { return nil }
                    guard input[i] != "\t", input[i] != "\n", input[i] != "\r" else { return nil }
                    i = input.index(after: i)

                case "\t", "\n", "\r":
                    return nil

                default:
                    i = input.index(after: i)
                }
            }
            return nil
        }
    }

    static let regexLiteralToken = Regex {
        PlainRegexLiteral()
    }.matchingSemantics(.unicodeScalar)

    // ── Parse-scoped scanners ───────────────────────────────────────────────────
    //
    // A `@builder` terminal listed in `scannedTerminals` is matched by a scanner object instead of a
    // stateless `Regex`. The parser makes one scanner per factory key per parse (`MessageParser
    // .prepareInput`), so terminals with the same key share state: a string `stringPart` only matches
    // where a `stringHead` scanned earlier in this parse has a piece.

    /// Terminal name → factory key in `scannerFactories`.
    static let scannedTerminals: [String: String] = [
        "stringLiteralToken":      "swiftStringLiteral",
        "plainStringLiteralToken": "swiftStringLiteral",
        "stringHead":              "swiftStringLiteral",
        "stringPart":              "swiftStringLiteral",
        "stringTail":              "swiftStringLiteral",
    ]

    static let scannerFactories: [String: () -> any ApusTokenScanner] = [
        "swiftStringLiteral": { SwiftStringLiteralTokens() },
    ]

    // ── Registry (key == `.apus` terminal name) ─────────────────────────────────
    static let patterns: [String: Regex<AnyRegexOutput>] = [
        "identifier":                  Regex<AnyRegexOutput>(identifier.regex),
        "operatorName":                Regex<AnyRegexOutput>(operatorToken.regex),
        "postfixOperatorToken":        Regex<AnyRegexOutput>(postfixOperatorToken.regex),
        "nonArrowOperatorToken":       Regex<AnyRegexOutput>(nonArrowOperatorToken.regex),
        "functionNameOperator":        Regex<AnyRegexOutput>(functionNameOperator.regex),
        "dotOperator":                 Regex<AnyRegexOutput>(dotOperator.regex),
        "poundName":                   Regex<AnyRegexOutput>(poundName.regex),
        "propertyWrapperProjection":   Regex<AnyRegexOutput>(propertyWrapperProjection.regex),
        "escapedIdentifier":           Regex<AnyRegexOutput>(escapedIdentifier.regex),
        "regexLiteralToken":           Regex<AnyRegexOutput>(regexLiteralToken.regex),
        "extendedRegularExpressionLiteral": Regex<AnyRegexOutput>(extendedRegularExpressionLiteral.regex),
    ]
}

// MARK: - Parse-scoped token scanners

/// A `@builder` terminal matcher with state that lives for one parse (see
/// `ApusRegexLibrary.scannedTerminals`). Not thread-safe: each parser owns its instances.
protocol ApusTokenScanner: AnyObject {
    /// End of the token `terminal` that starts exactly at `start`, or nil when it does not match.
    func match(terminal: String, in input: String, at start: String.Index) -> String.Index?
}

// MARK: - Swift string literals

/// The lexical layout of one Swift string literal: what the compiler's lexer knows about it.
///
/// The parser lexes an interpolated literal as separate tokens (a head, parts and a tail, with the
/// interpolated expressions parsed by the grammar in between). The layout ties them together: it is
/// computed once from the opener, so every token of the literal sees the same pound count, form and
/// closer indentation.
struct SwiftStringLiteralLayout: Equatable {
    struct Interpolation: Equatable {
        /// The `\` that starts `\#(`.
        let backslash: String.Index
        /// The `(` of `\#(`.
        let openParen: String.Index
        /// The `)` that ends the interpolation.
        let closeParen: String.Index
    }

    /// The first `#`, or the opening quote when there are none.
    let start: String.Index
    /// After the opening quote(s).
    let contentStart: String.Index
    /// The first closing quote.
    let contentEnd: String.Index
    /// After the closing delimiter.
    let end: String.Index
    /// N: the number of `#` on each side.
    let poundCount: Int
    let isMultiline: Bool
    let interpolations: [Interpolation]
    /// Multiline only: the whitespace before the closing quotes, which every line must start with.
    /// Empty for single-line literals.
    let closerIndent: Range<String.Index>

    /// End of the head token: after the `(` of the first interpolation.
    func headEnd(in input: String) -> String.Index? {
        interpolations.first.map { input.unicodeScalars.index(after: $0.openParen) }
    }

    /// The piece that starts at the `)` of interpolation `k`: a part up to and including the next
    /// interpolation's `(`, or the tail up to the end of the literal.
    func piece(after k: Int, in input: String) -> (end: String.Index, isTail: Bool) {
        if k + 1 < interpolations.count {
            return (input.unicodeScalars.index(after: interpolations[k + 1].openParen), false)
        }
        return (end, true)
    }
}

/// Lexes one Swift string literal the way the compiler does. A port of `swiftlang/swift`
/// `lib/Parse/Lexer.cpp` (main, 2026-10-08): `lexStringLiteral`, `lexCharacter`,
/// `advanceIfCustomDelimiter`, `delimiterMatches`, `advanceIfMultilineDelimiter`,
/// `skipToEndOfInterpolatedExpression`, `getMultilineTrailingIndent` and `validateMultilineIndents`.
///
/// A literal the compiler diagnoses (a lexer error, not a warning) gives no layout, so the parser
/// rejects it. Works on Unicode scalars, as the compiler works on bytes: `\r\n` is two characters.
enum SwiftStringLiteralScanner {
    typealias Index = String.Index
    typealias Scalars = String.UnicodeScalarView

    /// The layout of the literal that starts at `start` (its first `#` or quote), or nil when there
    /// is no valid literal there.
    static func layout(in input: String, at start: Index) -> SwiftStringLiteralLayout? {
        let u = input.unicodeScalars
        var (n, i) = poundRun(u, from: start)
        guard at(u, i) == "\"" else { return nil }
        i = u.index(after: i)
        let isMultiline = opensMultiline(u, afterQuote: i, pounds: n)
        if isMultiline {
            i = u.index(i, offsetBy: 2)
            // "multi-line string literal content must begin on a new line"
            guard at(u, i) == "\n" || at(u, i) == "\r" else { return nil }
        }
        let contentStart = i
        var interpolations: [SwiftStringLiteralLayout.Interpolation] = []

        while let c = at(u, i) {
            switch c {
            case "\\":
                let afterBackslash = u.index(after: i)
                let (k, afterPounds) = poundRun(u, from: afterBackslash)
                // Fewer than N `#`: the `\` is text. More: "too many '#' characters in delimited
                // escape". (With N = 0 a following `#` is an invalid escape character.)
                if n > 0, k < n { i = afterBackslash; continue }
                guard k == n, let e = at(u, afterPounds) else { return nil }
                let afterEscape = u.index(after: afterPounds)
                switch e {
                case "(":
                    guard let close = interpolationEnd(u, from: afterEscape, multiline: isMultiline) else { return nil }
                    interpolations.append(.init(backslash: i, openParen: afterPounds, closeParen: close))
                    i = u.index(after: close)
                case "0", "n", "r", "t", "\"", "'", "\\":
                    i = afterEscape
                case "u":
                    guard let after = unicodeEscapeEnd(u, from: afterEscape) else { return nil }
                    i = after
                case " ", "\t", "\n", "\r":
                    // Line continuation: `\`, optional spaces/tabs, line break. Multiline only.
                    guard isMultiline, let after = lineContinuationEnd(u, from: afterPounds) else { return nil }
                    i = after
                default:
                    return nil   // "invalid escape sequence in literal"
                }

            case "\"":
                switch closer(u, at: i, pounds: n, multiline: isMultiline) {
                case .none:
                    i = u.index(after: i)
                case .invalid:
                    return nil   // "too many '#' characters in closing delimiter"
                case .end(let end):
                    var closerIndent = i..<i
                    if isMultiline {
                        guard let indent = multilineIndent(u, content: contentStart..<i, pounds: n) else { return nil }
                        closerIndent = indent
                    }
                    return SwiftStringLiteralLayout(
                        start: start, contentStart: contentStart, contentEnd: i, end: end,
                        poundCount: n, isMultiline: isMultiline,
                        interpolations: interpolations, closerIndent: closerIndent)
                }

            case "\n", "\r":
                guard isMultiline else { return nil }   // "unterminated string literal"
                i = u.index(after: i)

            case "\t":
                guard isMultiline else { return nil }   // "unprintable ASCII character"
                i = u.index(after: i)

            default:
                // ASCII control characters (including NUL) and DEL are "unprintable".
                guard c.value >= 0x20, c.value != 0x7F else { return nil }
                i = u.index(after: i)
            }
        }
        return nil   // "unterminated string literal"
    }

    // MARK: Delimiters

    private static func at(_ u: Scalars, _ i: Index) -> Unicode.Scalar? {
        i < u.endIndex ? u[i] : nil
    }

    /// The number of `#` from `i`, and the position after them.
    private static func poundRun(_ u: Scalars, from i: Index) -> (count: Int, after: Index) {
        var i = i, count = 0
        while at(u, i) == "#" { count += 1; i = u.index(after: i) }
        return (count, i)
    }

    /// `advanceIfMultilineDelimiter(IsOpening: true)`: after the first opening quote, are there two
    /// more? With N > 0 a `#"""…"#` on one line is a single-line literal whose content starts with `""`.
    private static func opensMultiline(_ u: Scalars, afterQuote i: Index, pounds n: Int) -> Bool {
        guard at(u, i) == "\"" else { return false }
        let third = u.index(after: i)
        guard at(u, third) == "\"" else { return false }
        if n > 0 {
            var j = third
            while let c = at(u, j), c != "\n", c != "\r" {
                j = u.index(after: j)
                if c == "\"", poundRun(u, from: j).count >= n { return false }
            }
        }
        return true
    }

    private enum Closer { case none, invalid, end(Index) }

    /// Does the quote at `i` close the literal? `"` (or `"""`) followed by N `#`; more `#` is an error.
    private static func closer(_ u: Scalars, at i: Index, pounds n: Int, multiline: Bool) -> Closer {
        var j = u.index(after: i)
        if multiline {
            guard at(u, j) == "\"", at(u, u.index(after: j)) == "\"" else { return .none }
            j = u.index(j, offsetBy: 2)
        }
        guard n > 0 else { return .end(j) }
        let (k, _) = poundRun(u, from: j)
        if k < n { return .none }
        if k > n { return .invalid }
        return .end(u.index(j, offsetBy: n))
    }

    // MARK: Escapes

    /// `\u{…}` from after the `u`: 1–8 hex digits that form a valid Unicode scalar (no surrogates,
    /// at most U+10FFFF).
    private static func unicodeEscapeEnd(_ u: Scalars, from i: Index) -> Index? {
        guard at(u, i) == "{" else { return nil }
        var j = u.index(after: i)
        var digits = 0
        var value: UInt32 = 0
        while let c = at(u, j), let d = hexValue(c) {
            if digits < 8 { value = value << 4 | d }
            digits += 1
            j = u.index(after: j)
        }
        guard at(u, j) == "}", (1...8).contains(digits), Unicode.Scalar(value) != nil else { return nil }
        return u.index(after: j)
    }

    private static func hexValue(_ c: Unicode.Scalar) -> UInt32? {
        switch c {
        case "0"..."9": return c.value - 0x30
        case "a"..."f": return c.value - 0x61 + 10
        case "A"..."F": return c.value - 0x41 + 10
        default: return nil
        }
    }

    /// `maybeConsumeNewlineEscape`: spaces and tabs, then a line break; the position after it.
    private static func lineContinuationEnd(_ u: Scalars, from i: Index) -> Index? {
        var j = i
        while let c = at(u, j) {
            switch c {
            case " ", "\t":
                j = u.index(after: j)
            case "\r":
                j = u.index(after: j)
                return at(u, j) == "\n" ? u.index(after: j) : j
            case "\n":
                return u.index(after: j)
            default:
                return nil
            }
        }
        return nil
    }

    // MARK: Interpolations

    private enum Open {
        case paren
        case string(quote: Unicode.Scalar, multiline: Bool, pounds: Int)
    }

    /// `skipToEndOfInterpolatedExpression`: from after `\#(`, the position of the `)` that ends the
    /// interpolation, or nil. A simple scanner, as in the compiler: it matches parentheses, nested
    /// string literals (also `'…'`) and comments, nothing else. A line break is allowed only where
    /// the innermost enclosing literal is multiline.
    private static func interpolationEnd(_ u: Scalars, from start: Index, multiline: Bool) -> Index? {
        var open: [Open] = []
        var allowNewline = [multiline]
        func innermostString() -> (quote: Unicode.Scalar, multiline: Bool, pounds: Int)? {
            if case .string(let q, let m, let p) = open.last { return (q, m, p) }
            return nil
        }

        var i = start
        while let c = at(u, i) {
            var j = u.index(after: i)
            var quote: Unicode.Scalar? = nil
            var pounds = 0
            switch c {
            case "\n", "\r":
                guard allowNewline.last == true else { return nil }
            case "#":
                // `advanceIfCustomDelimiter`: `#…#"` opens a raw literal.
                if innermostString() == nil {
                    let (k, after) = poundRun(u, from: j)
                    if at(u, after) == "\"" {
                        quote = "\""
                        pounds = k + 1
                        j = u.index(after: after)
                    }
                }
            case "\"", "'":
                quote = c
            case "\\":
                if let s = innermostString() {
                    let (k, _) = poundRun(u, from: j)
                    if k >= s.pounds {
                        j = u.index(j, offsetBy: s.pounds)
                        switch at(u, j) {
                        case "(":                       // nested interpolation
                            open.append(.paren)
                            j = u.index(after: j)
                        case "\n", "\r", nil:           // handled by the next iteration
                            break
                        default:
                            j = u.index(after: j)       // skip the escaped character
                        }
                    }
                }
            case "(":
                if innermostString() == nil { open.append(.paren) }
            case ")":
                if open.isEmpty { return i }
                if case .paren = open.last { open.removeLast() }
            case "/":
                if innermostString() == nil {
                    if at(u, j) == "*" {
                        guard let (end, spansLines) = blockCommentEnd(u, from: i) else { return nil }
                        if spansLines, allowNewline.last != true { return nil }
                        j = end
                    } else if at(u, j) == "/" {
                        guard allowNewline.last == true else { return nil }
                        while let d = at(u, j), d != "\n", d != "\r" { j = u.index(after: j) }
                        if j < u.endIndex { j = u.index(after: j) }
                    }
                }
            default:
                break
            }

            if let quote {
                if let s = innermostString() {
                    // Close the innermost literal: same quote, `"""` if multiline, N `#`.
                    if s.quote == quote, !s.multiline || (at(u, j) == "\"" && at(u, u.index(after: j)) == "\"") {
                        if s.multiline { j = u.index(j, offsetBy: 2) }
                        if poundRun(u, from: j).count >= s.pounds {
                            j = u.index(j, offsetBy: s.pounds)
                            open.removeLast()
                            allowNewline.removeLast()
                        }
                    }
                } else {
                    let nestedMultiline = quote == "\"" && opensMultiline(u, afterQuote: j, pounds: pounds)
                    if nestedMultiline { j = u.index(j, offsetBy: 2) }
                    open.append(.string(quote: quote, multiline: nestedMultiline, pounds: pounds))
                    allowNewline.append(nestedMultiline)
                }
            }
            i = j
        }
        return nil
    }

    /// `skipToEndOfSlashStarComment` from the `/` of `/*`: the position after the comment (comments
    /// nest) and whether it contains a line break.
    private static func blockCommentEnd(_ u: Scalars, from i: Index) -> (Index, Bool)? {
        var j = u.index(i, offsetBy: 2)
        var depth = 1
        var spansLines = false
        while let c = at(u, j) {
            j = u.index(after: j)
            switch c {
            case "*" where at(u, j) == "/":
                j = u.index(after: j)
                depth -= 1
                if depth == 0 { return (j, spansLines) }
            case "/" where at(u, j) == "*":
                j = u.index(after: j)
                depth += 1
            case "\n", "\r":
                spansLines = true
            default:
                break
            }
        }
        return nil
    }

    // MARK: Multiline indentation

    /// `getMultilineTrailingIndent` + `validateMultilineIndents`: the closer's indentation, or nil
    /// when the literal is invalid. `content` is everything between the opening and closing quotes,
    /// including the source text of interpolations, which the compiler checks too.
    private static func multilineIndent(_ u: Scalars, content: Range<Index>, pounds n: Int) -> Range<Index>? {
        // The closing quotes must be preceded by only spaces and tabs on their line. The content
        // starts with a line break, so this loop always stops at one.
        var indentStart = content.upperBound
        while indentStart > content.lowerBound {
            let p = u.index(before: indentStart)
            if u[p] == "\n" || u[p] == "\r" { break }
            // "multi-line string literal closing delimiter must begin on a new line"
            guard u[p] == " " || u[p] == "\t" else { return nil }
            indentStart = p
        }
        let indent = indentStart..<content.upperBound

        // "escaped newline at the last line is not allowed": the line break before the closer's line
        // must not be escaped by an odd number of `\` (non-raw literals only).
        if n == 0 {
            var p = u.index(before: indentStart)               // the line break
            if u[p] == "\n", p > content.lowerBound { p = u.index(before: p) }
            if u[p] == "\r", p > content.lowerBound { p = u.index(before: p) }
            while p > content.lowerBound, u[p] == " " || u[p] == "\t" { p = u.index(before: p) }
            if u[p] == "\\" {
                var escaped = true
                while p > content.lowerBound {
                    p = u.index(before: p)
                    guard u[p] == "\\" else { break }
                    escaped.toggle()
                }
                if escaped { return nil }
            }
        }

        // "insufficient indentation of line in multi-line string literal": every line after a `\n`
        // that is not empty must start with the indent (a whitespace-only line is not empty).
        guard !indent.isEmpty else { return indent }
        let indentScalars = u[indent]
        var p = content.lowerBound
        while p < content.upperBound {
            let c = u[p]
            p = u.index(after: p)
            guard c == "\n", p < content.upperBound, u[p] != "\n", u[p] != "\r" else { continue }
            var q = p
            for expected in indentScalars {
                guard q < content.upperBound, u[q] == expected else { return nil }
                q = u.index(after: q)
            }
        }
        return indent
    }
}

/// The five string terminals of `Swift.apus`, sharing one layout cache per parse.
///
/// - `stringLiteralToken`: a whole literal without interpolation, any form.
/// - `plainStringLiteralToken`: the same, without `#` delimiters (for `@available` messages).
/// - `stringHead`: from the opener up to and including the `(` of the first interpolation.
/// - `stringPart`: from an interpolation's `)` up to and including the next interpolation's `(`.
/// - `stringTail`: from the last interpolation's `)` up to and including the closer.
///
/// A head records the pieces of its literal; a part or tail only matches where a recorded piece
/// starts. In GLL a part is only tried after the grammar parsed a head and an interpolated expression
/// on that path, so the head was scanned before.
final class SwiftStringLiteralTokens: ApusTokenScanner {
    private var layouts: [String.Index: SwiftStringLiteralLayout?] = [:]
    /// Piece start (an interpolation's `)`) → the literals with a piece there, by opener position.
    private var pieces: [String.Index: [(opener: String.Index, end: String.Index, isTail: Bool)]] = [:]

    func match(terminal: String, in input: String, at start: String.Index) -> String.Index? {
        switch terminal {
        case "stringLiteralToken":
            guard let l = layout(input, start), l.interpolations.isEmpty else { return nil }
            return l.end
        case "plainStringLiteralToken":
            guard let l = layout(input, start), l.interpolations.isEmpty, l.poundCount == 0 else { return nil }
            return l.end
        case "stringHead":
            guard let l = layout(input, start), let headEnd = l.headEnd(in: input) else { return nil }
            record(l, input)
            return headEnd
        case "stringPart", "stringTail":
            // Several literals with a piece here only happens on paths that lexed one literal's text
            // as another literal; the outermost (first) opener is the one the compiler sees.
            let isTail = terminal == "stringTail"
            return pieces[start]?.filter { $0.isTail == isTail }.min { $0.opener < $1.opener }?.end
        default:
            return nil
        }
    }

    private func layout(_ input: String, _ start: String.Index) -> SwiftStringLiteralLayout? {
        if let cached = layouts[start] { return cached }
        let l = SwiftStringLiteralScanner.layout(in: input, at: start)
        layouts[start] = l
        return l
    }

    private func record(_ l: SwiftStringLiteralLayout, _ input: String) {
        for (k, interpolation) in l.interpolations.enumerated() {
            let piece = l.piece(after: k, in: input)
            guard !(pieces[interpolation.closeParen]?.contains { $0.opener == l.start } ?? false) else { continue }
            pieces[interpolation.closeParen, default: []].append((l.start, piece.end, piece.isTail))
        }
    }
}

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
    // name-consuming sites in Swift.apus via `---("_")`. Unlike coarse `\p{So}`,
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
        "A"..."Z", "a"..."z", "0"..."9", "_"..."_",
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
    /// keypath dev 6 / `Lexical Disambiguation Tools.md` for the keyPathDot coexistence.
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
        OneOrMore { dotOperatorCharacter }
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

    // ── String literal escape components ────────────────────────────────────────
    // Shared by the single-line and multiline forms. Written out as NAMED components even
    // though the trailing catch-alls below subsume them, because that is exactly what
    // Group B1 (REJECTS.md § C2) has to change: dropping the catch-all leaves the legal
    // escape set behind, which is what makes `"\1"` / `"\#"` invalid in swift.

    static let hexDigit = CharacterClass("0"..."9", "a"..."f", "A"..."F")

    /// `\u{…}` — unicode scalar escape.
    static let unicodeScalarEscape = Regex {
        "\\u{"
        OneOrMore { hexDigit }
        "}"
    }

    /// The simple escapes swift recognises: `\0 \\ \t \n \r \" \'`.
    static let simpleEscape = Regex {
        "\\"
        CharacterClass.anyOf("0\\tnr\"'")
    }

    // The two `\` + anything CATCH-ALLS that used to live here are deleted (Group B1). They were
    // the faithful translation of the old `\\(?!\().` / `\\.`, and they were also what let every
    // invalid escape through. Historical note kept because it is a live trap for whoever
    // reintroduces one: they used `.anyNonNewline`, NOT `.any` — a regex `.` does not match a
    // newline but `CharacterClass.any` does, so `.any` would silently admit `\`+newline inside a
    // SINGLE-LINE string. The multiline forms use `.any` deliberately, since there `\`+newline is
    // a legal line continuation.

    /// Any scalar that is not a `"` or `\` and not a line break — single-line body filler.
    static let singleLinePlainScalar = CharacterClass.anyOf("\"\\\r\n").inverted

    /// Single-line body item: a plain scalar or one of the LEGAL escapes, and nothing else.
    ///
    /// The `\` + anything catch-all is GONE (Group B1, REJECTS.md § C2). swift's escape set is
    /// closed — `\0 \\ \t \n \r \" \'`, `\u{…}`, and `\(` — so `"\1"`, `"\#"`, `"\q"` are
    /// *"invalid escape sequence in literal"*. With no catch-all they are simply unmatchable.
    ///
    /// This also collapses what used to be two components. `\(` needs no special handling in
    /// either direction: for the STATIC literal a `\(` now ends the body and the required
    /// closing `"` fails, so the literal is rejected and the interpolated Head/Part/Tail path
    /// takes it; for HEAD/PART the `\(` is the terminator, which the reluctant body stops at.
    /// `"\\(x)"` still works — `simpleEscape` takes the `\\`, then `(x)` is plain scalars.
    static let singleLineBodyItem = ChoiceOf {
        singleLinePlainScalar
        unicodeScalarEscape
        simpleEscape
    }

    // ── Single-line string literals ─────────────────────────────────────────────

    /// `singleLineStringLiteral` — `"…"`, one line, no interpolation.
    static let singleLineStringLiteral = Regex {
        "\""
        ZeroOrMore(.reluctant) { singleLineBodyItem }
        "\""
    }.matchingSemantics(.unicodeScalar)

    /// `extendedSinglelineStringLiteral` — `#"…"#`, raw: no escape processing, and a `"` is
    /// ordinary content unless followed by the matching `#` run.
    static let extendedSinglelinePoundDelimiter = Reference(Substring.self)
    static let extendedSinglelineStringLiteral = Regex {
        Capture(poundRun, as: extendedSinglelinePoundDelimiter)
        "\""
        ZeroOrMore(.reluctant) {
            ChoiceOf {
                CharacterClass.anyOf("\"\\\r\n").inverted
                // Group B2 — "too many '#' characters to start string interpolation".
                // In an N-`#` raw string, interpolation is `\` + exactly N `#`s + `(`; MORE than N
                // is an error (`#"\##("invalid")"#`). Expressed with the delimiter BACKREFERENCE
                // inside a negative lookahead: a `\` is body content only if it is not followed by
                // the pound run PLUS at least one further `#`. With N=1, `\##` trips it while
                // `\#(` does not — no predicate over the token text needed after all.
                Regex {
                    "\\"
                    NegativeLookahead {
                        extendedSinglelinePoundDelimiter
                        "("
                    }
                    NegativeLookahead {
                        extendedSinglelinePoundDelimiter
                        OneOrMore { "#" }
                    }
                }
                Regex {
                    "\""
                    NegativeLookahead { extendedSinglelinePoundDelimiter }
                }
            }
        }
        "\""
        extendedSinglelinePoundDelimiter
    }.matchingSemantics(.unicodeScalar)

    static let extendedInterpolatedSinglelinePoundDelimiter = Reference(Substring.self)
    static let extendedInterpolatedStringLiteralHead = Regex {
        Capture(poundRun, as: extendedInterpolatedSinglelinePoundDelimiter)
        "\""
        ZeroOrMore(.reluctant) {
            ChoiceOf {
                CharacterClass.anyOf("\"\\\r\n").inverted
                Regex {
                    "\\"
                    NegativeLookahead {
                        extendedInterpolatedSinglelinePoundDelimiter
                        "("
                    }
                    NegativeLookahead {
                        extendedInterpolatedSinglelinePoundDelimiter
                        OneOrMore { "#" }
                    }
                }
                Regex {
                    "\""
                    NegativeLookahead { extendedInterpolatedSinglelinePoundDelimiter }
                }
            }
        }
        "\\"
        extendedInterpolatedSinglelinePoundDelimiter
        "("
    }.matchingSemantics(.unicodeScalar)

    static let extendedInterpolatedStringLiteralPart = Regex {
        ")"
        ZeroOrMore(.reluctant) {
            ChoiceOf {
                CharacterClass.anyOf("\\\r\n").inverted
                Regex {
                    "\\"
                    NegativeLookahead {
                        OneOrMore { "#" }
                        "("
                    }
                }
            }
        }
        "\\"
        OneOrMore { "#" }
        "("
    }.matchingSemantics(.unicodeScalar)

    static let extendedInterpolatedStringLiteralTail = Regex {
        ")"
        ZeroOrMore(.reluctant) {
            ChoiceOf {
                CharacterClass.anyOf("\"\\\r\n").inverted
                Regex {
                    "\\"
                    NegativeLookahead {
                        OneOrMore { "#" }
                        "("
                    }
                }
                Regex {
                    "\""
                    NegativeLookahead { OneOrMore { "#" } }
                }
            }
        }
        "\""
        OneOrMore { "#" }
    }.matchingSemantics(.unicodeScalar)

    /// `interpolatedStringLiteralHead` — `"` … up to the first `\(`.
    static let interpolatedStringLiteralHead = Regex {
        "\""
        ZeroOrMore(.reluctant) { singleLineBodyItem }
        "\\("
    }.matchingSemantics(.unicodeScalar)

    /// `interpolatedStringLiteralPart` — `)` … up to the next `\(`.
    static let interpolatedStringLiteralPart = Regex {
        ")"
        ZeroOrMore(.reluctant) { singleLineBodyItem }
        "\\("
    }.matchingSemantics(.unicodeScalar)

    /// `interpolatedStringLiteralTail` — `)` … up to the closing `"`.
    static let interpolatedStringLiteralTail = Regex {
        ")"
        ZeroOrMore(.reluctant) { singleLineBodyItem }
        "\""
    }.matchingSemantics(.unicodeScalar)

    // ── Multiline string literals ───────────────────────────────────────────────
    // The DELIMITER SHAPE below is probe-confirmed against swift-syntax (2026-08-29)
    // and holds identically for all four multiline forms — plain, raw, and the
    // interpolated Head/Tail:
    //
    //   • "content must begin on a new line" — a line break must follow the opening
    //     `"""` IMMEDIATELY. Not even a space or tab: `"""␠␠⏎"""` and `"""⇥⏎"""` both
    //     error; only `"""⏎` is legal. (The old `extendedMultilineStringLiteral`
    //     allowed `[ \t]*` here, which was wrong — `#"""␠␠⏎"""#` errors too.)
    //   • "closing delimiter must begin on a new line" — the closing `"""` may be
    //     preceded on its own line by horizontal whitespace only.
    //
    // `#"""A"""#` and `#""""""#` are NOT counter-examples: with content on the opener
    // line they are SINGLE-line raw strings holding `"` characters ("false
    // delimiters"), handled by `extendedSinglelineStringLiteral`.
    //
    // NOT enforced here (Group D in REJECTS.md § C2): the indentation rule — every
    // line must be indented at least as far as the closing delimiter — and the ban on
    // an escaped newline in the last body line. Both are post-lex checks on the
    // matched text, not shape.
    //
    // These carry `.matchingSemantics(.unicodeScalar)` like every other terminal here.
    // That matters for line breaks: under the default GRAPHEME semantics `\r\n` is ONE
    // Character, so a component matching `"\n"` alone would not match the `\n` of a
    // CRLF pair.

    /// Swift's line terminators — CRLF first, so it is consumed as a unit. Deliberately
    /// NOT `CharacterClass.newlineSequence`, which also matches U+000B/U+000C/U+0085/
    /// U+2028/U+2029; those are not line terminators for Swift's lexer.
    static let lineBreak = ChoiceOf {
        "\r\n"
        "\n"
        "\r"
    }

    static let horizontalWhitespace = CharacterClass.anyOf(" \t")


    static let tripleQuote = "\"\"\""

    // STANDING RULE for this library: **alternatives inside a quantifier must be DISJOINT.**
    // `ZeroOrMore { ChoiceOf { A; B } }` where A and B can both match the same text gives the
    // engine 2^n ways to consume n such items, and a `NegativeLookahead` around it has to exhaust
    // every one in order to FAIL. Two separate defects of exactly this shape have been fixed here:
    // the `multilineBodyItem` alternation below, and (2026-09-17) the lookahead scalar used by
    // `multilineStringLiteral` / `extendedMultilineStringLiteral`, which was
    // `ChoiceOf { lineBreak; CharacterClass.any }` — and `.any` already matches a line break, so
    // every newline had two derivations. Cost: parse time DOUBLED per newline following a `"""`
    // literal (2.8s → 171.5s over seven lines) with every parser counter byte-identical;
    // `Oracle.swift` never finished. Now plain `CharacterClass.any` at both sites: same language,
    // one derivation, `Oracle.swift` parses in 3.7s.
    //
    // When touching any `ChoiceOf` in a quantifier here, check the first-character sets are
    // disjoint, and prefer a single `CharacterClass` over a `ChoiceOf` that merely looks broader.

    /// Body item of a NON-raw multiline string. The three alternatives are DISJOINT on
    /// their first character, which keeps matching linear — an earlier overlapping
    /// alternation here caused catastrophic backtracking on large inputs:
    ///   • any scalar that is neither `"` nor `\` (newlines included — the body spans lines)
    ///   • `\` + ANY scalar, so a `\⏎` line-continuation is body content (Cursor.swift:1766)
    ///   • a `"` that does not begin the closing `"""`
    static let multilineBodyItem = ChoiceOf {
        CharacterClass.anyOf("\"\\").inverted
        Regex {
            "\\"
            CharacterClass.any
        }
        Regex {
            "\""
            NegativeLookahead { "\"\"" }
        }
    }

    /// As `multilineBodyItem`, but a `\` may not introduce an interpolation — used by the
    /// Tail, where a `\(` would instead start another `…Part`.
    static let multilineTailBodyItem = ChoiceOf {
        CharacterClass.anyOf("\"\\").inverted
        Regex {
            "\\"
            NegativeLookahead { "(" }
            CharacterClass.any
        }
        Regex {
            "\""
            NegativeLookahead { "\"\"" }
        }
    }

    /// Body item of a RAW multiline string, used only to BOUND lookaheads. A raw literal processes
    /// no escapes, so `\` is ordinary content and the only thing that can end the body is a `"`
    /// beginning the closing delimiter. Two alternatives, DISJOINT on first character (see the
    /// standing rule above): anything that is not a quote, or a quote that does not begin `"""`.
    static let extendedMultilineBodyItem = ChoiceOf {
        CharacterClass.anyOf("\"").inverted
        Regex {
            "\""
            NegativeLookahead { "\"\"" }
        }
    }

    static let poundRun = OneOrMore { "#" }
    static let poundDelimiter = Reference(Substring.self)

    /// As `multilineBodyItem` but never crossing a line break — the line-partition model below
    /// delimits lines explicitly. `\(` is not static text in a plain Swift string; it terminates
    /// the static token so the interpolated Head/Part/Tail path owns the literal. Other
    /// backslash escapes, including escaped newlines, remain body content here.
    static let multilineLineItem = ChoiceOf {
        CharacterClass.anyOf("\"\\\r\n").inverted
        Regex {
            "\\"
            NegativeLookahead { "(" }
            CharacterClass.any
        }
        Regex {
            "\""
            NegativeLookahead { "\"\"" }
        }
    }

    /// The closing delimiter's indentation, bound by a zero-width lookahead so it can be used
    /// as a BACKREFERENCE while matching the body lines that PRECEDE it.
    static let closerIndent = Reference(Substring.self)

    /// `multilineStringLiteral` — static (non-interpolated) plain multiline string, modelled as a
    /// SEQUENCE OF LINES each carrying a layout prefix.
    ///
    /// This shape encodes swift's indentation rule declaratively. Transcribed from
    /// `StringLiterals.swift` (`visitTokenNode`): the rule is
    /// `SyntaxText(rebasing: leadingTrivia[indentationStartIndex...]).hasPrefix(expectedIndentation)`
    /// — a PREFIX test against the closing delimiter's indentation, not column arithmetic. So tabs
    /// and spaces must match literally, and a line indented DEEPER than the closer is fine because
    /// the closer's whitespace is still a prefix of it. Expressed here as `closerIndent` at the
    /// start of every line.
    ///
    /// Truly EMPTY lines are exempt — swift-syntax's own `testEmptyLineInMultilineStringLiteral`
    /// shows a zero-character line parsing as `.stringSegment("\n")` with no leading trivia, while
    /// `testUnderIndentedWhitespaceonlyLineInMultilineStringLiteral` shows a whitespace-only line
    /// with 7 of 8 spaces IS an error. Hence the bare-`lineBreak` alternative, and hence a
    /// whitespace-only line still has to carry the full prefix.
    ///
    /// The line loop cannot swallow the closer's own line: that line is `<indent>"""`, and `"""`
    /// fails the `"(?!"")` item, so no item consumes it and the required trailing `lineBreak`
    /// never arrives.
    static let multilineStringLiteral = Regex {
        tripleQuote
        // A `\(` inside THIS literal means the INTERPOLATED Head/Part/Tail path owns it, not the
        // static one.
        //
        // The scan is bounded by `multilineBodyItem`, and that bound is the whole point. It used to
        // be `ZeroOrMore { CharacterClass.any }`, which scanned the ENTIRE REMAINING INPUT — so a
        // `\(` in some unrelated literal hundreds of bytes later rejected this one. Measured in
        // `ApusToHTML.swift`: the identical literal matched (248 chars) with one statement of
        // context and vanished from the lexicalisation fan when a later statement containing
        // `\(esc(l))` was appended, leaving `singleLineStringLiteral ""` to eat two of the three
        // opening quotes and derail the parse at the third.
        //
        // `multilineBodyItem`'s quote branch is `"\"" + NegativeLookahead { "\"\"" }` — a `"` that
        // does NOT begin `"""` — so a run of body items cannot cross the closing delimiter. The
        // scan is therefore confined to this literal's own extent, which is what the rule always
        // meant. (Same fix on `extendedMultilineStringLiteral` below.)
        NegativeLookahead {
            ZeroOrMore(.reluctant) { multilineBodyItem }
            "\\("
        }
        // Zero-width: scan to the closing delimiter and bind its indentation. The reluctant scan
        // can only stop at the real closer (a `"""` inside the body would itself close the
        // literal), and the captured run is forced to be MAXIMAL because `"""` is not whitespace.
        //
        // Placed BEFORE the opener's line break is consumed, not after. For an EMPTY literal
        // (`_ = """⏎␠␠␠␠"""`) the closer sits on the line that the opener's newline starts, so
        // there is no SECOND line break — running this after the opener's `lineBreak` demanded one
        // and rejected every empty multiline string with an indented closer.
        Lookahead {
            ZeroOrMore(.reluctant) { CharacterClass.any }
            lineBreak
            Capture(ZeroOrMore(horizontalWhitespace), as: closerIndent)
            tripleQuote
        }
        lineBreak
        // These two alternatives DO overlap when `closerIndent` captured empty (a column-0 closer):
        // the second can then also match a bare line break. TESTED 2026-09-17 and it is HARMLESS —
        // both a valid literal and an UNTERMINATED one stay flat at 0.00s across 0…14 blank lines,
        // with constant descriptor counts. The reason is the `Lookahead` above: it proves a closing
        // delimiter exists BEFORE this loop runs, so on a valid literal the loop matches
        // deterministically line by line and succeeds on its first path, and on an unterminated one
        // the lookahead fails and the regex aborts before reaching here. Exponential exhaustion
        // needs a FAILING match reaching the ambiguous loop, which that guard prevents.
        // So: do NOT "fix" this, and do not re-flag it — it is guarded by construction.
        ZeroOrMore {
            ChoiceOf {
                lineBreak                       // truly empty line — exempt
                Regex {
                    closerIndent                // every other line must carry the closer's prefix
                    ZeroOrMore { multilineLineItem }
                    lineBreak
                }
            }
        }
        closerIndent
        tripleQuote
    }.matchingSemantics(.unicodeScalar)

    /// `extendedMultilineStringLiteral` — raw multiline string. Raw means NO escape
    /// processing, so the body is any scalar run; the closing `#` count must equal the
    /// opening one, matched via the `poundDelimiter` backreference.
    static let extendedMultilineStringLiteral = Regex {
        Capture(poundRun, as: poundDelimiter)
        tripleQuote
        lineBreak
        // A `\#(` inside THIS literal means the interpolated path owns it. Bounded by
        // `extendedMultilineBodyItem`, which cannot cross a `"""`, so the scan stays inside the
        // literal. It used to be `ZeroOrMore { CharacterClass.any }` — the entire remaining input —
        // the same defect measured and fixed on the non-raw literal above, where a `\(` in an
        // unrelated literal 355 bytes later made this one vanish from the lexicalisation fan.
        //
        // Deliberately simple, and the residual imprecision is in the SAFE direction: a raw body
        // may legitimately contain `"""` when the closer needs `"""` plus more pounds, and the scan
        // stops there. Stopping early can only MISS a `\#(` — allowing the raw reading for a literal
        // that also has an interpolated reading, so multi-lex offers both and the parser chooses —
        // whereas the old unbounded form FALSELY REJECTED. Under-scanning costs an extra candidate;
        // over-scanning lost the parse.
        NegativeLookahead {
            ZeroOrMore(.reluctant) { extendedMultilineBodyItem }
            "\\"
            poundDelimiter
            "("
        }
        Optionally {
            ZeroOrMore(.reluctant) { CharacterClass.any }
            lineBreak
        }
        ZeroOrMore { horizontalWhitespace }
        tripleQuote
        poundDelimiter
    }.matchingSemantics(.unicodeScalar)

    static let extendedMultilineInterpolatedPoundDelimiter = Reference(Substring.self)
    static let extendedMultilineInterpolatedStringLiteralHead = Regex {
        Capture(poundRun, as: extendedMultilineInterpolatedPoundDelimiter)
        tripleQuote
        lineBreak
        ZeroOrMore(.reluctant) {
            ChoiceOf {
                CharacterClass.anyOf("\"\\").inverted
                Regex {
                    "\\"
                    NegativeLookahead {
                        extendedMultilineInterpolatedPoundDelimiter
                        "("
                    }
                    CharacterClass.any
                }
                Regex {
                    "\""
                    NegativeLookahead {
                        "\"\""
                        extendedMultilineInterpolatedPoundDelimiter
                    }
                }
            }
        }
        "\\"
        extendedMultilineInterpolatedPoundDelimiter
        "("
    }.matchingSemantics(.unicodeScalar)

    static let extendedMultilineInterpolatedStringLiteralPart = Regex {
        ")"
        ZeroOrMore(.reluctant) {
            ChoiceOf {
                CharacterClass.anyOf("\\").inverted
                Regex {
                    "\\"
                    NegativeLookahead {
                        OneOrMore { "#" }
                        "("
                    }
                    CharacterClass.any
                }
            }
        }
        "\\"
        OneOrMore { "#" }
        "("
    }.matchingSemantics(.unicodeScalar)

    static let extendedMultilineInterpolatedStringLiteralTail = Regex {
        ")"
        ZeroOrMore(.reluctant) {
            ChoiceOf {
                CharacterClass.anyOf("\"\\").inverted
                Regex {
                    "\\"
                    NegativeLookahead {
                        OneOrMore { "#" }
                        "("
                    }
                    CharacterClass.any
                }
                Regex {
                    "\""
                    // A `"` is content unless it begins the CLOSER, which for a raw literal is
                    // `"""` + the pound run — not a bare `"""`. This guard was the NON-raw one
                    // (`NegativeLookahead { "\"\"" }`), so the body stopped at any bare `"""` and
                    // `SourceEdit.swift` failed: its `#"""` literal contains `"""` lines on purpose,
                    // legal because the closer is `"""#`. The Head above already had it right.
                    NegativeLookahead {
                        "\"\""
                        OneOrMore { "#" }
                    }
                }
            }
        }
        lineBreak
        ZeroOrMore { horizontalWhitespace }
        tripleQuote
        OneOrMore { "#" }
    }.matchingSemantics(.unicodeScalar)

    /// `multilineInterpolatedStringLiteralHead` — `"""⏎` … up to the first `\(`.
    static let multilineInterpolatedStringLiteralHead = Regex {
        tripleQuote
        lineBreak
        ZeroOrMore(.reluctant) { multilineBodyItem }
        "\\("
    }.matchingSemantics(.unicodeScalar)

    /// `multilineInterpolatedStringLiteralPart` — `)` … up to the next `\(`. Touches no
    /// delimiter, so the Group A shape rule does not apply to it.
    static let multilineInterpolatedStringLiteralPart = Regex {
        ")"
        ZeroOrMore(.reluctant) { multilineBodyItem }
        "\\("
    }.matchingSemantics(.unicodeScalar)

    /// `multilineInterpolatedStringLiteralTail` — `)` … up to the closing `"""`, which must
    /// begin its own line.
    static let multilineInterpolatedStringLiteralTail = Regex {
        ")"
        ZeroOrMore(.reluctant) { multilineTailBodyItem }
        lineBreak
        ZeroOrMore { horizontalWhitespace }
        tripleQuote
    }.matchingSemantics(.unicodeScalar)

    // ── Extended regex literal `#/…/#` ──────────────────────────────────────────
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

        "singleLineStringLiteral":                Regex<AnyRegexOutput>(singleLineStringLiteral.regex),
        "extendedSinglelineStringLiteral":        Regex<AnyRegexOutput>(extendedSinglelineStringLiteral.regex),
        "extendedInterpolatedStringLiteralHead":  Regex<AnyRegexOutput>(extendedInterpolatedStringLiteralHead.regex),
        "extendedInterpolatedStringLiteralPart":  Regex<AnyRegexOutput>(extendedInterpolatedStringLiteralPart.regex),
        "extendedInterpolatedStringLiteralTail":  Regex<AnyRegexOutput>(extendedInterpolatedStringLiteralTail.regex),
        "interpolatedStringLiteralHead":          Regex<AnyRegexOutput>(interpolatedStringLiteralHead.regex),
        "interpolatedStringLiteralPart":          Regex<AnyRegexOutput>(interpolatedStringLiteralPart.regex),
        "interpolatedStringLiteralTail":          Regex<AnyRegexOutput>(interpolatedStringLiteralTail.regex),

        "extendedRegularExpressionLiteral":                 Regex<AnyRegexOutput>(extendedRegularExpressionLiteral.regex),
        "multilineStringLiteral":                           Regex<AnyRegexOutput>(multilineStringLiteral.regex),
        "extendedMultilineStringLiteral":                   Regex<AnyRegexOutput>(extendedMultilineStringLiteral.regex),
        "extendedMultilineInterpolatedStringLiteralHead":   Regex<AnyRegexOutput>(extendedMultilineInterpolatedStringLiteralHead.regex),
        "extendedMultilineInterpolatedStringLiteralPart":   Regex<AnyRegexOutput>(extendedMultilineInterpolatedStringLiteralPart.regex),
        "extendedMultilineInterpolatedStringLiteralTail":   Regex<AnyRegexOutput>(extendedMultilineInterpolatedStringLiteralTail.regex),
        "multilineInterpolatedStringLiteralHead":           Regex<AnyRegexOutput>(multilineInterpolatedStringLiteralHead.regex),
        "multilineInterpolatedStringLiteralPart":           Regex<AnyRegexOutput>(multilineInterpolatedStringLiteralPart.regex),
        "multilineInterpolatedStringLiteralTail":           Regex<AnyRegexOutput>(multilineInterpolatedStringLiteralTail.regex),
    ]
}

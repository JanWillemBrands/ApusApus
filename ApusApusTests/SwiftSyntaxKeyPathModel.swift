import Foundation

/// EXECUTABLE MODEL of swift's key-path component loop — a faithful port of
/// `SwiftParser/Expressions.swift`: `parseKeyPathExpression`, `getNumOptionalKeyPathPostfixComponents`
/// and `consumeOptionalKeyPathPostfix`.
///
/// WHY THIS EXISTS. The key-path rules in `Swift.apus` grew to 40 across 21 nonterminals by
/// symptom-driven patching: trace a failing case, add a filter, repeat. That is a local search, and
/// its residue reappeared one sequence-length deeper each time (0 divergences at length 2,
/// 26 at length 3, 168+112 at length 4, length 5 never tested). The missing step was never
/// difficulty — it was that nobody derived WHAT LANGUAGE the imperative loop accepts before trying
/// to encode it as a CFG.
///
/// This model is that derivation, made executable so every claim about the language is falsifiable
/// at any length in seconds. It is deliberately NOT used by the parser: it is an oracle. Once it
/// agrees with swift-syntax everywhere, the DFA it implements can be read off and encoded as ~3
/// grammar rules instead of 13.
///
/// The PARSER LOOP below is transcribed and should be exact. The TOKENIZER is the uncertain part —
/// swift's operator lexing is context-dependent (a `.` after an operand is a `period`; a run of
/// `.?!` between operands is a single operator token) and is reproduced here from observed token
/// dumps. `KeyPathModelTests` measures the model against swift-syntax; every disagreement is a
/// defect IN THIS FILE, to be fixed here until agreement is total.
enum KeyPathModel {

    // MARK: - Tokens — a PORT of swift's lexer, not a reconstruction
    //
    // `SwiftParser/Lexer/Cursor.swift`: `lexNormalQuestionOrExclamation`, `lexPostfixOptionalChain`,
    // `lexOperatorIdentifier`, `classifyOperatorToken`, `isLeftBound`, `isRightBound`.

    /// Exactly the token kinds the key-path loop discriminates on.
    enum Token: Equatable, CustomStringConvertible {
        case period                  // a length-1 `.` — `classifyOperatorToken` returns `.period`
        case postfixQuestionMark     // a left-bound `?`
        case exclamationMark         // a left-bound `!`
        case infixQuestionMark       // a NOT-left-bound length-1 `?` — the ternary `?`
        case oper(String, Fixity, rightBound: Bool)  // operator + fixity + its RIGHT context

        /// "It's binary if either both sides are bound or both sides are not bound. Otherwise,
        /// it's postfix if left-bound and prefix if right-bound." A POSTFIX operator needs no
        /// operand after it; binary and prefix ones do. That is the whole difference between
        /// `\Foo.?.p<T>.?` (trailing `.?` is postfix on `T`, clean) and `\Foo.p<T> ??`
        /// (spaced `??` is binary, its rhs is missing, so swift recovers).
        enum Fixity { case prefix, binary, postfix }
        case leftSquare
        case rightSquare
        case leftBrace
        case rightBrace
        case moduleSeparator   // `::` (SE-0491)
        case identifier(String)
        case integerLiteral(String)
        case other(Character)

        /// `parseKeyPathExpression` branch 2 guard:
        /// `at(.prefixOperator, .binaryOperator, .postfixOperator) || at(.postfixQuestionMark, .exclamationMark)`.
        /// `.infixQuestionMark` is DELIBERATELY absent — that is the ternary exemption, and it is
        /// why `\Foo.bar ? a : b` is legal while `\Foo.bar ?? fallback` is not.
        var isKeyPathPostfixCandidate: Bool {
            switch self {
            case .postfixQuestionMark, .exclamationMark, .oper: return true
            default: return false
            }
        }

        /// `self.at(prefix: ".")` — a TEXT-prefix test. `.?` is an OPERATOR token whose text
        /// starts with a dot, so it satisfies it just as a bare `.period` does. Testing the token
        /// KIND instead wrongly rejected the contextual key paths `\.?` and `\.!`.
        var startsWithDot: Bool {
            switch self {
            case .period: return true
            case .oper(let text, _, _): return text.hasPrefix(".")
            default: return false
            }
        }

        /// The text branch 2 hands to `getNumOptionalKeyPathPostfixComponents`.
        var operatorText: String? {
            switch self {
            case .postfixQuestionMark: return "?"
            case .exclamationMark: return "!"
            case .oper(let text, _, _): return text
            default: return nil
            }
        }

        var description: String {
            switch self {
            case .period: return "."
            case .postfixQuestionMark: return "?post"
            case .exclamationMark: return "!"
            case .infixQuestionMark: return "?infix"
            case .oper(let s, let f, _): return "op(\(s),\(f))"
            case .leftSquare: return "["
            case .rightSquare: return "]"
            case .leftBrace: return "{"
            case .rightBrace: return "}"
            case .moduleSeparator: return "::"
            case .identifier(let s): return s
            case .integerLiteral(let s): return "int(\(s))"
            case .other(let c): return String(c)
            }
        }
    }

    private static func isOperatorChar(_ c: Character) -> Bool {
        "/=-+!*%<>&|^~?.".contains(c)
    }

    /// `isLeftBound`: false when the PREVIOUS character is whitespace, an opening delimiter, or an
    /// expression separator — or at the start of the buffer. True otherwise.
    private static func isLeftBound(previous: Character?) -> Bool {
        guard let previous else { return false }
        switch previous {
        case " ", "\r", "\n", "\t", "(", "[", "{", ",", ";", ":": return false
        default: return true
        }
    }

    /// `isRightBound(isLeftBound:)`: false when the NEXT character is whitespace, a closing
    /// delimiter, or an expression separator, or end of buffer. For `.` it is `!isLeftBound` —
    /// "prefer the `^` in `x^.y` to be a postfix op, not binary".
    private static func isRightBound(next: Character?, isLeftBound: Bool) -> Bool {
        guard let next else { return false }
        switch next {
        case " ", "\r", "\n", "\t", ")", "]", "}", ",", ";", ":": return false
        case ".": return !isLeftBound
        default: return true
        }
    }

    /// Tokenize the text FOLLOWING the backslash. `previous` is seeded with the character before
    /// it — `\` for a key path — because `isLeftBound` reads the preceding buffer character, and a
    /// backslash is not in the not-left-bound set.
    static func tokenize(_ text: String, seedPrevious: Character = "\\") -> [Token] {
        var tokens: [Token] = []
        let chars = Array(text)
        var i = 0
        var previous: Character? = seedPrevious

        func classifyRun(_ run: String, at runStart: Int) -> Token {
            let leftBound = isLeftBound(previous: previous)
            // `classifyOperatorToken`, reserved-word cases for length 1.
            if run.count == 1 {
                switch run.first! {
                case ".": return .period
                case "?": return leftBound ? .postfixQuestionMark : .infixQuestionMark
                default: break
                }
            }
            let next = runStart + run.count < chars.count ? chars[runStart + run.count] : nil
            let rightBound = isRightBound(next: next, isLeftBound: leftBound)
            let fixity: Token.Fixity =
                leftBound == rightBound ? .binary : (leftBound ? .postfix : .prefix)
            return .oper(run, fixity, rightBound: rightBound)
        }

        while i < chars.count {
            let c = chars[i]
            if c == " " || c == "\t" || c == "\n" || c == "\r" {
                previous = c; i += 1; continue
            }
            if c == "`" {
                // `lexEscapedIdentifier`: a backtick-quoted identifier is an IDENTIFIER token.
                var name = ""
                i += 1
                while i < chars.count, chars[i] != "`" { name.append(chars[i]); i += 1 }
                if i < chars.count { i += 1 }   // closing backtick
                tokens.append(.identifier(name)); previous = "`"; continue
            }
            if c.isLetter || c == "_" {
                var name = ""
                while i < chars.count, chars[i].isLetter || chars[i].isNumber || chars[i] == "_" {
                    name.append(chars[i]); i += 1
                }
                tokens.append(.identifier(name)); previous = name.last; continue
            }
            if c.isNumber {
                var digits = ""
                while i < chars.count, chars[i].isNumber { digits.append(chars[i]); i += 1 }
                tokens.append(.integerLiteral(digits)); previous = digits.last; continue
            }
            if c == "{" { tokens.append(.leftBrace); previous = c; i += 1; continue }
            if c == "}" { tokens.append(.rightBrace); previous = c; i += 1; continue }
            if c == ":", i + 1 < chars.count, chars[i + 1] == ":" {
                tokens.append(.moduleSeparator); previous = ":"; i += 2; continue
            }
            if c == "[" { tokens.append(.leftSquare); previous = c; i += 1; continue }
            if c == "]" { tokens.append(.rightSquare); previous = c; i += 1; continue }

            if c == "?" || c == "!" {
                // `lexNormalQuestionOrExclamation`: try `lexPostfixOptionalChain` FIRST — it
                // requires left-boundness and emits a SINGLE character.
                if isLeftBound(previous: previous) {
                    tokens.append(c == "?" ? .postfixQuestionMark : .exclamationMark)
                    previous = c; i += 1; continue
                }
                // Otherwise an operator run. It did NOT start with `.`, so a `.` BREAKS it.
                let runStart = i
                var run = ""
                while i < chars.count, isOperatorChar(chars[i]), chars[i] != "." {
                    run.append(chars[i]); i += 1
                }
                tokens.append(classifyRun(run, at: runStart))
                previous = run.last; continue
            }

            if isOperatorChar(c) {
                // Started with `.` (or another operator char); `.` may continue the run only
                // because the run STARTS with `.`.
                let runStart = i
                let startsWithDot = c == "."
                var run = ""
                while i < chars.count, isOperatorChar(chars[i]) {
                    if chars[i] == "." && !startsWithDot { break }
                    run.append(chars[i]); i += 1
                }
                tokens.append(classifyRun(run, at: runStart))
                previous = run.last; continue
            }

            tokens.append(.other(c)); previous = c; i += 1
        }
        return tokens
    }

    /// How many tokens `parseSimpleType(allowMemberTypes: false)` would consume as a ROOT TYPE,
    /// or nil if no type is there. `allowMemberTypes: false` is why `Foo.Bar` stops at `Foo`.
    static func simpleTypePrefixLength(_ tokens: [Token]) -> Int? {
        guard let head = tokens.first else { return nil }
        // A SUPPRESSED type `~T` (SE-0390) is a type, so `\ ~ x` has `~ x` as its ROOT and needs
        // no leading dot.
        if case .oper(let text, _, _) = head, text == "~", tokens.count > 1,
           let rest = simpleTypePrefixLength(Array(tokens.dropFirst())) {
            return rest + 1
        }
        switch head {
        case .identifier:
            var length = 1
            // an optional generic argument clause
            if tokens.count > 1, case .oper("<", _, _) = tokens[1] {
                var depth = 0
                var index = 1
                while index < tokens.count {
                    if case .oper("<", _, _) = tokens[index] { depth += 1 }
                    if case .oper(">", _, _) = tokens[index] {
                        depth -= 1; if depth == 0 { index += 1; break }
                    }
                    index += 1
                }
                if depth == 0 { length = index }
            }
            return length
        case .leftSquare, .other("("):
            let close: Token = head == .leftSquare ? .rightSquare : .other(")")
            var index = 1
            while index < tokens.count, tokens[index] != close {
                // A literal inside means this is a subscript/tuple EXPRESSION, not a type.
                if case .integerLiteral = tokens[index] { return nil }
                index += 1
            }
            guard index < tokens.count else { return nil }
            return index + 1
        default:
            return nil
        }
    }

    // MARK: - The splitter (exact port)

    /// `getNumOptionalKeyPathPostfixComponents`. Returns nil when the token is not a key-path
    /// postfix at all; otherwise how many `?`/`!` components it contributes.
    static func numOptionalPostfixComponents(_ text: String, mayBeAfterTypeName: Bool) -> Int? {
        var mayBeAfterTypeName = mayBeAfterTypeName
        var count = 0
        var lastWasDot = false
        for byte in text {
            if byte == "." {
                if !mayBeAfterTypeName { break }   // stop scanning, keep the count so far
                if lastWasDot { return nil }       // `..` is not a key-path postfix
                lastWasDot = true
                continue
            }
            if byte == "!" || byte == "?" {
                mayBeAfterTypeName = false
                lastWasDot = false
                count += 1
                continue
            }
            return nil
        }
        return count
    }

    /// How many CHARACTERS `consumeOptionalKeyPathPostfix` eats for `count` components, and whether
    /// any of them parked a period in `unexpectedBeforeComponent` (which is what makes the tree
    /// unclean).
    static func consumeOptionalPostfix(_ text: String, count: Int,
                                       mayBeAfterTypeName: inout Bool) -> (consumed: Int, clean: Bool) {
        let chars = Array(text)
        var index = 0
        var clean = true
        for _ in 0..<count {
            if index < chars.count, chars[index] == "." {
                // `consume(ifPrefix: ".")` takes it either way; when the flag is false it becomes
                // an UNEXPECTED node, which is precisely the recovery we must reject.
                if !mayBeAfterTypeName { clean = false }
                index += 1
            }
            if index < chars.count, chars[index] == "!" || chars[index] == "?" { index += 1 }
            mayBeAfterTypeName = false
        }
        return (index, clean)
    }

    // MARK: - The loop (exact port)

    /// Does swift parse this key-path suffix CLEANLY — no recovery, nothing left over?
    ///
    /// A port of `parseKeyPathExpression`'s loop. The four branches are in swift's order, and the
    /// guards use the TOKEN KINDS the real guards test.
    static func parsesCleanly(suffix: String, rootWasPresent: Bool) -> Bool {
        var tokens = tokenize(suffix)

        // `if !self.at(prefix: ".") { rootType = self.parseSimpleType(allowMemberTypes: false) }`.
        // Modelled for the root forms `keyPathRootBase` admits: an identifier (with optional
        // generic arguments), a bracketed array/dictionary type, a parenthesised tuple type, or
        // `Any`. A bracket whose contents contain a LITERAL is not a type — which is exactly why
        // `\[a: b]` is a dictionary-type root and `\[0]` is a contextual subscript (and so,
        // per SE-0161, a recovery).
        var rootWasPresent = rootWasPresent
        if !rootWasPresent, tokens.first?.startsWithDot != true,
           let consumed = simpleTypePrefixLength(tokens) {
            tokens.removeFirst(consumed)
            rootWasPresent = true
        }

        // SE-0161, accepted with this exact clarification: every CONTEXTUAL key path — one with no
        // root type — must start with `\.`. Checked AFTER the root parse, because that is the
        // order swift uses: `\[a: b]` is a DICTIONARY-TYPE root and clean, while `\[0]` has no
        // parseable type, so it is contextual and must have begun with a dot.
        if !rootWasPresent, tokens.first?.startsWithDot != true { return false }

        var mayBeAfterTypeName = true

        // `parseSimpleType(allowMemberTypes: false)` consumes a trailing `?`/`!` run into the ROOT
        // TYPE (`Foo?` is an optional type), so those marks are not components.
        if rootWasPresent {
            // `parseSimpleType` keeps consuming TYPE syntax after the base: metatype suffixes
            // (`.Type`, `.Protocol`) and optional/IUO marks, interleaved. All of it belongs to the
            // ROOT TYPE, so none of it is a component and `mayBeAfterTypeName` stays true. Without
            // the marks, `\Foo?.?` counted the `?` as a component and then rejected the legal
            // dotted `.?`; without the metatypes, `\Foo.Type?.?` did the same.
            while true {
                if tokens.first == .postfixQuestionMark || tokens.first == .exclamationMark {
                    tokens.removeFirst(); continue
                }
                if tokens.first == .period, tokens.count > 1,
                   tokens[1] == .identifier("Type") || tokens[1] == .identifier("Protocol") {
                    tokens.removeFirst(2); continue
                }
                break
            }
        }

        /// `<T, U>` following a declaration name — but ONLY when it is really a generic argument
        /// list. swift gates this on `canParseAsGenericArgumentList` plus
        /// `isGenericTypeDisambiguatingToken`: the token AFTER the closing `>` must be one that can
        /// follow a generic argument clause. Otherwise `<`/`>` are comparison operators, which is
        /// why `\Foo.p<T>.p` is clean (generic args, key path continues) while `\Foo.p<T> ??`
        /// recovers (`p < T > ?? <missing>`).
        ///
        /// The closing `>` may be only the PREFIX of an operator run: the lexer produces `>?` as
        /// one token in `\Foo.p<T>?`, and the parser splits the `>` out when it commits to a
        /// generic argument list — which is how `rightAngle` + `postfixQuestionMark` appear in the
        /// tree. So the remainder after the `>` is re-lexed back into the stream.
        func consumeGenericArgumentClause() {
            guard case .oper(let openText, _, _) = tokens.first, openText.hasPrefix("<") else { return }
            // Find the token that closes the clause — the first whose text starts with `>`.
            var index = 0
            var closing: (index: Int, text: String)? = nil
            while index < tokens.count {
                if case .oper(let text, _, _) = tokens[index], text.hasPrefix(">") {
                    closing = (index, text); break
                }
                index += 1
            }
            guard let closing else { return }

            // What follows the `>`: the rest of its own run if any, else the next token.
            let remainder = String(closing.text.dropFirst())
            let followTokens = remainder.isEmpty
                ? Array(tokens.dropFirst(closing.index + 1))
                : tokenize(remainder, seedPrevious: ">") + Array(tokens.dropFirst(closing.index + 1))
            switch followTokens.first {
            case nil, .period, .postfixQuestionMark, .exclamationMark, .leftSquare, .rightSquare,
                 .other(")"), .other("]"), .other(","), .other(":"), .other(";"):
                tokens.removeFirst(closing.index + 1)
                if !remainder.isEmpty {
                    tokens.insert(contentsOf: tokenize(remainder, seedPrevious: ">"), at: 0)
                }
            default:
                return   // a comparison, not a generic argument list
            }
        }

        /// `(a:)` / `(_:b:)` — argument LABELS, part of the declaration name.
        /// At least ONE label is required: `()` is not a declaration name, which is why
        /// `\Foo.m()` is a RECOVERY while `\Foo.m(a:)` is clean.
        func consumeArgumentLabelClause() {
            guard tokens.first == .other("("), tokens.count > 1, tokens[1] != .other(")") else { return }
            var index = 1
            while index < tokens.count, tokens[index] != .other(")") { index += 1 }
            guard index < tokens.count else { return }
            tokens.removeFirst(index + 1)
        }

        while !tokens.isEmpty {
            // 1. `[`, or `.` `[` while still after the type name.
            if tokens.first == .leftSquare
                || (mayBeAfterTypeName && tokens.first == .period
                    && tokens.dropFirst().first == .leftSquare) {
                if tokens.first == .period { tokens.removeFirst() }
                guard tokens.first == .leftSquare else { return false }
                tokens.removeFirst()
                while let head = tokens.first, head != .rightSquare { tokens.removeFirst(); _ = head }
                guard tokens.first == .rightSquare else { return false }
                tokens.removeFirst()
                // A trailing closure attaches to the subscript call and ENDS the expression:
                // `\Foo[0]{ }` is clean, but `\Foo[0]{ }.p` recovers — nothing may follow it.
                if tokens.first == .leftBrace {
                    var depth = 0
                    while let head = tokens.first {
                        if head == .leftBrace { depth += 1 }
                        if head == .rightBrace { depth -= 1 }
                        tokens.removeFirst()
                        if depth == 0 { break }
                    }
                    return tokens.isEmpty
                }
                mayBeAfterTypeName = false
                continue
            }

            // 2. An operator or mark whose text expands into optional components.
            if let head = tokens.first, head.isKeyPathPostfixCandidate,
               let text = head.operatorText,
               let count = numOptionalPostfixComponents(text, mayBeAfterTypeName: mayBeAfterTypeName),
               count > 0 {
                let (consumed, clean) = consumeOptionalPostfix(
                    text, count: count, mayBeAfterTypeName: &mayBeAfterTypeName)
                if !clean { return false }
                let originalRightBound: Bool
                if case .oper(_, _, let rb) = head { originalRightBound = rb } else { originalRightBound = false }
                tokens.removeFirst()
                let leftover = String(text.dropFirst(consumed))
                if !leftover.isEmpty {
                    // `consume(ifPrefix:)` does NOT re-lex from scratch: it shortens the token and
                    // re-classifies it. The left side is now bound by the mark just consumed; the
                    // RIGHT side is whatever followed the original token. Re-tokenizing the
                    // leftover in isolation lost that and mis-classified `.?.` in `\Foo.?.?.p` as
                    // postfix instead of binary.
                    let leftoverFixity: Token.Fixity =
                        originalRightBound ? .binary : .postfix   // left is bound either way
                    if leftover == "." {
                        tokens.insert(.period, at: 0)
                    } else {
                        tokens.insert(.oper(leftover, leftoverFixity, rightBound: originalRightBound), at: 0)
                    }
                }
                continue
            }

            // 3. `.` — a property component, which needs a declaration NAME.
            //    `parseDottedExpressionSuffix` yields `(unexpectedPeriod, period, declName,
            //    generics)`, and a declName may carry an argument-label clause — `.m(a:)` and
            //    `.m(_:b:)` are ONE component whose name includes the labels, not a call. It may
            //    also carry a generic argument clause (`.p<T>`).
            if tokens.first == .period {
                tokens.removeFirst()
                // `keyPathMemberName` is an identifier OR decimal digits (`\Foo.0`, a tuple member).
                switch tokens.first {
                case .identifier, .integerLiteral: tokens.removeFirst()
                default: return false
                }
                // `keyPathMemberName = moduleSelector? softIdentifier` with
                // `moduleSelector = hardIdentifier "::"` (SE-0491): what we just consumed may have
                // been the MODULE, with the real member name after `::`.
                if tokens.first == .moduleSeparator {
                    tokens.removeFirst()
                    guard case .identifier = tokens.first else { return false }
                    tokens.removeFirst()
                }
                consumeGenericArgumentClause()
                consumeArgumentLabelClause()
                continue
            }

            // 4. Anything else: the loop BREAKS and the enclosing expression parser resumes.
            break
        }

        // Whatever is left must be consumable as postfix/member syntax on the key-path expression.
        return tokens.isEmpty ? true : canPostfixConsume(tokens)
    }

    /// Can the ENCLOSING EXPRESSION parser consume what the key-path loop left behind?
    ///
    /// Once the loop breaks, `parseExprSequence` resumes with the key-path expression as the first
    /// element. It accepts a POSTFIX chain on it, and then any number of
    /// `binaryOperator operand postfixChain` groups. That is why `\Foo.?.?.p` is CLEAN: the loop
    /// consumes `.?`, the remainder `.?.` is a legal user-definable dot-operator, and `p` is its
    /// right operand — an ordinary infix expression, not a recovery. `\Foo.?.?` is NOT clean
    /// because the same remainder has no operand after it and degrades to a postfix operator.
    ///
    /// RESTRICTED, deliberately: `parseExprSequence` is far larger than this, but the enumerated
    /// alphabet only produces identifiers, integer literals, `[...]`, marks and `.`-runs, so only
    /// those forms are modelled. Widening the alphabet means widening this.
    private static func canPostfixConsume(_ tokens: [Token]) -> Bool {
        var tokens = tokens

        /// `.member`, optional-chaining `?`, force `!`, and `[...]` subscripts.
        ///
        /// `allowOperatorPostfix` is FALSE directly on the key path and TRUE on any later operand.
        /// That asymmetry is SE-0161's postfix island: no postfix operator may follow an
        /// unparenthesised key path (`\Foo.?.?` is unclean), but an ordinary operand later in the
        /// sequence takes them freely (`\Foo.? .?. p.?` is clean).
        func consumePostfixChain(allowOperatorPostfix: Bool) -> Bool {
            while true {
                if allowOperatorPostfix, case .oper(_, .postfix, _) = tokens.first {
                    tokens.removeFirst()   // a POSTFIX operator on this operand
                    continue
                }
                switch tokens.first {
                case .period:
                    tokens.removeFirst()
                    switch tokens.first {
                    case .identifier, .integerLiteral: tokens.removeFirst()
                    default: return false
                    }
                    if tokens.first == .moduleSeparator {
                        tokens.removeFirst()
                        guard case .identifier = tokens.first else { return false }
                        tokens.removeFirst()
                    }
                    // A member may be CALLED: `p.m()` and `p.m(a:)` are postfix on the operand.
                    if tokens.first == .other("(") {
                        var index = 1
                        while index < tokens.count, tokens[index] != .other(")") { index += 1 }
                        guard index < tokens.count else { return false }
                        tokens.removeFirst(index + 1)
                    }
                case .leftBrace:
                    // a trailing closure on the preceding call / subscript
                    var depth = 0
                    while let head = tokens.first {
                        if head == .leftBrace { depth += 1 }
                        if head == .rightBrace { depth -= 1 }
                        tokens.removeFirst()
                        if depth == 0 { break }
                    }
                case .postfixQuestionMark, .exclamationMark:
                    tokens.removeFirst()
                case .leftSquare:
                    guard consumeBracketed() else { return false }
                    if tokens.first == .leftBrace {
                        var depth = 0
                        while let head = tokens.first {
                            if head == .leftBrace { depth += 1 }
                            if head == .rightBrace { depth -= 1 }
                            tokens.removeFirst()
                            if depth == 0 { break }
                        }
                    }
                default:
                    return true
                }
            }
        }

        func consumeBracketed() -> Bool {
            guard tokens.first == .leftSquare else { return false }
            tokens.removeFirst()
            while let head = tokens.first, head != .rightSquare { tokens.removeFirst(); _ = head }
            guard tokens.first == .rightSquare else { return false }
            tokens.removeFirst()
            return true
        }

        /// An operand an infix operator can take: an identifier / literal, or an array literal.
        func consumeOperand() -> Bool {
            // A PREFIX operator may precede the operand: in `X ?? ??.p` the second `??` is
            // prefix (space before, `.` after — and `isRightBound` returns `!isLeftBound` for a
            // following `.`), applied to the implicit member `.p`.
            while case .oper(_, .prefix, _) = tokens.first { tokens.removeFirst() }
            // `.name` — an implicit member expression, as in `X ?? .p`.
            if tokens.first == .period {
                tokens.removeFirst()
                // An implicit member needs a DECLARATION NAME. `.0` is not one — a tuple index is
                // only a member of an actual expression — so `?? ??.0` has no operand and swift
                // recovers, while `?? ??.p` is clean. (Branch 3 still accepts `.0` as a key-path
                // PROPERTY: `\Foo.0` is fine. Different position, different rule.)
                switch tokens.first {
                case .identifier: tokens.removeFirst()
                default: return false
                }
                // ...which may be module-qualified: `?? .Mod::p`.
                if tokens.first == .moduleSeparator {
                    tokens.removeFirst()
                    guard case .identifier = tokens.first else { return false }
                    tokens.removeFirst()
                }
                // ...which may itself be CALLED: `?? ??.m()` applies a prefix operator to the
                // implicit member call `.m()`.
                if tokens.first == .other("(") {
                    var index = 1
                    while index < tokens.count, tokens[index] != .other(")") { index += 1 }
                    guard index < tokens.count else { return false }
                    tokens.removeFirst(index + 1)
                }
                return true
            }
            switch tokens.first {
            case .identifier, .integerLiteral:
                tokens.removeFirst()
                // a module-qualified reference: `Mod::p` (SE-0491)
                if tokens.first == .moduleSeparator {
                    tokens.removeFirst()
                    guard case .identifier = tokens.first else { return false }
                    tokens.removeFirst()
                }
                // an optional call argument list — `m()` and `m(a:)` are operands
                if tokens.first == .other("(") {
                    var index = 1
                    while index < tokens.count, tokens[index] != .other(")") { index += 1 }
                    if index < tokens.count { tokens.removeFirst(index + 1) }
                }
                return true
            case .leftSquare:
                return consumeBracketed()
            default:
                return false
            }
        }

        guard consumePostfixChain(allowOperatorPostfix: false) else { return false }
        while !tokens.isEmpty {
            // `as` / `is` are KEYWORD binary operators taking a TYPE on the right. A type — not an
            // expression — so it accepts `.member` (a qualified/member type, with an optional
            // `::` module selector), `?`/`!` (optional / IUO) and generic arguments, but NOT `.?`:
            // `\Foo as T.p`, `as T?`, `as T.Mod::p` are clean while `as T.?` recovers.
            if tokens.first == .identifier("as") || tokens.first == .identifier("is") {
                tokens.removeFirst()
                // `as?` / `as!` carry a mark before the type.
                if tokens.first == .postfixQuestionMark || tokens.first == .exclamationMark {
                    tokens.removeFirst()
                }
                guard case .identifier = tokens.first else { return false }
                tokens.removeFirst()
                typeTail: while true {
                    if tokens.first == .postfixQuestionMark || tokens.first == .exclamationMark {
                        tokens.removeFirst(); continue
                    }
                    // `T & U` — a protocol COMPOSITION type, so it stays in type-land: `as T & x.p`
                    // extends it with a member type (clean) while `as T & x.?` and `as T & x[0]`
                    // are expression syntax and recover.
                    if case .oper("&", _, _) = tokens.first, tokens.count > 1,
                       case .identifier = tokens[1] {
                        tokens.removeFirst(2); continue
                    }
                    if tokens.first == .moduleSeparator {
                        tokens.removeFirst()
                        guard case .identifier = tokens.first else { return false }
                        tokens.removeFirst(); continue
                    }
                    if tokens.first == .period, tokens.count > 1, case .identifier = tokens[1] {
                        tokens.removeFirst(2); continue
                    }
                    if case .oper("<", _, _) = tokens.first {
                        var depth = 0
                        var index = 0
                        while index < tokens.count {
                            if case .oper(let t, _, _) = tokens[index], t.hasPrefix("<") { depth += 1 }
                            if case .oper(let t, _, _) = tokens[index], t.hasPrefix(">") {
                                depth -= 1; if depth == 0 { index += 1; break }
                            }
                            index += 1
                        }
                        if depth == 0, index > 0 { tokens.removeFirst(index); continue }
                    }
                    break typeTail
                }
                continue
            }
            // Only a BINARY operator continues the sequence, and it REQUIRES an operand. A
            // PREFIX operator here is an error: `\Foo.p<T> ??[0]` classifies `??` as prefix
            // (space before, `[` after) and swift recovers, inserting a missing token.
            guard case .oper(_, .binary, _) = tokens.first else { return false }
            tokens.removeFirst()
            guard consumeOperand() else { return false }
            guard consumePostfixChain(allowOperatorPostfix: true) else { return false }
        }
        return true
    }
}

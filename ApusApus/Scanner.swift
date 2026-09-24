//
//  Scanner.swift
//  ApusApus
//
//  Created by Johannes Brands on 01/03/2024.
//

import OSLog
import Foundation

enum ScannerFailure: Error {
    case charactersDoNotMatchAnySymbol(position: String.Index, input: String)
    case nonAdvancingMatch(position: String.Index, tokenKind: String, tokenImage: String)
    case couldNotReadFile
}

struct TokenPattern {
    let source: String
    let regex: Regex<AnyRegexOutput>
    let isLiteral: Bool
    let isSkip: Bool
    /// `@literalMunch` — this regex terminal participates in literal-suppression
    /// maximal munch (e.g. identifier, operator). A literal match is suppressed when a
    /// literal-munch terminal has a strictly longer match at the same start
    /// (`for` inside `foreach`). Grammar-declared; see TODO #0 / `Multiple
    /// Lexicalisation` §4.1 (suffix-property longest-across).
    var isLiteralMunch: Bool = false
    /// `@preempt(X, …)` first operand — besides its maximal match, this (regex) terminal also
    /// offers the prefix ending before each *internal* position where terminal `X`
    /// begins a non-empty match. Ports swift-syntax's `lexOperatorIdentifier`
    /// regex-scan (Cursor.swift:2275): an operator token is split before an internal
    /// `regexOpenSlash` so a regex literal can follow a prefix operator
    /// (`^^/regex/` → `^^` + `/regex/`). A leading match position is not a split
    /// point. Keying on a *terminal* (not a raw char) names the construct. The
    /// parser keeps only split points where `preemptConstruct` is viable, so
    /// production-body lookaround gates live with that construct. Stores the
    /// terminal *name*; resolved to an ID at parser build.
    var preemptStart: String? = nil
    /// `@preempt(X, N)` second operand — the COMMIT half. The first operand only *offers* the split
    /// ("give X a chance"); this says the shorter reading WINS where the named construct `N` actually
    /// parses. Among the candidate matches at one position (all sharing the start), if `N` is viable at
    /// the end of a shorter candidate, every longer candidate is dropped — so the maximal-munch token
    /// never swallows the start of a real `N`. Viability is answered by a memoised speculative
    /// recogniser sub-parse of `N` (not FOLLOW-gated), mirroring swift's `tryLexOperatorAsRegexLiteral`,
    /// which scans an operator for an internal `/`, tries the regex, and COMMITS when it scans — while
    /// keeping the whole operator when it does not (`^/x`). Stores the nonterminal *name*.
    var preemptConstruct: String? = nil
    /// Structured `-` lexical-nonterminal marker. This terminal has no regex/literal source; its match
    /// is computed by a GLL sub-parse of the same-named nonterminal (see `GrammarNode.isLexicalToken`
    /// and `MessageParser` lexicalTokenRecognisers). Skipped when building regexByID/literalSourceByID.
    var isLexicalToken: Bool = false

    // Accept any RegexComponent (e.g. Swift literal `/foo/` typed as Regex<Substring>) and wrap
    // to Regex<AnyRegexOutput> so the storage can also hold regexes that include capturing
    // groups (e.g. backreference forms like `(#+)…\1`).
    init<R: RegexComponent>(_ source: String, _ regex: R, _ isLiteral: Bool, _ isSkip: Bool) {
        self.source = source
        self.regex = Regex<AnyRegexOutput>(regex.regex)
        self.isLiteral = isLiteral
        self.isSkip = isSkip
    }
}

final class Token: CustomStringConvertible {
    var image: Substring
    var kind: String

    init(image: Substring, kind: String) {
        self.image = image
        self.kind = kind
    }

    var stripped: String {
        switch kind {
        case "literal", "empty":
            return String(image.dropFirst().dropLast())
        case "regex":
            return String(image.dropFirst().dropLast())
        case "action":
            return image.dropFirst().dropLast()
                .replacingOccurrences(of: "\\'", with: "'")
        case "message":
            return String(image.dropFirst(3))
        case "pragma":
            return String(image.dropFirst())
        default:
            return String(image)
        }
    }

    var description: String { "'" + kind + "'" }

    var debugDescription: String {
        "'" + kind + "'"
    }
}

private struct Pattern {
    let kind: String
    let source: String
    let regex: Regex<AnyRegexOutput>
    let isLiteral: Bool
    let isSkip: Bool
}

/// Scanner takes an input string and token patterns, and produces a token array.
/// One instance per scan — no shared mutable state.
/// Literal keywords are matched via hasPrefix; only true regex patterns use the regex engine.
final class Scanner {
    
    let input: String
    var tokens: [Token] = []                // normal, visible tokens that can be referenced in the grammar production rules
    var trivia: [[Token]] = [[]]            // skipped tokens are stored as lists in an array indexed by the visible token following them
    
    private var literalPatterns: [Pattern] = []
    private var regexPatterns: [Pattern] = []
    private let telemetry: any ScannerTelemetry
    
    init(fromString inputString: String, patterns: [String: TokenPattern], telemetry: (any ScannerTelemetry)? = nil) throws {
        self.input = inputString
        self.telemetry = telemetry ?? makeDefaultScannerTelemetry()
        
        // Partition: keyword terminals use fast hasPrefix, the rest use regex engine.
        for (kind, pattern) in patterns {
            let p = Pattern(kind: kind, source: pattern.source, regex: pattern.regex, isLiteral: pattern.isLiteral, isSkip: pattern.isSkip)
            if pattern.isLiteral {
                literalPatterns.append(p)
            } else {
                regexPatterns.append(p)
            }
        }
        
        self.telemetry.scannerConfigured(literalPatternCount: literalPatterns.count, regexPatternCount: regexPatterns.count)
        try scanAllTokens()
    }
    
    private struct Candidate {
        let token: Token
        let pattern: Pattern
    }
    
    private func scanAllTokens() throws {
        var matchStart = input.startIndex

        var charsScanned = 0
        let inputSize = input.utf8.count
        let scanInterval = 10_000
        let scanByteLimit = 0
        telemetry.scanStarted(inputSize: inputSize, literalPatternCount: literalPatterns.count, regexPatternCount: regexPatterns.count)

        while matchStart != input.endIndex {
            var matchEnd = matchStart
            var candidates: [Candidate] = []
            let remaining = input[matchStart...]

            // Phase 1: literal keywords via hasPrefix.
            let litT0 = CFAbsoluteTimeGetCurrent()
            for lp in literalPatterns {
                if remaining.hasPrefix(lp.source) {
                    let literalEnd = input.index(matchStart, offsetBy: lp.source.count)
                    if literalEnd > matchEnd {
                        matchEnd = literalEnd
                        candidates.removeAll()
                    }
                    if literalEnd == matchEnd {
                        candidates.append(Candidate(
                            token: Token(image: input[matchStart..<literalEnd], kind: lp.kind),
                            pattern: lp))
                    }
                }
            }

            telemetry.recordLiteralPhase(elapsed: CFAbsoluteTimeGetCurrent() - litT0)

            // Phase 2: regex patterns via prefixMatch.
            let regT0 = CFAbsoluteTimeGetCurrent()

            for rp in regexPatterns {
                let t0 = CFAbsoluteTimeGetCurrent()

                let match = remaining.prefixMatch(of: rp.regex)

                let elapsed = CFAbsoluteTimeGetCurrent() - t0
                telemetry.recordRegexCall(kind: rp.kind, elapsed: elapsed, charsScanned: charsScanned, inputSize: inputSize)

                if let match {
                    if match.0.endIndex > matchEnd {
                        matchEnd = match.0.endIndex
                        candidates.removeAll()
                    }
                    if match.0.endIndex == matchEnd {
                        candidates.append(Candidate(
                            token: Token(image: match.0, kind: rp.kind),
                            pattern: rp))
                    }
                }
            }
            
            telemetry.recordRegexPhase(elapsed: CFAbsoluteTimeGetCurrent() - regT0)

            // Phase 3: resolve candidates — longest match wins, ties form Schrödinger chain
            guard !candidates.isEmpty else {
                try scanError(position: matchStart)
            }

            // Same-span ties (Schrödinger duals) are no longer tracked — Phase D
            // moved disambiguation to per-end LCNP filters in the parser, so the
            // eager scanner only needs to commit one candidate per position.
            // Order: literal-emit first, everything else after (stable within
            // group), so a literal keyword wins over a same-length identifier
            // regex by default.
            let front = candidates.filter { $0.pattern.isLiteral && !$0.pattern.isSkip }
            let back = candidates.filter { !($0.pattern.isLiteral && !$0.pattern.isSkip) }
            let ordered = front + back

            let headMatch = ordered[0].token
            let headPattern = ordered[0].pattern

            if headMatch.image.isEmpty {
                let pos = input.linePosition(of: matchStart)
                telemetry.recordNonAdvancingMatch(
                    kind: headMatch.kind,
                    image: String(headMatch.image),
                    position: pos,
                    candidates: ordered.map { $0.token.kind }
                )
                throw ScannerFailure.nonAdvancingMatch(position: matchStart, tokenKind: headMatch.kind, tokenImage: String(headMatch.image))
            }

            telemetry.recordMatchedToken(tokenDescription: headMatch.description, image: String(headMatch.image))

            if headPattern.isSkip {
                trivia[tokens.count].append(headMatch)
            } else {
                tokens.append(headMatch)
                trivia.append([])
            }
            matchStart = matchEnd
            charsScanned += headMatch.image.utf8.count
            if charsScanned % scanInterval < headMatch.image.utf8.count {
                telemetry.recordProgress(charsScanned: charsScanned, inputSize: inputSize, tokenCount: tokens.count)
            }
            if scanByteLimit > 0 && charsScanned >= scanByteLimit {
                telemetry.recordByteLimitStop(scanByteLimit)
                break
            }
        }
        
        let end = input.endIndex
        tokens.append(Token(image: input[end..<end], kind: "○"))  // append EndOfString token anchored in input
        telemetry.scanFinished(inputSize: inputSize, tokenCount: tokens.count)
    }

    private func scanError(position: String.Index) throws -> Never {
        var error = "scan error: input characters at position \(input.linePosition(of: position)) do not match any symbol in the grammar\n"
        let lineRange = input.lineRange(for: position ..< input.index(after: position))
        error += input[lineRange]
        let before = lineRange.lowerBound ..< position
        for _ in 0 ..< input[before].count {
            error += " "
        }
        error += "^~~~~~~~"
        Logger.scan.error("\(error, privacy: .public)")
        throw ScannerFailure.charactersDoNotMatchAnySymbol(position: position, input: input)
    }
}

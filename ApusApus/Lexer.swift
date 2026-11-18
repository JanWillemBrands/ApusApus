//
//  Lexer.swift
//  ApusApus
//
//  Created by Johannes Brands on 2026.08.28.
//

import Foundation
import BitCollections

// MARK: - LCNP source-position model
//
// See `Ambiguity.md` §3. Positions everywhere (BSR/CRF/
// Descriptor/Oracle) are `CharPosition`s, UTF-8 offsets into the parser's input. Lex queries
// are answered on-demand by `OnDemandLiteralLexer`.

/// One terminal match returned by the lexer.
/// Empty result from `lex` means the terminal does not match at that position.
///
/// Carries the three positions every consumer needs (mirrors swift-syntax's
/// `positionAfterSkippingLeadingTrivia` / `endPositionBeforeTrailingTrivia`
/// / `endPosition` — the fourth, "start of leading trivia", is just the `pos`
/// argument the caller passed in):
///
///   - `start`      — content start (after leading-trivia skip)
///   - `end`        — content end (before trailing-trivia skip)
///   - `triviaEnd`  — cursor position after trailing-trivia handling. Normal parses skip trailing
///                    trivia; recognizer sub-parses leave it for the surrounding recognizer.
///
/// `boundaryMatches` uses `end` vs. `triviaEnd` to answer
/// `<s>`/`>s<`/`<n>`/`>n<` from a single commit record.
struct LexMatch: Hashable {
    let terminalID: Int
    let start: CharPosition
    let end: CharPosition
    let triviaEnd: CharPosition
}

/// Key for the parser's `(pos, terminalID) → [LexMatch]` memoization table.
/// Lex queries are pure given the input; the same (pos, terminalID) gets asked
/// many times during a parse (viable iterates `firstBS`, descriptor re-entry
/// revisits positions). Without this cache the per-terminal LCNP path would
/// re-run pattern matching tens of thousands of times.
struct LexCacheKey: Hashable {
    let pos: CharPosition
    let terminalID: Int
}

// The `LCNPLexer` protocol was removed (2026-08-28). It had exactly one conformer
// (`OnDemandLiteralLexer`) and one use site (`MessageParser.lexer`), so it was pure indirection —
// and an existential on the hottest path in the parser. Its two extension defaults were dead:
// `triviaSkipEnd` is implemented by the struct, and `lexLKH` — the paper's
// `lexLKH(t, i, β, X)` — had NO overrides and NO call sites, so it never did anything. The
// predict-set filter that realises that idea lives parser-side in `MessageParser.tokenMatch`,
// which is where the decision belongs; naming a dead lexer method after it only muddled which
// layer owned the responsibility.

/// How one terminal kind is matched. `OnDemandLiteralLexer.terminals` holds one per symbol ID
/// (nil for symbols without a lex source: nonterminals, ε, virtual layout tokens).
enum TerminalMatcher {
    /// A literal, compared as UTF-8 bytes, like swiftc's lexer (no `Character` or
    /// canonical-equivalence semantics). A complete UTF-8 literal always ends on a scalar boundary.
    case literal([UInt8])
    /// A hand-written matcher (`ApusRegexLibrary.matchers`), run instead of its regex.
    case handWritten((MatcherInput, CharPosition) -> CharPosition?)
    /// A regex, run by Swift `Regex`.
    case regex(Regex<AnyRegexOutput>)
    /// A recogniser returning the longest end at a position: the GLL sub-parse of a structured
    /// `-` / `:` nonterminal, or a parse-scoped `@builder` scanner.
    case recogniser((CharPosition) -> CharPosition?)
}

/// The lexer: answers "does terminal t match at position p, and where does it end?" on demand,
/// directly against the input, plus the trivia skip between tokens.
///
/// Virtual tokens: zero-length matches at source-derived positions, for layout-sensitive synthetic
/// tokens like `INDENT` / `DEDENT` (Python). `virtualTokensAt` is computed once per input; `lex`
/// consults it after the trivia skip. `transitions`-annotated terminals (Python's
/// `bracketNewline`) have no mode-gating here, a known regression.
///
/// In normal parses, `triviaEnd` coincides with the next visible-token start in well-formed inputs.
/// Recognizer sub-parses return at `end` so the surrounding structured token keeps ownership of
/// following trivia.
///
/// A `final class`, not a struct: the parser stores it as `var lexer: OnDemandLiteralLexer!`, and a
/// struct there was copied out of the optional on every `lexer.lex(…)`, one retain and one release
/// per reference-counted field per lex question (measured: a struct costs 11%).
final class OnDemandLiteralLexer {
    let input: String
    /// `input.endPosition`, the position one past the last byte.
    let inputEnd: CharPosition
    /// The input's UTF-8 bytes (with `input`, for the matchers' non-ASCII slow path). Positions
    /// index `matcherInput.bytes` directly.
    let matcherInput: MatcherInput
    /// How each terminal kind is matched, by symbol ID.
    let terminals: [TerminalMatcher?]
    /// Trivia, tried in this order at every point of the skip: the grammar's skip terminals, then
    /// its structured `:` trivia nonterminals (sub-parses, for nested constructs a regex cannot
    /// express).
    let trivia: [TerminalMatcher]
    /// `@preempt(X, …)` per terminal: besides the maximal match, also offer the
    /// prefix ending before each internal position where terminal `X` (the value)
    /// begins a non-empty match. Ports swift-syntax's operator regex-scan
    /// (`^^/regex/` → `^^` + `/regex/`, keyed on `regexOpenSlash`).
    let preemptStartByID: [Int: Int]
    /// Terminal IDs of `@literalMunch` terminals (identifier, operator, …).
    /// Maximal-munch (default, longest-across): a literal match is suppressed when
    /// any literal-munch terminal has a strictly longer match at the same start
    /// (`for` inside `foreach`, `_` inside `_foo`, `&` inside `&&`). The check is
    /// a runtime match of the declared terminal — the ground truth, not a
    /// derived extension set. See `Multiple Lexicalisation` §4.1.
    let literalMunchIDs: [Int]
    /// Terminal ID of the synthetic EOS sentinel (`"○"`). Matched directly at
    /// `inputEnd` (after trivia skip), since EOS isn't in
    /// `grammar.terminals` and wouldn't otherwise have a lex source.
    let eosID: Int
    /// Source-derived zero-length tokens keyed by position. Used by
    /// layout-sensitive grammars (Python's INDENT/DEDENT, etc.). Populated
    /// once at parse setup, gated on `grammar.usesInjectedLayoutTokens`.
    /// Multiple synthetic terminals at the same position appear once each in
    /// the value array (e.g. two DEDENTs at the same column).
    let virtualTokensAt: [CharPosition: [Int]]

    init(
        input: String,
        terminals: [TerminalMatcher?],
        trivia: [TerminalMatcher],
        preemptStartByID: [Int: Int],
        literalMunchIDs: [Int],
        eosID: Int,
        virtualTokensAt: [CharPosition: [Int]]
    ) {
        self.input = input
        self.inputEnd = input.endPosition
        self.matcherInput = MatcherInput(input)
        self.terminals = terminals
        self.trivia = trivia
        self.preemptStartByID = preemptStartByID
        self.literalMunchIDs = literalMunchIDs
        self.eosID = eosID
        self.virtualTokensAt = virtualTokensAt
    }

    /// `contentStart`: the caller already ran `skipTrivia(from: pos)` and is handing us the answer,
    /// so we must not redo it. Trivia is a pure function of `(input, pos)`, and the parser asks
    /// every terminal in a FIRST set about the SAME position — so without this the trivia before
    /// that position is rescanned once per candidate terminal (~100×), each rescan being a loop of
    /// regex `prefixMatch` calls over the whole comment block. That is what made heavily
    /// doc-commented files superlinear: `class Oracle` (40KB) never finished, while the same code
    /// with its `///` blocks stripped parsed fine.
    ///
    /// Passing the content start is transparent to trivia bookkeeping because `LexMatch` carries no
    /// `triviaStart` — the parser supplies that from its own cursor when it builds the
    /// `TerminalCommit`, so `<s>`/`>s<`/`<n>`/`>n<` still see the true gap.
    func lex(
        at pos: CharPosition,
        terminalID: Int,
        suppressesLeadingTrivia: Bool = false,
        consumesTrailingTrivia: Bool = true,
        appliesLiteralMunch: Bool = true,
        contentStart: CharPosition? = nil
    ) -> [LexMatch] {
        let scanStart = suppressesLeadingTrivia ? pos : (contentStart ?? skipTrivia(from: pos))
        // Virtual zero-length match: registered at this position by the
        // layout-table precompute (e.g. INDENT/DEDENT in Python).
        if let virtuals = virtualTokensAt[scanStart], virtuals.contains(terminalID) {
            return [LexMatch(terminalID: terminalID, start: scanStart, end: scanStart, triviaEnd: scanStart)]
        }
        if terminalID == eosID {
            // EOS matches at end of input (after any trailing trivia).
            guard scanStart == inputEnd else { return [] }
            return [LexMatch(terminalID: terminalID, start: scanStart, end: scanStart, triviaEnd: scanStart)]
        }
        guard scanStart < inputEnd, let matcher = terminals[terminalID],
              let end = matchEnd(matcher, at: scanStart) else { return [] }
        if case .literal = matcher, appliesLiteralMunch {
            // Maximal munch (longest-across): suppress this literal if any declared
            // `@literalMunch` terminal has a strictly longer match at the same
            // start — `for` inside `foreach`, `_` inside `_foo`. TODO #0.
            for classID in literalMunchIDs where classID != terminalID {
                if let munch = terminals[classID], let longer = matchEnd(munch, at: scanStart), longer > end { return [] }
            }
        }
        let cursorEnd = consumesTrailingTrivia ? skipTrivia(from: end) : end
        var results = [LexMatch(terminalID: terminalID, start: scanStart, end: end, triviaEnd: cursorEnd)]
        // @preempt(X, …): besides the maximal match, offer the prefix ending
        // before each internal position where terminal `X` begins — ports
        // swift-syntax lexOperatorIdentifier's regex-scan (Cursor.swift:2275),
        // letting `^^/regex/` split into `^^` + `/regex/` (X = regexOpenSlash).
        // A leading match position is not a split point. No trivia sits before
        // the split, so end == triviaEnd. Whether the split survives is
        // decided by `@preempt` construct viability in `MessageParser.tokenMatch`.
        if let splitID = preemptStartByID[terminalID], let split = terminals[splitID] {
            var i = scalarEnd(at: scanStart)
            while i < end {
                if matchEnd(split, at: i) != nil {
                    results.append(LexMatch(terminalID: terminalID, start: scanStart, end: i, triviaEnd: i))
                }
                i = scalarEnd(at: i)
            }
        }
        return results
    }

    /// Where a match of `matcher` starting exactly at `pos` ends (the longest one), or nil. Only a
    /// literal may match empty; every other kind must consume input.
    @inline(__always)
    private func matchEnd(_ matcher: TerminalMatcher, at pos: CharPosition) -> CharPosition? {
        switch matcher {
        case .literal(let literal):
            return bytesMatch(literal, at: pos) ? pos + literal.count : nil
        case .handWritten(let match):
            return match(matcherInput, pos)
        case .regex(let regex):
            return regexEnd(regex, at: pos)
        case .recogniser(let recognise):
            guard let end = recognise(pos), end > pos else { return nil }
            return end
        }
    }

    /// The `Regex` path, kept out of line: a regex `Match` needs a large stack frame, which an
    /// inlined copy imposed on every lex question, the hand-written ones included (measured:
    /// `___chkstk_darwin` 2.8%). `m.range.upperBound` is type-agnostic, so this works for any
    /// `Regex<AnyRegexOutput>`, including regexes with capturing groups (`(#+)…\1`).
    @inline(never)
    private func regexEnd(_ regex: Regex<AnyRegexOutput>, at pos: CharPosition) -> CharPosition? {
        guard let m = input[from: pos].prefixMatch(of: regex) else { return nil }
        let end = input.position(of: m.range.upperBound)
        return end > pos ? end : nil
    }

    /// Do the input's bytes at `pos` start with `literal`?
    @inline(__always)
    func bytesMatch(_ literal: [UInt8], at pos: CharPosition) -> Bool {
        let bytes = matcherInput.bytes
        guard pos + literal.count <= bytes.count else { return false }
        for k in 0..<literal.count where bytes[pos + k] != literal[k] { return false }
        return true
    }

    /// The end of the scalar that starts at `pos`: past its UTF-8 continuation bytes.
    @inline(__always)
    private func scalarEnd(at pos: CharPosition) -> CharPosition {
        let bytes = matcherInput.bytes
        var i = pos + 1
        while i < bytes.count, bytes[i] & 0xC0 == 0x80 { i += 1 }
        return i
    }

    /// Advance past any sequence of trivia matches starting at `pos`, trying `trivia` in order.
    /// Stops as soon as nothing advances the cursor.
    ///
    /// What this costs now (≈ 6% of a Swift parse, 2026-11-18): not `whitespace`, which has a
    /// hand-written matcher, but the `comment` regex and the `multilineComment` sub-parse, both tried
    /// at every position where no whitespace starts. A hand-written matcher for `comment` (as a
    /// library `@builder`) and a `/*` check before the sub-parse would remove most of it.
    func skipTrivia(from pos: CharPosition) -> CharPosition {
        var cursor = pos
        outer: while cursor < inputEnd {
            for matcher in trivia {
                if let end = matchEnd(matcher, at: cursor), end > cursor {
                    cursor = end
                    continue outer
                }
            }
            break
        }
        return cursor
    }
}

/// A position in the parser's input: a UTF-8 offset (0 … `input.utf8.count`). Positions are always
/// on a scalar boundary, since every one comes from a lex step over whole scalars.
///
/// An `Int`, not a `String.Index`, so positions are array indices (`lexEntryOf`, and later the
/// position-keyed tables), fit into packed keys (`Descriptor`), and match the Bend twin's natural
/// numbers. A native `String` is stored as UTF-8 (`prepareInput` makes sure with
/// `makeContiguousUTF8()`), so converting to and from `String.Index` (the helpers below) is O(1).
/// `String.Index` appears only where a `String` API needs one: regexes and slicing text.
typealias CharPosition = Int

extension String {
    /// The index at UTF-8 offset `position`. O(1) on a native string.
    @inline(__always)
    func index(at position: CharPosition) -> String.Index {
        utf8.index(utf8.startIndex, offsetBy: position)
    }

    /// The UTF-8 offset of `index`. O(1) on a native string.
    @inline(__always)
    func position(of index: String.Index) -> CharPosition {
        utf8.distance(from: utf8.startIndex, to: index)
    }

    /// The position one past the end: `utf8.count`.
    @inline(__always)
    var endPosition: CharPosition { utf8.count }

    /// The text from `range.lowerBound` up to `range.upperBound`.
    @inline(__always)
    subscript(positions range: Range<CharPosition>) -> Substring {
        self[index(at: range.lowerBound)..<index(at: range.upperBound)]
    }

    /// The text from `position` to the end.
    @inline(__always)
    subscript(from position: CharPosition) -> Substring {
        self[index(at: position)...]
    }

    /// The `Character` starting at `position`.
    @inline(__always)
    subscript(characterAt position: CharPosition) -> Character {
        self[index(at: position)]
    }

    /// The position after the `Character` that starts at `position`.
    @inline(__always)
    func position(afterCharacterAt position: CharPosition) -> CharPosition {
        self.position(of: index(after: index(at: position)))
    }
}

extension CharPosition {
    /// Locate the token index whose image starts at this position. Returns
    /// `tokens.count` if `self` is at or past the end of `input`. Used only for
    /// diagnostics (`recordMismatch`, AST/diagram builders) — the parse loop
    /// never falls off a token boundary.
    func tokenIndex(in tokens: [Token], input: String) -> Int {
        if self >= input.endPosition { return tokens.count }
        // Binary search by the image's start position.
        var lo = 0, hi = tokens.count
        while lo < hi {
            let mid = (lo + hi) >> 1
            if input.position(of: tokens[mid].image.startIndex) < self { lo = mid + 1 } else { hi = mid }
        }
        return lo
    }
}

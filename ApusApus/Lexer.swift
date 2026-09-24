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
// Per "Multi-Lex Adoption Design 2.md". Positions everywhere (BSR/CRF/
// Descriptor/Oracle) are `String.Index` into the parser's input. Lex queries
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
/// many times during a parse (testSelect iterates `firstBS`, descriptor re-entry
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

/// On-demand per-terminal lexer covering literal terminals (Phase B Step 2) and regex
/// terminals (Phase C Step 1) directly against `input`. Trivia skipping uses
/// the grammar's `isSkip` patterns plus structured `:` non-terminal recognisers.
///
/// Phase E Step 2d (Jun 14, 2026): `LegacyScannerLexAdapter` retired — this
/// lexer is the only path now. Terminals not present in `literalSourceByID`
/// nor `regexByID` simply return no match. `transitions`-annotated terminals
/// (Python's `bracketNewline`) lose their mode-gating; that's a documented
/// regression captured in the design doc.
///
/// Virtual tokens (Phase G, Jun 14, 2026): zero-length matches at source-
/// derived positions. Used for layout-sensitive synthetic tokens like
/// `INDENT` / `DEDENT` (Python, Haskell offside) and EOS. The
/// `virtualTokensAt` table is computed once at parse setup by walking the
/// input lexically; the lex consults it after trivia-skipping the cursor.
/// EOS still has a fallback special-case for grammars that don't populate
/// the table.
///
/// In normal parses, `triviaEnd` coincides with the next visible-token start in well-formed inputs.
/// Recognizer sub-parses return at `end` so the surrounding structured token keeps ownership of
/// following trivia.
struct OnDemandLiteralLexer {
    let input: String
    /// `terminalID → literal source text` for every literal terminal in the grammar.
    let literalSourceByID: [Int: String]
    /// `terminalID → compiled regex` for every regex terminal (non-literal,
    /// non-skip). Answered from `input` directly via `prefixMatch`.
    let regexByID: [Int: Regex<AnyRegexOutput>]
    /// `@preempt(X, …)` per terminal: besides the maximal match, also offer the
    /// prefix ending before each internal position where terminal `X` (the value)
    /// begins a non-empty match. Ports swift-syntax's operator regex-scan
    /// (`^^/regex/` → `^^` + `/regex/`, keyed on `regexOpenSlash`).
    let preemptStartByID: [Int: Int]
    /// Terminal IDs of `@literalMunch` regex terminals (identifier, operator, …).
    /// Maximal-munch (default, longest-across): a literal match is suppressed when
    /// any literal-munch terminal has a strictly longer match at the same start
    /// (`for` inside `foreach`, `_` inside `_foo`, `&` inside `&&`). The check is
    /// a runtime prefix-match of the declared regex — the ground truth, not a
    /// derived extension set. See `Multiple Lexicalisation` §4.1.
    let literalMunchIDs: [Int]
    /// Compiled `isSkip` patterns from the grammar, used to skip whitespace /
    /// comments / etc. between the parser's cursor and the next meaningful
    /// character.
    let triviaRegexes: [Regex<AnyRegexOutput>]
    /// Recognisers for structured `:` non-terminal trivia (Phase E Step 2). Each closure
    /// runs a recursive `MessageParser` sub-parse rooted at the trivia non-
    /// terminal and returns the longest accepting end position at `pos`, or
    /// `nil` if no match. Tried after `triviaRegexes` in `skipTrivia`.
    let triviaRecognisers: [(CharPosition) -> CharPosition?]
    /// Structured `-` lexical-nonterminal recognisers, keyed by terminal kind ID. Each runs a GLL
    /// sub-parse rooted at the lexical nonterminal and returns its longest accept end at `pos`.
    /// A terminal in this map is matched by its recogniser (one token) instead of a regex/literal.
    let lexicalTokenRecognisers: [Int: (CharPosition) -> CharPosition?]
    /// Terminal ID of the synthetic EOS sentinel (`"○"`). Matched directly at
    /// `input.endIndex` (after trivia skip), since EOS isn't in
    /// `grammar.terminals` and wouldn't otherwise have a lex source.
    let eosID: Int
    /// Source-derived zero-length tokens keyed by character position. Used by
    /// layout-sensitive grammars (Python's INDENT/DEDENT, etc.). Populated
    /// once at parse setup, gated on `grammar.usesInjectedLayoutTokens`.
    /// Multiple synthetic terminals at the same position appear once each in
    /// the value array (e.g. two DEDENTs at the same column).
    let virtualTokensAt: [CharPosition: [Int]]
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
            guard scanStart == input.endIndex else { return [] }
            return [LexMatch(terminalID: terminalID, start: scanStart, end: scanStart, triviaEnd: scanStart)]
        }
        // Structured `-` lexical nonterminal: match extent via the GLL sub-parse recogniser. One token
        // spanning the sub-parse's longest accept from `scanStart`; no match → no token.
        if let recognise = lexicalTokenRecognisers[terminalID] {
            guard scanStart < input.endIndex, let end = recognise(scanStart), end > scanStart else { return [] }
            let cursorEnd = consumesTrailingTrivia ? skipTrivia(from: end) : end
            return [LexMatch(terminalID: terminalID, start: scanStart, end: end, triviaEnd: cursorEnd)]
        }
        if let literal = literalSourceByID[terminalID] {
            guard scanStart < input.endIndex else { return [] }
            let remaining = input[scanStart...]
            guard remaining.hasPrefix(literal) else { return [] }
            let literalEnd = input.index(scanStart, offsetBy: literal.count)
            // Maximal munch (longest-across): suppress this literal if any declared
            // `@literalMunch` terminal has a strictly longer match at the same
            // start — `for` inside `foreach`, `_` inside `_foo`. Runtime prefix-
            // match of the declared regex is the faithful test (no extension-set
            // extraction, no probes). TODO #0.
            for classID in literalMunchIDs where classID != terminalID {
                guard let rx = regexByID[classID] else { continue }
                if let rm = remaining.prefixMatch(of: rx), rm.range.upperBound > literalEnd {
                    return []
                }
            }
            let cursorEnd = consumesTrailingTrivia ? skipTrivia(from: literalEnd) : literalEnd
            return [LexMatch(terminalID: terminalID, start: scanStart, end: literalEnd, triviaEnd: cursorEnd)]
        }
        if let regex = regexByID[terminalID] {
            guard scanStart < input.endIndex else { return [] }
            // m.range.upperBound is type-agnostic — works for any Regex<Output>, including AnyRegexOutput
            // which is needed for regexes containing capturing groups (e.g. backreference forms like `(#+)…\1`).
            guard let m = input[scanStart...].prefixMatch(of: regex),
                  m.range.upperBound > scanStart else { return [] }
            let maxEnd = m.range.upperBound
            let cursorEnd = consumesTrailingTrivia ? skipTrivia(from: maxEnd) : maxEnd
            var results = [LexMatch(terminalID: terminalID, start: scanStart, end: maxEnd, triviaEnd: cursorEnd)]
            // @preempt(X, …): besides the maximal match, offer the prefix ending
            // before each internal position where terminal `X` begins — ports
            // swift-syntax lexOperatorIdentifier's regex-scan (Cursor.swift:2275),
            // letting `^^/regex/` split into `^^` + `/regex/` (X = regexOpenSlash).
            // A leading match position is not a split point. No trivia sits before
            // the split, so end == triviaEnd. Whether the split survives is
            // decided by `@preempt` construct viability in `MessageParser.tokenMatch`.
            if let splitID = preemptStartByID[terminalID] {
                var i = input.index(after: scanStart)
                while i < maxEnd {
                    if splitTerminalMatches(splitID, at: i) {
                        results.append(LexMatch(terminalID: terminalID, start: scanStart, end: i, triviaEnd: i))
                    }
                    i = input.index(after: i)
                }
            }
            return results
        }
        return []
    }

    /// Does the `@preempt` start terminal `terminalID` begin a non-empty match
    /// exactly at `pos` — no trivia skip (split points sit mid-token)? Used by the
    /// `@preempt` split loop to offer an operator prefix ending where terminal `X`
    /// can start. `X` is a single-char delimiter in practice (`regexOpenSlash`,
    /// `openAngle`), so this is cheap.
    private func splitTerminalMatches(_ terminalID: Int, at pos: CharPosition) -> Bool {
        if let literal = literalSourceByID[terminalID] {
            return input[pos...].hasPrefix(literal)
        }
        if let regex = regexByID[terminalID],
           let m = input[pos...].prefixMatch(of: regex), m.range.upperBound > pos {
            return true
        }
        return false
    }

    /// Advance past any sequence of trivia matches starting at `pos`. Tries
    /// regex trivia first (fast path), then structured `:` non-terminal recognisers
    /// (heavier, for nested constructs that regex can't express). Stops as
    /// soon as nothing advances the cursor.
    func skipTrivia(from pos: CharPosition) -> CharPosition {
        var cursor = pos
        outer: while cursor < input.endIndex {
            for re in triviaRegexes {
                if let m = input[cursor...].prefixMatch(of: re), m.range.upperBound > cursor {
                    cursor = m.range.upperBound
                    continue outer
                }
            }
            for recognise in triviaRecognisers {
                if let end = recognise(cursor), end > cursor {
                    cursor = end
                    continue outer
                }
            }
            break
        }
        return cursor
    }
}

/// Character index into the parser's input string.
/// `String.Index` for the initial implementation — a later perf pass may swap
/// to an interned integer if descriptor pressure justifies the complexity.
typealias CharPosition = String.Index

extension CharPosition {
    /// Locate the token index whose image starts at this position. Returns
    /// `tokens.count` if `self` is at or past `input.endIndex`. Used only for
    /// diagnostics (`recordMismatch`, AST/diagram builders) — the parse loop
    /// never falls off a token boundary.
    func tokenIndex(in tokens: [Token], input: String) -> Int {
        if self >= input.endIndex { return tokens.count }
        // Binary search by image.startIndex.
        var lo = 0, hi = tokens.count
        while lo < hi {
            let mid = (lo + hi) >> 1
            if tokens[mid].image.startIndex < self { lo = mid + 1 } else { hi = mid }
        }
        return lo
    }
}

//
//  LayoutTokenInjection.swift
//  ApusApus
//
//  Created by Johannes Brands on 2026.04.25.
//

// Layer 2 of the layout-sensitive parsing architecture (see "Layout Sensitive Parsing.md").
//
// Injects synthetic >>| (INDENT) and |<< (DEDENT) tokens into the token stream before parsing.
// The GLL parser sees these as ordinary terminals — no parser modifications required.
//
// Bracket suppression: indent tracking is suspended inside matched bracket pairs (e.g. Python's
// implicit line continuation inside (), [], {}).
//
// Newline-only tokens (visible NEWLINE terminals whose image is purely \n/\r) are passed through
// without triggering indent/dedent. This prevents blank lines and comment-only lines — which
// appear at column 0 — from causing premature dedent inside indented blocks.

import OSLog

/// Phase G (Jun 14, 2026), rewritten in Phase I (Jun 15, 2026) to walk
/// `input` directly without a scanner-produced token stream.
///
/// Returns a `[CharPosition: [kindID]]` table of zero-length synthetic tokens
/// (`>>|` / `|<<`) keyed by the source position where each fires. Used by
/// `OnDemandLiteralLexer.lex` to answer `INDENT`/`DEDENT` queries on-demand.
///
/// Algorithm: char-by-char walk of `input`. For each line, measure indent
/// column at the first visible char, compare to the indent stack, emit
/// `>>|` on increase or `|<<` for each level closed on decrease. Skip indent
/// tracking inside string literals, comments, and bracket nesting (implicit
/// line continuation). At end-of-input emit `|<<` for each remaining indent
/// level on the stack.
///
/// String/comment delimiters are Python-shaped (hardcoded for now): `"`, `'`,
/// `"""`, `'''` for strings (with backslash escapes); `#` for line comments.
/// Future grammars may parameterize these — they're the only language-
/// specific choices the algorithm makes.
///
/// Gating: caller checks `grammar.usesInjectedLayoutTokens` first; with the
/// flag off no work is done.
func computeVirtualLayoutTokens(
    input: String,
    indentKindID: Int,
    dedentKindID: Int,
    tabWidth: Int = 8,
    bracketPairs: [(open: String, close: String)] = []
) -> [CharPosition: [Int]] {
    var result: [CharPosition: [Int]] = [:]
    // Single-char bracket recognition. Multi-char brackets aren't supported
    // here yet (no concrete grammar needs them).
    let openers = Set(bracketPairs.compactMap { $0.open.first })
    let closers = Set(bracketPairs.compactMap { $0.close.first })

    var indentStack: [Int] = [0]
    var bracketDepth = 0
    var cursor = input.startIndex

    while cursor < input.endIndex {
        // (1) Measure indent column at line start.
        var col = 0
        while cursor < input.endIndex {
            let ch = input[cursor]
            if ch == " " { col += 1 }
            else if ch == "\t" { col += tabWidth - (col % tabWidth) }
            else { break }
            cursor = input.index(after: cursor)
        }

        // (2) Decide if this line has visible content. Blank lines (only a
        //     newline) and comment-only lines (# … \n) do not trigger
        //     indent/dedent — matches CPython's tokenizer.
        let firstVisible = cursor
        var hasContent = false
        if cursor < input.endIndex {
            let ch = input[cursor]
            if ch != "\n", ch != "\r", ch != "#" {
                hasContent = true
            }
        }

        // (3) Emit INDENT/DEDENT at the first-visible position, outside
        //     brackets. Multiple dedents at the same column collapse into a
        //     multi-element entry.
        if hasContent, bracketDepth == 0 {
            if col > indentStack.last! {
                indentStack.append(col)
                result[firstVisible, default: []].append(indentKindID)
            } else {
                while indentStack.count > 1, col < indentStack.last! {
                    indentStack.removeLast()
                    result[firstVisible, default: []].append(dedentKindID)
                }
            }
        }

        // (4) Walk to end of line, updating bracket depth, skipping string
        //     literals and comments.
        while cursor < input.endIndex {
            let ch = input[cursor]
            if ch == "\n" || ch == "\r" {
                cursor = input.index(after: cursor)
                if ch == "\r", cursor < input.endIndex, input[cursor] == "\n" {
                    cursor = input.index(after: cursor)
                }
                break
            }
            if ch == "#" {
                while cursor < input.endIndex, input[cursor] != "\n", input[cursor] != "\r" {
                    cursor = input.index(after: cursor)
                }
                continue
            }
            if ch == "\"" || ch == "'" {
                cursor = skipPythonStringLiteral(input, from: cursor, delim: ch)
                continue
            }
            if openers.contains(ch) { bracketDepth += 1 }
            else if closers.contains(ch), bracketDepth > 0 { bracketDepth -= 1 }
            cursor = input.index(after: cursor)
        }
    }

    // (5) Trailing dedents at end-of-input — pop the indent stack.
    while indentStack.count > 1 {
        indentStack.removeLast()
        result[input.endIndex, default: []].append(dedentKindID)
    }

    return result
}

/// Skip a Python string literal starting at `cursor`. Handles single-line
/// (`"…"`, `'…'`) and triple-quoted (`"""…"""`, `'''…'''`) variants, with
/// backslash escapes inside both. Returns the position just past the
/// terminating delimiter (or `input.endIndex` if the string is unterminated).
private func skipPythonStringLiteral(_ input: String, from cursor: CharPosition, delim: Character) -> CharPosition {
    // Detect triple-quoted by peeking two chars ahead.
    let secondIndex = input.index(after: cursor)
    let isTriple: Bool
    if secondIndex < input.endIndex, input[secondIndex] == delim {
        let thirdIndex = input.index(after: secondIndex)
        isTriple = thirdIndex < input.endIndex && input[thirdIndex] == delim
    } else {
        isTriple = false
    }

    if isTriple {
        var c = input.index(cursor, offsetBy: 3)
        while c < input.endIndex {
            if input[c] == "\\" {
                let next = input.index(after: c)
                c = next < input.endIndex ? input.index(after: next) : input.endIndex
                continue
            }
            if input[c] == delim {
                let one = input.index(after: c)
                let two = one < input.endIndex ? input.index(after: one) : input.endIndex
                if one < input.endIndex, two < input.endIndex,
                   input[one] == delim, input[two] == delim {
                    return input.index(after: two)
                }
            }
            c = input.index(after: c)
        }
        return input.endIndex
    } else {
        var c = input.index(after: cursor)
        while c < input.endIndex {
            let ch = input[c]
            if ch == "\\" {
                let next = input.index(after: c)
                c = next < input.endIndex ? input.index(after: next) : input.endIndex
                continue
            }
            if ch == delim { return input.index(after: c) }
            // Unterminated single-line string at line break — give up.
            if ch == "\n" || ch == "\r" { return c }
            c = input.index(after: c)
        }
        return input.endIndex
    }
}


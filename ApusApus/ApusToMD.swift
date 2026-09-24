//
//  ApusToMD.swift
//  ApusApus
//
//  Converts an APUS grammar into Markdown. APUS productions are kept as APUS
//  code blocks, `///` TSPL grammar comments become prose, and implementation
//  comments are dropped.
//

import Foundation

/// Convert an APUS grammar string into Markdown.
///
/// `///` comments are treated as the source-of-truth TSPL grammar text. Plain
/// line comments and block comments are omitted from the generated document.
func convertApusToMD(_ apus: String, title: String = "Summary of the Grammar") -> String {
    ApusMarkdownConverter(source: apus, title: title).convert()
}

private final class ApusMarkdownConverter {
    private enum ScanMode {
        case normal
        case string
        case regex
        case action
    }

    private let source: String
    private let title: String

    private var output: [String] = []
    private var isInCodeBlock = false
    private var isInBlockComment = false
    private var hasEmittedTitle = false
    private var emptyLineRun = 0
    private var literalTokens: Set<String> = []
    private var literalTokensByLength: [String] = []

    init(source: String, title: String) {
        self.source = source
        self.title = title
    }

    func convert() -> String {
        let grammar = sourceBeforeMessages()
        literalTokens = collectLiteralTokens(from: grammar)
        literalTokensByLength = literalTokens
            .filter { !$0.isEmpty }
            .sorted { lhs, rhs in
                lhs.count == rhs.count ? lhs < rhs : lhs.count > rhs.count
            }
        for line in grammar.split(separator: "\n", omittingEmptySubsequences: false) {
            processLine(String(line))
        }
        closeCodeBlock()

        while output.first == "" {
            output.removeFirst()
        }
        while output.last == "" {
            output.removeLast()
        }

        return output.joined(separator: "\n") + "\n"
    }

    private func sourceBeforeMessages() -> String {
        guard let marker = source.range(of: "^^^") else { return source }
        return String(source[..<marker.lowerBound])
    }

    private func collectLiteralTokens(from source: String) -> Set<String> {
        var literals: Set<String> = []
        var mode: ScanMode = .normal
        var escaped = false
        var literal = ""
        var isInComment = false
        var i = source.startIndex

        func advance(_ count: Int = 1) {
            i = source.index(i, offsetBy: count)
        }

        while i < source.endIndex {
            if isInComment {
                if source[i...].hasPrefix("*/") {
                    isInComment = false
                    advance(2)
                } else {
                    advance()
                }
                continue
            }

            let c = source[i]
            switch mode {
            case .normal:
                if source[i...].hasPrefix("///") {
                    while i < source.endIndex, source[i] != "\n" {
                        advance()
                    }
                } else if source[i...].hasPrefix("//") {
                    while i < source.endIndex, source[i] != "\n" {
                        advance()
                    }
                } else if source[i...].hasPrefix("/*") {
                    isInComment = true
                    advance(2)
                } else if c == "\"" {
                    literal.removeAll(keepingCapacity: true)
                    mode = .string
                    advance()
                } else if c == "/" {
                    mode = .regex
                    advance()
                } else if c == "'" {
                    mode = .action
                    advance()
                } else {
                    advance()
                }
            case .string:
                if escaped {
                    literal.append(c)
                    escaped = false
                } else if c == "\\" {
                    escaped = true
                } else if c == "\"" {
                    literals.insert(literal)
                    mode = .normal
                } else {
                    literal.append(c)
                }
                advance()
            case .regex:
                if escaped {
                    escaped = false
                } else if c == "\\" {
                    escaped = true
                } else if c == "/" {
                    mode = .normal
                }
                advance()
            case .action:
                if escaped {
                    escaped = false
                } else if c == "\\" {
                    escaped = true
                } else if c == "'" {
                    mode = .normal
                }
                advance()
            }
        }

        return literals
    }

    private func processLine(_ line: String) {
        if let doc = documentationCommentText(in: line) {
            closeCodeBlock()
            emptyLineRun = 0
            appendDocumentationLine(doc)
            return
        }

        guard let code = stripImplementationComments(from: line), !code.isEmpty else {
            if line.trimmingCharacters(in: .whitespaces).isEmpty {
                processEmptyLine()
            }
            return
        }

        emptyLineRun = 0
        openCodeBlock()
        output.append(code)
    }

    private func processEmptyLine() {
        guard isInCodeBlock else { return }

        emptyLineRun += 1
        if emptyLineRun == 1 {
            output.append("")
        } else {
            if output.last == "" {
                output.removeLast()
            }
            closeCodeBlock()
            emptyLineRun = 0
        }
    }

    private func documentationCommentText(in line: String) -> String? {
        let trimmed = line.trimmingCharacters(in: .whitespaces)
        guard trimmed.hasPrefix("///") else { return nil }
        var text = String(trimmed.dropFirst(3))
        if text.first == " " {
            text.removeFirst()
        }
        return text
    }

    private func appendDocumentationLine(_ text: String) {
        let trimmed = text.trimmingCharacters(in: .whitespaces)
        guard !trimmed.isEmpty else {
            output.append("")
            return
        }

        if isSectionTitle(trimmed) {
            output.append("")
            output.append((hasEmittedTitle ? "## " : "# ") + titleCase(trimmed))
            hasEmittedTitle = true
        } else if trimmed.hasPrefix("Grammar of ") {
            output.append("")
            output.append("### \(trimmed)")
        } else {
            output.append("_\(formatGrammarText(trimmed))_")
        }
    }

    private func openCodeBlock() {
        guard !isInCodeBlock else { return }
        if !output.isEmpty, output.last != "" {
            output.append("")
        }
        output.append("```apus")
        isInCodeBlock = true
    }

    private func closeCodeBlock() {
        guard isInCodeBlock else { return }
        if output.last == "" {
            output.removeLast()
        }
        output.append("```")
        output.append("")
        isInCodeBlock = false
        emptyLineRun = 0
    }

    private func stripImplementationComments(from line: String) -> String? {
        var result = ""
        var mode: ScanMode = .normal
        var escaped = false
        var i = line.startIndex

        func advance(_ count: Int = 1) {
            i = line.index(i, offsetBy: count)
        }

        while i < line.endIndex {
            if isInBlockComment {
                if line[i...].hasPrefix("*/") {
                    isInBlockComment = false
                    advance(2)
                } else {
                    advance()
                }
                continue
            }

            let c = line[i]

            switch mode {
            case .normal:
                if line[i...].hasPrefix("//") {
                    i = line.endIndex
                } else if line[i...].hasPrefix("/*") {
                    isInBlockComment = true
                    advance(2)
                } else {
                    result.append(c)
                    if c == "\"" {
                        mode = .string
                    } else if c == "/" {
                        mode = .regex
                    } else if c == "'" {
                        mode = .action
                    }
                    advance()
                }
            case .string:
                result.append(c)
                if escaped {
                    escaped = false
                } else if c == "\\" {
                    escaped = true
                } else if c == "\"" {
                    mode = .normal
                }
                advance()
            case .regex:
                result.append(c)
                if escaped {
                    escaped = false
                } else if c == "\\" {
                    escaped = true
                } else if c == "/" {
                    mode = .normal
                }
                advance()
            case .action:
                result.append(c)
                if escaped {
                    escaped = false
                } else if c == "\\" {
                    escaped = true
                } else if c == "'" {
                    mode = .normal
                }
                advance()
            }
        }

        let trimmed = trimTrailingWhitespace(result)
        return trimmed.trimmingCharacters(in: .whitespaces).isEmpty ? nil : trimmed
    }

    private func isSectionTitle(_ text: String) -> Bool {
        guard text.count >= 3, text.count <= 60,
              text.contains(where: { $0.isLetter })
        else { return false }
        return text.allSatisfy { c in
            c.isUppercase || c.isNumber || c == " " || c == "." || c == "$"
        }
    }

    private func titleCase(_ text: String) -> String {
        text.lowercased()
            .split(separator: " ")
            .enumerated()
            .map { index, word in
                if index != 0, ApusMarkdownConverter.smallTitleWords.contains(String(word)) {
                    return String(word)
                }
                guard let first = word.first else { return "" }
                return String(first).uppercased() + String(word.dropFirst())
            }
            .joined(separator: " ")
    }

    private func formatGrammarText(_ text: String) -> String {
        var rendered = ""
        var token = ""
        var i = text.startIndex

        func flushToken() {
            guard !token.isEmpty else { return }
            if literalTokens.contains(token) {
                rendered += "**\(escapeMarkdownLiteral(token))**"
            } else {
                rendered += escapeMarkdownLiteral(token)
            }
            token.removeAll(keepingCapacity: true)
        }

        while i < text.endIndex {
            if let literal = matchingLiteral(in: text, at: i) {
                flushToken()
                rendered += "**\(escapeMarkdownLiteral(literal))**"
                i = text.index(i, offsetBy: literal.count)
                continue
            }

            let c = text[i]
            if c.isLetter || c.isNumber || c == "_" || c == "#" || c == "-" {
                token.append(c)
            } else {
                flushToken()
                rendered.append(contentsOf: escapeMarkdownPunctuation(c))
            }
            i = text.index(after: i)
        }
        flushToken()

        return rendered
    }

    private func matchingLiteral(in text: String, at index: String.Index) -> String? {
        for literal in literalTokensByLength {
            guard text[index...].hasPrefix(literal),
                  literalCanRender(in: text, at: index, literal: literal)
            else { continue }
            return literal
        }
        return nil
    }

    private func literalCanRender(in text: String, at index: String.Index, literal: String) -> Bool {
        let end = text.index(index, offsetBy: literal.count)
        let before = index > text.startIndex ? text[text.index(before: index)] : nil
        let after = end < text.endIndex ? text[end] : nil

        if literal.allSatisfy({ isGrammarWordCharacter($0) }) {
            return !isGrammarNameCharacter(before) && !isGrammarNameCharacter(after)
        }

        if literal.count == 1, let first = literal.first, !isGrammarWordCharacter(first) {
            return !isGrammarNameCharacter(before) && !isGrammarNameCharacter(after)
                && isWhitespaceOrBoundary(before)
                && isWhitespaceOrBoundary(after)
        }

        return !isGrammarNameInteriorMatch(before: before, after: after)
    }

    private func isGrammarWordCharacter(_ c: Character?) -> Bool {
        guard let c else { return false }
        return c.isLetter || c.isNumber || c == "_" || c == "#"
    }

    private func isGrammarNameCharacter(_ c: Character?) -> Bool {
        guard let c else { return false }
        return isGrammarWordCharacter(c) || c == "-"
    }

    private func isWhitespaceOrBoundary(_ c: Character?) -> Bool {
        guard let c else { return true }
        return c.isWhitespace
    }

    private func isGrammarNameInteriorMatch(before: Character?, after: Character?) -> Bool {
        isGrammarNameCharacter(before) && isGrammarNameCharacter(after)
    }

    private func escapeMarkdownLiteral(_ text: String) -> String {
        text.map { c in
            switch c {
            case "\\", "`", "*", "_":
                return "\\\(c)"
            default:
                return String(c)
            }
        }.joined()
    }

    private func escapeMarkdownPunctuation(_ c: Character) -> String {
        switch c {
        case "\\", "`", "*", "_":
            return "\\\(c)"
        default:
            return String(c)
        }
    }

    private func trimTrailingWhitespace(_ text: String) -> String {
        var result = text
        while let last = result.last, last == " " || last == "\t" {
            result.removeLast()
        }
        return result
    }

    private static let smallTitleWords: Set<String> = [
        "a", "an", "and", "as", "at", "but", "by", "for", "from", "in", "of",
        "on", "or", "the", "to", "with",
    ]
}

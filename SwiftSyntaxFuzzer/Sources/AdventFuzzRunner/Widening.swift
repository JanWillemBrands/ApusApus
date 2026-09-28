import Foundation

// Widening lanes (FUZZER.md / Wide lanes): single-token-boundary mutation of a large real-code
// corpus, placed in varied contexts, plus a reducer that shrinks every new failure so a long run
// yields short, deduplicated cases instead of thousands of wrapper variants.

// MARK: - Approximate tokenizer

/// A token and the trivia (whitespace, comments) in front of it. Approximate by design: the
/// mutated text is judged by swift-syntax anyway, so a token boundary only has to be plausible.
struct FuzzToken {
    enum Kind { case word, number, string, op, punct }
    var leading: String
    var text: String
    var kind: Kind
}

struct FuzzTokens {
    var tokens: [FuzzToken]
    var trailing: String

    var rendered: String {
        var out = ""
        for (index, token) in tokens.enumerated() {
            var leading = token.leading
            // Two words or numbers that would fuse after an edit get one space.
            if leading.isEmpty, index > 0, gluesToPrevious(index) { leading = " " }
            out += leading + token.text
        }
        return out + trailing
    }

    private func gluesToPrevious(_ index: Int) -> Bool {
        let previous = tokens[index - 1].kind, current = tokens[index].kind
        let wordLike: Set<FuzzToken.Kind> = [.word, .number]
        return (wordLike.contains(previous) && wordLike.contains(current)) || (previous == .op && current == .op)
    }

    init(tokens: [FuzzToken], trailing: String) {
        self.tokens = tokens
        self.trailing = trailing
    }

    init(_ source: String) {
        let chars = Array(source.unicodeScalars)
        var i = 0
        var leading = ""
        var tokens: [FuzzToken] = []
        func isWordStart(_ c: Unicode.Scalar) -> Bool { c == "_" || c == "$" || CharacterSet.letters.contains(c) }
        func isWord(_ c: Unicode.Scalar) -> Bool { isWordStart(c) || CharacterSet.decimalDigits.contains(c) }
        let opChars = Set("/=-+!*%<>&|^~?.".unicodeScalars)
        func text(_ a: Int, _ b: Int) -> String { String(String.UnicodeScalarView(chars[a..<b])) }

        while i < chars.count {
            let c = chars[i]
            let next: Unicode.Scalar? = i + 1 < chars.count ? chars[i + 1] : nil
            if CharacterSet.whitespacesAndNewlines.contains(c) {
                leading.unicodeScalars.append(c); i += 1; continue
            }
            if c == "/", next == "/" {
                let start = i
                while i < chars.count, chars[i] != "\n" { i += 1 }
                leading += text(start, i); continue
            }
            if c == "/", next == "*" {
                let start = i
                i += 2
                while i + 1 < chars.count, !(chars[i] == "*" && chars[i + 1] == "/") { i += 1 }
                i = min(chars.count, i + 2)
                leading += text(start, i); continue
            }
            let start = i
            var kind = FuzzToken.Kind.punct
            if c == "`" {
                i += 1
                while i < chars.count, chars[i] != "`", chars[i] != "\n" { i += 1 }
                i = min(chars.count, i + 1); kind = .word
            } else if isWordStart(c) || c == "#" && next.map(isWordStart) == true {
                i += 1
                while i < chars.count, isWord(chars[i]) { i += 1 }
                kind = .word
            } else if CharacterSet.decimalDigits.contains(c) {
                i += 1
                while i < chars.count, isWord(chars[i]) || (chars[i] == "." && i + 1 < chars.count
                        && CharacterSet.decimalDigits.contains(chars[i + 1])) { i += 1 }
                kind = .number
            } else if c == "\"" || (c == "#" && (next == "\"" || next == "#")) {
                // String literal, raw (`#"…"#`) or multi-line (`"""…"""`); skip to the matching close.
                var hashes = 0
                while i < chars.count, chars[i] == "#" { hashes += 1; i += 1 }
                let multiline = i + 2 < chars.count && chars[i] == "\"" && chars[i + 1] == "\"" && chars[i + 2] == "\""
                i += multiline ? 3 : 1
                let quote = multiline ? "\"\"\"" : "\""
                let close = Array((quote + String(repeating: "#", count: hashes)).unicodeScalars)
                while i < chars.count {
                    if hashes == 0, chars[i] == "\\" { i += 2; continue }
                    if !multiline, chars[i] == "\n" { break }
                    if i + close.count <= chars.count, Array(chars[i..<(i + close.count)]) == close { i += close.count; break }
                    i += 1
                }
                i = min(chars.count, i); kind = .string
            } else if opChars.contains(c) {
                while i < chars.count, opChars.contains(chars[i]) { i += 1 }
                kind = .op
            } else {
                i += 1
            }
            tokens.append(FuzzToken(leading: leading, text: text(start, i), kind: kind))
            leading = ""
        }
        self.tokens = tokens
        self.trailing = leading
    }
}

// MARK: - Mutation

/// Lexer-classified keywords plus the contextual words most often involved in parse decisions.
let fuzzKeywords = [
    "Any", "as", "associatedtype", "break", "case", "catch", "class", "continue", "default", "defer",
    "deinit", "do", "else", "enum", "extension", "fallthrough", "false", "fileprivate", "for", "func",
    "guard", "if", "import", "in", "init", "inout", "internal", "is", "let", "nil", "operator",
    "precedencegroup", "private", "protocol", "public", "repeat", "rethrows", "return", "self", "Self",
    "static", "struct", "subscript", "super", "switch", "throw", "throws", "true", "try", "typealias",
    "var", "where", "while",
    "any", "some", "each", "async", "await", "borrowing", "consuming", "sending", "isolated",
    "nonisolated", "mutating", "nonmutating", "override", "required", "convenience", "lazy", "weak",
    "unowned", "get", "set", "willSet", "didSet", "_modify", "_read", "yield", "macro", "package",
    "consume", "copy", "discard", "then", "using", "open", "final", "indirect", "dynamic", "optional",
    "_", "Type", "Protocol",
]

struct TokenMutator {
    /// Tokens sampled from the corpus, by kind, for same-kind splicing.
    let pool: [FuzzToken.Kind: [String]]

    init(corpus: [SeedEntry]) {
        var pool: [FuzzToken.Kind: [String]] = [:]
        for entry in corpus.prefix(2000) {
            for token in FuzzTokens(entry.source).tokens where token.text.count <= 24 {
                pool[token.kind, default: []].append(token.text)
            }
        }
        self.pool = pool
    }

    /// Applies 1–3 edits, each at ONE token boundary, and names them for the lane label.
    func mutate(_ source: String, using rng: inout SplitMix64) -> (String, String) {
        var stream = FuzzTokens(source)
        guard !stream.tokens.isEmpty else { return (source, "none") }
        var names: [String] = []
        for _ in 0...rng.nextInt(upperBound: 3) {
            let i = rng.nextInt(upperBound: stream.tokens.count)
            switch rng.nextInt(upperBound: 11) {
            case 0:
                stream.tokens[i].leading = stream.tokens[i].leading.contains("\n") ? " " : "\n"; names.append("newline")
            case 1:
                stream.tokens[i].leading = ""; names.append("glue")
            case 2:
                stream.tokens[i].leading += " "; names.append("space")
            case 3:
                stream.tokens[i].leading += ["/*c*/", " /* c */ ", "/*\n*/"].random(using: &rng); names.append("block-comment")
            case 4:
                stream.tokens[i].leading = " // c\n" + stream.tokens[i].leading; names.append("line-comment")
            case 5 where stream.tokens.count > 1:
                let leading = stream.tokens[i].leading
                stream.tokens.remove(at: i)
                if i < stream.tokens.count, stream.tokens[i].leading.isEmpty { stream.tokens[i].leading = leading }
                names.append("delete")
            case 6:
                stream.tokens.insert(stream.tokens[i], at: i); names.append("duplicate")
            case 7 where i + 1 < stream.tokens.count:
                stream.tokens.swapAt(i, i + 1)
                let leading = stream.tokens[i].leading
                stream.tokens[i].leading = stream.tokens[i + 1].leading
                stream.tokens[i + 1].leading = leading
                names.append("swap")
            case 8, 9:
                if stream.tokens[i].kind == .word {
                    stream.tokens[i].text = fuzzKeywords.random(using: &rng); names.append("keyword")
                } else {
                    stream.tokens[i].leading = "\n"; names.append("newline")
                }
            default:
                if let candidates = pool[stream.tokens[i].kind], !candidates.isEmpty {
                    stream.tokens[i].text = candidates.random(using: &rng); names.append("splice")
                } else {
                    stream.tokens[i].leading += " "; names.append("space")
                }
            }
            if stream.tokens.isEmpty { break }
        }
        return (stream.rendered, names.joined(separator: "+"))
    }
}

// MARK: - Contexts

/// Places a fragment where a declaration, statement or expression can appear. Fragments that do
/// not fit a context are simply rejected by both parsers (`same`).
let fuzzContexts: [(name: String, wrap: (String) -> String)] = [
    ("top", { $0 }),
    ("func-body", { "func fuzz() {\n\($0)\n}" }),
    ("struct-member", { "struct Fuzz {\n\($0)\n}" }),
    ("extension-member", { "extension Fuzz {\n\($0)\n}" }),
    ("closure", { "let fuzzClosure = {\n\($0)\n}" }),
    ("trailing-closure", { "fuzz {\n\($0)\n}" }),
    ("ifconfig", { "#if FOO\n\($0)\n#endif" }),
    ("after-statement", { "let prior = value\n\($0)" }),
    ("before-statement", { "\($0)\nlet after = value" }),
    ("interpolation", { "_ = \"a\\(\($0))b\"" }),
]

// MARK: - Reducer

/// Shrinks a failing source while a predicate on the probe result keeps holding: line chunks, then
/// token chunks (delta debugging with halving chunk sizes), then trivia simplification. Every step
/// is one probe call; `budget` caps them.
struct FailureReducer {
    let probe: (String) -> ProbeOutput?
    let budget: Int

    /// What must survive reduction: the compiler-first status, and for tree differences /
    /// ambiguities the SHAPE of the failure (divergent node pair, ambiguous nonterminal) so a
    /// reduction cannot drift onto an unrelated bug with the same status.
    static func key(_ output: ProbeOutput) -> String {
        switch output.status {
        case "tree-difference":
            let signal = dumpDifferenceSignal(reference: output.referenceDump, advent: output.adventDump)
            return "tree-difference|" + signal.split(separator: "|").dropFirst().joined(separator: "|")
        case "residual-ambiguity":
            let first = output.residualAmbiguities.first ?? ""
            return "residual-ambiguity|" + first
        default:
            return output.status
        }
    }

    static let reducibleStatuses: Set<String> = [
        "advent-underaccept", "advent-overaccept", "tree-difference", "residual-ambiguity",
        "advent-no-generated-tree",
    ]

    func reduce(_ source: String, key target: String) -> (source: String, probes: Int) {
        var calls = 0
        func holds(_ candidate: String) -> Bool {
            guard calls < budget else { return false }
            calls += 1
            guard let output = probe(candidate) else { return false }
            return FailureReducer.key(output) == target
        }

        // 1. Lines.
        var lines = source.components(separatedBy: "\n")
        var chunk = max(1, lines.count / 2)
        while chunk >= 1, calls < budget {
            var start = 0
            var removedAny = false
            while start < lines.count, calls < budget {
                var candidate = lines
                candidate.removeSubrange(start..<min(lines.count, start + chunk))
                if !candidate.isEmpty, holds(candidate.joined(separator: "\n")) {
                    lines = candidate; removedAny = true
                } else {
                    start += chunk
                }
            }
            if chunk == 1 && !removedAny { break }
            chunk = removedAny && chunk == 1 ? 1 : chunk / 2
        }

        // 2. Tokens.
        var stream = FuzzTokens(lines.joined(separator: "\n"))
        chunk = max(1, stream.tokens.count / 2)
        while chunk >= 1, calls < budget {
            var start = 0
            var removedAny = false
            while start < stream.tokens.count, calls < budget {
                var candidate = stream
                let leading = candidate.tokens[start].leading
                candidate.tokens.removeSubrange(start..<min(stream.tokens.count, start + chunk))
                if start < candidate.tokens.count, !leading.isEmpty, candidate.tokens[start].leading.isEmpty {
                    candidate.tokens[start].leading = leading
                }
                if !candidate.tokens.isEmpty, holds(candidate.rendered) {
                    stream = candidate; removedAny = true
                } else {
                    start += chunk
                }
            }
            if chunk == 1 && !removedAny { break }
            chunk = removedAny && chunk == 1 ? 1 : chunk / 2
        }

        // 3. Trivia: comments and runs of whitespace down to one space or one newline.
        for index in stream.tokens.indices where calls < budget {
            let leading = stream.tokens[index].leading
            let simpler = leading.contains("\n") ? "\n" : (leading.isEmpty ? "" : " ")
            guard simpler != leading else { continue }
            var candidate = stream
            candidate.tokens[index].leading = simpler
            if holds(candidate.rendered) { stream = candidate }
        }
        stream.trailing = ""
        return (stream.rendered, calls)
    }
}

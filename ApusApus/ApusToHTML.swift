//
//  ApusToHTML.swift
//  ApusApus
//
//  Converts an APUS grammar into a standalone HTML page styled to look like the
//  "Summary of the Grammar" pages on the TSPL website
//  (https://docs.swift.org/swift-book/documentation/the-swift-programming-language/summaryofthegrammar/).
//
//  The single public entry point is `convertApusToHTML(_:)`.
//
//  ─────────────────────────────────────────────────────────────────────────────
//  Notation mapping (APUS ──▶ TSPL-style HTML)
//  ─────────────────────────────────────────────────────────────────────────────
//  APUS construct              TSPL / chosen rendering
//  ──────────────────────      ────────────────────────────────────────────────
//  ruleName = …                <em>rule-name</em>   (camelCase ▶ kebab-case, italic)
//  productions                 one line per apus production, one aside per name
//  "keyword"  / "{"            <strong><code>keyword</code></strong>   (bold mono)
//  namedLiteral alias ref      resolved to its literal and shown bold-mono
//  identifier / number (regex) <em>identifier</em>   (a lexical category, italic — as TSPL does)
//  /regex/                     <code class="apus-regex">/regex/</code>  (mono, tinted — no fill)
//  A | B                       A <span class="apus-bar">|</span> B
//  a b c  (sequence)           a b c  (space separated)
//  ε  and  ""                  <em class="apus-eps">ε</em>
//  ( … )   grouping            ( … )  — literal brackets, delimiters styled like the | bar
//  [ … ]   option              [ … ]  — literal brackets (postfix x? still renders as x?)
//  { … }   Kleene (0+)         { … }  — literal brackets (postfix x* still renders as x*)
//  < … >   positive (1+)       < … >  — literal brackets (postfix x+ still renders as x+)
//  ---("if" "for")  exclusion  <span class="apus-annot">∖ {if, for}</span>  (suppressed here)
//  >+>( … )  pos. lookahead    <span class="apus-annot">≻ { … }</span>  (only if followed by)
//  >->( … )  neg. lookahead    <span class="apus-annot">⊁ { … }</span>  (only if NOT followed by)
//  <+<( … )  pos. lookbehind   <span class="apus-annot">≺ { … }</span>  (only if preceded by)
//  <-<( … )  neg. lookbehind   <span class="apus-annot">⊀ { … }</span>  (only if NOT preceded by)
//  ~~~       Frankenstein      <span class="apus-annot">✂</span>  (may match a prefix)
//  >>|  indent   |<<  dedent   <span class="apus-layout">▸ INDENT</span> / ◂ DEDENT
//  >s< <s> >n< <n>  boundaries ⟨joined⟩ ⟨space⟩ ⟨same-line⟩ ⟨new-line⟩  (spatial predicates)
//  'action'                    <span class="apus-action">‹ action ›</span>
//  @pragma  / @longest etc.    <span class="apus-pragma">@pragma</span>  (tag on rule/alternate)
//
//  Definition operators get distinct arrows (no separate "kind" tag):
//    =   production          →      -   token terminal     ↦
//    :   discarded terminal  ⇢
//
//  Standalone ALL-CAPS comment lines (e.g. `// TYPES`, `// EXPRESSIONS`) become
//  section headers, mirroring the TSPL chapter structure. All other comments,
//  and the `^^^` message section, are dropped.
//  ─────────────────────────────────────────────────────────────────────────────
//

import Foundation

/// Convert an APUS grammar string into a complete, self-contained HTML document
/// laid out to resemble the TSPL "Summary of the Grammar" pages.
///
/// - Parameters:
///   - apus: the full text of an `.apus` grammar (productions plus optional `^^^` messages).
///   - title: the page/document title shown in the header and `<title>`.
/// - Returns: a full HTML document (with embedded CSS) as a `String`.
func convertApusToHTML(_ apus: String, title: String = "Summary of the Grammar") -> String {
    ApusHTMLConverter(source: apus, title: title).convert()
}

// MARK: - Converter

private final class ApusHTMLConverter {

    // A lexical token of the APUS grammar language.
    private struct Tok { let kind: String; let text: String; let line: Int }

    // A single rendered definition line, tagged with the source line it starts on
    // (used to place the definition under the right section header).
    private struct GroupLine { let html: String; let startLine: Int }

    // All definitions sharing one left-hand-side name are gathered into one aside.
    private final class Group {
        var name: String
        var lines: [GroupLine] = []
        var firstLine: Int = .max        // source line of the first definition (for sectioning)
        init(name: String) { self.name = name }
    }

    private let source: String
    private let title: String

    private var toks: [Tok] = []
    private var pos = 0
    private var comments: [(line: Int, text: String)] = []
    private var literalAliases: [String: String] = [:]   // alias name ▶ raw literal token text

    private var order: [String] = []
    private var groups: [String: Group] = [:]

    // Section headers derived from standalone ALL-CAPS comments, sorted by line.
    private var sectionHeaders: [(line: Int, display: String)] = []
    // Subsection box labels derived from standalone `// Grammar of …` comments, sorted by line.
    private var boxMarkers: [(line: Int, label: String)] = []
    private var docTitle: String = ""

    init(source: String, title: String) {
        self.source = source
        self.title = title
    }

    // MARK: Entry

    func convert() -> String {
        lex()
        prescanAliases()
        computeSections()
        parse()
        return renderDocument()
    }

    // MARK: Lexer

    // Anchored patterns for the variable-length tokens. Mirror `ApusTerminals.swift`.
    private let reIdent   = /\p{XID_Start}\p{XID_Continue}*/
    private let reLiteral = /"(?:[^"\\]|\\.)+"/
    private let reRegex   = /\/(?!\*)(?:[^\/\\]|\\.)+\//
    private let reAction  = /'(?:[^'\\]|\\.)*'/
    private let rePragma  = /@\p{XID_Start}\p{XID_Continue}*/

    // Multi-character operators, longest-first so prefixes never shadow them.
    private let multiOps = [">>|", "|<<", ">+>", ">->", "<+<", "<-<",
                            ">n<", ">s<", "<n>", "<s>", "---", "~~~"]
    private let singleOps: Set<Character> = [".", ":", "=", "-", "|", "(", ")",
                                             "[", "]", "{", "}", "<", ">",
                                             "?", "*", "+", ","]

    private func lex() {
        // The grammar ends where the `^^^` message section begins; drop everything after.
        var s = source
        if let r = s.range(of: "^^^") { s = String(s[..<r.lowerBound]) }

        var idx = s.startIndex
        let end = s.endIndex
        var line = 1

        // Advance to `to`, counting newlines that are skipped over.
        func adv(to target: String.Index) {
            var j = idx
            while j < target { if s[j] == "\n" { line += 1 }; j = s.index(after: j) }
            idx = target
        }

        while idx < end {
            let c = s[idx]

            // whitespace
            if c.isWhitespace { if c == "\n" { line += 1 }; idx = s.index(after: idx); continue }

            // line comment
            if s[idx...].hasPrefix("//") {
                var j = idx
                while j < end, s[j] != "\n" { j = s.index(after: j) }
                comments.append((line, String(s[idx..<j])))
                idx = j
                continue
            }

            // block comment
            if s[idx...].hasPrefix("/*") {
                var j = s.index(idx, offsetBy: 2, limitedBy: end) ?? end
                while j < end, !s[j...].hasPrefix("*/") { j = s.index(after: j) }
                if j < end { j = s.index(j, offsetBy: 2, limitedBy: end) ?? end }
                let startLine = line
                comments.append((startLine, String(s[idx..<j])))
                adv(to: j)
                continue
            }

            let startLine = line

            switch c {
            case "/":   // regex (comments already handled above)
                if let m = s[idx...].prefixMatch(of: reRegex) {
                    toks.append(Tok(kind: "regex", text: String(m.0), line: startLine))
                    adv(to: m.range.upperBound)
                } else { idx = s.index(after: idx) }
                continue
            case "\"":
                if let m = s[idx...].prefixMatch(of: reLiteral) {
                    toks.append(Tok(kind: "literal", text: String(m.0), line: startLine))
                    adv(to: m.range.upperBound)
                } else if s[idx...].hasPrefix("\"\"") {
                    toks.append(Tok(kind: "empty", text: "\"\"", line: startLine))
                    idx = s.index(idx, offsetBy: 2)
                } else { idx = s.index(after: idx) }
                continue
            case "'":
                if let m = s[idx...].prefixMatch(of: reAction) {
                    toks.append(Tok(kind: "action", text: String(m.0), line: startLine))
                    adv(to: m.range.upperBound)
                } else { idx = s.index(after: idx) }
                continue
            case "@":
                if let m = s[idx...].prefixMatch(of: rePragma) {
                    toks.append(Tok(kind: "pragma", text: String(m.0), line: startLine))
                    adv(to: m.range.upperBound)
                } else { idx = s.index(after: idx) }
                continue
            case "ε":
                toks.append(Tok(kind: "epsilon", text: "ε", line: startLine))
                idx = s.index(after: idx)
                continue
            default:
                break
            }

            // multi-character operators
            var matchedOp = false
            for op in multiOps where s[idx...].hasPrefix(op) {
                toks.append(Tok(kind: op, text: op, line: startLine))
                idx = s.index(idx, offsetBy: op.count)
                matchedOp = true
                break
            }
            if matchedOp { continue }

            // single-character operators
            if singleOps.contains(c) {
                toks.append(Tok(kind: String(c), text: String(c), line: startLine))
                idx = s.index(after: idx)
                continue
            }

            // identifier
            if let m = s[idx...].prefixMatch(of: reIdent) {
                toks.append(Tok(kind: "identifier", text: String(m.0), line: startLine))
                adv(to: m.range.upperBound)
                continue
            }

            // unknown character — skip so the converter never hangs
            idx = s.index(after: idx)
        }
    }

    /// Find `name - "literal" .` / `name : "literal" .` aliases so references to
    /// them elsewhere can be rendered as the bold keyword rather than an italic name.
    private func prescanAliases() {
        var i = 0
        while i + 2 < toks.count {
            if toks[i].kind == "identifier",
               toks[i + 1].kind == "-" || toks[i + 1].kind == ":",
               toks[i + 2].kind == "literal" {
                literalAliases[toks[i].text] = toks[i + 2].text
            }
            i += 1
        }
    }

    /// A standalone comment line whose text is entirely upper-case letters / digits /
    /// spaces / dots (e.g. `// TYPES`, `// WHITESPACE AND COMMENT`, `// SWIFT 6.3 GRAMMAR`)
    /// is treated as a section header. The first such header becomes the document title;
    /// the rest become `<h2>` section dividers. Everything else is discarded.
    /// Standalone `// Grammar of …` comments become the label of a subsection box.
    private func computeSections() {
        let tokenLines = Set(toks.map { $0.line })
        for c in comments where !tokenLines.contains(c.line) {
            let text = c.text.drop { $0 == "/" }.trimmingCharacters(in: .whitespaces)

            // Subsection box marker: `// Grammar of a type`
            if text.hasPrefix("Grammar of ") {
                boxMarkers.append((line: c.line, label: text))
                continue
            }
            // Section header: entirely upper-case letters / digits / spaces / dots.
            guard text.count >= 3, text.count <= 40,
                  text.contains(where: { $0.isLetter }),
                  text.allSatisfy({ $0.isUppercase || $0.isNumber || $0 == " " || $0 == "." || $0 == "$" }),
                  text.split(separator: " ").count <= 5
            else { continue }
            sectionHeaders.append((line: c.line, display: titleCase(text)))
        }
        sectionHeaders.sort { $0.line < $1.line }
        boxMarkers.sort { $0.line < $1.line }
        docTitle = sectionHeaders.first?.display ?? title
    }

    /// Section index for a source line: the header with the greatest line ≤ `line`.
    /// Index 0 is the title section (rendered without an `<h2>`); ≥1 gets a divider.
    private func sectionIndex(for line: Int) -> Int {
        var idx = 0
        for (i, h) in sectionHeaders.enumerated() where h.line <= line { idx = i }
        return idx
    }

    /// Box index for a source line: the `// Grammar of …` marker with the greatest
    /// line ≤ `line`, or -1 for rules that precede the first marker (unlabeled box).
    private func boxIndex(for line: Int) -> Int {
        var idx = -1
        for (i, m) in boxMarkers.enumerated() where m.line <= line { idx = i }
        return idx
    }

    // MARK: Token cursor

    private var k: String { pos < toks.count ? toks[pos].kind : "○" }
    private var t: String { pos < toks.count ? toks[pos].text : "" }
    private var curLine: Int { pos < toks.count ? toks[pos].line : (toks.last?.line ?? 0) }

    private func expect(_ kind: String) { if k == kind { pos += 1 } }

    private func skipBalancedParens() {
        guard k == "(" else { return }
        var depth = 0
        while pos < toks.count {
            if k == "(" { depth += 1 } else if k == ")" { depth -= 1 }
            pos += 1
            if depth == 0 { break }
        }
    }

    // MARK: Parser

    private func parse() {
        while k == "identifier" || k == "pragma" {
            let before = pos
            parseProduction()
            if pos == before { pos += 1 }   // guarantee forward progress
        }
    }

    private func group(named name: String) -> Group {
        if let g = groups[name] { return g }
        let g = Group(name: name)
        groups[name] = g
        order.append(name)
        return g
    }

    private func parseProduction() {
        let startLine = curLine
        var pragmas: [String] = []

        // leading pragmas: @longest / @literalMunch / @preempt(X, N) / …
        while k == "pragma" {
            pragmas.append(t)
            pos += 1
            if k == "(" { skipBalancedParens() }
        }

        guard k == "identifier" else { return }
        let name = t
        pos += 1

        // Production-level pragmas render inline (orange), like @prefer / @avoid —
        // placed at the head of the line, where they appear in the apus source.
        let pragmaPrefix = pragmas.isEmpty ? "" : pragmas.map { pragmaTag($0) }.joined(separator: " ") + " "

        var lineHTML: String

        if k == "-" || (k == ":" && productionStartsWithDirectTerminalBody(at: pos)) {
            // terminal definition — the operator picks the arrow, so no "kind" tag
            let op = k
            pos += 1
            let body = parseTerminalRHS()
            expect(".")
            lineHTML = pragmaPrefix + nt(name) + arrow(for: op) + body
        } else if k == "=" || k == ":" || k == "-" {
            // production rule
            let op = k
            pos += 1
            let (body, _) = parseSelection()
            expect(".")
            lineHTML = pragmaPrefix + nt(name) + arrow(for: op) + body
        } else {
            // unrecognised — skip to the next full stop to stay in sync
            while pos < toks.count, k != "." { pos += 1 }
            expect(".")
            return
        }

        let g = group(named: name)
        g.lines.append(GroupLine(html: lineHTML, startLine: startLine))
        g.firstLine = min(g.firstLine, startLine)
    }

    private func productionStartsWithDirectTerminalBody(at operatorIndex: Int) -> Bool {
        var i = operatorIndex + 1
        guard i < toks.count else { return false }
        switch toks[i].kind {
        case "regex", "literal":
            i += 1
        case "pragma" where toks[i].text == "@builder":
            i += 1
            if i < toks.count, toks[i].kind == "(" {
                i += 1
                guard i < toks.count, toks[i].kind == "identifier" || toks[i].kind == "literal" else { return false }
                i += 1
                guard i < toks.count, toks[i].kind == ")" else { return false }
                i += 1
            }
        default:
            return false
        }
        return i < toks.count && toks[i].kind == "."
    }

    /// Right-hand side of a `:` / `-` terminal definition: a regex, a literal, or `@builder`.
    private func parseTerminalRHS() -> String {
        switch k {
        case "regex":
            let h = regexHTML(t); pos += 1; return h
        case "literal":
            let h = kw(literalContent(t)); pos += 1; return h
        case "pragma" where t == "@builder":
            pos += 1
            var key = ""
            if k == "(" {
                pos += 1
                if k == "literal" { key = literalContent(t) } else { key = t }
                pos += 1
                expect(")")
            }
            let label = key.isEmpty ? "@builder" : "@builder(\(key))"
            return "<code class=\"apus-regex\" title=\"regex from the RegexBuilder library\">\(esc(label))</code>"
        default:
            let h = t.isEmpty ? "?" : kw(t); pos += 1; return h
        }
    }

    /// selection = sequence { "|" sequence } .
    /// Returns the HTML and whether the whole selection is a single bare atom
    /// (one alternative, one factor) — used to decide bracket parenthesisation.
    private func parseSelection() -> (html: String, singleAtom: Bool) {
        var seqs: [(String, Int)] = [parseSequence()]
        while k == "|" {
            pos += 1
            seqs.append(parseSequence())
        }
        let html = seqs.map { $0.0 }.joined(separator: " <span class=\"apus-bar\">|</span> ")
        let single = seqs.count == 1 && seqs[0].1 == 1
        return (html, single)
    }

    private let factorStarters: Set<String> = [
        "identifier", "literal", "empty", "epsilon", "regex",
        "(", "[", "{", "<",
        ">>|", "|<<", "<n>", "<s>", ">n<", ">s<",
        "action", "pragma",
    ]

    /// sequence = < layout | factor [ "?" | "*" | "+" ] > .
    /// Returns the HTML and a count of factor-like parts (for single-atom detection).
    private func parseSequence() -> (String, Int) {
        var parts: [String] = []
        var factorCount = 0

        if k == "pragma", t == "@prefer" {
            parts.append(pragmaTag("@prefer"))
            pos += 1
        }

        while factorStarters.contains(k) {
            switch k {
            case ">>|", "|<<", "<n>", "<s>", ">n<", ">s<":
                parts.append(layoutHTML(k)); pos += 1
            case "action":
                parts.append(actionHTML(t)); pos += 1
            case "pragma":
                parts.append(pragmaTag(t)); pos += 1
                if k == "(" { skipBalancedParens() }
            default:
                var h = parseFactor()
                switch k {
                case "?": h += optMark;  pos += 1
                case "*": h += starMark; pos += 1
                case "+": h += plusMark; pos += 1
                default: break
                }
                parts.append(h)
                factorCount += 1
            }
        }
        return (parts.joined(separator: " "), factorCount)
    }

    private func parseFactor() -> String {
        var core: String

        switch k {
        case "identifier":
            let name = t; pos += 1
            core = identHTML(name)
        case "literal":
            core = kw(literalContent(t)); pos += 1
            if k == "~~~" { core += frankMark; pos += 1 }
        case "empty", "epsilon":
            core = epsHTML; pos += 1
        case "regex":
            core = regexHTML(t); pos += 1
        case "(":
            pos += 1
            let (inner, _) = parseSelection()
            expect(")")
            core = ebnfBracket("(", inner, ")", avoid: false)
        case "[":
            pos += 1
            let avoid = consumeAvoid()
            let (inner, _) = parseSelection()
            expect("]")
            core = ebnfBracket("[", inner, "]", avoid: avoid)
        case "{":
            pos += 1
            let avoid = consumeAvoid()
            let (inner, _) = parseSelection()
            expect("}")
            core = ebnfBracket("{", inner, "}", avoid: avoid)
        case "<":
            pos += 1
            let avoid = consumeAvoid()
            let (inner, _) = parseSelection()
            expect(">")
            core = ebnfBracket("<", inner, ">", avoid: avoid)
        default:
            core = "?"; pos += 1
        }

        // Schrödinger exclusion: ---("if" "for" …)
        if k == "---" {
            pos += 1
            expect("(")
            var items: [String] = []
            while k == "literal" { items.append(literalContent(t)); pos += 1 }
            expect(")")
            core += " <span class=\"apus-annot\" title=\"these keywords are suppressed here\">---(\(esc(items.joined(separator: " "))))</span>"
        }

        // Forward lookahead: >+>( … ) positive / >->( … ) negative
        if k == ">+>" || k == ">->" {
            let positive = (k == ">+>")
            pos += 1
            expect("(")
            var items: [String] = []
            while k == "literal" || k == "identifier" {
                items.append(k == "literal" ? literalContent(t) : t)
                pos += 1
            }
            expect(")")
            core += positive
                ? annot(followGlyph, items, "only when followed by")
                : annot(notFollowGlyph, items, "only when NOT followed by")
        }

        return core
    }

    private func consumeAvoid() -> Bool {
        if k == "pragma", t == "@avoid" { pos += 1; return true }
        return false
    }

    // MARK: Rendering primitives

    /// Distinct arrow glyph per definition operator (the operator's meaning, so no
    /// separate "kind" tag on the label):
    ///   =  → (production)   -  ↦ (token terminal)   :  ⇢ (discarded terminal)
    private func arrow(for op: String) -> String {
        let g: String
        switch op {
        case "-":  g = "↦"
        case ":":  g = "⇢"
        default:   g = "→"
        }
        return " <span class=\"apus-arrow\">\(g)</span> "
    }

    private let optMark  = "<span class=\"apus-rep\">?</span>"
    private let starMark = "<sup class=\"apus-rep\">*</sup>"
    private let plusMark = "<sup class=\"apus-rep\">+</sup>"

    /// Lookahead / lookbehind glyphs. The triangle points at the neighbouring token
    /// (▷ next / ◁ previous); a struck triangle negates it.
    ///   >+>  ⊳ next must be in set      >->  ⋫ next must NOT be in set
    ///   <+<  ⊲ previous must be in set  <-<  ⋪ previous must NOT be in set
//    private let followGlyph     = "⊳"
//    private let notFollowGlyph  = "⋫"
//    private let precedeGlyph    = "⊲"
//    private let notPrecedeGlyph = "⋪"
    private let followGlyph     = ">+>"
    private let notFollowGlyph  = ">->"
    private let precedeGlyph    = "<+<"
    private let notPrecedeGlyph = "<-<"

    /// One annotation chip: a glyph followed by a space-separated `(…)` operand list,
    /// all in the pragma colour (`.apus-annot`).
    private func annot(_ glyph: String, _ items: [String], _ tip: String) -> String {
        " <span class=\"apus-annot\" title=\"\(tip)\"><span class=\"apus-tri\">\(glyph)</span> (\(esc(items.joined(separator: " "))))</span>"
    }
//    private let frankMark = " <span class=\"apus-annot\" title=\"may match a prefix of a longer token\">✂</span>"
    private let frankMark = " <span class=\"apus-annot\" title=\"may match a prefix of a longer token\">~~~</span>"
    private let epsHTML  = "<em class=\"apus-eps\">ε</em>"

    private func nt(_ name: String) -> String { "<em>\(esc(kebab(name)))</em>" }
    private func kw(_ text: String) -> String { "<strong><code>\(esc(text))</code></strong>" }
    private func regexHTML(_ text: String) -> String { "<code class=\"apus-regex\">\(esc(text))</code>" }
    private func pragmaTag(_ text: String) -> String { "<span class=\"apus-pragma\">\(esc(text))</span>" }

    /// An EBNF bracket construct rendered with its literal delimiters — grouping `( )`,
    /// option `[ ]`, Kleene `{ }`, positive `< >` — the brackets styled like the `|` bar.
    private func ebnfBracket(_ open: String, _ inner: String, _ close: String, avoid: Bool) -> String {
        let lead = avoid ? pragmaTag("@avoid") + " " : ""
        return "<span class=\"apus-bracket\">\(open)</span> \(lead)\(inner) <span class=\"apus-bracket\">\(close)</span>"
    }

    private func actionHTML(_ text: String) -> String {
        var body = text
        if body.hasPrefix("'") && body.hasSuffix("'") && body.count >= 2 {
            body = String(body.dropFirst().dropLast())
        }
        return "<span class=\"apus-action\" title=\"semantic action\">‹ \(esc(body)) ›</span>"
    }

    private func layoutHTML(_ kind: String) -> String {
        switch kind {
//        case ">>|": return "<span class=\"apus-layout\" title=\"indent (column increased)\">▸ INDENT</span>"
//        case "|<<": return "<span class=\"apus-layout\" title=\"dedent (column decreased)\">◂ DEDENT</span>"
//        case ">s<": return "<span class=\"apus-constraint\" title=\"tokens must be adjacent — no space\">⟨joined⟩</span>"
//        case "<s>": return "<span class=\"apus-constraint\" title=\"tokens must not be adjacent — space required\">⟨space⟩</span>"
//        case ">n<": return "<span class=\"apus-constraint\" title=\"tokens must be on the same line\">⟨same-line⟩</span>"
//        case "<n>": return "<span class=\"apus-constraint\" title=\"tokens must be on different lines\">⟨new-line⟩</span>"
        case ">>|": return "<span class=\"apus-layout\" title=\"indent (column increased)\">indent</span>"
        case "|<<": return "<span class=\"apus-layout\" title=\"dedent (column decreased)\">dedent</span>"
        case ">s<": return "<span class=\"apus-constraint\" title=\"tokens must be adjacent — no space\">joined</span>"
        case "<s>": return "<span class=\"apus-constraint\" title=\"tokens must not be adjacent — space required\">space</span>"
        case ">n<": return "<span class=\"apus-constraint\" title=\"tokens must be on the same line\">same-line</span>"
        case "<n>": return "<span class=\"apus-constraint\" title=\"tokens must be on different lines\">new-line</span>"
        default:    return esc(kind)
        }
    }

    private func identHTML(_ name: String) -> String {
        if let raw = literalAliases[name] { return kw(literalContent(raw)) }
        return nt(name)
    }

    // MARK: Text helpers

    /// camelCase / snake_case ▶ kebab-case (as used by the TSPL grammar rule names).
    private func kebab(_ s: String) -> String {
        let chars = Array(s)
        var out = ""
        for (i, ch) in chars.enumerated() {
            if ch == "_" || ch == " " { out.append("-"); continue }
            if ch.isUppercase {
                if i > 0 {
                    let prev = chars[i - 1]
                    let nextLower = i + 1 < chars.count && chars[i + 1].isLowercase
                    if prev.isLowercase || prev.isNumber || (prev.isUppercase && nextLower) {
                        out.append("-")
                    }
                }
                out.append(contentsOf: ch.lowercased())
            } else {
                out.append(ch)
            }
        }
        return out
    }

    /// Strip the surrounding quotes and resolve the common backslash escapes of a literal token.
    private func literalContent(_ token: String) -> String {
        var s = token
        if s.hasPrefix("\"") && s.hasSuffix("\"") && s.count >= 2 {
            s = String(s.dropFirst().dropLast())
        }
        var out = ""
        let chars = Array(s)
        var i = 0
        while i < chars.count {
            let c = chars[i]
            if c == "\\", i + 1 < chars.count {
                let n = chars[i + 1]
                switch n {
                case "n": out.append("\n")
                case "t": out.append("\t")
                case "r": out.append("\r")
                case "\\": out.append("\\")
                case "\"": out.append("\"")
                case "/": out.append("/")
                default: out.append(n)
                }
                i += 2
            } else {
                out.append(c)
                i += 1
            }
        }
        return out
    }

    private func esc(_ s: String) -> String {
        s.replacingOccurrences(of: "&", with: "&amp;")
         .replacingOccurrences(of: "<", with: "&lt;")
         .replacingOccurrences(of: ">", with: "&gt;")
    }

    private static let smallWords: Set<String> = ["and", "or", "of", "the", "a", "an", "to", "in", "for", "with", "on"]

    /// ALL-CAPS section text ▶ Title Case ("WHITESPACE AND COMMENT" ▶ "Whitespace and Comment").
    private func titleCase(_ s: String) -> String {
        let words = s.lowercased().split(separator: " ").map(String.init)
        return words.enumerated().map { i, w in
            if i != 0, ApusHTMLConverter.smallWords.contains(w) { return w }
            return w.prefix(1).uppercased() + w.dropFirst()
        }.joined(separator: " ")
    }

    // MARK: Document assembly

    private func renderDocument() -> String {
        var body = ""
        body += "<h1 class=\"apus-title\">\(esc(docTitle))</h1>\n"
        body += """
        <p class="apus-legend">\
        <b>→</b> production &nbsp;·&nbsp; <b>↦</b> token terminal &nbsp;·&nbsp; \
        <b>⇢</b> discarded terminal &nbsp;·&nbsp; <b>↝</b> trivia &nbsp;·&nbsp; \
        <b>↠</b> lexical token</p>

        """

        // One labelled box per `// Grammar of …` subsection (TSPL-style), grouped under
        // the section's <h2>. Rules stay in source order; a nonterminal's definitions
        // stay adjacent. Rules before the first marker form an unlabelled box.
        var currentSection = -2
        var currentBox = Int.min
        var currentLabel: String? = nil
        var ruleLines: [String] = []

        func flushBox() {
            guard !ruleLines.isEmpty else { return }
            body += "<aside class=\"note\">\n"
            if let l = currentLabel { body += "  <p class=\"label\">\(esc(l))</p>\n" }
            body += "  <p class=\"rule\">" + ruleLines.joined(separator: "<br>\n") + "</p>\n</aside>\n"
            ruleLines = []
        }

        for name in order {
            guard let g = groups[name] else { continue }
            let sIdx = sectionIndex(for: g.firstLine)
            let bIdx = boxIndex(for: g.firstLine)
            if sIdx != currentSection {
                flushBox()
                currentSection = sIdx
                if sIdx >= 1 {
                    body += "<h2 class=\"apus-section\">\(esc(sectionHeaders[sIdx].display))</h2>\n"
                }
                currentBox = Int.min   // force a fresh box after the divider
            }
            if bIdx != currentBox {
                flushBox()
                currentBox = bIdx
                // Only label the box when its marker lives in the current section; a
                // marker whose rules spill past a section header continues unlabelled.
                if bIdx >= 0, sectionIndex(for: boxMarkers[bIdx].line) == currentSection {
                    currentLabel = boxMarkers[bIdx].label
                } else {
                    currentLabel = nil
                }
            }
            ruleLines.append(contentsOf: g.lines.map { $0.html })
        }
        flushBox()

        return htmlShell(body: body)
    }

    private func htmlShell(body: String) -> String {
        """
        <!DOCTYPE html>
        <html lang="en-US">
        <head>
        <meta charset="utf-8">
        <meta name="viewport" content="width=device-width, initial-scale=1">
        <title>\(esc(title))</title>
        <style>
        :root {
          --text: #1d1d1f;
          --muted: #6e6e73;
          --keyword: #ad3da4;
          --regex: #0f68a0;
          --rule: #333336;
          --note-bg: #f5f5f7;
          --note-border: #d2d2d7;
          --annot: #b25e00;   /* shared by @pragmas and ---/lookaround annotations */
        }
        * { box-sizing: border-box; }
        body {
          font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, Helvetica, Arial, sans-serif;
          color: var(--text);
          line-height: 1.5;
          margin: 0;
          padding: 2.5rem 1.5rem 6rem;
          background: #ffffff;
          -webkit-font-smoothing: antialiased;
        }
        .apus-title {
          max-width: 820px;
          margin: 0 auto 0.5rem;
          font-size: 2.4rem;
          font-weight: 600;
          letter-spacing: -0.01em;
        }
        .apus-legend {
          max-width: 820px;
          margin: 0 auto 2rem;
          color: var(--muted);
          font-size: 0.85rem;
        }
        .apus-legend b { color: var(--rule); font-weight: 600; }
        h2.apus-section {
          max-width: 820px;
          margin: 2.6rem auto 1rem;
          font-size: 1.8rem;
          font-weight: 600;
          letter-spacing: -0.01em;
          color: var(--text);
        }
        aside.note {
          max-width: 820px;
          margin: 0 auto 0.5rem;
          background: var(--note-bg);
          border: 1px solid var(--note-border);
          border-left: 3px solid #b0b0b8;
          border-radius: 6px;
          padding: 0.6rem 1rem 0.7rem;
        }
        aside.note .label {
          margin: 0 0 0.35rem;
          font-size: 0.8rem;
          font-weight: 600;
          color: var(--muted);
        }
        aside.note .rule {
          margin: 0;
          color: var(--rule);
          line-height: 1.65;
          font-size: 1.02rem;
        }
        /* nonterminals & lexical categories */
        .rule em {
          font-style: italic;
          color: var(--rule);
        }
        .rule em.apus-eps { color: var(--muted); font-weight: 600; }
        /* keywords / literal terminals */
        .rule strong code,
        code {
          font-family: "SF Mono", ui-monospace, Menlo, Consolas, "Liberation Mono", monospace;
          font-size: 0.92em;
        }
        .rule strong code {
          font-weight: 600;
          color: var(--keyword);
        }
        /* monospace reads larger than the proportional body text at the same em,
           so nudge the regex down to match the surrounding production visually */
        code.apus-regex { color: var(--regex); font-size: 0.82em; }
        .apus-arrow { color: var(--muted); }
        .apus-bar { color: var(--muted); font-weight: 600; padding: 0 0.15em; }
        /* EBNF delimiters ( ) [ ] { } < > — same treatment as the | bar */
        .apus-bracket { color: var(--muted); font-weight: 600; }
        .apus-rep { color: var(--muted); font-style: normal; }
        sup.apus-rep { font-size: 0.75em; }
        /* invented-notation annotations — coloured text only, no fill */
        /* monospace, same size and colour as an @pragma */
        .apus-annot {
          color: var(--annot);
          font-size: 0.78em;
          font-family: "SF Mono", ui-monospace, Menlo, monospace;
        }
        /* the lookaround triangle is a thin math glyph — enlarge & embolden it so it
           reads as the focal point of the annotation (operand list stays small) */
        .apus-tri {
          font-size: 1.45em;
          font-weight: 700;
          line-height: 0;
          vertical-align: -0.12em;
        }
        .apus-layout {
          font-size: 0.74em;
          font-weight: 700;
          letter-spacing: 0.04em;
          color: #2f7d32;
        }
        .apus-constraint {
          font-size: 0.78em;
          color: #5a4b8a;
        /*          color: #5a4b8a; */
        color: #6a5b9a;
        }
        .apus-action {
          font-size: 0.82em;
          color: var(--muted);
          font-style: italic;
        }
        .apus-pragma {
          font-size: 0.78em;
          color: var(--annot);
          font-family: "SF Mono", ui-monospace, Menlo, monospace;
        }
        @media (prefers-color-scheme: dark) {
          :root {
            --text: #f5f5f7; --muted: #a1a1a6; --rule: #e3e3e6;
            --note-bg: #1c1c1e; --note-border: #3a3a3c;
            --keyword: #ff7ab2; --regex: #6bb8e6; --annot: #e0955a;
          }
          body { background: #000000; }
          aside.note { border-left-color: #5a5a60; }
        }
        </style>
        </head>
        <body>
        \(body)</body>
        </html>
        """
    }
}

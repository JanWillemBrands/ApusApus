import Foundation
import Testing

/// Writes small grammars, inputs and the BSR yields Swift Apus computes for them as Bend files, so
/// `Bend/COMPARE.bend` can set them next to the proven exact BSR set (see `Bend/README.md`).
/// Two opt-in suites use it:
/// - "Bend export" (`APUS_EXPORT_BEND=<directory>`, point it at `Bend/swift`) writes the cases below
///   as files; then `bend swift/<case>.bend` prints the report for one case.
/// - "Bend check" (`APUS_BEND=<path to bend>`, or `APUS_BEND=1` for `~/.bend/bin/bend`) runs Bend on
///   every accepted message of the `TestCase` tables, and fails a case when Swift misses a step of a
///   parse tree. Dead wood and grammars the export refuses are reported, not failed; after the
///   Oracle, dead wood fails too. A case Bend gives no answer for (fuel shortage, a failed check,
///   a refusal, the time limit) fails: it was not compared. A third test runs grammars with `@prefer`/`@avoid`
///   through the Oracle and compares them with `Bend/PREFER.bend`, the proven twin of those rules;
///   a fourth does the same for `>?>`/`>!>`/`@left`/`@right` and `Bend/GUARD.bend`,
///   and a fifth for `@longest`/`@shortest` and `Bend/EXTENT.bend`.
/// Set the variable in the test plan, or as `TEST_RUNNER_<name>` via xcodebuild.
///
/// The export translates, and refuses rather than guesses:
/// - the grammar's GrammarNode graph to `Spec.Production`s: one per (nonterminal, alternate), with
///   brackets as `Spec.Brack` and an EPS node ("" or ε) as `Spec.Eps`; an alternate's `@prefer` or
///   `@avoid` to a `Spec.Mark`; its `>?>`/`>!>`/`@left`/`@right` to `Spec.GuardMark`s;
///   `@longest`/`@shortest` on a left-hand nonterminal or a bracket to a `Spec.ExtentMark`;
/// - each node's yields to `Spec.Bsr` elements: a node's yields are those of the slot after it; a
///   left-hand nonterminal's yields (the extra completion elements) are left out;
/// - character positions to token indices, along the single chain of terminal commits from the
///   start of the input to its end.
/// Boundaries, lookaround, an alternate with no item at all, and more than one token at a position
/// are outside the Bend specification, and stop the export of that case. So do rejected inputs: Swift
/// lexes on demand, so past the error there is no token chain (and no parse tree to compare with).
@Suite("Bend export", .enabled(if: ProcessInfo.processInfo.environment["APUS_EXPORT_BEND"] != nil,
                               "opt-in: set APUS_EXPORT_BEND=<output directory>"))
struct BendExport {

    struct Case {
        let name: String
        let grammar: String
        let input: String
    }

    /// The examples of `Bend/EXAMPLES.bend`, plus a few from `CoreGrammarTests`.
    static let cases: [Case] = [
        Case(name: "loop", grammar: #"X = "a" { "b" } "c"."#, input: "abbbc"),
        Case(name: "loop_empty", grammar: #"X = "a" { "b" } "c"."#, input: "ac"),
        Case(name: "choice", grammar: #"X = "a" ( "a" "b" | "a" ) ( "b" "c" | "c" )."#, input: "aabc"),
        Case(name: "nullable_loop", grammar: #"S = { A } "a". A = "b" "b" | ε."#, input: "bba"),
        Case(name: "optional", grammar: #"S = [ A ] "b". A = "a" | ε."#, input: "b"),
        Case(name: "split", grammar: #"X = { "a" | "a" "a" }."#, input: "aaa"),
        Case(name: "left", grammar: #"E = E "+" "a" | "a"."#, input: "a+a+a"),
        Case(name: "positive", grammar: #"S = < "a" | "b" > "c"."#, input: "abac"),
        Case(name: "brackets", grammar: #"S = "(" S ")" S | ε."#, input: "(()())"),
    ]

    enum ExportError: Error, CustomStringConvertible {
        case unsupported(String)
        var description: String {
            switch self { case .unsupported(let what): return "not exported to Bend: \(what)" }
        }
    }

    @Test func exportCases() throws {
        let directory = try #require(ProcessInfo.processInfo.environment["APUS_EXPORT_BEND"])
        try FileManager.default.createDirectory(atPath: directory, withIntermediateDirectories: true)
        for c in Self.cases {
            do {
                let text = try withParserIsolation { try Self.export(grammar: c.grammar, input: c.input, imports: "../").text }
                let url = URL(fileURLWithPath: directory).appendingPathComponent("\(c.name).bend")
                try text.write(to: url, atomically: true, encoding: .utf8)
            } catch {
                Issue.record("\(c.name): \(error)")
            }
        }
    }

    // MARK: - One case

    /// The Bend file of one grammar and input; `imports` is the directory of `SPEC.bend` and
    /// `COMPARE.bend`, relative to the file or absolute, ending in "/".
    /// With `oracle`, the yields are
    /// taken after `Oracle.disambiguate()` instead of straight from the parser. With `prefer`, they
    /// are too, and the file compares them with the steps of the unbeaten trees (`preferReport`);
    /// with `guards`, with the steps of the admissible trees (`guardReport`); with `extents`, with
    /// the steps of the best-extent trees (`extentReport`).
    /// `rootKept` says whether the root still spans the input (after the Oracle, if it ran).
    static func export(grammar text: String, input: String, imports: String, oracle: Bool = false, prefer: Bool = false, guards: Bool = false, extents: Bool = false) throws -> (text: String, rootKept: Bool) {
        let oracle = oracle || prefer || guards || extents
        let parser = try ApusParser(fromString: "whitespace : /\\s+/.\n" + text)
        let grammar = try parser.parse(explicitStartSymbol: "")
        let messageParser = MessageParser(grammar: grammar)
        messageParser.parse(input: input)
        if oracle { Oracle(parser: messageParser, input: input).disambiguate() }
        let rootKept = messageParser.yield(of: messageParser.currentParseRoot).contains {
            $0.i == input.startIndex && $0.j == input.endIndex
        }

        var translation = Translation(grammar: grammar)
        translation.comparesExtents = extents
        try translation.run()
        let tokens = try tokenChain(messageParser, input: input)
        let steps = try translation.steps(messageParser.yields, positions: tokens.positions)
        guard let startID = translation.nonterminalID[grammar.root.name] else {
            throw ExportError.unsupported("start symbol \(grammar.root.name)")
        }

        var out = "# Generated by ApusApusTests/BendExport.swift — do not edit; re-export instead.\n"
        out += "# Grammar: \(text)\n# Input:   \(input)\n"
        out += oracle ? "# Yields after Oracle.disambiguate()\n" : ""
        out += "# Nonterminals: " + translation.nonterminalNames.enumerated().map { "\($0.offset) = \($0.element)" }.joined(separator: ", ") + "\n"
        out += "# Swift yields kept: \(steps.count); completion yields left out: \(translation.droppedCompletionYields)\n\n"
        out += "import Base\nimport \(imports)SPEC.bend as Spec\nimport \(imports)COMPARE.bend as Compare\n\n"
        out += "def grammar() -> +List<Spec.Production>:\n  [" + translation.productions.joined(separator: ",\n   ") + "]\n\n"
        out += "def start() -> Nat:\n  \(startID)n\n\n"
        out += "def input() -> +List<Nat>:\n  [" + tokens.kinds.map { "\($0)n" }.joined(separator: ", ") + "]\n\n"
        out += "def marks() -> +List<Spec.Mark>:\n  [" + translation.marks.joined(separator: ",\n   ") + "]\n\n"
        out += "def guards() -> +List<Spec.GuardMark>:\n  [" + translation.guards.joined(separator: ",\n   ") + "]\n\n"
        out += "def extents() -> +List<Spec.ExtentMark>:\n  [" + translation.extents.joined(separator: ",\n   ") + "]\n\n"
        out += "def swiftSteps() -> +List<Spec.Bsr>:\n  [" + steps.joined(separator: ",\n   ") + "]\n\n"
        out += extents
            ? "def main() -> Compare.Report:\n  Compare.extentReport(grammar(), guards(), marks(), extents(), start(), input(), swiftSteps())\n"
            : guards
            ? "def main() -> Compare.Report:\n  Compare.guardReport(grammar(), guards(), start(), input(), swiftSteps())\n"
            : prefer
            ? "def main() -> Compare.Report:\n  Compare.preferReport(grammar(), guards(), marks(), start(), input(), swiftSteps())\n"
            : "def main() -> Compare.Report:\n  Compare.report(grammar(), start(), input(), swiftSteps())\n"
        return (out, rootKept)
    }

    // MARK: - Tokens

    /// The single chain of terminal commits from the start of the input to its end, as token kinds,
    /// and the token index of each position on it.
    static func tokenChain(_ parser: MessageParser, input: String) throws -> (kinds: [Int], positions: [CharPosition: Int]) {
        var kinds: [Int] = []
        var positions: [CharPosition: Int] = [input.startIndex: 0]
        var pos = input.startIndex
        while pos < input.endIndex {
            let here = (parser.commitsByStart[pos] ?? []).map { parser.commits[$0] }.filter { $0.triviaEnd > pos }
            let distinct = Set(here.map { "\($0.terminalID)@\(input.distance(from: input.startIndex, to: $0.triviaEnd))" })
            guard distinct.count == 1, let commit = here.first else {
                throw ExportError.unsupported("\(distinct.count) tokens at character \(input.distance(from: input.startIndex, to: pos))")
            }
            kinds.append(commit.terminalID)
            pos = commit.triviaEnd
            positions[pos] = kinds.count
        }
        return (kinds, positions)
    }

    // MARK: - Grammar

    struct Slot {
        let index: Int
        let path: [Int]
        /// As the Bend check prints it: `Slot{index, [path]}`.
        var text: String { "Slot{\(index), [\(path.map(String.init).joined(separator: ", "))]}" }
    }

    struct Translation {
        let grammar: Grammar
        var nonterminalNames: [String] = []
        var nonterminalID: [String: Int] = [:]
        var productions: [String] = []
        /// The slot of every node whose yields are exported, by node number.
        var slots: [Int: Slot] = [:]
        var droppedCompletionYields = 0
        /// The `@prefer` and `@avoid` marks, as `Spec.Mark`s.
        var marks: [String] = []
        /// The `>?>`/`>!>`/`@left`/`@right` rules, as `Spec.GuardMark`s.
        var guards: [String] = []
        /// The `@longest`/`@shortest` marks, as `Spec.ExtentMark`s.
        var extents: [String] = []

        /// Whether the export is compared with `EXTENT.bend`, which handles one mark per sequence.
        var comparesExtents = false
        init(grammar: Grammar) { self.grammar = grammar }

        mutating func run() throws {
            nonterminalNames = grammar.nonTerminals.filter { !$0.value.isTrivia }.keys.sorted()
            for (id, name) in nonterminalNames.enumerated() { nonterminalID[name] = id }
            for (id, name) in nonterminalNames.enumerated() {
                let lhs = grammar.nonTerminals[name]!
                if let ext = try Self.extent(lhs) { extents.append("Spec.NtExtent{\(id)n, \(ext)}") }
                var alternate = lhs.alt
                while let alt = alternate {
                    let index = productions.count
                    if let rank = Self.rank(alt) { marks.append("Spec.ProdMark{\(index)n, \(rank)}") }
                    for g in try guardsOf(alt) { guards.append("Spec.ProdGuard{\(index)n, \(g)}") }
                    productions.append("Spec.Production{\(id)n, \(try sequence(alt, index: index, prefix: []))}")
                    alternate = alt.alt
                }
            }
        }

        /// The rank an alternate's mark gives it, as a `Spec.Rank`; nil without a mark.
        static func rank(_ alt: GrammarNode) -> String? {
            alt.isPreferred ? "Spec.Preferred{}" : alt.isAvoided ? "Spec.Avoided{}" : nil
        }

        /// A node's `@longest`/`@shortest`, as a `Spec.Extent`; nil without one.
        static func extent(_ node: GrammarNode) throws -> String? {
            switch node.disambiguation {
            case .longest: return "Spec.Longest{}"
            case .shortest: return "Spec.Shortest{}"
            case nil: return nil
            case .some(let d): throw ExportError.unsupported("@\(d.rawValue) on node \(node.name)")
            }
        }

        /// An alternate's rules, as `Spec.Guard`s: each `>?>(N)`/`>!>(N)` operand is
        /// its own `Spec.Ahead`/`Spec.NotAhead`; `@left`/`@right` keep their operand list.
        func guardsOf(_ alt: GrammarNode) throws -> [String] {
            func ids(_ names: [String]) throws -> String {
                try "[" + names.map { name -> String in
                    guard let id = nonterminalID[name] else { throw ExportError.unsupported("rule operand \(name)") }
                    return "\(id)n"
                }.joined(separator: ", ") + "]"
            }
            let ahead = try alt.forwardPredicates.map { p in
                "Spec.\(p.negated ? "NotAhead" : "Ahead"){\(try ids([p.targetName]))}"
            }
            let edges = try alt.associativityFilters.map { f in
                "Spec.\(f.direction == .left ? "LeftAssoc" : "RightAssoc"){\(try ids(f.targets))}"
            }
            return ahead + edges
        }

        /// The items after an ALT node, up to its END node.
        func items(_ alt: GrammarNode) -> [GrammarNode] {
            var out: [GrammarNode] = []
            var node = alt.seq
            while let n = node, n.kind != .END { out.append(n); node = n.seq }
            return out
        }

        /// The alternates of a bracket or left-hand nonterminal.
        func alternates(_ node: GrammarNode) -> [GrammarNode] {
            var out: [GrammarNode] = []
            var alt = node.alt
            while let a = alt { out.append(a); alt = a.alt }
            return out
        }

        /// The Bend list of items of the sequence after `alt`; records the slot of each item.
        mutating func sequence(_ alt: GrammarNode, index: Int, prefix: [Int]) throws -> String {
            let nodes = items(alt)
            if nodes.isEmpty { throw ExportError.unsupported("an alternate with no item") }
            // The spec serves several marks in one sequence left to right, and Swift Apus does too;
            // Bend's extent oracle only handles one, and would answer nothing.
            let marked = nodes.filter { node in
                let mark = node.kind == .N ? node.alt?.disambiguation : (node.kind.isBracket ? node.disambiguation : nil)
                return mark == .longest || mark == .shortest
            }
            if comparesExtents, marked.count > 1 { throw ExportError.unsupported("several @longest/@shortest items in one sequence (EXTENT.bend handles one)") }
            var parts: [String] = []
            for (m, node) in nodes.enumerated() {
                let slot = Slot(index: index, path: prefix + [m + 1])
                slots[node.number] = slot
                parts.append(try item(node, index: index, prefix: prefix, position: m))
            }
            return "[" + parts.joined(separator: ", ") + "]"
        }

        mutating func item(_ node: GrammarNode, index: Int, prefix: [Int], position m: Int) throws -> String {
            switch node.kind {
            case .T, .TI, .C:
                if node.disambiguation != nil { throw ExportError.unsupported("an extent on terminal \(node.name)") }
                return "Spec.Sym{Spec.Terminal{\(node.nameID!)n}}"
            case .N:
                guard let id = nonterminalID[node.name] else { throw ExportError.unsupported("nonterminal \(node.name)") }
                // The spec marks a nonterminal everywhere (on its left-hand side), not one occurrence.
                if node.disambiguation != nil { throw ExportError.unsupported("an extent on one occurrence of \(node.name)") }
                return "Spec.Sym{Spec.Nonterminal{\(id)n}}"
            case .DO, .OPT, .KLN, .POS:
                let kind = [GrammarNodeKind.DO: "Group", .OPT: "Optional", .KLN: "Closure", .POS: "Positive"][node.kind]!
                var alts: [String] = []
                if let ext = try Self.extent(node) {
                    let path = (prefix + [m]).map { "\($0)n" }.joined(separator: ", ")
                    extents.append("Spec.BrackExtent{\(index)n, [\(path)], \(ext)}")
                }
                for (a, alt) in alternates(node).enumerated() {
                    let path = (prefix + [m]).map { "\($0)n" }.joined(separator: ", ")
                    if let rank = Self.rank(alt) {
                        marks.append("Spec.AltMark{\(index)n, [\(path)], \(a)n, \(rank)}")
                    }
                    for g in try guardsOf(alt) { guards.append("Spec.AltGuard{\(index)n, [\(path)], \(a)n, \(g)}") }
                    alts.append(try sequence(alt, index: index, prefix: prefix + [m, a]))
                }
                return "Spec.Brack{Spec.\(kind){}, [" + alts.joined(separator: ", ") + "]}"
            case .EPS:
                return "Spec.Eps{}"
            default:
                throw ExportError.unsupported("\(node.kind) node \(node.name)")
            }
        }

        /// Every exported yield as a Bend element.
        mutating func steps(_ yields: [Set<BinarySpan>], positions: [CharPosition: Int]) throws -> [String] {
            let lhsNumbers = Set(nonterminalNames.compactMap { grammar.nonTerminals[$0]?.number })
            var out: [String] = []
            for (number, spans) in yields.enumerated() where !spans.isEmpty {
                guard let slot = slots[number] else {
                    if lhsNumbers.contains(number) { droppedCompletionYields += spans.count; continue }
                    throw ExportError.unsupported("yields on node \(number), which has no slot")
                }
                for span in spans.sorted() {
                    guard let i = positions[span.i], let k = positions[span.k], let j = positions[span.j] else {
                        throw ExportError.unsupported("a yield off the token boundaries")
                    }
                    let path = slot.path.map { "\($0)n" }.joined(separator: ", ")
                    out.append("Spec.Bsr{Spec.Slot{\(slot.index)n, [\(path)]}, \(i)n, \(k)n, \(j)n}")
                }
            }
            return out
        }
    }
}

// MARK: - Running Bend

/// What `Bend/COMPARE.bend` reported for one grammar and input.
enum BendReport: Equatable {
    /// Swift has exactly the `count` steps of the parse trees.
    case agree(count: Int)
    /// `missing`: parse-tree steps Swift lacks; `extra`: Swift steps in no parse tree (dead wood).
    case differ(exact: Int, swift: Int, missing: [String], extra: [String])
    /// The exact parser ran out of fuel, or one of its checks failed.
    case noAnswer
}

enum BendRunner {
    enum RunError: Error, CustomStringConvertible {
        case failed(status: Int32, output: String)
        case unreadable(String)
        var description: String {
            switch self {
            case .failed(let status, let output): return "bend exited with \(status):\n\(output)"
            case .unreadable(let output): return "unreadable bend report: \(output)"
            }
        }
    }

    /// The bend executable named by `APUS_BEND` (`1` means `~/.bend/bin/bend`), if it exists.
    static let executable: String? = {
        guard let value = ProcessInfo.processInfo.environment["APUS_BEND"], !value.isEmpty else { return nil }
        let path = value == "1"
            ? FileManager.default.homeDirectoryForCurrentUser.appendingPathComponent(".bend/bin/bend").path
            : (value as NSString).expandingTildeInPath
        return FileManager.default.isExecutableFile(atPath: path) ? path : nil
    }()

    /// How long one Bend run may take: `APUS_BEND_TIMEOUT` seconds, 300 by default.
    static let timeLimit: Double = Double(ProcessInfo.processInfo.environment["APUS_BEND_TIMEOUT"] ?? "") ?? 300

    private final class TimeoutFlag: @unchecked Sendable { var value = false }

    /// `Bend/`, with SPEC.bend and COMPARE.bend, as an import prefix.
    static let bendDirectory = testProjectDirectory().appendingPathComponent("Bend").path + "/"

    /// Exports one grammar and input, runs Bend on it, and reads the report; also returns the file.
    static func check(grammar: String, input: String, oracle: Bool = false, prefer: Bool = false, guards: Bool = false, extents: Bool = false) throws -> (report: BendReport, file: String, rootKept: Bool) {
        let executable = try #require(executable)
        let (text, rootKept) = try withParserIsolation {
            try BendExport.export(grammar: grammar, input: input, imports: bendDirectory, oracle: oracle, prefer: prefer, guards: guards, extents: extents)
        }
        let directory = FileManager.default.temporaryDirectory.appendingPathComponent("apus-bend")
        try FileManager.default.createDirectory(at: directory, withIntermediateDirectories: true)
        let file = directory.appendingPathComponent("\(UUID().uuidString).bend")
        try text.write(to: file, atomically: true, encoding: .utf8)
        defer { try? FileManager.default.removeItem(at: file) }

        let process = Process()
        process.executableURL = URL(fileURLWithPath: executable)
        process.arguments = [file.path]
        let pipe = Pipe()
        process.standardOutput = pipe
        process.standardError = pipe
        try process.run()
        // Fuel bounds the depth of Bend's recursion, not its total work, so a run can still take
        // very long. Past the limit the case counts as "no answer", which fails the test.
        let stopped = TimeoutFlag()
        let stopper = DispatchWorkItem { if process.isRunning { stopped.value = true; process.terminate() } }
        DispatchQueue.global().asyncAfter(deadline: .now() + timeLimit, execute: stopper)
        let output = String(decoding: pipe.fileHandleForReading.readDataToEndOfFile(), as: UTF8.self)
        process.waitUntilExit()
        stopper.cancel()
        if stopped.value { return (.noAnswer, text, rootKept) }
        guard process.terminationStatus == 0 else { throw RunError.failed(status: process.terminationStatus, output: output) }
        return (try read(output), text, rootKept)
    }

    /// Reads `…COMPARE.Agree{6n}`, `…COMPARE.NoAnswer{}` or `…COMPARE.Differ{e, s, [..], [..]}`,
    /// with module prefixes taken out of the elements. Only the report's own line is read: bend
    /// may add other lines (such as "bend 2.0.40 is available: run bend update").
    static func read(_ output: String) throws -> BendReport {
        guard let found = output.split(separator: "\n").first(where: { $0.contains("COMPARE.") }) else { throw RunError.unreadable(output) }
        let line = found.trimmingCharacters(in: .whitespaces)
        guard let marker = line.range(of: "COMPARE.") else { throw RunError.unreadable(output) }
        let report = String(line[marker.upperBound...])
        if report.hasPrefix("NoAnswer") { return .noAnswer }
        guard let open = report.firstIndex(of: "{"), report.hasSuffix("}") else { throw RunError.unreadable(output) }
        let fields = topLevel(String(report[report.index(after: open)..<report.index(before: report.endIndex)]))
        func number(_ s: String) throws -> Int {
            guard let n = Int(s.trimmingCharacters(in: .whitespaces).dropLast()) else { throw RunError.unreadable(output) }
            return n
        }
        func elements(_ s: String) -> [String] {
            let inner = s.trimmingCharacters(in: .whitespaces).dropFirst().dropLast()
            return topLevel(String(inner)).filter { !$0.isEmpty }.map(plain)
        }
        if report.hasPrefix("Agree"), fields.count == 1 { return .agree(count: try number(fields[0])) }
        if report.hasPrefix("Differ"), fields.count == 4 {
            return .differ(exact: try number(fields[0]), swift: try number(fields[1]),
                           missing: elements(fields[2]), extra: elements(fields[3]))
        }
        throw RunError.unreadable(output)
    }

    /// Splits at the commas outside brackets and braces.
    static func topLevel(_ s: String) -> [String] {
        var parts: [String] = [], current = "", depth = 0
        for ch in s {
            switch ch {
            case "[", "{": depth += 1
            case "]", "}": depth -= 1
            case "," where depth == 0:
                parts.append(current.trimmingCharacters(in: .whitespaces)); current = ""; continue
            default: break
            }
            current.append(ch)
        }
        parts.append(current.trimmingCharacters(in: .whitespaces))
        return parts
    }

    /// `../SPEC.Bsr{../SPEC.Slot{0n, [1n]}, 0n, 0n, 1n}` as `Bsr{Slot{0, [1]}, 0, 0, 1}`.
    static func plain(_ element: String) -> String {
        var s = element
        while let r = s.range(of: "SPEC.") {
            var start = r.lowerBound
            while start > s.startIndex, !"{[, ".contains(s[s.index(before: start)]) { start = s.index(before: start) }
            s.removeSubrange(start..<r.upperBound)
        }
        return s.replacingOccurrences(of: "n,", with: ",").replacingOccurrences(of: "n]", with: "]")
            .replacingOccurrences(of: "n}", with: "}")
    }
}

// MARK: - Checking the test tables

/// Every accepted message of the `TestCase` tables, against the proven exact BSR set.
@Suite("Bend check", .enabled(if: BendRunner.executable != nil,
                              "opt-in: set APUS_BEND=<path to bend>, or APUS_BEND=1 for ~/.bend/bin/bend"))
struct BendCheck {
    static let cases: [TestCase] = (
        CoreGrammarTests.LiteralsAndSequences.cases + CoreGrammarTests.Selection.cases
        + CoreGrammarTests.EBNFBrackets.cases + CoreGrammarTests.Indirection.cases
        + CoreGrammarTests.Recursion.cases + CoreGrammarTests.Ambiguity.cases
        + CoreGrammarTests.NamedGrammars.cases + CoreGrammarTests.EmptyConstructs.cases
        + CoreGrammarTests.Regex.cases + CoreGrammarTests.TokenKinds.cases
        + CoreGrammarTests.TriviaNonTerminal.cases
        + BendExport.cases.map { TestCase(grammar: $0.grammar, pass: [$0.input], label: "bend: \($0.name)") }
    ).filter { !$0.illegalGrammar && !$0.pass.isEmpty }

    /// Fails when Swift misses a step of a parse tree. Dead wood is allowed (GLL keeps dead ends),
    /// and so are cases outside the Bend specification. Each case attaches its `BEND` lines, and the
    /// Bend file of every difference, to the test report.
    @Test(arguments: cases)
    func againstExactSet(_ tc: TestCase) throws {
        try compare(tc, oracle: false)
    }

    /// The same messages after `Oracle.disambiguate()`. These grammars carry no annotations, so
    /// only its phase 1 acts: it removes the yields on no complete derivation. Its contract:
    /// - the root still spans the input: the Oracle never removes the last parse;
    /// - it removes no step of a parse tree;
    /// - it leaves no dead wood: exactly the steps of the parse trees stay.
    @Test(arguments: cases)
    func oraclePhase1IsExact(_ tc: TestCase) throws {
        try compare(tc, oracle: true)
    }

    /// Grammars with `@prefer` and `@avoid`, from `OracleDisambiguationTests`, after the Oracle,
    /// against the steps of the selected trees (`Bend/PREFER.bend`, `prefer_avoid_exact`). A step
    /// Swift lacks belongs to a selected tree, so Swift removed a reading the annotations keep; a
    /// step Swift has in addition belongs to no selected tree. Both fail. Bend refuses grammars whose preferences go round a cycle, as Swift does.
    static let preferCases: [TestCase] = [
        TestCase(grammar: #"S = @prefer A | B . A = "t" . B = "t" ."#, pass: ["t"], label: "prefer: production"),
        TestCase(grammar: #"S = ( @prefer "a" B | "a" ) . B = "b" | "" ."#, pass: ["a"], label: "prefer: ε tail"),
        TestCase(grammar: #"b - /b/ . S = ( @prefer "a" b? | "a" ) ."#, pass: ["a"], label: "prefer: skipped tail"),
        TestCase(grammar: #"t - /t/ . S = @prefer A | @prefer B | @prefer C | D . A = t . B = t . C = t . D = t ."#, pass: ["t"], label: "prefer: three of four"),
        TestCase(grammar: #"t - /t/ . S = A | B | C | @avoid D . A = t . B = t . C = t . D = t ."#, pass: ["t"], label: "avoid: one of four"),
        TestCase(grammar: #"t - /t/ . S = @avoid A | @avoid B . A = t . B = t ."#, pass: ["t"], label: "avoid: two avoided"),
        TestCase(grammar: #"t - /t/ . S = @avoid A | @avoid B | C . A = t . B = t . C = t ."#, pass: ["t"], label: "avoid: unmarked wins"),
        TestCase(grammar: #"t - /t/ . S = @prefer A | B | @avoid C . A = t . B = t . C = t ."#, pass: ["t"], label: "ranks: three"),
        TestCase(grammar: #"t - /t/ . u - /u/ . S = @prefer A | B | @avoid C . A = u . B = t . C = t ."#, pass: ["t"], label: "ranks: no preferred match"),
        TestCase(grammar: #"a - /a/ . S = { @prefer A | B } . A = a a . B = a ."#, pass: ["a a"], label: "loop: rounds"),
        TestCase(grammar: #"a - /a/ . S = < @prefer A | B > . A = a a . B = a ."#, pass: ["a a"], label: "loop: positive rounds"),
        TestCase(grammar: #"a - /a/ . S = { @prefer A | B } "x" . A = a a . B = a ."#, pass: ["a a x"], label: "loop: rounds then x"),
        TestCase(grammar: #"a - /a/ . S = { @prefer A | B } . A = a . B = a ."#, pass: ["a a"], label: "loop: same-span rounds"),
        TestCase(grammar: #"x - /x/ . S = "[" ( @prefer root comps? | comps ) "]" . root = x . comps = x ."#, pass: ["[x]"], label: "prefer: in a group"),
        TestCase(grammar: #"item - /[a-z]/ . S = "[" list? "]" . list = @prefer item | item "," list ."#, pass: ["[]", "[a]", "[a, b]", "[a, b, c]"], label: "prefer: under an optional"),
        TestCase(grammar: #"item - /[a-z]/ . S = "[" ( @prefer item | item "," S2 )? "]" . S2 = item | item "," S2 ."#, pass: ["[]", "[a]", "[a, b]"], label: "prefer: optional group"),
        TestCase(grammar: #"a - /a/ . c - /c/ . S = [ @avoid A | B ] c . A = a . B = a ."#, pass: ["a c"], label: "avoid: in an optional"),
        TestCase(grammar: #"a - /a/ . S = [ @avoid A | B ] a? . A = a . B = a ."#, pass: ["a"], label: "avoid: optional and skip"),
        TestCase(grammar: #"S = A . A = @prefer "a" | A ."#, pass: ["a"], label: "prefer: over a cycle"),
        TestCase(grammar: #"S = A . A = @prefer B | C . B = "b" . C = "b" ."#, pass: ["b"], label: "prefer: through nonterminals"),
        TestCase(grammar: #"S = @prefer "if" "e" "then" S "else" S | "if" "e" "then" S | "a" ."#, pass: ["if e then if e then a else a"], label: "prefer: dangling else, with else"),
        TestCase(grammar: #"S = "if" "e" "then" S "else" S | @prefer "if" "e" "then" S | "a" ."#, pass: ["if e then if e then a else a"], label: "prefer: dangling else, without else"),
    ]

    @Test(arguments: preferCases)
    func preferencesAgainstBend(_ tc: TestCase) throws {
        try compare(tc, oracle: true, prefer: true)
    }

    /// `@prefer` on top of hard rules (`Bend/UNBEATEN.bend`, `prefer_avoid_exact`): a preferred
    /// alternative that has no admissible tree is no rival. Swift runs `@left`/`@right` before
    /// `@prefer`, as the spec does.
    @Test func joinAgainstBend() throws {
        let tc = TestCase(grammar: #"n - /[0-9]+/ . S = @prefer A | B . A = @left(P) P "+" P . P = n | n "+" n . B = n "+" n "+" n ."#, pass: ["1 + 2 + 3"], label: "join: inadmissible preferred rival")
        try compare(tc, oracle: true, prefer: true)
    }

    /// Grammars with `>?>`/`>!>`/`@left`/`@right`, after the Oracle, against the
    /// steps of the admissible trees (`Bend/GUARD.bend`, `guards_exact`). Both read a predicate as
    /// the language: some prefix of the rest derives N (Swift: the parser's probe of N).
    static let guardCases: [TestCase] = [
        TestCase(grammar: #"number - /[0-9]+/ . E = @left E "+" E | number ."#, pass: ["1 + 2", "1 + 2 + 3", "1 + 2 + 3 + 4"], label: "left: bare"),
        TestCase(grammar: #"number - /[0-9]+/ . E = @right E "+" E | number ."#, pass: ["1 + 2 + 3", "1 + 2 + 3 + 4"], label: "right: bare"),
        // The text, not the node: the last child `2 + 3` read via `E "+" F` is out too, because
        // `E "+" E` can derive its tokens (Bend/SPEC.bend, Guard, note 2).
        TestCase(grammar: #"n - /[0-9]+/ . E = @left E "+" E | E "+" F | n . F = n ."#, pass: ["1 + 2 + 3"], label: "left: by the text, not the node"),
        // BendDifferential seeds 110 and 119: the parse never called the listed `A`, nor started the
        // bare alternate where the last child starts; the parser probes them (documentation/Oracle.md § 4).
        TestCase(grammar: #"S = { "c" B | @left(A) "a" S } . A = A "a" @shortest ( S | "c" ) | @avoid "a" "b" "c" | "" . B = B "c" ."#, pass: ["a", "a a", "a a a"], label: "left: listed nonterminal the parse never called"),
        TestCase(grammar: #"S = [ >?>( B ) "a" | @left "c" A ] . A = "c" | @prefer "b" B "c" | "" . B = @prefer "a" ( "c" "a" ) S | "a" ."#, pass: ["c c"], label: "left: bare alternate the parse never started"),
        TestCase(grammar: #"n - /[0-9]+/ . S = E . E = ( @left E "+" E | n ) ."#, pass: ["1 + 2 + 3"], label: "left: in a group"),
        TestCase(grammar: #"n - /[0-9]+/ . S = E . E = ( @right E "+" E | n ) ."#, pass: ["1 + 2 + 3"], label: "right: in a group"),
        TestCase(grammar: #"S = @left(B) A B | A . A = "a" | "a" "a" . B = "a" ."#, pass: ["a a"], label: "left: with operand"),
        // The `f(1) {}⏎{}` pattern of Swift.apus: the parenless closure call `P K` may not take
        // `f ( ) { }` as its callee, because its items derive it (plain derives; its own `@right(AC)`
        // does not count).
        TestCase(grammar: #"S = F . F = AC | P "(" ")" K | @right @right(AC) P K . AC = P "(" ")" . P = "f" | F . K = "{" "}" ."#, pass: ["f ( ) { } { }"], label: "right: edge child derived only with a forbidden callee"),
        TestCase(grammar: #"S = @right(A) A B | B . B = "a" "a" | "a" . A = "a" ."#, pass: ["a a"], label: "right: with operand"),
        TestCase(grammar: #"a - /a/ . S = >!>(A) "a" . A = "a" ."#, pass: ["a"], label: "cannotParse: removes all"),
        TestCase(grammar: #"S = >!>(X) "a" B | "a" "c" . B = "b" . X = "a" "b" ."#, pass: ["a c"], label: "cannotParse: alternative"),
        TestCase(grammar: #"a - /a/ . S = >?>(A) B | "b" . B = A . A = "a" ."#, pass: ["a", "b"], label: "canParse: positive"),
        TestCase(grammar: #"t - /t/ . S = A A . A = >!>(D) t | t . D = t t ."#, pass: ["t t"], label: "cannotParse: ambiguous"),
        TestCase(grammar: #"t - /t/ . S = A A . A = >?>(D) t | t . D = t t ."#, pass: ["t t"], label: "canParse: ambiguous"),
        TestCase(grammar: #"S = >?>(X) "a" "b" | "a" Y . Y = "b" . X = "a" ."#, pass: ["a b"], label: "canParse: unpredicted target"),
        TestCase(grammar: #"S = >!>(X) "a" "b" | "a" Y . Y = "b" . X = "a" ."#, pass: ["a b"], label: "cannotParse: unpredicted target"),
        // BendDifferential seeds 2 and 18: the target derives where the parse never called it, and
        // derives by reading nothing before a token outside its FOLLOW.
        TestCase(grammar: #"S = "b" S | >!>(A) S "b" | "b" [ "c" ] "b" . A = "b" "c" | "" ."#, pass: ["b b b"], label: "cannotParse: target the parse did not call here"),
        TestCase(grammar: #"S = "c" | >?>(B) "c" "c" . B = { "b" } | "a" ."#, pass: ["c c"], label: "canParse: target that reads nothing"),
    ]

    @Test(arguments: guardCases)
    func guardsAgainstBend(_ tc: TestCase) throws {
        try compare(tc, oracle: true, guards: true)
    }

    /// Grammars with `@longest`/`@shortest`, after the Oracle, against the steps of the
    /// best-extent trees (`Bend/EXTENT.bend`, `extent_exact`). Bend compares extents locally,
    /// within the sequence the mark sits in, and refuses two marks in one sequence and a mark
    /// on a loop's alternative.
    static let extentCases: [TestCase] = [
        TestCase(grammar: #"word - /[a-z]+/ . @longest S = < word > ."#, pass: ["hello world foo"], label: "longest: start symbol"),
        TestCase(grammar: #"word - /[a-z]+/ . S = @longest < word > ."#, pass: ["hello world foo"], label: "longest: positive closure"),
        TestCase(grammar: #"word - /[a-z]+/ . S = @longest { word } ."#, pass: ["hello world foo"], label: "longest: closure"),
        TestCase(grammar: #"a - /a/ . S = @longest { a } { a } ."#, pass: ["a a", "a a a"], label: "longest: first of two closures"),
        TestCase(grammar: #"a - /a/ . S = @shortest { a } { a } ."#, pass: ["a a", "a a a"], label: "shortest: first of two closures"),
        TestCase(grammar: #"a - /a/ . S = { a } @longest { a } ."#, pass: ["a a"], label: "longest: second of two closures"),
        TestCase(grammar: #"x - /x/ . S = @longest { x } { x } { x } ."#, pass: ["xxx"], label: "longest: first of three closures"),
        TestCase(grammar: #"x - /x/ . S = @shortest { x } { x } { x } ."#, pass: ["xxx"], label: "shortest: first of three closures"),
        TestCase(grammar: #"x - /x/ . S = @shortest [ x ] [ x ] ."#, pass: ["x"], label: "shortest: first optional"),
        TestCase(grammar: #"x - /x/ . S = [ x ] @shortest [ x ] ."#, pass: ["x"], label: "shortest: second optional"),
        TestCase(grammar: #"op - /-/ . id - /[a-z]+/ . S = @shortest [ op ] id ."#, pass: ["-x", "x"], label: "shortest: forced take"),
        TestCase(grammar: #"a - /a/ . S = A B . @longest A = { a } . B = { a } ."#, pass: ["a a"], label: "longest: nonterminal"),
        TestCase(grammar: #"a - /a/ . S = A B . @shortest A = { a } . B = { a } ."#, pass: ["a a"], label: "shortest: nonterminal"),
        TestCase(grammar: #"a - /a/ . S = "(" A B ")" | A . @longest A = { a } . B = { a } ."#, pass: ["(a a)"], label: "longest: nonterminal in two sequences"),
        // Local, not global per start: `# e` (then a call) and `# e ( )` are readings of M in
        // different enclosing sequences, so both stay (the meaning Swift Apus had until 2026-11-10
        // kept only the longer).
        TestCase(grammar: ##"S = P . P = M | P "(" ")" . @longest M = "#" "e" [ "(" ")" ] ."##, pass: ["# e ( )"], label: "longest: nonterminal, rivals in different sequences"),
        TestCase(grammar: #"S = "if" "e" "then" S @longest [ "else" S ] | "a" ."#, pass: ["if e then if e then a else a"], label: "longest: dangling else"),
        TestCase(grammar: #"S = "if" "e" "then" S @shortest [ "else" S ] | "a" ."#, pass: ["if e then if e then a else a"], label: "shortest: dangling else"),
    ]

    @Test(arguments: extentCases)
    func extentsAgainstBend(_ tc: TestCase) throws {
        try compare(tc, oracle: true, extents: true)
    }

    @discardableResult
    func compare(_ tc: TestCase, oracle: Bool, prefer: Bool = false, guards: Bool = false, extents: Bool = false) throws -> [String] {
        var lines: [String] = []
        for message in tc.pass {
            let checked: (report: BendReport, file: String, rootKept: Bool)
            do {
                checked = try BendRunner.check(grammar: tc.grammar, input: message, oracle: oracle, prefer: prefer, guards: guards, extents: extents)
            } catch let error as BendExport.ExportError {
                lines.append("BEND refused   \(tc.label) '\(message)': \(error)")
                continue
            }
            if oracle, !checked.rootKept {
                lines.append("BEND lost parse \(tc.label) '\(message)'")
                // A hard rule may leave no tree at all; preferences may not.
                if !guards { Issue.record("\(tc.label) '\(message)': the Oracle removed the last parse, with grammar: \(tc.grammar)") }
            }
            switch checked.report {
            case .agree(let count):
                lines.append("BEND agree     \(tc.label) '\(message)': \(count) steps")
            case .noAnswer:
                // The laws cover only answers Bend gives (Bend/README.md, "What the laws
                // promise"): a case without one was not compared, so it fails.
                lines.append("BEND no answer \(tc.label) '\(message)'")
                Attachment.record(checked.file, named: "\(tc.label) '\(message)'.bend")
                Issue.record("\(tc.label) '\(message)': Bend gave no answer (out of fuel, a failed check, a refusal or the time limit), so the case was not compared, with grammar: \(tc.grammar)")
            case .differ(let exact, let swift, let missing, let extra):
                lines.append("BEND differ    \(tc.label) '\(message)': exact \(exact), swift \(swift), "
                             + "missing \(missing.count) \(missing), dead wood \(extra.count) \(extra)")
                Attachment.record(checked.file, named: "\(tc.label) '\(message)'.bend")
                #expect(missing.isEmpty, "\(tc.label) '\(message)': Swift misses parse-tree steps \(missing) with grammar: \(tc.grammar)")
                if oracle {
                    #expect(extra.isEmpty, "\(tc.label) '\(message)': the Oracle leaves dead wood \(extra) with grammar: \(tc.grammar)")
                }
            }
        }
        Attachment.record(lines.joined(separator: "\n") + "\n", named: extents ? "bend extent report.txt" : guards ? "bend guard report.txt" : prefer ? "bend prefer report.txt" : oracle ? "bend oracle report.txt" : "bend report.txt")
        return lines
    }
}

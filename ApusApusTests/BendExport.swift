import Foundation
import Testing

/// Writes small grammars, inputs and the BSR yields Swift Apus computes for them as Bend files, so
/// `Bend/COMPARE.bend` can set them next to the proven exact BSR set (see `Bend/README.md`).
/// Two opt-in suites use it:
/// - "Bend export" (`APUS_EXPORT_BEND=<directory>`, point it at `Bend/swift`) writes the cases below
///   as files; then `bend swift/<case>.bend` prints the report for one case.
/// - "Bend check" (`APUS_BEND=<path to bend>`, or `APUS_BEND=1` for `~/.bend/bin/bend`) runs Bend on
///   every accepted message of the `TestCase` tables, and fails a case when Swift misses a step of a
///   parse tree. Dead wood, refusals and fuel shortage are reported, not failed; after the Oracle,
///   dead wood fails too, except at loops.
/// Set the variable in the test plan, or as `TEST_RUNNER_<name>` via xcodebuild.
///
/// The export translates, and refuses rather than guesses:
/// - the grammar's GrammarNode graph to `Spec.Production`s: one per (nonterminal, alternate), with
///   brackets as `Spec.Brack` and an EPS node ("" or ε) as `Spec.Eps`;
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
            switch self { case .unsupported(let what): return "outside the Bend specification: \(what)" }
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
    /// Also returns which slots belong to loops (see `LoopSlots`). With `oracle`, the yields are
    /// taken after `Oracle.disambiguate()` instead of straight from the parser.
    /// `rootKept` says whether the root still spans the input (after the Oracle, if it ran).
    static func export(grammar text: String, input: String, imports: String, oracle: Bool = false) throws -> (text: String, loops: LoopSlots, rootKept: Bool) {
        let parser = try ApusParser(fromString: "whitespace : /\\s+/.\n" + text)
        let grammar = try parser.parse(explicitStartSymbol: "")
        let messageParser = MessageParser(grammar: grammar)
        messageParser.parse(input: input)
        if oracle { Oracle(parser: messageParser, input: input).disambiguate() }
        let rootKept = messageParser.yield(of: messageParser.currentParseRoot).contains {
            $0.i == input.startIndex && $0.j == input.endIndex
        }

        var translation = Translation(grammar: grammar)
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
        out += "def swiftSteps() -> +List<Spec.Bsr>:\n  [" + steps.joined(separator: ",\n   ") + "]\n\n"
        out += "def main() -> Compare.Report:\n  Compare.report(grammar(), start(), input(), swiftSteps())\n"
        return (out, translation.loops, rootKept)
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

    /// The slots of loops (`{ }` and `< >`), as `Slot{index, [path]}`.
    struct LoopSlots {
        /// Every slot inside a loop's alternates, nested ones included.
        var body: Set<String> = []
        /// The slot right after a loop.
        var after: Set<String> = []

        /// A step at or inside a loop.
        func isLoop(_ step: BendStep) -> Bool {
            body.contains(step.slot) || after.contains(step.slot)
        }
    }

    struct Translation {
        let grammar: Grammar
        var nonterminalNames: [String] = []
        var nonterminalID: [String: Int] = [:]
        var productions: [String] = []
        /// The slot of every node whose yields are exported, by node number.
        var slots: [Int: Slot] = [:]
        var droppedCompletionYields = 0
        var loops = LoopSlots()

        init(grammar: Grammar) { self.grammar = grammar }

        mutating func run() throws {
            nonterminalNames = grammar.nonTerminals.filter { !$0.value.isTrivia }.keys.sorted()
            for (id, name) in nonterminalNames.enumerated() { nonterminalID[name] = id }
            for (id, name) in nonterminalNames.enumerated() {
                let lhs = grammar.nonTerminals[name]!
                var alternate = lhs.alt
                while let alt = alternate {
                    let index = productions.count
                    productions.append("Spec.Production{\(id)n, \(try sequence(alt, index: index, prefix: [], inLoop: false))}")
                    alternate = alt.alt
                }
            }
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
        mutating func sequence(_ alt: GrammarNode, index: Int, prefix: [Int], inLoop: Bool) throws -> String {
            let nodes = items(alt)
            if nodes.isEmpty { throw ExportError.unsupported("an alternate with no item") }
            var parts: [String] = []
            for (m, node) in nodes.enumerated() {
                let slot = Slot(index: index, path: prefix + [m + 1])
                slots[node.number] = slot
                if inLoop { loops.body.insert(slot.text) }
                parts.append(try item(node, index: index, prefix: prefix, position: m, inLoop: inLoop))
            }
            return "[" + parts.joined(separator: ", ") + "]"
        }

        mutating func item(_ node: GrammarNode, index: Int, prefix: [Int], position m: Int, inLoop: Bool) throws -> String {
            switch node.kind {
            case .T, .TI, .C:
                return "Spec.Sym{Spec.Terminal{\(node.nameID!)n}}"
            case .N:
                guard let id = nonterminalID[node.name] else { throw ExportError.unsupported("nonterminal \(node.name)") }
                return "Spec.Sym{Spec.Nonterminal{\(id)n}}"
            case .DO, .OPT, .KLN, .POS:
                let kind = [GrammarNodeKind.DO: "Group", .OPT: "Optional", .KLN: "Closure", .POS: "Positive"][node.kind]!
                var alts: [String] = []
                let isLoop = node.kind == .KLN || node.kind == .POS
                if isLoop { loops.after.insert(Slot(index: index, path: prefix + [m + 1]).text) }
                for (a, alt) in alternates(node).enumerated() {
                    alts.append(try sequence(alt, index: index, prefix: prefix + [m, a], inLoop: inLoop || isLoop))
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

/// One element of a report, `Bsr{Slot{index, [path]}, i, k, j}`, split into slot and positions.
struct BendStep {
    let slot: String
    let i: Int, k: Int, j: Int

    init?(_ text: String) {
        guard text.hasPrefix("Bsr{"), let close = text.range(of: "]}") else { return nil }
        slot = String(text[text.index(text.startIndex, offsetBy: 4)..<close.upperBound])
        let numbers = text[close.upperBound...].split(whereSeparator: { !$0.isNumber }).compactMap { Int($0) }
        guard numbers.count == 3 else { return nil }
        (i, k, j) = (numbers[0], numbers[1], numbers[2])
    }
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

    /// `Bend/`, with SPEC.bend and COMPARE.bend, as an import prefix.
    static let bendDirectory = testProjectDirectory().appendingPathComponent("Bend").path + "/"

    /// Exports one grammar and input, runs Bend on it, and reads the report; also returns the file.
    static func check(grammar: String, input: String, oracle: Bool = false) throws -> (report: BendReport, file: String, loops: BendExport.LoopSlots, rootKept: Bool) {
        let executable = try #require(executable)
        let (text, loops, rootKept) = try withParserIsolation {
            try BendExport.export(grammar: grammar, input: input, imports: bendDirectory, oracle: oracle)
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
        let output = String(decoding: pipe.fileHandleForReading.readDataToEndOfFile(), as: UTF8.self)
        process.waitUntilExit()
        guard process.terminationStatus == 0 else { throw RunError.failed(status: process.terminationStatus, output: output) }
        return (try read(output), text, loops, rootKept)
    }

    /// Reads `…COMPARE.Agree{6n}`, `…COMPARE.NoAnswer{}` or `…COMPARE.Differ{e, s, [..], [..]}`,
    /// with module prefixes taken out of the elements.
    static func read(_ output: String) throws -> BendReport {
        let line = output.trimmingCharacters(in: .whitespacesAndNewlines)
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
    /// - it leaves no dead wood, except at loops: phase 1 deliberately keeps every loop iteration
    ///   end, for `@longest` to compare with (`Oracle.swift`, `pruneUnproductive`; TODO.md).
    @Test(arguments: cases)
    func oraclePhase1IsExact(_ tc: TestCase) throws {
        try compare(tc, oracle: true)
    }

    func compare(_ tc: TestCase, oracle: Bool) throws {
        var lines: [String] = []
        for message in tc.pass {
            let checked: (report: BendReport, file: String, loops: BendExport.LoopSlots, rootKept: Bool)
            do {
                checked = try BendRunner.check(grammar: tc.grammar, input: message, oracle: oracle)
            } catch let error as BendExport.ExportError {
                lines.append("BEND refused   \(tc.label) '\(message)': \(error)")
                continue
            }
            if oracle, !checked.rootKept {
                lines.append("BEND lost parse \(tc.label) '\(message)'")
                Issue.record("\(tc.label) '\(message)': the Oracle removed the last parse, with grammar: \(tc.grammar)")
            }
            switch checked.report {
            case .agree(let count):
                lines.append("BEND agree     \(tc.label) '\(message)': \(count) steps")
            case .noAnswer:
                lines.append("BEND no answer \(tc.label) '\(message)'")
            case .differ(let exact, let swift, let allMissing, let allExtra):
                let missing = allMissing
                let loopEnds = oracle ? allExtra.filter { BendStep($0).map(checked.loops.isLoop) ?? false } : []
                let extra = allExtra.filter { !loopEnds.contains($0) }
                lines.append("BEND differ    \(tc.label) '\(message)': exact \(exact), swift \(swift), "
                             + "missing \(missing.count) \(missing), "
                             + "dead wood \(extra.count) \(extra)"
                             + (oracle ? ", at loops \(loopEnds.count) \(loopEnds)" : ""))
                Attachment.record(checked.file, named: "\(tc.label) '\(message)'.bend")
                #expect(missing.isEmpty, "\(tc.label) '\(message)': Swift misses parse-tree steps \(missing) with grammar: \(tc.grammar)")
                if oracle {
                    #expect(extra.isEmpty, "\(tc.label) '\(message)': the Oracle leaves dead wood \(extra) with grammar: \(tc.grammar)")
                }
            }
        }
        Attachment.record(lines.joined(separator: "\n") + "\n", named: oracle ? "bend oracle report.txt" : "bend report.txt")
    }
}

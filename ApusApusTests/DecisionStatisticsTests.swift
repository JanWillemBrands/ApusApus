//
//  DecisionStatisticsTests.swift
//  ApusApusTests
//
//  Opt-in measurement (`APUS_DECISION_STATS=1`): how LL(1)-like the Swift grammar's parses are on
//  large real sources, and how many of the wasted alternatives two tokens of lookahead could cut.
//  See the decision statistics in Descriptor.swift. Appends a report to /tmp/apus-decision-stats.txt;
//  asserts only that each file parsed.
//

import Testing
import Foundation

@Suite("Decision statistics", .serialized,
       .enabled(if: ProcessInfo.processInfo.environment["APUS_DECISION_STATS"] == "1",
                "opt-in: set APUS_DECISION_STATS=1"))
struct DecisionStatisticsTests {

    static let files = ["Oracle.swift", "MessageParser.swift", "ApusParser.swift", "ApusToHTML.swift"]

    @Test(arguments: files)
    func swiftSource(_ file: String) throws {
        let grammar = try loadGrammarFile(named: "Swift")
        let url = testSourceDirectory().appendingPathComponent(file)
        let input = try String(contentsOf: url, encoding: .utf8)
        let parser = MessageParser(grammar: grammar)
        let start = Date()
        parser.parse(input: input)
        let seconds = Date().timeIntervalSince(start)
        let report = parser.decisionStatistics()
        let dead = parser.deadCallStatistics()
        let text = """
        === \(file): \(input.utf8.count) bytes, parse \(String(format: "%.2f", seconds)) s, \
        descriptors \(parser.descriptorCount), duplicates \(parser.duplicateDescriptorCount), \
        tokens \(Set(parser.commits.map { $0.triviaEnd }).count)
        \(lexMultiplicity(parser))
        \(dead.summary())
        \(report.summary())

        """
        // Test stdout does not reach xcodebuild's log: append the report to a file.
        let out = URL(fileURLWithPath: "/tmp/apus-decision-stats.txt")
        if let handle = try? FileHandle(forWritingTo: out) {
            handle.seekToEndOfFile(); handle.write(Data(text.utf8)); try? handle.close()
        } else {
            try text.write(to: out, atomically: true, encoding: .utf8)
        }
        #expect(parser.successfullParses > 0, "\(file) did not parse")
    }

    /// A long-running parse to attach a profiler to (`sample <xctest pid>`): Oracle.swift, 10 times.
    @Test func profileTarget() throws {
        let grammar = try loadGrammarFile(named: "Swift")
        let input = try String(contentsOf: testSourceDirectory().appendingPathComponent("Oracle.swift"), encoding: .utf8)
        for _ in 0..<10 {
            let parser = MessageParser(grammar: grammar)
            parser.parse(input: input)
            #expect(parser.successfullParses > 0)
        }
    }

    static let grammarInputs = ["apus.apus", "Swift.apus", "Python/Python.apus", "tortureEBNF.apus"]

    /// The APUS grammar is (nearly) LL(1): an LL(1) engine would need one descriptor. Where do
    /// the descriptors GLL makes come from? Classified by the slot they start at.
    @Test(arguments: grammarInputs)
    func apusGrammar(_ file: String) throws {
        let grammar = try loadGrammarFile(named: "apus")
        let url = testProjectDirectory().appendingPathComponent("grammars").appendingPathComponent(file)
        let input = try String(contentsOf: url, encoding: .utf8)
        let parser = MessageParser(grammar: grammar)
        let start = Date()
        parser.parse(input: input)
        let seconds = Date().timeIntervalSince(start)

        // The symbol each slot follows: alternate start, or after a terminal, nonterminal, bracket.
        var after = [Int: String]()
        var seen = Set<Int>()
        func walk(_ node: GrammarNode?) {
            guard let node, seen.insert(node.number).inserted else { return }
            if node.isLHS || node.kind.isBracket {
                var alt = node.alt
                while let a = alt {
                    if let first = a.seq { after[first.number] = "alternate start" }
                    for b in a.bodySymbols {
                        if let next = b.seq {
                            after[next.number] = b.kind == .N ? "after nonterminal (return)"
                                : b.kind.isBracket ? "after bracket (return or skip)" : "after terminal (multi-match)"
                        }
                    }
                    alt = a.alt
                }
            }
            if node.kind != .END { walk(node.seq) }
            if !node.isRHS { walk(node.alt) }
        }
        for nt in grammar.allProductions { walk(nt) }
        var byOrigin = [String: Int]()
        for d in parser.unique { byOrigin[after[d.L.number] ?? "other", default: 0] += 1 }

        let tokens = Set(parser.commits.map { $0.triviaEnd }).count
        let report = parser.decisionStatistics()
        let dead = parser.deadCallStatistics()
        var text = """
        === apus.apus on \(file): \(input.utf8.count) bytes, parse \(String(format: "%.3f", seconds)) s, \
        tokens \(tokens), descriptors \(parser.descriptorCount) (\(String(format: "%.2f", Double(parser.descriptorCount) / Double(max(tokens, 1)))) per token), \
        duplicates \(parser.duplicateDescriptorCount), clusters \(parser.crf.count), parses \(parser.successfullParses)
        descriptors by origin:

        """
        if parser.successfullParses == 0 {
            let line = input[positions: 0..<parser.furthestMismatchIndex].filter { $0 == "\n" }.count + 1
            let rest = input[from: parser.furthestMismatchIndex].prefix(60)
            text += "  FAILED at line \(line), expected \(parser.furthestMismatchExpected.sorted()): \(rest.debugDescription)\n"
        }
        for (origin, n) in byOrigin.sorted(by: { $0.value > $1.value }) { text += "  \(n)  \(origin)\n" }
        text += lexMultiplicity(parser)
        text += "\(dead.summary())\(report.summary())\n"
        let out = URL(fileURLWithPath: "/tmp/apus-decision-stats.txt")
        if let handle = try? FileHandle(forWritingTo: out) {
            handle.seekToEndOfFile(); handle.write(Data(text.utf8)); try? handle.close()
        } else {
            try text.write(to: out, atomically: true, encoding: .utf8)
        }
        #expect(parser.successfullParses > 0, "\(file) did not parse")
    }
}

/// How often does lexing on demand give more than one token at a position? Read from the parser's
/// lex cache, which holds every (position, terminal) question asked during the parse (Oracle
/// sub-parses included: the cache lives for the whole input).
func lexMultiplicity(_ parser: MessageParser) -> String {
    var name = [Int: String]()
    for (symbol, id) in parser.grammar.symbolToID { name[id] = symbol }
    var asked = [CharPosition: Int]()
    var matched = [CharPosition: [LexMatch]]()
    parser.forEachLexAnswer { key, matches in
        asked[key.pos, default: 0] += 1
        if !matches.isEmpty { matched[key.pos, default: []].append(contentsOf: matches) }
    }
    var questions = 0, maxAsked = 0
    for n in asked.values { questions += n; maxAsked = max(maxAsked, n) }
    var byTerminals = [Int](repeating: 0, count: 4)   // positions where 0, 1, 2, 3+ terminals matched
    var sameLength = 0, differentLength = 0           // among positions with 2+ terminals
    var multiEnd = 0                                  // one terminal with 2+ ends (preempt splits)
    var sameLengthSets = [String: Int](), differentLengthSets = [String: Int]()
    for pos in asked.keys {
        let ms = matched[pos] ?? []
        let terminals = Set(ms.map(\.terminalID))
        byTerminals[min(terminals.count, 3)] += 1
        if Dictionary(grouping: ms, by: \.terminalID).values.contains(where: { Set($0.map(\.end)).count > 1 }) { multiEnd += 1 }
        guard terminals.count > 1 else { continue }
        let set = terminals.map { name[$0] ?? "#\($0)" }.sorted().joined(separator: " | ")
        if Set(ms.map(\.end)).count == 1 { sameLength += 1; sameLengthSets[set, default: 0] += 1 }
        else { differentLength += 1; differentLengthSets[set, default: 0] += 1 }
    }
    func pct(_ a: Int, _ b: Int) -> String { b == 0 ? "-" : String(format: "%.1f%%", 100.0 * Double(a) / Double(b)) }
    let positions = asked.count
    var s = "lexing: \(positions) positions asked, \(questions) (position, terminal) questions "
    s += "(\(String(format: "%.1f", Double(questions) / Double(max(positions, 1)))) per position, max \(maxAsked))\n"
    s += "  terminals matching per position: 0: \(byTerminals[0])  1: \(byTerminals[1]) (\(pct(byTerminals[1], positions)))  "
    s += "2: \(byTerminals[2]) (\(pct(byTerminals[2], positions)))  3+: \(byTerminals[3]) (\(pct(byTerminals[3], positions)))\n"
    s += "  of the positions with 2+ terminals: same length \(sameLength), different lengths \(differentLength); "
    s += "one terminal with 2+ ends: \(multiEnd)\n"
    s += "  same length, top sets:\n"
    for (set, n) in sameLengthSets.sorted(by: { $0.value > $1.value }).prefix(12) { s += "    \(n)  \(set)\n" }
    s += "  different lengths, top sets:\n"
    for (set, n) in differentLengthSets.sorted(by: { $0.value > $1.value }).prefix(12) { s += "    \(n)  \(set)\n" }

    // Questions by terminal kind: what a precomputed tΣᵢ would have to lex, and what it costs now.
    let lexer = parser.lexer!
    func kind(_ matcher: TerminalMatcher?) -> String {
        switch matcher {
        case .literal?:     return "literal"
        case .handWritten?: return "hand-written"
        case .regex?:       return "regex"
        case .recogniser?:  return "recogniser"
        case nil:           return "other"
        }
    }
    func kind(_ id: Int) -> String { kind(lexer.terminals[id]) }
    var byKind = [String: (asked: Int, matched: Int)]()
    var regexAsked = [Int: Int]()
    parser.forEachLexAnswer { key, matches in
        let k = kind(key.terminalID)
        var e = byKind[k] ?? (0, 0)
        e.asked += 1
        if !matches.isEmpty { e.matched += 1 }
        byKind[k] = e
        if k == "regex" || k == "hand-written" { regexAsked[key.terminalID, default: 0] += 1 }
    }
    func census(_ matchers: [TerminalMatcher?]) -> String {
        Dictionary(grouping: matchers.compactMap { $0 }, by: { kind($0) })
            .map { "\($0.value.count) \($0.key)" }.sorted().joined(separator: ", ")
    }
    s += "  grammar terminals: \(census(lexer.terminals)); \(lexer.literalMunchIDs.count) literal-munch; "
    s += "trivia: \(census(lexer.trivia)); virtual-token positions \(lexer.virtualTokensAt.count)\n"
    for (k, e) in byKind.sorted(by: { $0.value.asked > $1.value.asked }) {
        s += "  \(k): \(e.asked) questions (\(String(format: "%.1f", Double(e.asked) / Double(max(positions, 1)))) per position), matched \(e.matched) (\(pct(e.matched, e.asked)))\n"
    }
    s += "  regex terminals most asked (questions per position):\n"
    for (id, n) in regexAsked.sorted(by: { $0.value > $1.value }).prefix(15) {
        s += "    \(String(format: "%.2f", Double(n) / Double(max(positions, 1))))  \(name[id] ?? "#\(id)")\n"
    }
    return s
}

//
//  BendDifferential.swift
//  ApusApusTests
//
//  Differential testing of the Oracle against the Bend twin (TODO.md, "Oracle: open items"): small random
//  grammars with random disambiguation annotations, every short input Swift parses, and the whole
//  pipeline (`Compare.extentReport`: admissible, unbeaten, best extent) on each. A disagreement
//  fails the case with its Bend file attached, as in `BendCheck`.
//
//  Opt-in: `APUS_BEND` as for `BendCheck`, and `APUS_BEND_FUZZ=<number of grammars>`;
//  `APUS_BEND_FUZZ_SEED=<first seed>` shifts the range. A case's label is its seed, so a failure
//  is reproduced by running that seed again. Every case is also appended to
//  `$TMPDIR/apus-bend-differential.txt`.

import Foundation
import Testing

/// SplitMix64: a small seeded generator, so a seed always gives the same grammar.
struct SeededGenerator: RandomNumberGenerator {
    private var state: UInt64
    init(seed: UInt64) { state = seed &+ 0x9E37_79B9_7F4A_7C15 }
    mutating func next() -> UInt64 {
        state &+= 0x9E37_79B9_7F4A_7C15
        var z = state
        z = (z ^ (z >> 30)) &* 0xBF58_476D_1CE4_E5B9
        z = (z ^ (z >> 27)) &* 0x94D0_49BB_1331_11EB
        return z ^ (z >> 31)
    }
}

/// A random grammar over the tokens `a b c` with nonterminals `S A B`, in Apus syntax.
struct RandomGrammar {
    static let tokens = ["a", "b", "c"]
    static let nonterminals = ["S", "A", "B"]

    var rng: SeededGenerator

    mutating func chance(_ percent: Int) -> Bool { Int.random(in: 0..<100, using: &rng) < percent }
    mutating func pick<T>(_ options: [T]) -> T { options[Int.random(in: 0..<options.count, using: &rng)] }

    /// A terminal or a nonterminal reference.
    mutating func symbol() -> String {
        chance(60) ? "\"\(pick(Self.tokens))\"" : pick(Self.nonterminals)
    }

    /// A bracket with one or two simple alternatives, sometimes marked `@longest`/`@shortest`.
    mutating func bracket() -> String {
        let (open, close) = pick([("(", ")"), ("[", "]"), ("{", "}"), ("<", ">")])
        var alternatives: [String] = []
        for _ in 0..<Int.random(in: 1...2, using: &rng) {
            let items = (0..<Int.random(in: 1...2, using: &rng)).map { _ in symbol() }
            alternatives.append(annotate(items))
        }
        let mark = chance(20) ? pick(["@longest ", "@shortest "]) : ""
        return "\(mark)\(open) \(alternatives.joined(separator: " | ")) \(close)"
    }

    /// The items with the annotations an alternative may carry: a rank, a parse predicate, and
    /// `@left`/`@right` (bare, or with a nonterminal operand).
    mutating func annotate(_ items: [String]) -> String {
        var prefix: [String] = []
        if chance(15) { prefix.append(pick(["@prefer", "@avoid"])) }
        if chance(8) { prefix.append("\(pick([">?>", ">!>"]))( \(pick(Self.nonterminals)) )") }
        if items.count >= 2, chance(15) {
            let direction = pick(["@left", "@right"])
            prefix.append(chance(50) ? direction : "\(direction)(\(pick(Self.nonterminals)))")
        }
        return (prefix + items).joined(separator: " ")
    }

    mutating func alternative() -> String {
        let count = Int.random(in: 0...3, using: &rng)
        if count == 0 { return "\"\"" }
        let items = (0..<count).map { _ in chance(20) ? bracket() : symbol() }
        return annotate(items)
    }

    mutating func text() -> String {
        Self.nonterminals.map { name in
            let alternatives = (0..<Int.random(in: 1...3, using: &rng)).map { _ in alternative() }
            let mark = chance(10) ? pick(["@longest ", "@shortest "]) : ""
            return "\(mark)\(name) = \(alternatives.joined(separator: " | ")) ."
        }.joined(separator: " ")
    }
}

/// The run's settings, outside the suite so that its `.enabled` trait can read them.
enum BendDifferentialSettings {
    static let count = Int(ProcessInfo.processInfo.environment["APUS_BEND_FUZZ"] ?? "") ?? 0
    static let firstSeed = UInt64(ProcessInfo.processInfo.environment["APUS_BEND_FUZZ_SEED"] ?? "") ?? 0
}

@Suite("Bend differential", .enabled(if: BendRunner.executable != nil && BendDifferentialSettings.count > 0,
                                     "opt-in: set APUS_BEND (see Bend check) and APUS_BEND_FUZZ=<number of grammars>"))
struct BendDifferential {
    static let seeds: [UInt64] = (0..<UInt64(BendDifferentialSettings.count)).map { BendDifferentialSettings.firstSeed + $0 }
    static let log = FileManager.default.temporaryDirectory.appendingPathComponent("apus-bend-differential.txt")
    static let logLock = NSLock()

    static func append(_ line: String) {
        logLock.lock()
        defer { logLock.unlock() }
        if let handle = try? FileHandle(forWritingTo: log) {
            handle.seekToEndOfFile()
            handle.write(Data((line + "\n").utf8))
            try? handle.close()
        } else {
            try? (line + "\n").write(to: log, atomically: true, encoding: .utf8)
        }
    }

    /// Every input of one to three tokens that Swift parses, longest first, at most three.
    static func inputs(for grammar: String) -> [String] {
        var all: [String] = []
        for length in 1...3 {
            var words: [[String]] = [[]]
            for _ in 0..<length { words = words.flatMap { w in RandomGrammar.tokens.map { w + [$0] } } }
            all += words.map { $0.joined(separator: " ") }
        }
        var found: [String] = []
        for input in all.reversed() where found.count < 3 {
            if (try? parseMatches(grammar: grammar, message: input)) == true { found.append(input) }
        }
        return found
    }

    @Test("seed", arguments: seeds)
    func seed(_ seed: UInt64) throws {
        var generator = RandomGrammar(rng: SeededGenerator(seed: seed))
        let grammar = generator.text()
        // Grammars Swift refuses (a preference cycle, a malformed annotation) are no test.
        guard (try? parseGrammar(grammar)) != nil else {
            Self.append("seed \(seed) refused   \(grammar)")
            return
        }
        let inputs = Self.inputs(for: grammar)
        guard !inputs.isEmpty else {
            Self.append("seed \(seed) no input  \(grammar)")
            return
        }
        let tc = TestCase(grammar: grammar, pass: inputs, label: "seed \(seed)")
        let lines = try BendCheck().compare(tc, oracle: true, guards: true, extents: true)
        Self.append("seed \(seed) checked \(grammar)\n  " + lines.joined(separator: "\n  "))
    }
}

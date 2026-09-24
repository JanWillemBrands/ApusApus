//
//  ParserModel.swift
//  tinyGLL
//
//  The explorer's state: a grammar, an input, and the parse of the two.
//

import Foundation
import Observation

/// Owns everything the explorer shows. Views read it and never touch the engine directly.
///
/// The engine used to keep its state in globals, which is why the old explorer copied pieces
/// of it into `@State` — "SwiftUI cannot observe a global". A parse now produces a `Parser`
/// and a `ParseResult`, and this is the one observable place they live.
@Observable
final class ParserModel {

    enum Status {
        case idle
        case accepted(Int)
        case rejected
        case failed(String)
    }

    var grammarText: String {
        didSet { defaults.set(grammarText, forKey: Key.grammar) }
    }

    var inputText: String {
        didSet { defaults.set(inputText, forKey: Key.input) }
    }

    private(set) var result = ParseResult()
    private(set) var status = Status.idle

    /// Bumped by every parse, and used as the derivation pane's identity so that its state —
    /// which derivation, which nodes collapsed — starts fresh on a new tree rather than
    /// carrying collapse paths over to a tree they no longer describe.
    private(set) var parseID = 0

    /// Where the last successful Generate wrote its parser.
    private(set) var generatedParser: URL?

    private(set) var benchmark: BenchmarkReport?
    private(set) var isBenchmarking = false

    /// Driven by the Benchmark… menu item, which is outside the view that presents the sheet.
    var isShowingBenchmark = false

    /// Surfaced as an alert: unlike a grammar error, a failed Generate or benchmark is about
    /// the machine rather than the grammar, so it does not belong in the status label.
    var toolError: String?

    private enum Key {
        static let grammar = "grammarText"
        static let input = "inputText"
    }

    private let defaults: UserDefaults

    init(defaults: UserDefaults = .standard) {
        self.defaults = defaults
        grammarText = defaults.string(forKey: Key.grammar) ?? "S = a S | ε ."
        inputText = defaults.string(forKey: Key.input) ?? "aa"
    }

    // MARK: Parsing

    func parse() {
        parseID += 1
        generatedParser = nil

        let parser = Parser(syntax: grammarText, input: inputText)

        do {
            try parser.parseGrammar()
            // Captured before the input parse, so the grammar diagram still draws when the
            // input is rejected or the grammar is being edited toward something parseable.
            result = ParseResult(grammarOf: parser)
            try parser.parseInput()
        } catch {
            status = .failed("\(error)")
            return
        }

        // Captured before the acceptance check: a rejected parse still builds a CRF, and
        // looking at where the calls got to is exactly how you find out why it failed.
        result.add(parseOf: parser)

        guard parser.parseAccepted else {
            status = .rejected
            return
        }

        let derivations = DerivationBuilder(parser: parser).allDerivations()
        result.derivations = derivations
        result.addTrace(of: derivations)
        status = derivations.isEmpty ? .rejected : .accepted(derivations.count)

        // A successful parse means the grammar is worth compiling, so the generated parser
        // is one menu item away — but it is not written unasked, the way the CLI did on
        // every accepting run.
    }

    var canGenerate: Bool {
        if case .accepted = status { return true }
        return false
    }

    // MARK: Generating

    /// Writes a standalone parser for the grammar just parsed. Generated only after a
    /// successful parse: the templates assume a grammar the interpreter has already agreed
    /// with.
    func generateParser() {
        let parser = Parser(syntax: grammarText, input: inputText)
        do {
            try parser.parseGrammar()
            generatedParser = try generate(from: parser)
        } catch {
            toolError = "\(error)"
        }
    }

    // MARK: Benchmarking

    func runBenchmark(maxLength: Int = Benchmark.defaultMaxLength) async {
        guard !isBenchmarking else { return }
        isBenchmarking = true
        defer { isBenchmarking = false }

        do {
            benchmark = try await Benchmark.run(maxLength: maxLength)
        } catch {
            toolError = "\(error)"
        }
    }
}

extension UserDefaults {
    /// A throwaway domain, so a preview neither reads nor writes the grammar you were
    /// working on.
    static let tinyGLLPreview = UserDefaults(suiteName: "tinyGLL.preview") ?? .standard
}

//
//  ParseResult.swift
//  tinyGLL
//
//  What one parse leaves behind, as values the views can hold on to.
//

import Foundation

/// A parse, frozen at the moment it finished.
///
/// The diagram panes used to read the engine's globals directly — `input` for the source
/// strip, `yields` for the BSR inspectors — which meant they redrew from whatever the *next*
/// parse had done to those globals. Everything they need is copied out here instead, so a
/// pane draws the parse it was handed and nothing else.
struct ParseResult {

    var input: [Character] = []

    /// BSR yields by GrammarNode.number, exactly as the parser left them.
    var yields: [Set<BinarySpan>] = []

    /// The grammar read by the last successful parseGrammar().
    var definitions: [Character: GrammarNode] = [:]

    /// The call return forest. A value copy, because the engine's clusters are classes it
    /// mutates in place.
    var crf = CRFSnapshot()

    var derivations: [DerivationNode] = []

    /// The link table and BSR listing the CLI's trace mode used to print.
    var trace = ""

    /// Built after `parseGrammar()` but before `parseInput()`, so the grammar pane still
    /// draws while the input is rejected or the grammar is being edited toward something
    /// parseable.
    init(grammarOf parser: Parser) {
        definitions = parser.nonTerminalDefinitions
        input = parser.input
    }

    init() {}

    /// Fills in everything the input parse produced. Called even when the parse is rejected:
    /// a failed parse still builds a CRF, and looking at where the calls got to is exactly
    /// how you find out why it failed.
    mutating func add(parseOf parser: Parser) {
        input = parser.input
        yields = parser.yields
        definitions = parser.nonTerminalDefinitions
        crf = CRFSnapshot(crf: parser.crf, root: parser.nonTerminalDefinitions["S"])
        trace = Self.trace(of: parser)
    }

    /// The grammar's seq/alt link table followed by the start symbol's yields — the two
    /// things `tinyGLL` and `tinyGLL --trace` printed to stdout.
    private static func trace(of parser: Parser) -> String {
        var text = "grammar nodes\nnumber\tkind\tlinks\n"
        for definition in parser.nonTerminalDefinitions.values.sorted(by: { $0.number < $1.number }) {
            text += definition.dump()
        }

        text += "\n\(parser.parseAccepted ? "Parse pass" : "Parse fail")\n"

        if let root = parser.nonTerminalDefinitions["S"],
           parser.yields.indices.contains(root.number) {
            text += "\nstart symbol yields  (i:k:j)\n"
            text += parser.yields[root.number].sorted().map(\.description).joined(separator: " ")
            text += "\n"
        }
        return text
    }

    /// The indented derivation trees `tinyGLL --tree` printed, appended to the trace once the
    /// derivations are known.
    mutating func addTrace(of derivations: [DerivationNode]) {
        trace += "\n\(derivations.count) derivation\(derivations.count == 1 ? "" : "s")\n"
        for (n, tree) in derivations.enumerated() {
            trace += "\nderivation \(n + 1):\n"
            trace += tree.dump(indent: 1)
        }
    }
}

#if DEBUG
extension ParseResult {
    /// A finished parse for previews, so each pane can be previewed on its own without the
    /// explorer and its model around it.
    static func preview(grammar: String = "S = a S | ε .", input: String = "aa") -> ParseResult {
        let parser = Parser(syntax: grammar, input: input)
        var result = ParseResult()

        do {
            try parser.parseGrammar()
            result = ParseResult(grammarOf: parser)
            try parser.parseInput()
        } catch {
            return result
        }

        result.add(parseOf: parser)
        let derivations = DerivationBuilder(parser: parser).allDerivations()
        result.derivations = derivations
        result.addTrace(of: derivations)
        return result
    }

    /// The ambiguous tortureART grammar, which is the interesting case for every pane.
    static var previewAmbiguous: ParseResult {
        preview(grammar: " S = b | S S | S S S .", input: "bbb")
    }
}
#endif

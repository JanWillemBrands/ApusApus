import Foundation
import Testing

/// TODO.md / Add a preserving-trivia round-trip test — the guard for the trivia refactor (item 7).
///
/// Every terminal leaf of the post-Oracle derivation owns `[from, to)`: its content plus the trivia
/// that follows it. For an accepted input the leaves must therefore TILE the parsed span exactly —
/// contiguous, no gaps, no overlaps — and each leaf's image must lie inside its own span. Then
/// concatenating `input[leaf.from ..< leaf.to]` reproduces the source byte for byte. A converter,
/// Oracle or builder change that loses, duplicates or misattributes trivia breaks this.
@Suite("Trivia round-trip")
struct TriviaRoundTripTests {
    static let snippets: [SwiftSnippet] = {
        let collections: [[SwiftSnippet]] = [
            translatedSnippets, attributeSnippets, declarationSnippets, expressionSnippets,
            statementSnippets, typeSnippets, patternSnippets, phase4StringSnippets, phase4KeyPathSnippets,
            phase4IfConfigSnippets, regexWhitespaceAcceptSnippets, fuzzHarvestSnippets,
        ]
        var seen = Set<String>()
        return collections.joined().filter { seen.insert($0.source).inserted }
    }()

    @Test("leaves tile the source", arguments: snippets)
    func leavesTileTheSource(_ snippet: SwiftSnippet) throws {
        guard let result = try adventParse(snippet), let root = result.tree else { return }   // acceptance is tested elsewhere
        let input = snippet.source
        var leaves: [ParseTreeNode] = []
        func collect(_ node: ParseTreeNode) {
            if node.isTerminal {
                if node.from < node.to { leaves.append(node) }   // zero-width boundaries own nothing
            } else {
                node.children.forEach(collect)
            }
        }
        collect(root)
        guard let first = leaves.first, let last = leaves.last else { return }

        #expect(first.from == root.from, "first leaf does not start at the root: \(snippet.diagnosticID)")
        #expect(last.to == root.to, "last leaf does not end at the root: \(snippet.diagnosticID)")
        var rebuilt = ""
        for (index, leaf) in leaves.enumerated() {
            if index > 0 {
                let previous = leaves[index - 1]
                #expect(previous.to == leaf.from, """
                    gap or overlap between leaves '\(previous.name)' and '\(leaf.name)' at \
                    \(input.distance(from: input.startIndex, to: leaf.from)) in \(snippet.diagnosticID)
                    """)
            }
            if let image = leaf.image {
                #expect(image.startIndex >= leaf.from && image.endIndex <= leaf.to,
                        "image of '\(leaf.name)' lies outside its span in \(snippet.diagnosticID)")
            }
            rebuilt += input[leaf.from..<leaf.to]
        }
        #expect(rebuilt == String(input[root.from..<root.to]), "round trip differs: \(snippet.diagnosticID)")
    }
}

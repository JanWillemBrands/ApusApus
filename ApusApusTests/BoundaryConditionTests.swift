import Testing
import SwiftSyntax
@_spi(ExperimentalLanguageFeatures) import SwiftParser

/// A small differential harness for trivia-sensitive grammar predicates.
///
/// Each case inserts one trivia class at a known boundary. Acceptance alone is
/// insufficient: a newline can turn one expression into two valid statements,
/// so the generated ApusApus tree must also match SwiftSyntax exactly.
@Suite("grammar boundary conditions")
struct BoundaryConditionTests {
    struct TriviaCase: Sendable, CustomTestStringConvertible {
        let name: String
        let trivia: String

        var testDescription: String { name }
        var source: String { "let x = f\(trivia)(1)" }
    }

    static let callParenthesisCases = [
        TriviaCase(name: "tight", trivia: ""),
        TriviaCase(name: "space", trivia: " "),
        TriviaCase(name: "line comment", trivia: " // boundary\n"),
        TriviaCase(name: "newline", trivia: "\n"),
        TriviaCase(name: "single-line block comment", trivia: "/* boundary */"),
        TriviaCase(name: "multiline block comment", trivia: "/* boundary\n */"),
    ]

    @Test("call parenthesis >n<", arguments: callParenthesisCases)
    func callParenthesis(case boundary: TriviaCase) throws {
        let source = boundary.source
        let reference = Parser.parse(source: source)

        #expect(swiftSyntaxParsesCleanly(source),
                "SwiftSyntax rejected the generated fixture: \(boundary.name)")

        let result = try #require(adventParse(source),
                                  "ApusApus rejected: \(boundary.name)")
        #expect(result.isUnambiguous,
                "Residual ambiguity at boundary: \(boundary.name)")

        let tree = try #require(adventSwiftSyntaxTree(source),
                                "ApusApus produced no tree: \(boundary.name)")
        #expect(
            dumpSwiftSyntaxNode(Syntax(tree), indent: 0)
                == dumpSwiftSyntaxNode(Syntax(reference), indent: 0),
            "Tree differs at boundary: \(boundary.name)"
        )
    }
}

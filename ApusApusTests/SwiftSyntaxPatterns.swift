//
//  SwiftSyntaxPatterns.swift
//  AdventTests
//
//  Patterns snippets extracted from SwiftSyntax PatternTests.swift (603.0.1).
//  See SwiftSyntaxTests.swift for shared infrastructure.
//

import Testing
import Foundation
import SwiftSyntax
import SwiftParser

// MARK: - Snippet Catalog

let patternSnippets: [SwiftSnippet] = [
    SwiftSnippet(
        label: "testNonBinding1#1",
        source: """
      if case let E<Int>.e(y) = x {}
      """,
        origin: "PatternTests.testNonBinding1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testNonBinding2#1",
        source: """
      switch e {
      case let E<Int>.e(y):
        y
      }
      """,
        origin: "PatternTests.testNonBinding2",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testNonBinding3#1",
        source: """
      if case let (y[0], z) = x {}
      """,
        origin: "PatternTests.testNonBinding3",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testNonBinding4#1",
        source: """
      switch x {
      case let (y[0], z):
        z
      }
      """,
        origin: "PatternTests.testNonBinding4",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testNonBinding5#1",
        source: """
      if case let y[z] = x {}
      """,
        origin: "PatternTests.testNonBinding5",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testNonBinding6#1",
        source: """
      switch 0 {
      case let y[z]:
        z
      case y[z]:
        0
      default:
        0
      }
      """,
        origin: "PatternTests.testNonBinding6",
        syntaxVersion: "603.0.1"
    ),
]


// MARK: - Test Suite

extension SwiftSyntax603Tests {

@Suite("Patterns")
struct PatternSyntaxTests {

    @Test("SwiftSyntax accepts", .tags(.swiftSyntaxReference), arguments: patternSnippets)
    func swiftSyntaxAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let parsed = Parser.parse(source: snippet.source)
        #expect(!parsed.hasError, "SwiftSyntax parse error for: \(snippet.source)")
    }

    @Test("Advent accepts", arguments: patternSnippets)
    func adventAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let result = try adventParse(snippet)
        #expect(result != nil, "Advent failed to parse: \(snippet.source)")
    }

    @Test("no residual ambiguity", arguments: patternSnippets)
    func unambiguous(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        guard let result = try adventParse(snippet) else {
            Issue.record("Advent failed to parse: \(snippet.source)")
            return
        }
        #expect(result.isUnambiguous,
                "Residual ambiguity in '\(snippet.diagnosticID)': \(result.builder.diagnostics)")
    }

    @Test("trees match", arguments: patternSnippets)
    func treesMatch(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let reference = Parser.parse(source: snippet.source)
        let refDump = dumpSwiftSyntaxNode(Syntax(reference), indent: 0)

        guard let adventTree = try adventSwiftSyntaxTree(snippet) else {
            Issue.record("Advent failed to produce SwiftSyntax tree: \(snippet.source)")
            return
        }
        let adventDump = dumpSwiftSyntaxNode(Syntax(adventTree), indent: 0)

        #expect(refDump == adventDump, "Trees differ for '\(snippet.diagnosticID)'")
    }
}
}

// MARK: - SwiftSyntax 604 Corpus

let pattern604Snippets: [SwiftSnippet] = [
    SwiftSnippet(
        label: "testNonBinding1#1",
        source: """
      if case let E<Int>.e(y) = x {}
      """,
        origin: "PatternTests.testNonBinding1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testNonBinding2#1",
        source: """
      switch e {
      case let E<Int>.e(y):
        y
      }
      """,
        origin: "PatternTests.testNonBinding2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testNonBinding3#1",
        source: """
      if case let (y[0], z) = x {}
      """,
        origin: "PatternTests.testNonBinding3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testNonBinding4#1",
        source: """
      switch x {
      case let (y[0], z):
        z
      }
      """,
        origin: "PatternTests.testNonBinding4",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testNonBinding5#1",
        source: """
      if case let y[z] = x {}
      """,
        origin: "PatternTests.testNonBinding5",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testNonBinding6#1",
        source: """
      switch 0 {
      case let y[z]:
        z
      case y[z]:
        0
      default:
        0
      }
      """,
        origin: "PatternTests.testNonBinding6",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
]

extension SwiftSyntax604Tests {

@Suite("Patterns")
struct PatternSyntax604Tests {

    @Test("SwiftSyntax accepts", .tags(.swiftSyntaxReference), arguments: pattern604Snippets)
    func swiftSyntaxAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        #expect(!swiftSyntaxReferenceHasError(snippet), "SwiftSyntax parse error for: \(snippet.source)")
    }

    @Test("Advent accepts", arguments: pattern604Snippets)
    func adventAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let result = try adventParse(snippet)
        #expect(result != nil, "Advent failed to parse: \(snippet.source)")
    }

    @Test("no residual ambiguity", arguments: pattern604Snippets)
    func unambiguous(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        guard let result = try adventParse(snippet) else {
            Issue.record("Advent failed to parse: \(snippet.source)")
            return
        }
        #expect(result.isUnambiguous,
                "Residual ambiguity in '\(snippet.diagnosticID)': \(result.builder.diagnostics)")
    }

    @Test("trees match", arguments: pattern604Snippets)
    func treesMatch(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let refDump = swiftSyntaxReferenceDump(snippet)

        guard let adventTree = try adventSwiftSyntaxTree(snippet) else {
            Issue.record("Advent failed to produce SwiftSyntax tree: \(snippet.source)")
            return
        }
        let adventDump = dumpSwiftSyntaxNode(Syntax(adventTree), indent: 0)

        #expect(refDump == adventDump, "Trees differ for '\(snippet.diagnosticID)'")
    }
}
}

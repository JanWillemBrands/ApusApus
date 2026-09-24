//
//  SwiftSyntaxStatements.swift
//  AdventTests
//
//  Statements snippets extracted from SwiftSyntax StatementTests.swift (603.0.1).
//  See SwiftSyntaxTests.swift for shared infrastructure.
//

import Testing
import Foundation
import SwiftSyntax
import SwiftParser

// MARK: - Snippet Catalog

let statementSnippets: [SwiftSnippet] = [
    SwiftSnippet(
        label: "testIf#1",
        source: """
      if let baz {}
      """,
        origin: "StatementTests.testIf",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testIf#2",
        source: """
      if let self = self {}
      """,
        origin: "StatementTests.testIf",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testIf#3", source: "if let x { }", origin: "StatementTests.testIf", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testIf#4",
        source: """
      if includeSavedHints { a = a.flatMap{ $0 } ?? nil }
      """,
        origin: "StatementTests.testIf",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDo#1",
        source: """
      do {

      }
      """,
        origin: "StatementTests.testDo",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDoCatch#1",
        source: """
      do {

      } catch {

      }
      """,
        origin: "StatementTests.testDoCatch",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDoCatch#2",
        source: """
      do {}
      catch where (error as NSError) == NSError() {}
      """,
        origin: "StatementTests.testDoCatch",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testReturn#1", source: "return actor", origin: "StatementTests.testReturn", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testReturn#2", source: "{ return 0 }", origin: "StatementTests.testReturn", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testReturn#3", source: "return", origin: "StatementTests.testReturn", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testReturn#4",
        source: #"""
      return "assert(\(assertChoices.joined(separator: " || ")))"
      """#,
        origin: "StatementTests.testReturn",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testReturn#5", source: "return true ? nil : nil", origin: "StatementTests.testReturn", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testReturn#6",
        source: """
      switch command {
      case .start:
        break

      case .stop:
        return

      default:
        break
      }
      """,
        origin: "StatementTests.testReturn",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch#1",
        source: """
      switch x {
      case .A, .B:
        break
      }
      """,
        origin: "StatementTests.testSwitch",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch#2",
        source: """
      switch 0 {
      @$dollar case _:
        break
      }
      """,
        origin: "StatementTests.testSwitch",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch#3",
        source: """
      switch x {
      case .A:
        break
      case .B:
        break
      #if NEVER
      #elseif ENABLE_C
      case .C:
        break
      #endif
      }
      """,
        origin: "StatementTests.testSwitch",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testMissingIfClauseIntroducer#1", source: "if _ = 42 {}", origin: "StatementTests.testMissingIfClauseIntroducer", syntaxVersion: "603.0.1", compilerRejects: "use of '=' in a boolean context, did you mean '=='?"),
    SwiftSnippet(
        label: "testIfHasSymbol#1",
        source: """
      if #_hasSymbol(foo) {}
      """,
        origin: "StatementTests.testIfHasSymbol",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testIfHasSymbol#2",
        source: """
      if #_hasSymbol(foo as () -> ()) {}
      """,
        origin: "StatementTests.testIfHasSymbol",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testIdentifierPattern#1", source: "switch x { case let .y(z): break }", origin: "StatementTests.testIdentifierPattern", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testCaseContext#1",
        source: """
      graphQLMap["clientMutationId"] as? Swift.Optional<String?> ?? Swift.Optional<String?>.none
      """,
        origin: "StatementTests.testCaseContext",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testCaseContext#2",
        source: """
      if case Optional<Any>.none = object["anyCol"] { }
      """,
        origin: "StatementTests.testCaseContext",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testHangingYieldArgument#1",
        source: """
      yield
      print("huh")
      """,
        origin: "StatementTests.testHangingYieldArgument",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testYield#1",
        source: """
      var x: Int {
        _read {
          yield &x
        }
      }
      """,
        origin: "StatementTests.testYield",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testYield#2",
        source: """
      @inlinable internal subscript(key: Key) -> Value? {
        @inline(__always) get {
          return lookup(key)
        }
        @inline(__always) _modify {
          guard isNative else {
            let cocoa = asCocoa
            var native = _NativeDictionary<Key, Value>(
              cocoa, capacity: cocoa.count + 1)
            self = .init(native: native)
            yield &native[key, isUnique: true]
            return
          }
          let isUnique = isUniquelyReferenced()
          yield &asNative[key, isUnique: isUnique]
        }
      }
      """,
        origin: "StatementTests.testYield",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testYield#3",
        source: """
      var x: Int {
        _read {
          yield ()
        }
      }
      """,
        origin: "StatementTests.testYield",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testYield#4",
        source: """
      var x: Int {
        get {
          yield ()
        }
      }
      """,
        origin: "StatementTests.testYield",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testYield#5",
        source: """
      yield([])
      """,
        origin: "StatementTests.testYield",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testYield#6",
        source: """
      func f() -> Int {
        yield & 5
      }
      """,
        origin: "StatementTests.testYield",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testYield#7",
        source: """
      func f() -> Int {
        yield&5
      }
      """,
        origin: "StatementTests.testYield",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDiscard#1",
        source: """
      discard self
      """,
        origin: "StatementTests.testDiscard",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDiscard#2",
        source: """
      discard Self
      """,
        origin: "StatementTests.testDiscard",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDiscard#3",
        source: """
      discard SarahMarshall
      """,
        origin: "StatementTests.testDiscard",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDiscard#4",
        source: """
      func discard<T>(_ t: T) {}

      func caller() {
        discard(self)
      }
      """,
        origin: "StatementTests.testDiscard",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testDefaultIdentIdentifierInReturnStmt#1", source: "return FileManager.default", origin: "StatementTests.testDefaultIdentIdentifierInReturnStmt", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testDefaultAsIdentifierInSubscript#1",
        source: """
      data[position, default: 0]
      """,
        origin: "StatementTests.testDefaultAsIdentifierInSubscript",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTrailingTriviaIncludesNewline#1",
        source: """
      let a = 2/*
      */let b = 3
      """,
        origin: "StatementTests.testTrailingTriviaIncludesNewline",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTrailingTriviaIncludesNewline#2",
        source: """
      let a = 2/*



      */let b = 3
      """,
        origin: "StatementTests.testTrailingTriviaIncludesNewline",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testTrailingClosureInIfCondition#1", source: "if test { $0 } {}", origin: "StatementTests.testTrailingClosureInIfCondition", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testTrailingClosureInIfCondition#2",
        source: """
      if test { $0
      } {}
      """,
        origin: "StatementTests.testTrailingClosureInIfCondition",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTrailingClosureInIfCondition#3",
        source: """
      if test { x in
        x
      } {}
      """,
        origin: "StatementTests.testTrailingClosureInIfCondition",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testClosureInsideIfCondition#1", source: "if true, {x}() {}", origin: "StatementTests.testClosureInsideIfCondition", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testClosureInsideIfCondition#2",
        source: """
      if true, {
        x
      }() {}
      """,
        origin: "StatementTests.testClosureInsideIfCondition",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testClosureInsideIfCondition#3",
        source: """
      if true, { x
      }() {}
      """,
        origin: "StatementTests.testClosureInsideIfCondition",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testClosureInsideIfCondition#4",
        source: """
      if true, { a in
        x + a
      }(1) {}
      """,
        origin: "StatementTests.testClosureInsideIfCondition",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypedThrows#1",
        source: """
      do throws(any Error) {
        throw myError
      }
      """,
        origin: "StatementTests.testTypedThrows",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypedThrows#2",
        source: """
      do throws(MyError) {
        throw myError
      }
      """,
        origin: "StatementTests.testTypedThrows",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypedThrows#3",
        source: """
      do throws {
        throw myError
      }
      """,
        origin: "StatementTests.testTypedThrows",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testForUnsafeStatement#1", source: "for try await unsafe x in e { }", origin: "StatementTests.testForUnsafeStatement", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testForUnsafeStatement#2", source: "for try await unsafe in e { }", origin: "StatementTests.testForUnsafeStatement", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testForUnsafeStatement#3", source: "for unsafe in e { }", origin: "StatementTests.testForUnsafeStatement", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testForUnsafeStatement#4", source: "for unsafe: Int in e { }", origin: "StatementTests.testForUnsafeStatement", syntaxVersion: "603.0.1"),
]


// MARK: - Test Suite

extension SwiftSyntax603Tests {

@Suite("Statements")
struct StatementSyntaxTests {

    @Test("SwiftSyntax accepts", .tags(.swiftSyntaxReference), arguments: statementSnippets)
    func swiftSyntaxAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let parsed = Parser.parse(source: snippet.source)
        #expect(!parsed.hasError, "SwiftSyntax parse error for: \(snippet.source)")
    }

    @Test("Advent accepts", arguments: statementSnippets)
    func adventAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let result = try adventParse(snippet)
        #expect(result != nil, "Advent failed to parse: \(snippet.source)")
    }

    @Test("no residual ambiguity", arguments: statementSnippets)
    func unambiguous(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        guard let result = try adventParse(snippet) else {
            Issue.record("Advent failed to parse: \(snippet.source)")
            return
        }
        #expect(result.isUnambiguous,
                "Residual ambiguity in '\(snippet.diagnosticID)': \(result.builder.diagnostics)")
    }

    @Test("trees match", arguments: statementSnippets)
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

let statement604Snippets: [SwiftSnippet] = [
    SwiftSnippet(
        label: "testIf#1",
        source: """
      if let baz {}
      """,
        origin: "StatementTests.testIf",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIf#2",
        source: """
      if let self = self {}
      """,
        origin: "StatementTests.testIf",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testIf#3", source: "if let x { }", origin: "StatementTests.testIf", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testIf#4",
        source: """
      if includeSavedHints { a = a.flatMap{ $0 } ?? nil }
      """,
        origin: "StatementTests.testIf",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDo#1",
        source: """
      do {

      }
      """,
        origin: "StatementTests.testDo",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDoCatch#1",
        source: """
      do {

      } catch {

      }
      """,
        origin: "StatementTests.testDoCatch",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDoCatch#2",
        source: """
      do {}
      catch where (error as NSError) == NSError() {}
      """,
        origin: "StatementTests.testDoCatch",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testReturn#1", source: "return actor", origin: "StatementTests.testReturn", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testReturn#2", source: "{ return 0 }", origin: "StatementTests.testReturn", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testReturn#3", source: "return", origin: "StatementTests.testReturn", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testReturn#4",
        source: #"""
      return "assert(\(assertChoices.joined(separator: " || ")))"
      """#,
        origin: "StatementTests.testReturn",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testReturn#5", source: "return true ? nil : nil", origin: "StatementTests.testReturn", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testReturn#6",
        source: """
      switch command {
      case .start:
        break

      case .stop:
        return

      default:
        break
      }
      """,
        origin: "StatementTests.testReturn",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch#1",
        source: """
      switch x {
      case .A, .B:
        break
      }
      """,
        origin: "StatementTests.testSwitch",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch#2",
        source: """
      switch 0 {
      @$dollar case _:
        break
      }
      """,
        origin: "StatementTests.testSwitch",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch#3",
        source: """
      switch x {
      case .A:
        break
      case .B:
        break
      #if NEVER
      #elseif ENABLE_C
      case .C:
        break
      #endif
      }
      """,
        origin: "StatementTests.testSwitch",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testMissingIfClauseIntroducer#1", source: "if _ = 42 {}", origin: "StatementTests.testMissingIfClauseIntroducer", syntaxVersion: "604.0.0-prerelease-2026-06-05", compilerRejects: "use of '=' in a boolean context, did you mean '=='?"),
    SwiftSnippet(
        label: "testIfHasSymbol#1",
        source: """
      if #_hasSymbol(foo) {}
      """,
        origin: "StatementTests.testIfHasSymbol",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIfHasSymbol#2",
        source: """
      if #_hasSymbol(foo as () -> ()) {}
      """,
        origin: "StatementTests.testIfHasSymbol",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testIdentifierPattern#1", source: "switch x { case let .y(z): break }", origin: "StatementTests.testIdentifierPattern", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testCaseContext#1",
        source: """
      graphQLMap["clientMutationId"] as? Swift.Optional<String?> ?? Swift.Optional<String?>.none
      """,
        origin: "StatementTests.testCaseContext",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testCaseContext#2",
        source: """
      if case Optional<Any>.none = object["anyCol"] { }
      """,
        origin: "StatementTests.testCaseContext",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testHangingYieldArgument#1",
        source: """
      yield
      print("huh")
      """,
        origin: "StatementTests.testHangingYieldArgument",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testYield#1",
        source: """
      var x: Int {
        _read {
          yield &x
        }
      }
      """,
        origin: "StatementTests.testYield",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testYield#2",
        source: """
      @inlinable internal subscript(key: Key) -> Value? {
        @inline(__always) get {
          return lookup(key)
        }
        @inline(__always) _modify {
          guard isNative else {
            let cocoa = asCocoa
            var native = _NativeDictionary<Key, Value>(
              cocoa, capacity: cocoa.count + 1)
            self = .init(native: native)
            yield &native[key, isUnique: true]
            return
          }
          let isUnique = isUniquelyReferenced()
          yield &asNative[key, isUnique: isUnique]
        }
      }
      """,
        origin: "StatementTests.testYield",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testYield#3",
        source: """
      var x: Int {
        _read {
          yield ()
        }
      }
      """,
        origin: "StatementTests.testYield",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testYield#4",
        source: """
      var x: Int {
        get {
          yield ()
        }
      }
      """,
        origin: "StatementTests.testYield",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testYield#5",
        source: """
      yield([])
      """,
        origin: "StatementTests.testYield",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testYield#6",
        source: """
      func f() -> Int {
        yield & 5
      }
      """,
        origin: "StatementTests.testYield",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testYield#7",
        source: """
      func f() -> Int {
        yield&5
      }
      """,
        origin: "StatementTests.testYield",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDiscard#1",
        source: """
      discard self
      """,
        origin: "StatementTests.testDiscard",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDiscard#2",
        source: """
      discard Self
      """,
        origin: "StatementTests.testDiscard",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDiscard#3",
        source: """
      discard SarahMarshall
      """,
        origin: "StatementTests.testDiscard",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDiscard#4",
        source: """
      func discard<T>(_ t: T) {}

      func caller() {
        discard(self)
      }
      """,
        origin: "StatementTests.testDiscard",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testDefaultIdentIdentifierInReturnStmt#1", source: "return FileManager.default", origin: "StatementTests.testDefaultIdentIdentifierInReturnStmt", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testDefaultAsIdentifierInSubscript#1",
        source: """
      data[position, default: 0]
      """,
        origin: "StatementTests.testDefaultAsIdentifierInSubscript",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTrailingTriviaIncludesNewline#1",
        source: """
      let a = 2/*
      */let b = 3
      """,
        origin: "StatementTests.testTrailingTriviaIncludesNewline",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTrailingTriviaIncludesNewline#2",
        source: """
      let a = 2/*



      */let b = 3
      """,
        origin: "StatementTests.testTrailingTriviaIncludesNewline",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testTrailingClosureInIfCondition#1", source: "if test { $0 } {}", origin: "StatementTests.testTrailingClosureInIfCondition", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testTrailingClosureInIfCondition#2",
        source: """
      if test { $0
      } {}
      """,
        origin: "StatementTests.testTrailingClosureInIfCondition",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTrailingClosureInIfCondition#3",
        source: """
      if test { x in
        x
      } {}
      """,
        origin: "StatementTests.testTrailingClosureInIfCondition",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testClosureInsideIfCondition#1", source: "if true, {x}() {}", origin: "StatementTests.testClosureInsideIfCondition", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testClosureInsideIfCondition#2",
        source: """
      if true, {
        x
      }() {}
      """,
        origin: "StatementTests.testClosureInsideIfCondition",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testClosureInsideIfCondition#3",
        source: """
      if true, { x
      }() {}
      """,
        origin: "StatementTests.testClosureInsideIfCondition",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testClosureInsideIfCondition#4",
        source: """
      if true, { a in
        x + a
      }(1) {}
      """,
        origin: "StatementTests.testClosureInsideIfCondition",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypedThrows#1",
        source: """
      do throws(any Error) {
        throw myError
      }
      """,
        origin: "StatementTests.testTypedThrows",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypedThrows#2",
        source: """
      do throws(MyError) {
        throw myError
      }
      """,
        origin: "StatementTests.testTypedThrows",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypedThrows#3",
        source: """
      do throws {
        throw myError
      }
      """,
        origin: "StatementTests.testTypedThrows",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testForUnsafeStatement#1", source: "for try await unsafe x in e { }", origin: "StatementTests.testForUnsafeStatement", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testForUnsafeStatement#2", source: "for try await unsafe in e { }", origin: "StatementTests.testForUnsafeStatement", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testForUnsafeStatement#3", source: "for unsafe in e { }", origin: "StatementTests.testForUnsafeStatement", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testForUnsafeStatement#4", source: "for unsafe: Int in e { }", origin: "StatementTests.testForUnsafeStatement", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
]

extension SwiftSyntax604Tests {

@Suite("Statements")
struct StatementSyntax604Tests {

    @Test("SwiftSyntax accepts", .tags(.swiftSyntaxReference), arguments: statement604Snippets)
    func swiftSyntaxAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        #expect(!swiftSyntaxReferenceHasError(snippet), "SwiftSyntax parse error for: \(snippet.source)")
    }

    @Test("Advent accepts", arguments: statement604Snippets)
    func adventAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let result = try adventParse(snippet)
        #expect(result != nil, "Advent failed to parse: \(snippet.source)")
    }

    @Test("no residual ambiguity", arguments: statement604Snippets)
    func unambiguous(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        guard let result = try adventParse(snippet) else {
            Issue.record("Advent failed to parse: \(snippet.source)")
            return
        }
        #expect(result.isUnambiguous,
                "Residual ambiguity in '\(snippet.diagnosticID)': \(result.builder.diagnostics)")
    }

    @Test("trees match", arguments: statement604Snippets)
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

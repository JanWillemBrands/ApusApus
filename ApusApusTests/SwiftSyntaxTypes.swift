//
//  SwiftSyntaxTypes.swift
//  AdventTests
//
//  Types snippets extracted from SwiftSyntax TypeTests.swift (603.0.1).
//  See SwiftSyntaxTests.swift for shared infrastructure.
//

import Testing
import Foundation
import SwiftSyntax
import SwiftParser

// MARK: - Snippet Catalog

let typeSnippets: [SwiftSnippet] = [
    SwiftSnippet(label: "testClosureParsing#1", source: "let a: (a, b) -> c", origin: "TypeTests.testClosureParsing", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testClosureParsing#2", source: "let a: @MainActor (a, b) async throws -> c", origin: "TypeTests.testClosureParsing", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testClosureParsing#3", source: "() -> (\u{feff})", origin: "TypeTests.testClosureParsing", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testGenericTypeWithTrivia#1",
        source: """
      let a:
              Foo<Bar<
                  V, Baz<Quux>
              >>
      """,
        origin: "TypeTests.testGenericTypeWithTrivia",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testClosureSignatures#1",
        source: """
      simple { [] str in
        print("closure with empty capture list")
      }
      """,
        origin: "TypeTests.testClosureSignatures",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testClosureSignatures#2",
        source: """
      { ()
      throws -> Void in }
      """,
        origin: "TypeTests.testClosureSignatures",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testClosureSignatures#3",
        source: """
      { [weak a, unowned(safe) self, b = 3] (a: Int, b: Int, _: Int) -> Int in }
      """,
        origin: "TypeTests.testClosureSignatures",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOpaqueReturnTypes#1",
        source: """
      public typealias Body = @_opaqueReturnTypeOf("$s6CatKit10pspspspspsV5cmereV6lilguyQrvp", 0) __
      """,
        origin: "TypeTests.testOpaqueReturnTypes",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testVariadics#1",
        source: #"""
      func takesVariadicFnWithGenericRet<T>(_ fn: (S...) -> T) {}
      let _: (S...) -> Int = \.i
      let _: (S...) -> Int = \Array.i
      let _: (S...) -> Int = \S.i
      """#,
        origin: "TypeTests.testVariadics",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testConvention#1",
        source: #"""
      let _: @convention(thin) (@convention(thick) () -> (),
                                @convention(thin) () -> (),
                                @convention(c) () -> (),
                                @convention(c, cType: "intptr_t (*)(size_t)") (Int) -> Int,
                                @convention(block) () -> (),
                                @convention(method) () -> (),
                                @convention(objc_method) () -> (),
                                @convention(witness_method: Bendable) (Fork) -> ()) -> ()
      """#,
        origin: "TypeTests.testConvention",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testNamedOpaqueReturnTypes#1",
        source: """
      func f2() -> <T: SignedInteger, U: SignedInteger> Int {
      }

      dynamic func lazyMapCollection<C: Collection, T>(_ collection: C, body: @escaping (C.Element) -> T)
          -> <R: Collection where R.Element == T> R {
        return collection.lazy.map { body($0) }
      }

      struct Boom<T: P> {
        var prop1: Int = 5
        var prop2: <U, V> (U, V) = ("hello", 5)
      }
      """,
        origin: "TypeTests.testNamedOpaqueReturnTypes",
        syntaxVersion: "603.0.1", compilerRejects: "expected type for function result"
    ),
    SwiftSnippet(label: "testUppercaseSelf#1", source: "let a: Self", origin: "TypeTests.testUppercaseSelf", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testNestedLowercaseSelf#1", source: "let a: Foo.self", origin: "TypeTests.testNestedLowercaseSelf", syntaxVersion: "603.0.1", compilerRejects: "'self' is not a member type of struct 'Foo'"),
    SwiftSnippet(label: "testNestedUppercaseSelf#1", source: "let a: Foo.Self", origin: "TypeTests.testNestedUppercaseSelf", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testInverseTypes#1", source: "[~Copyable]()", origin: "TypeTests.testInverseTypes", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testInverseTypes#2", source: "[any ~Copyable]()", origin: "TypeTests.testInverseTypes", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testInverseTypes#3", source: "[any P & ~Copyable]()", origin: "TypeTests.testInverseTypes", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testInverseTypes#4", source: "[P & ~Copyable]()", origin: "TypeTests.testInverseTypes", syntaxVersion: "603.0.1"),
    // Tilde-position coverage (TODO 1a). `~T` is a type only where `~` lexes as `.prefixOperator`
    // (swift-syntax Types.swift `canParseSimpleType`), i.e. where `~` is NOT left-bound. These five
    // all MATCH swift-syntax already and exist to keep it that way: a `<-<( openAngle )` lookbehind
    // would break the first one, because `<-<` is token-identity and not adjacency-sensitive.
    // The ONE divergent case is `X<~Copyable>()` (testInverseTypes#5), where `<` is munch-exempt.
    SwiftSnippet(label: "probeTildeAngleSpaced#1",  source: "X< ~Copyable>()",   origin: "TODO1a probe", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "probeTildeCommaTight#1",   source: "X<A,~Copyable>()",  origin: "TODO1a probe", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "probeTildeCommaSpaced#1",  source: "X<A, ~Copyable>()", origin: "TODO1a probe", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "probeTildeAmpTight#1",     source: "X<A&~Copyable>()",  origin: "TODO1a probe", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "probeTildeAfterParen#1",   source: "f(~Copyable.self)", origin: "TODO1a probe", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testInverseTypes#5", source: "X<~Copyable>()", origin: "TypeTests.testInverseTypes", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testInverseTypes#6", source: "X<any ~Copyable>()", origin: "TypeTests.testInverseTypes", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testInverseTypes#7", source: "X<P & ~Copyable>()", origin: "TypeTests.testInverseTypes", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testInverseTypes#8", source: "X<any P & ~Copyable>()", origin: "TypeTests.testInverseTypes", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testInverseTypesAsExpr#1", source: "(~Copyable).self", origin: "TypeTests.testInverseTypesAsExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testInverseTypesAsExpr#2", source: "~Copyable.self", origin: "TypeTests.testInverseTypesAsExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testInverseTypesAsExpr#3", source: "(any ~Copyable).self", origin: "TypeTests.testInverseTypesAsExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testInverseTypesInParameter#1", source: "func f(_: borrowing ~Copyable) {}", origin: "TypeTests.testInverseTypesInParameter", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testInverseTypesInParameter#2", source: "func f(_: consuming ~Copyable) {}", origin: "TypeTests.testInverseTypesInParameter", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testInverseTypesInParameter#3", source: "func f(_: borrowing any ~Copyable) {}", origin: "TypeTests.testInverseTypesInParameter", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testInverseTypesInParameter#4", source: "func f(_: consuming any ~Copyable) {}", origin: "TypeTests.testInverseTypesInParameter", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testInverseTypesInParameter#5", source: "func f(_: ~Copyable) {}", origin: "TypeTests.testInverseTypesInParameter", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testInverseTypesInParameter#6", source: "typealias T = (~Copyable) -> Void", origin: "TypeTests.testInverseTypesInParameter", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testInverseTypesInParameter#7", source: "typealias T = (_ x: ~Copyable) -> Void", origin: "TypeTests.testInverseTypesInParameter", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testInverseTypesInParameter#8", source: "typealias T = (borrowing ~Copyable) -> Void", origin: "TypeTests.testInverseTypesInParameter", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testInverseTypesInParameter#9", source: "typealias T = (_ x: borrowing ~Copyable) -> Void", origin: "TypeTests.testInverseTypesInParameter", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testInverseTypesInParameter#10", source: "typealias T = (borrowing any ~Copyable) -> Void", origin: "TypeTests.testInverseTypesInParameter", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testInverseTypesInParameter#11", source: "typealias T = (_ x: borrowing any ~Copyable) -> Void", origin: "TypeTests.testInverseTypesInParameter", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testTypedThrows#1",
        source: """
      { () throws(PosixError) -> Void in }
      """,
        origin: "TypeTests.testTypedThrows",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testTypedThrows#2", source: "typealias T = () throws(PosixError) -> Void", origin: "TypeTests.testTypedThrows", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testTypedThrows#3", source: "[() throws(PosixError) -> Void]()", origin: "TypeTests.testTypedThrows", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testMultipleTypeSpecifiers#1", source: "func foo1(_ a: _const borrowing String) {}", origin: "TypeTests.testMultipleTypeSpecifiers", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testMultipleTypeSpecifiers#2", source: "func foo2(_ a: borrowing _const String) {}", origin: "TypeTests.testMultipleTypeSpecifiers", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testLifetimeSpecifier#1", source: "func foo() -> dependsOn(x) X", origin: "TypeTests.testLifetimeSpecifier", syntaxVersion: "603.0.1", disabledReason: "experimental feature"),
    SwiftSnippet(label: "testLifetimeSpecifier#2", source: "func foo() -> dependsOn(x, y) X", origin: "TypeTests.testLifetimeSpecifier", syntaxVersion: "603.0.1", disabledReason: "experimental feature"),
    SwiftSnippet(label: "testLifetimeSpecifier#3", source: "func foo() -> dependsOn(x) dependsOn(scoped y) X", origin: "TypeTests.testLifetimeSpecifier", syntaxVersion: "603.0.1", disabledReason: "experimental feature"),
    SwiftSnippet(label: "testLifetimeSpecifier#4", source: "func foo() -> dependsOn(scoped x) X", origin: "TypeTests.testLifetimeSpecifier", syntaxVersion: "603.0.1", disabledReason: "experimental feature"),
    SwiftSnippet(label: "testLifetimeSpecifier#5", source: "func foo() -> dependsOn(self) X", origin: "TypeTests.testLifetimeSpecifier", syntaxVersion: "603.0.1", compilerRejects: "consecutive statements on a line must be separated by ';'"),
    SwiftSnippet(
        label: "testNonisolatedSpecifier#1",
        source: """
      let x = nonisolated
      print("hello")
      """,
        origin: "TypeTests.testNonisolatedSpecifier",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testNonisolatedSpecifier#2", source: "let _: nonisolated(nonsending) () async -> Void = {}", origin: "TypeTests.testNonisolatedSpecifier", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testNonisolatedSpecifier#3", source: "let _: [nonisolated(nonsending) () async -> Void]", origin: "TypeTests.testNonisolatedSpecifier", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testNonisolatedSpecifier#4", source: "let _ = [String: (nonisolated(nonsending) () async -> Void)?].self", origin: "TypeTests.testNonisolatedSpecifier", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testNonisolatedSpecifier#5", source: "let _ = Array<nonisolated(nonsending) () async -> Void>()", origin: "TypeTests.testNonisolatedSpecifier", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testNonisolatedSpecifier#6", source: "func foo(test: nonisolated(nonsending) () async -> Void)", origin: "TypeTests.testNonisolatedSpecifier", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testNonisolatedSpecifier#7", source: "func foo(test: nonisolated(nonsending) @escaping () async -> Void) {}", origin: "TypeTests.testNonisolatedSpecifier", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testNonisolatedSpecifier#8", source: "test(S<nonisolated(nonsending) () async -> Void>(), type(of: concurrentTest))", origin: "TypeTests.testNonisolatedSpecifier", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testNonisolatedSpecifier#9", source: "S<nonisolated(nonsending) @Sendable (Int) async -> Void>()", origin: "TypeTests.testNonisolatedSpecifier", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testNonisolatedSpecifier#10", source: "let _ = S<nonisolated(nonsending) consuming @Sendable (Int) async -> Void>()", origin: "TypeTests.testNonisolatedSpecifier", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testNonisolatedSpecifier#11", source: "struct S : nonisolated P {}", origin: "TypeTests.testNonisolatedSpecifier", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testNonisolatedSpecifier#12", source: "let _ = [nonisolated()]", origin: "TypeTests.testNonisolatedSpecifier", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testNonisolatedSpecifier#13", source: "let _ = [nonisolated(nonsending) () async -> Void]()", origin: "TypeTests.testNonisolatedSpecifier", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testNonisolatedSpecifier#14", source: "_ = S<nonisolated>()", origin: "TypeTests.testNonisolatedSpecifier", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testNonisolatedSpecifier#15",
        source: """
      let x: nonisolated
      (hello)
      """,
        origin: "TypeTests.testNonisolatedSpecifier",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testNonisolatedSpecifier#16",
        source: """
      struct S: nonisolated
                  P {
      }
      """,
        origin: "TypeTests.testNonisolatedSpecifier",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testNonisolatedSpecifier#17",
        source: """
      let x: nonisolated
          (Int) async -> Void  = {}
      """,
        origin: "TypeTests.testNonisolatedSpecifier",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTrailingCommas#1",
        source: """
      let foo: (
        bar: String,
        quux: String,
      )
      """,
        origin: "TypeTests.testTrailingCommas",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTrailingCommas#2",
        source: """
      let closure: (
        String,
        String,
      ) -> (
        bar: String,
        quux: String,
      )
      """,
        origin: "TypeTests.testTrailingCommas",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTrailingCommas#3",
        source: """
      struct Foo<T1, T2, T3,> {}

      typealias Bar<
        T1,
        T2,
      > = Foo<
        T1,
        T2,
        Bool,
      >
      """,
        origin: "TypeTests.testTrailingCommas",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testBasic#1", source: "[3 of Int]", origin: "TypeTests.testBasic", syntaxVersion: "603.0.1", compilerRejects: "expected member name or initializer call after type name"),
    SwiftSnippet(label: "testBasic#2", source: "[Int of _]", origin: "TypeTests.testBasic", syntaxVersion: "603.0.1", compilerRejects: "cannot pass type 'Int' as a value for generic value 'count'"),
    SwiftSnippet(
        label: "testMultiline#1",
        source: """
      S<[3 of
             Int]>()
      """,
        origin: "TypeTests.testMultiline",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMultiline#2",
        source: """
      S<[
        3 of Int
      ]>()
      """,
        origin: "TypeTests.testMultiline",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testEllipsis#1", source: "[x...of]", origin: "TypeTests.testEllipsis", syntaxVersion: "603.0.1"),
]


// MARK: - Test Suite

extension SwiftSyntax603Tests {

@Suite("Types")
struct TypeSyntaxTests {

    @Test("SwiftSyntax accepts", .tags(.swiftSyntaxReference), arguments: typeSnippets)
    func swiftSyntaxAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let parsed = Parser.parse(source: snippet.source)
        #expect(!parsed.hasError, "SwiftSyntax parse error for: \(snippet.source)")
    }

    @Test("Advent accepts", arguments: typeSnippets)
    func adventAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let result = try adventParse(snippet)
        #expect(result != nil, "Advent failed to parse: \(snippet.source)")
    }

    @Test("no residual ambiguity", arguments: typeSnippets)
    func unambiguous(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        guard let result = try adventParse(snippet) else {
            Issue.record("Advent failed to parse: \(snippet.source)")
            return
        }
        #expect(result.isUnambiguous,
                "Residual ambiguity in '\(snippet.diagnosticID)': \(result.builder.diagnostics)")
    }

    @Test("trees match", arguments: typeSnippets)
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

let type604Snippets: [SwiftSnippet] = [
    SwiftSnippet(label: "testClosureParsing#1", source: "let a: (a, b) -> c", origin: "TypeTests.testClosureParsing", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testClosureParsing#2", source: "let a: @MainActor (a, b) async throws -> c", origin: "TypeTests.testClosureParsing", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testClosureParsing#3", source: "() -> (\u{feff})", origin: "TypeTests.testClosureParsing", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testGenericTypeWithTrivia#1",
        source: """
      let a:
              Foo<Bar<
                  V, Baz<Quux>
              >>
      """,
        origin: "TypeTests.testGenericTypeWithTrivia",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testClosureSignatures#1",
        source: """
      simple { [] str in
        print("closure with empty capture list")
      }
      """,
        origin: "TypeTests.testClosureSignatures",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testClosureSignatures#2",
        source: """
      { ()
      throws -> Void in }
      """,
        origin: "TypeTests.testClosureSignatures",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testClosureSignatures#3",
        source: """
      { [weak a, unowned(safe) self, b = 3] (a: Int, b: Int, _: Int) -> Int in }
      """,
        origin: "TypeTests.testClosureSignatures",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOpaqueReturnTypes#1",
        source: """
      public typealias Body = @_opaqueReturnTypeOf("$s6CatKit10pspspspspsV5cmereV6lilguyQrvp", 0) __
      """,
        origin: "TypeTests.testOpaqueReturnTypes",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testVariadics#1",
        source: #"""
      func takesVariadicFnWithGenericRet<T>(_ fn: (S...) -> T) {}
      let _: (S...) -> Int = \.i
      let _: (S...) -> Int = \Array.i
      let _: (S...) -> Int = \S.i
      """#,
        origin: "TypeTests.testVariadics",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testConvention#1",
        source: #"""
      let _: @convention(thin) (@convention(thick) () -> (),
                                @convention(thin) () -> (),
                                @convention(c) () -> (),
                                @convention(c, cType: "intptr_t (*)(size_t)") (Int) -> Int,
                                @convention(block) () -> (),
                                @convention(method) () -> (),
                                @convention(objc_method) () -> (),
                                @convention(witness_method: Bendable) (Fork) -> ()) -> ()
      """#,
        origin: "TypeTests.testConvention",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testNamedOpaqueReturnTypes#1",
        source: """
      func f2() -> <T: SignedInteger, U: SignedInteger> Int {
      }

      dynamic func lazyMapCollection<C: Collection, T>(_ collection: C, body: @escaping (C.Element) -> T)
          -> <R: Collection where R.Element == T> R {
        return collection.lazy.map { body($0) }
      }

      struct Boom<T: P> {
        var prop1: Int = 5
        var prop2: <U, V> (U, V) = ("hello", 5)
      }
      """,
        origin: "TypeTests.testNamedOpaqueReturnTypes",
        syntaxVersion: "604.0.0-prerelease-2026-06-05",
        compilerRejects: "expected type for function result"
    ),
    SwiftSnippet(label: "testUppercaseSelf#1", source: "let a: Self", origin: "TypeTests.testUppercaseSelf", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testNestedLowercaseSelf#1", source: "let a: Foo.self", origin: "TypeTests.testNestedLowercaseSelf", syntaxVersion: "604.0.0-prerelease-2026-06-05", compilerRejects: "'self' is not a member type of struct 'Foo'"),
    SwiftSnippet(label: "testNestedUppercaseSelf#1", source: "let a: Foo.Self", origin: "TypeTests.testNestedUppercaseSelf", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testInverseTypes#1", source: "[~Copyable]()", origin: "TypeTests.testInverseTypes", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testInverseTypes#2", source: "[any ~Copyable]()", origin: "TypeTests.testInverseTypes", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testInverseTypes#3", source: "[any P & ~Copyable]()", origin: "TypeTests.testInverseTypes", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testInverseTypes#4", source: "[P & ~Copyable]()", origin: "TypeTests.testInverseTypes", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testInverseTypes#5", source: "X<~Copyable>()", origin: "TypeTests.testInverseTypes", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testInverseTypes#6", source: "X<any ~Copyable>()", origin: "TypeTests.testInverseTypes", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testInverseTypes#7", source: "X<P & ~Copyable>()", origin: "TypeTests.testInverseTypes", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testInverseTypes#8", source: "X<any P & ~Copyable>()", origin: "TypeTests.testInverseTypes", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testInverseTypesAsExpr#1", source: "(~Copyable).self", origin: "TypeTests.testInverseTypesAsExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testInverseTypesAsExpr#2", source: "~Copyable.self", origin: "TypeTests.testInverseTypesAsExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testInverseTypesAsExpr#3", source: "(any ~Copyable).self", origin: "TypeTests.testInverseTypesAsExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testInverseTypesInParameter#1", source: "func f(_: borrowing ~Copyable) {}", origin: "TypeTests.testInverseTypesInParameter", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testInverseTypesInParameter#2", source: "func f(_: consuming ~Copyable) {}", origin: "TypeTests.testInverseTypesInParameter", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testInverseTypesInParameter#3", source: "func f(_: borrowing any ~Copyable) {}", origin: "TypeTests.testInverseTypesInParameter", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testInverseTypesInParameter#4", source: "func f(_: consuming any ~Copyable) {}", origin: "TypeTests.testInverseTypesInParameter", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testInverseTypesInParameter#5", source: "func f(_: ~Copyable) {}", origin: "TypeTests.testInverseTypesInParameter", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testInverseTypesInParameter#6", source: "typealias T = (~Copyable) -> Void", origin: "TypeTests.testInverseTypesInParameter", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testInverseTypesInParameter#7", source: "typealias T = (_ x: ~Copyable) -> Void", origin: "TypeTests.testInverseTypesInParameter", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testInverseTypesInParameter#8", source: "typealias T = (borrowing ~Copyable) -> Void", origin: "TypeTests.testInverseTypesInParameter", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testInverseTypesInParameter#9", source: "typealias T = (_ x: borrowing ~Copyable) -> Void", origin: "TypeTests.testInverseTypesInParameter", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testInverseTypesInParameter#10", source: "typealias T = (borrowing any ~Copyable) -> Void", origin: "TypeTests.testInverseTypesInParameter", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testInverseTypesInParameter#11", source: "typealias T = (_ x: borrowing any ~Copyable) -> Void", origin: "TypeTests.testInverseTypesInParameter", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testTypedThrows#1",
        source: """
      { () throws(PosixError) -> Void in }
      """,
        origin: "TypeTests.testTypedThrows",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testTypedThrows#2", source: "typealias T = () throws(PosixError) -> Void", origin: "TypeTests.testTypedThrows", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testTypedThrows#3", source: "[() throws(PosixError) -> Void]()", origin: "TypeTests.testTypedThrows", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testMultipleTypeSpecifiers#1", source: "func foo1(_ a: _const borrowing String) {}", origin: "TypeTests.testMultipleTypeSpecifiers", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testMultipleTypeSpecifiers#2", source: "func foo2(_ a: borrowing _const String) {}", origin: "TypeTests.testMultipleTypeSpecifiers", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testLifetimeSpecifier#1", source: "func foo() -> dependsOn(x) X", origin: "TypeTests.testLifetimeSpecifier", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testLifetimeSpecifier#2", source: "func foo() -> dependsOn(x, y) X", origin: "TypeTests.testLifetimeSpecifier", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testLifetimeSpecifier#3", source: "func foo() -> dependsOn(x) dependsOn(scoped y) X", origin: "TypeTests.testLifetimeSpecifier", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testLifetimeSpecifier#4", source: "func foo() -> dependsOn(scoped x) X", origin: "TypeTests.testLifetimeSpecifier", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testLifetimeSpecifier#5", source: "func foo() -> dependsOn(self) X", origin: "TypeTests.testLifetimeSpecifier", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testNonisolatedSpecifier#1",
        source: """
      let x = nonisolated
      print("hello")
      """,
        origin: "TypeTests.testNonisolatedSpecifier",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testNonisolatedSpecifier#2", source: "let _: nonisolated(nonsending) () async -> Void = {}", origin: "TypeTests.testNonisolatedSpecifier", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testNonisolatedSpecifier#3", source: "let _: [nonisolated(nonsending) () async -> Void]", origin: "TypeTests.testNonisolatedSpecifier", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testNonisolatedSpecifier#4", source: "let _ = [String: (nonisolated(nonsending) () async -> Void)?].self", origin: "TypeTests.testNonisolatedSpecifier", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testNonisolatedSpecifier#5", source: "let _ = Array<nonisolated(nonsending) () async -> Void>()", origin: "TypeTests.testNonisolatedSpecifier", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testNonisolatedSpecifier#6", source: "func foo(test: nonisolated(nonsending) () async -> Void)", origin: "TypeTests.testNonisolatedSpecifier", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testNonisolatedSpecifier#7", source: "func foo(test: nonisolated(nonsending) @escaping () async -> Void) {}", origin: "TypeTests.testNonisolatedSpecifier", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testNonisolatedSpecifier#8", source: "test(S<nonisolated(nonsending) () async -> Void>(), type(of: concurrentTest))", origin: "TypeTests.testNonisolatedSpecifier", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testNonisolatedSpecifier#9", source: "S<nonisolated(nonsending) @Sendable (Int) async -> Void>()", origin: "TypeTests.testNonisolatedSpecifier", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testNonisolatedSpecifier#10", source: "let _ = S<nonisolated(nonsending) consuming @Sendable (Int) async -> Void>()", origin: "TypeTests.testNonisolatedSpecifier", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testNonisolatedSpecifier#11", source: "struct S : nonisolated P {}", origin: "TypeTests.testNonisolatedSpecifier", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testNonisolatedSpecifier#12", source: "let _ = [nonisolated()]", origin: "TypeTests.testNonisolatedSpecifier", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testNonisolatedSpecifier#13", source: "let _ = [nonisolated(nonsending) () async -> Void]()", origin: "TypeTests.testNonisolatedSpecifier", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testNonisolatedSpecifier#14", source: "_ = S<nonisolated>()", origin: "TypeTests.testNonisolatedSpecifier", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testNonisolatedSpecifier#15",
        source: """
      let x: nonisolated
      (hello)
      """,
        origin: "TypeTests.testNonisolatedSpecifier",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testNonisolatedSpecifier#16",
        source: """
      struct S: nonisolated
                  P {
      }
      """,
        origin: "TypeTests.testNonisolatedSpecifier",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testNonisolatedSpecifier#17",
        source: """
      let x: nonisolated
          (Int) async -> Void  = {}
      """,
        origin: "TypeTests.testNonisolatedSpecifier",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTrailingCommas#1",
        source: """
      let foo: (
        bar: String,
        quux: String,
      )
      """,
        origin: "TypeTests.testTrailingCommas",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTrailingCommas#2",
        source: """
      let closure: (
        String,
        String,
      ) -> (
        bar: String,
        quux: String,
      )
      """,
        origin: "TypeTests.testTrailingCommas",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTrailingCommas#3",
        source: """
      struct Foo<T1, T2, T3,> {}

      typealias Bar<
        T1,
        T2,
      > = Foo<
        T1,
        T2,
        Bool,
      >
      """,
        origin: "TypeTests.testTrailingCommas",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testBasic#1", source: "[3 of Int]", origin: "TypeTests.testBasic", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testBasic#2", source: "[Int of _]", origin: "TypeTests.testBasic", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testMultiline#1",
        source: """
      S<[3 of
             Int]>()
      """,
        origin: "TypeTests.testMultiline",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMultiline#2",
        source: """
      S<[
        3 of Int
      ]>()
      """,
        origin: "TypeTests.testMultiline",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testEllipsis#1", source: "[x...of]", origin: "TypeTests.testEllipsis", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testExpressionCount#1", source: "InlineArray<(1 + 3), Int>()", origin: "TypeTests.testExpressionCount", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testSugaredExpressionCount#1", source: "[(2 + 3) of Int]", origin: "TypeTests.testSugaredExpressionCount", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testNestedExpressionCount#1", source: "[(1 + 1) of [(2 + 1) of Int]]", origin: "TypeTests.testNestedExpressionCount", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
]

extension SwiftSyntax604Tests {

@Suite("Types")
struct TypeSyntax604Tests {

    @Test("SwiftSyntax accepts", .tags(.swiftSyntaxReference), arguments: type604Snippets)
    func swiftSyntaxAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        #expect(!swiftSyntaxReferenceHasError(snippet), "SwiftSyntax parse error for: \(snippet.source)")
    }

    @Test("Advent accepts", arguments: type604Snippets)
    func adventAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let result = try adventParse(snippet)
        #expect(result != nil, "Advent failed to parse: \(snippet.source)")
    }

    @Test("no residual ambiguity", arguments: type604Snippets)
    func unambiguous(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        guard let result = try adventParse(snippet) else {
            Issue.record("Advent failed to parse: \(snippet.source)")
            return
        }
        #expect(result.isUnambiguous,
                "Residual ambiguity in '\(snippet.diagnosticID)': \(result.builder.diagnostics)")
    }

    @Test("trees match", arguments: type604Snippets)
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

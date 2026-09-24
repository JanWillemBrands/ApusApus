//
//  SwiftSyntaxDeclarations.swift
//  AdventTests
//
//  Declaration snippets extracted from SwiftSyntax DeclarationTests.swift (603.0.1).
//  See SwiftSyntaxTests.swift for shared infrastructure.
//

import Testing
import Foundation
import SwiftSyntax
import SwiftParser

// MARK: - Snippet Catalog

let declarationSnippets: [SwiftSnippet] = [
    SwiftSnippet(label: "testImports#1", source: "import Foundation", origin: "DeclarationTests.testImports", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testImports#2", source: "@_spi(Private) import SwiftUI", origin: "DeclarationTests.testImports", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testImports#3", source: "@_exported import class Foundation.Thread", origin: "DeclarationTests.testImports", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testImports#4", source: #"@_private(sourceFile: "YetAnotherFile.swift") import Foundation"#, origin: "DeclarationTests.testImports", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testStructParsing#1", source: "struct Foo {}", origin: "DeclarationTests.testStructParsing", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testFuncParsing#1", source: "func foo() {}", origin: "DeclarationTests.testFuncParsing", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testFuncParsing#2", source: "func foo() -> Slice<MinimalMutableCollection<T>> {}", origin: "DeclarationTests.testFuncParsing", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testFuncParsing#3",
        source: """
      func onEscapingAutoclosure(_ fn: @Sendable @autoclosure @escaping () -> Int) { }
      func onEscapingAutoclosure2(_ fn: @escaping @autoclosure @Sendable () -> Int) { }
      func bar(_ : String) async -> [[String]: Array<String>] {}
      func tupleMembersFunc() -> (Type.Inner, Type2.Inner2) {}
      func myFun<S: T & U>(var1: S) {
        // do stuff
      }
      """,
        origin: "DeclarationTests.testFuncParsing",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testFuncParsing#4", source: "func /^/ (lhs: Int, rhs: Int) -> Int { 1 / 2 }", origin: "DeclarationTests.testFuncParsing", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testFuncParsing#5", source: "func /^ (lhs: Int, rhs: Int) -> Int { 1 / 2 }", origin: "DeclarationTests.testFuncParsing", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testFuncParsing#6",
        source: """
      func name(_ default: Int) {}
      """,
        origin: "DeclarationTests.testFuncParsing",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testClassParsing#1", source: "class Foo {}", origin: "DeclarationTests.testClassParsing", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testClassParsing#2",
        source: """
      @dynamicMemberLookup @available(swift 4.0)
      public class MyClass {
        let A: Int
        let B: Double
      }
      """,
        origin: "DeclarationTests.testClassParsing",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testClassParsing#3", source: "struct A<@NSApplicationMain T: AnyObject> {}", origin: "DeclarationTests.testClassParsing", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testActorParsing#1", source: "actor Foo {}", origin: "DeclarationTests.testActorParsing", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testActorParsing#2",
        source: """
      actor Foo {
        nonisolated init?() {
          for (x, y, z) in self.triples {
            precondition(isSafe)
          }
        }
        subscript(_ param: String) -> Int {
          return 42
        }
      }
      """,
        origin: "DeclarationTests.testActorParsing",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testProtocolParsing#1", source: "protocol Foo {}", origin: "DeclarationTests.testProtocolParsing", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testProtocolParsing#2", source: "protocol P { init() }", origin: "DeclarationTests.testProtocolParsing", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testProtocolParsing#3",
        source: """
      protocol P {
        associatedtype Foo: Bar where X.Y == Z.W.W.Self

        var foo: Bool { get set }
        subscript<R>(index: Int) -> R
      }
      """,
        origin: "DeclarationTests.testProtocolParsing",
        syntaxVersion: "603.0.1", compilerRejects: "subscript in protocol must have explicit { get } or { get set } specif"
    ),
    SwiftSnippet(
        label: "testVariableDeclarations#1",
        source: """
      z

      var x: Double = z
      """,
        origin: "DeclarationTests.testVariableDeclarations",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testVariableDeclarations#2",
        source: """
      async let a = fetch("1.jpg")
      async let b: Image = fetch("2.jpg")
      async let secondPhotoToFetch = fetch("3.jpg")
      async let theVeryLastPhotoWeWant = fetch("4.jpg")
      """,
        origin: "DeclarationTests.testVariableDeclarations",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testVariableDeclarations#3", source: "private unowned(unsafe) var foo: Int", origin: "DeclarationTests.testVariableDeclarations", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testVariableDeclarations#4", source: "unowned(unsafe) let unmanagedVar: Class = c", origin: "DeclarationTests.testVariableDeclarations", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testVariableDeclarations#5", source: "_ = foo?.description", origin: "DeclarationTests.testVariableDeclarations", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testVariableDeclarations#6", source: "var a = Array<Int>?(from: decoder)", origin: "DeclarationTests.testVariableDeclarations", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testVariableDeclarations#7", source: "@Wrapper var café = 42", origin: "DeclarationTests.testVariableDeclarations", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testVariableDeclarations#8",
        source: """
      var x: T {
        get async {
          foo()
          bar()
        }
      }
      """,
        origin: "DeclarationTests.testVariableDeclarations",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testVariableDeclarations#9",
        source: """
      var foo: Int {
        _read {
          yield 1234567890
        }
        _modify {
          var someLongVariable = 0
          yield &someLongVariable
        }
      }
      """,
        origin: "DeclarationTests.testVariableDeclarations",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testVariableDeclarations#10",
        source: """
      var foo: Int {
        @available(swift 5.0)
        func myFun() -> Int {
          return 42
        }
        return myFun()
      }
      """,
        origin: "DeclarationTests.testVariableDeclarations",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testVariableDeclarations#11",
        source: """
      var foo: Int {
        mutating set {
          test += 1
        }
      }
      """,
        origin: "DeclarationTests.testVariableDeclarations",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testTypealias#1", source: "typealias Foo = Int", origin: "DeclarationTests.testTypealias", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testTypealias#2", source: "typealias MyAlias = (_ a: Int, _ b: Double, _ c: Bool, _ d: String) -> Bool", origin: "DeclarationTests.testTypealias", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testTypealias#3", source: "typealias A = @attr1 @attr2(hello) (Int) -> Void", origin: "DeclarationTests.testTypealias", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testPrecedenceGroup#1",
        source: """
      precedencegroup FooGroup {
        higherThan: Group1, Group2
        lowerThan: Group3, Group4
        associativity: left
        assignment: false
      }
      """,
        origin: "DeclarationTests.testPrecedenceGroup",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testPrecedenceGroup#2",
        source: """
      precedencegroup FunnyPrecedence {
       associativity: left
       higherThan: MultiplicationPrecedence
      }
      """,
        origin: "DeclarationTests.testPrecedenceGroup",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testOperators#1", source: "infix operator *-* : FunnyPrecedence", origin: "DeclarationTests.testOperators", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testOperators#2",
        source: """
      infix operator  <*<<< : MediumPrecedence, &
      prefix operator ^^ : PrefixMagicOperatorProtocol
      infix operator  <*< : MediumPrecedence, InfixMagicOperatorProtocol
      postfix operator ^^ : PostfixMagicOperatorProtocol
      infix operator ^^ : PostfixMagicOperatorProtocol, Class, Struct
      """,
        origin: "DeclarationTests.testOperators",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testObjCAttribute#1",
        source: """
      @objc(
        thisMethodHasAVeryLongName:
        foo:
        bar:
      )
      func f() {}
      """,
        origin: "DeclarationTests.testObjCAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDifferentiableAttribute#1",
        source: """
      @differentiable(wrt: x where T: D)
      func foo<T>(_ x: T) -> T {}

      @differentiable(wrt: x where T: Differentiable)
      func foo<T>(_ x: T) -> T {}

      @differentiable(wrt: theVariableNamedX where T: Differentiable)
      func foo<T>(_ theVariableNamedX: T) -> T {}

      @differentiable(wrt: (x, y))
      func foo<T>(_ x: T) -> T {}
      """,
        origin: "DeclarationTests.testDifferentiableAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testParsePoundError#1", source: #"#error("Unsupported platform")"#, origin: "DeclarationTests.testParsePoundError", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testParsePoundWarning#1", source: #"#warning("Unsupported platform")"#, origin: "DeclarationTests.testParsePoundWarning", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testParseSpecializeAttribute#1",
        source: #"""
      @_specialize(where T == Int, U == Float)
      mutating func exchangeSecond<U>(_ u: U, _ t: T) -> (U, T) {
        x = t
        return (u, x)
      }

      @_specialize(exported: true, kind: full, where K == Int, V == Int)
      @_specialize(exported: false, kind: partial, where K: _Trivial64)
      func dictFunction<K, V>(dict: Dictionary<K, V>) {
      }

      @_specialize(where T == Int)
      public func play() {
        for _ in 0...100_000_000 { t = t.ping() }
      }

      @_specialize(exported: true,
                   spi: SwiftSpecialization,
                   target: copy(),
                   where Key == AnyHashable, Value == Any)
      @_specialize(exported: true,
                   spi: SwiftSpecialization,
                   target: copy(),
                   where Key == AnyHashable, Value == String)
      @_specialize(exported: true,
                   spi: SwiftSpecialization,
                   target: copy(),
                   where Key == String, Value == Any)
      @_specialize(exported: true,
                   spi: SwiftSpecialization,
                   target: copy(),
                   where Key == String, Value == AnyHashable)
      @_specialize(exported: true,
                   spi: SwiftSpecialization,
                   target: copy(),
                   where Key == String, Value == String)
      @available(SwiftStdlib 5.5, *)
      @usableFromInline
      mutating func __specialize_copy() { Builtin.unreachable() }

      @_specializeExtension
      extension Sequence {
        @_specialize(exported: true,
                     spi: SwiftSpecialization,
                     target: _copyContents(initializing:),
                     where Self == [String])
        @_specialize(exported: true,
                     spi: SwiftSpecialization,
                     target: _copyContents(initializing:),
                     where Self == Set<String>)
        @available(SwiftStdlib 5.5, *)
        @usableFromInline
        __consuming func __specialize__copyContents(initializing: Swift.UnsafeMutableBufferPointer<Element>)  -> (Iterator, Int) { Builtin.unreachable() }
      }
      """#,
        origin: "DeclarationTests.testParseSpecializeAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testParseSpecializeAttribute#2",
        source: """
      @_specialize(where T: _Trivial(32), T: _Trivial(64), T: _Trivial, T: _RefCountedObject)
      @_specialize(where T: _Trivial, T: _Trivial(64))
      @_specialize(where T: _RefCountedObject, T: _NativeRefCountedObject)
      @_specialize(where Array<T> == Int)
      @_specialize(where T.Element == Int)
      public func funcWithComplexSpecializeRequirements<T: ProtocolWithDep>(t: T) -> Int {
        return 55555
      }
      """,
        origin: "DeclarationTests.testParseSpecializeAttribute",
        syntaxVersion: "603.0.1", compilerRejects: "SIL layout constraint (_Trivial(32)) not modelled"
    ),
    SwiftSnippet(
        label: "testParseSpecializeAttribute#3",
        source: """
      @specialized(where Array<T> == Int)
      @specialized(where T.Element == Int)
      public func funcWithComplexSpecializeRequirements<T: ProtocolWithDep>(t: T) -> Int {
        return 55555
      }
      """,
        origin: "DeclarationTests.testParseSpecializeAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testParseRetroactiveExtension#1",
        source: """
      extension Int: @retroactive Identifiable {}
      """,
        origin: "DeclarationTests.testParseRetroactiveExtension",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testParsePreconcurrency#1",
        source: """
      struct MyValue: @preconcurrency P {}
      """,
        origin: "DeclarationTests.testParsePreconcurrency",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testParsePreconcurrency#2",
        source: """
      extension MyValue: @preconcurrency P {}
      """,
        origin: "DeclarationTests.testParsePreconcurrency",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testParseIsolatedConformances#1",
        source: """
      extension Int: nonisolated Q {}
      """,
        origin: "DeclarationTests.testParseIsolatedConformances",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testParseIsolatedConformances#2",
        source: """
      extension Int: @MainActor P {}
      """,
        origin: "DeclarationTests.testParseIsolatedConformances",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testParseIsolatedConformances#3",
        source: """
      extension Int: @preconcurrency nonisolated Q {}
      """,
        origin: "DeclarationTests.testParseIsolatedConformances",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testParseIsolatedConformances#4",
        source: """
      extension Int: @unsafe nonisolated Q {}
      """,
        origin: "DeclarationTests.testParseIsolatedConformances",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testParseDynamicReplacement#1",
        source: """
      @_dynamicReplacement(for: dynamic_replaceable())
      func replacement() {
        dynamic_replaceable()
      }
      """,
        origin: "DeclarationTests.testParseDynamicReplacement",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testParseDynamicReplacement#2",
        source: """
      @_dynamicReplacement(for: subscript(_:))
      subscript(x y: Int) -> Int {
        get {
          return self[y]
        }
        set {
          self[y] = newValue
        }
      }
      """,
        origin: "DeclarationTests.testParseDynamicReplacement",
        syntaxVersion: "603.0.1",
        compilerRejects: "'subscript' functions may only be declared within a type"
    ),
    SwiftSnippet(
        label: "testParseDynamicReplacement#3",
        source: """
      @_dynamicReplacement(for: dynamic_replaceable_var)
      var r : Int {
        return 0
      }
      """,
        origin: "DeclarationTests.testParseDynamicReplacement",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testParseDynamicReplacement#4",
        source: """
      @_dynamicReplacement(for: init(x:))
      init(y: Int) {
        self.init(x: y + 1)
      }
      """,
        origin: "DeclarationTests.testParseDynamicReplacement",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnumParsing#1",
        source: """
      enum Foo {
        @preconcurrency case custom(@Sendable () throws -> Void)
      }
      """,
        origin: "DeclarationTests.testEnumParsing",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnumParsing#2",
        source: """
      enum Content {
        case keyPath(KeyPath<FocusedValues, Value?>)
        case keyPath(KeyPath<FocusedValues, Binding<Value>?>)
        case value(Value?)
      }
      """,
        origin: "DeclarationTests.testEnumParsing",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testTypedThrows#1", source: "func test() throws(any Error) -> Int { }", origin: "DeclarationTests.testTypedThrows", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testTypedThrows#2",
        source: """
      struct X {
        init() throws(any Error) { }
      }
      """,
        origin: "DeclarationTests.testTypedThrows",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testTypedThrows#3", source: "func test() throws(MyError) {}", origin: "DeclarationTests.testTypedThrows", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testTypedThrows#4",
        source: """
      struct S<Element, Failure: Error> {
        init(produce: @escaping () async throws(Failure) -> Element?) {
        }
      }
      """,
        origin: "DeclarationTests.testTypedThrows",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAccessors#1",
        source: """
      var bad1 : Int {
        _read async { 0 }
      }
      """,
        origin: "DeclarationTests.testAccessors",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAccessors#2",
        source: """
      public var foo: Swift.Int {
        get
        @inlinable set {}
      }
      """,
        origin: "DeclarationTests.testAccessors",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInitAccessor#1",
        source: """
      struct S {
        var value: Int {
          init {}
          get {}
          set {}
        }
      }
      """,
        origin: "DeclarationTests.testInitAccessor",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInitAccessor#2",
        source: """
      struct S {
        let _value: Int

        init() {
        }
      }
      """,
        origin: "DeclarationTests.testInitAccessor",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInitAccessor#3",
        source: """
      struct S {
        var value: Int {
          init(newValue) {}
          get {}
          set(newValue) {}
        }
      }
      """,
        origin: "DeclarationTests.testInitAccessor",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInitAccessor#4",
        source: """
      struct S {
        var value: Int {
          init(newValue) {}
          get {}
          set(newValue) {}
        }
      }
      """,
        origin: "DeclarationTests.testInitAccessor",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInitializers#1",
        source: """
      struct S0 {
        init!(int: Int) { }
        init! (uint: UInt) { }
        init !(float: Float) { }

        init?(string: String) { }
        init ?(double: Double) { }
        init ? (char: Character) { }
      }
      """,
        origin: "DeclarationTests.testInitializers",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testDeinitializers#1", source: "deinit {}", origin: "DeclarationTests.testDeinitializers", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testDeinitializers#2", source: "deinit", origin: "DeclarationTests.testDeinitializers", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testAttributedMember#1",
        source: #"""
      struct Foo {
        @Argument(help: "xxx")
        var generatedPath: String
      }
      """#,
        origin: "DeclarationTests.testAttributedMember",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testAnyAsParameterLabel#1", source: "func at(any kinds: [RawTokenKind]) {}", origin: "DeclarationTests.testAnyAsParameterLabel", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testPublicClass#1", source: "public class Foo: Superclass {}", origin: "DeclarationTests.testPublicClass", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testReturnVariableNamedAsync#1",
        source: ##"""
      if let async = self.consume(if: .keyword(.async)) {
        return async
      }

      if let reasync = self.consume(if: .keyword(.reasync)) {
        return reasync
      }
      """##,
        origin: "DeclarationTests.testReturnVariableNamedAsync",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testModifiedParameter#1",
        source: """
      func const(_const _ map: String) {}
      """,
        origin: "DeclarationTests.testModifiedParameter",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testModifiedParameter#2",
        source: """
      func isolated(isolated _ map: String) {}
      """,
        origin: "DeclarationTests.testModifiedParameter",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testModifiedParameter#3",
        source: """
      func isolatedConst(isolated _const _ map: String) {}
      """,
        origin: "DeclarationTests.testModifiedParameter",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testModifiedParameter#4",
        source: """
      func nonEphemeralIsolatedConst(@_nonEmphemeral isolated _const _ map: String) {}
      """,
        origin: "DeclarationTests.testModifiedParameter",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testModifiedParameter#5",
        source: """
      func const(_const map: String) {}
      """,
        origin: "DeclarationTests.testModifiedParameter",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testModifiedParameter#6",
        source: """
      func isolated(isolated map: String) {}
      """,
        origin: "DeclarationTests.testModifiedParameter",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testModifiedParameter#7",
        source: """
      func isolatedConst(isolated _const map: String) {}
      """,
        origin: "DeclarationTests.testModifiedParameter",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testModifiedParameter#8",
        source: """
      func const(_const x: String) {}
      func isolated(isolated: String) {}
      func isolatedConst(isolated _const: String) {}
      """,
        origin: "DeclarationTests.testModifiedParameter",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testReasyncFunctions#1",
        source: """
      class MyType {
        init(_ f: () async -> Void) reasync {
          await f()
        }

        func foo(index: Int) reasync rethrows -> String {
          await f()
        }
      }
      """,
        origin: "DeclarationTests.testReasyncFunctions",
        syntaxVersion: "603.0.1",
        compilerRejects: "consecutive declarations on a line must be separated by ';'"
    ),
    SwiftSnippet(
        label: "testMacroExpansionDeclaration#1",
        source: """
      struct X {
        #memberwiseInit(access: .public)
      }
      """,
        origin: "DeclarationTests.testMacroExpansionDeclaration",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMacroExpansionDeclaration#2",
        source: """
      #expand
      """,
        origin: "DeclarationTests.testMacroExpansionDeclaration",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMacroExpansionDeclarationWithKeywordName#1",
        source: """
      struct X {
        #case
      }
      """,
        origin: "DeclarationTests.testMacroExpansionDeclarationWithKeywordName",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAttributedMacroExpansionDeclaration#1",
        source: """
      @attribute #topLevelWithAttr
      """,
        origin: "DeclarationTests.testAttributedMacroExpansionDeclaration",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAttributedMacroExpansionDeclaration#2",
        source: """
      public #topLevelWithModifier
      """,
        origin: "DeclarationTests.testAttributedMacroExpansionDeclaration",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAttributedMacroExpansionDeclaration#3",
        source: """
      #topLevelBare
      """,
        origin: "DeclarationTests.testAttributedMacroExpansionDeclaration",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAttributedMacroExpansionDeclaration#4",
        source: """
      struct S {
        @attribute #memberWithAttr
      }
      """,
        origin: "DeclarationTests.testAttributedMacroExpansionDeclaration",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAttributedMacroExpansionDeclaration#5",
        source: """
      struct S {
        public #memberWithModifier
      }
      """,
        origin: "DeclarationTests.testAttributedMacroExpansionDeclaration",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAttributedMacroExpansionDeclaration#6",
        source: """
      struct S {
        #memberBare
      }
      """,
        origin: "DeclarationTests.testAttributedMacroExpansionDeclaration",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAttributedMacroExpansionDeclaration#7",
        source: """
      func test() {
        @attribute #bodyWithAttr
      }
      """,
        origin: "DeclarationTests.testAttributedMacroExpansionDeclaration",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAttributedMacroExpansionDeclaration#8",
        source: """
      func test() {
        public #bodyWithModifier
      }
      """,
        origin: "DeclarationTests.testAttributedMacroExpansionDeclaration",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAttributedMacroExpansionDeclaration#9",
        source: """
      func test() {
        #bodyBare
      }
      """,
        origin: "DeclarationTests.testAttributedMacroExpansionDeclaration",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAttributedMacroExpansionDeclaration#10",
        source: """
      func test() {
        @attrib1
        @attrib2
        public
        #declMacro
      }
      """,
        origin: "DeclarationTests.testAttributedMacroExpansionDeclaration",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAttributedMacroExpansionDeclaration#11",
        source: """
      struct S {
        @attrib #class
      }
      """,
        origin: "DeclarationTests.testAttributedMacroExpansionDeclaration",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAttributedMacroExpansionDeclaration#12",
        source: """
      struct S {
        #struct
      }
      """,
        origin: "DeclarationTests.testAttributedMacroExpansionDeclaration",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testVariableGetSetNextLine#1",
        source: """
      struct X {
        var x: Int
        { 17 }
      }
      """,
        origin: "DeclarationTests.testVariableGetSetNextLine",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testVariableFollowedByReferenceToSet#1",
        source: """
      func bar() {
          let a = b
          set.c
      }
      """,
        origin: "DeclarationTests.testVariableFollowedByReferenceToSet",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testIssue1025#1",
        source: """
      struct Math {
        public static let pi = 3.14
        @available(*, unavailable) init() {}
      }
      """,
        origin: "DeclarationTests.testIssue1025",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testIssue1025#2", source: "func foo(body: (isolated String) -> Int) {}", origin: "DeclarationTests.testIssue1025", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testClassWithPrivateSet#1",
        source: """
      struct Properties {
        class private(set) var privateSetterCustomNames: Bool
      }
      """,
        origin: "DeclarationTests.testClassWithPrivateSet",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAttributeInPoundIf#1",
        source: """
      #if hasAttribute(foo)
      @foo
      #endif
      struct MyStruct {}
      """,
        origin: "DeclarationTests.testAttributeInPoundIf",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testCallToOpenThatLooksLikeDeclarationModifier#1",
        source: """
      func test() {
        open(set)
        var foo = 2
      }
      """,
        origin: "DeclarationTests.testCallToOpenThatLooksLikeDeclarationModifier",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testReferenceToOpenThatLooksLikeDeclarationModifier#1",
        source: """
      func test() {
        open
        var foo = 2
      }
      """,
        origin: "DeclarationTests.testReferenceToOpenThatLooksLikeDeclarationModifier",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOpenVarInCodeBlockItemList#1",
        source: """
      func test() {
        open var foo = 2
      }
      """,
        origin: "DeclarationTests.testOpenVarInCodeBlockItemList",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAsyncLetInLocalContext#1",
        source: """
      func foo() async {
        async let x: String = "x"
      }
      """,
        origin: "DeclarationTests.testAsyncLetInLocalContext",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testBorrowingConsumingParameterSpecifiers#1", source: "struct borrowing {}", origin: "DeclarationTests.testBorrowingConsumingParameterSpecifiers", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testBorrowingConsumingParameterSpecifiers#2", source: "struct consuming {}", origin: "DeclarationTests.testBorrowingConsumingParameterSpecifiers", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testBorrowingConsumingParameterSpecifiers#3", source: "struct Foo {}", origin: "DeclarationTests.testBorrowingConsumingParameterSpecifiers", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testBorrowingConsumingParameterSpecifiers#4", source: "func foo(x: borrowing Foo) {}", origin: "DeclarationTests.testBorrowingConsumingParameterSpecifiers", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testBorrowingConsumingParameterSpecifiers#5", source: "func bar(x: consuming Foo) {}", origin: "DeclarationTests.testBorrowingConsumingParameterSpecifiers", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testBorrowingConsumingParameterSpecifiers#6", source: "func baz(x: (borrowing Foo, consuming Foo) -> ()) {}", origin: "DeclarationTests.testBorrowingConsumingParameterSpecifiers", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testBorrowingConsumingParameterSpecifiers#7", source: "func zim(x: borrowing) {}", origin: "DeclarationTests.testBorrowingConsumingParameterSpecifiers", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testBorrowingConsumingParameterSpecifiers#8", source: "func zang(x: consuming) {}", origin: "DeclarationTests.testBorrowingConsumingParameterSpecifiers", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testBorrowingConsumingParameterSpecifiers#9", source: "func zung(x: borrowing consuming) {}", origin: "DeclarationTests.testBorrowingConsumingParameterSpecifiers", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testBorrowingConsumingParameterSpecifiers#10", source: "func zip(x: consuming borrowing) {}", origin: "DeclarationTests.testBorrowingConsumingParameterSpecifiers", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testBorrowingConsumingParameterSpecifiers#11", source: "func zap(x: (borrowing, consuming) -> ()) {}", origin: "DeclarationTests.testBorrowingConsumingParameterSpecifiers", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testBorrowingConsumingParameterSpecifiers#12", source: "func zoop(x: (borrowing consuming, consuming borrowing) -> ()) {}", origin: "DeclarationTests.testBorrowingConsumingParameterSpecifiers", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testBorrowingConsumingParameterSpecifiers#13", source: "func argumentLabelOnly(borrowing: Int) {}", origin: "DeclarationTests.testBorrowingConsumingParameterSpecifiers", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testBorrowingConsumingParameterSpecifiers#14", source: "func argumentLabelOnly(consuming: Int) {}", origin: "DeclarationTests.testBorrowingConsumingParameterSpecifiers", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testBorrowingConsumingParameterSpecifiers#15", source: "func argumentLabelOnly(__shared: Int) {}", origin: "DeclarationTests.testBorrowingConsumingParameterSpecifiers", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testBorrowingConsumingParameterSpecifiers#16", source: "func argumentLabelOnly(__owned: Int) {}", origin: "DeclarationTests.testBorrowingConsumingParameterSpecifiers", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testBorrowingConsumingParameterSpecifiers#17", source: "func argumentLabel(borrowing consuming: Int) {}", origin: "DeclarationTests.testBorrowingConsumingParameterSpecifiers", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testBorrowingConsumingParameterSpecifiers#18", source: "func argumentLabel(consuming borrowing: Int) {}", origin: "DeclarationTests.testBorrowingConsumingParameterSpecifiers", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testBorrowingConsumingParameterSpecifiers#19", source: "func argumentLabel(__shared __owned: Int) {}", origin: "DeclarationTests.testBorrowingConsumingParameterSpecifiers", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testBorrowingConsumingParameterSpecifiers#20", source: "func argumentLabel(__owned __shared: Int) {}", origin: "DeclarationTests.testBorrowingConsumingParameterSpecifiers", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testBorrowingConsumingParameterSpecifiers#21", source: "func argumentLabel(anonBorrowingInClosure: (_ borrowing: Int) -> ()) {}", origin: "DeclarationTests.testBorrowingConsumingParameterSpecifiers", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testBorrowingConsumingParameterSpecifiers#22", source: "func argumentLabel(anonConsumingInClosure: (_ consuming: Int) -> ()) {}", origin: "DeclarationTests.testBorrowingConsumingParameterSpecifiers", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testBorrowingConsumingParameterSpecifiers#23", source: "func argumentLabel(anonSharedInClosure: (_ __shared: Int) -> ()) {}", origin: "DeclarationTests.testBorrowingConsumingParameterSpecifiers", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testBorrowingConsumingParameterSpecifiers#24", source: "func argumentLabel(anonOwnedInClosure: (_ __owned: Int) -> ()) {}", origin: "DeclarationTests.testBorrowingConsumingParameterSpecifiers", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testWhereClauseWithFunctionType#1",
        source: """
      func badTypeConformance3<T>(_: T) where (T) -> () : EqualComparable { }
      """,
        origin: "DeclarationTests.testWhereClauseWithFunctionType",
        syntaxVersion: "603.0.1",
        compilerRejects: "type '(T) -> ()' in conformance requirement does not refer to a generic parameter or associated type"
    ),
    SwiftSnippet(
        label: "testSuppressedImplicitConformance#1",
        source: """
      struct Hello: ~Copyable {}
      """,
        origin: "DeclarationTests.testSuppressedImplicitConformance",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSuppressedImplicitConformance#2",
        source: """
      let _: any ~Copyable = 0
      """,
        origin: "DeclarationTests.testSuppressedImplicitConformance",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSuppressedImplicitConformance#3",
        source: """
      typealias Z = ~Copyable.Type
      """,
        origin: "DeclarationTests.testSuppressedImplicitConformance",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSuppressedImplicitConformance#4",
        source: """
      typealias Z = ~A.B.C
      """,
        origin: "DeclarationTests.testSuppressedImplicitConformance",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSuppressedImplicitConformance#5",
        source: """
      typealias Z = ~A?
      """,
        origin: "DeclarationTests.testSuppressedImplicitConformance",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSuppressedImplicitConformance#6",
        source: """
      typealias Z = ~A<T>
      """,
        origin: "DeclarationTests.testSuppressedImplicitConformance",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSuppressedImplicitConformance#7",
        source: """
      struct Hello<T: ~Copyable> {}
      """,
        origin: "DeclarationTests.testSuppressedImplicitConformance",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSuppressedImplicitConformance#8",
        source: """
      func henlo<T: ~Copyable>(_ t: T) {}
      """,
        origin: "DeclarationTests.testSuppressedImplicitConformance",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSuppressedImplicitConformance#9",
        source: """
      enum Whatever: Int, ~ Hashable, Equatable {}
      """,
        origin: "DeclarationTests.testSuppressedImplicitConformance",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSuppressedImplicitConformance#10",
        source: """
      typealias T = (~Int) -> Bool
      """,
        origin: "DeclarationTests.testSuppressedImplicitConformance",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInitAccessorsWithDefaultValues#1",
        source: """
      struct Test {
        var pair: (Int, Int) = (42, 0) {
          init(initialValue) {}

          get { (0, 42) }
          set { }
        }
      }
      """,
        origin: "DeclarationTests.testInitAccessorsWithDefaultValues",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testBorrowingGetAccessor#1",
        source: """
      struct Foo {
        var x: Int {
          borrowing get {}
        }
      }
      """,
        origin: "DeclarationTests.testBorrowingGetAccessor",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnumCaseWithGenericParameter#1",
        source: """
      enum Foo<T> {
        case five(param: T), six
      }
      """,
        origin: "DeclarationTests.testEnumCaseWithGenericParameter",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testLiteralInitializerWithTrailingClosure#1", source: "let foo = 1 { return 1 }", origin: "DeclarationTests.testLiteralInitializerWithTrailingClosure", syntaxVersion: "603.0.1", compilerRejects: "computed property must have an explicit type"),
    SwiftSnippet(label: "testInitializerWithReturnType#1", source: "init(_ ptr: UnsafeRawBufferPointer, _ a: borrowing Array<Int>) -> dependsOn(a) Self", origin: "DeclarationTests.testInitializerWithReturnType", syntaxVersion: "603.0.1", compilerRejects: "initializers may only be declared within a type"),
    SwiftSnippet(label: "testInitializerWithReturnType#2", source: "public init() -> Int", origin: "DeclarationTests.testInitializerWithReturnType", syntaxVersion: "603.0.1", compilerRejects: "initializers may only be declared within a type"),
    SwiftSnippet(label: "testSendingTypeSpecifier#1", source: "func testVarDeclTupleElt() -> (sending String, String) {}", origin: "DeclarationTests.testSendingTypeSpecifier", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testVarDeclTupleElt#1", source: "func testVarDeclTuple2(_ x: (sending String)) {}", origin: "DeclarationTests.testVarDeclTupleElt", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testVarDeclTuple2#1", source: "func testVarDeclTuple2(_ x: (sending String, String)) {}", origin: "DeclarationTests.testVarDeclTuple2", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testConstAsArgumentLabel#1", source: "func const(_const: String) {}", origin: "DeclarationTests.testConstAsArgumentLabel", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testConstAsArgumentLabel#2", source: "func const(_const map: String) {}", origin: "DeclarationTests.testConstAsArgumentLabel", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testConstAsArgumentLabel#3", source: "func const(_const x y: String) {}", origin: "DeclarationTests.testConstAsArgumentLabel", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testCoroutineAccessors#1",
        source: """
      var irm: Int {
        read {
          yield _i
        }
        modify {
          yield &_i
        }
      }
      """,
        origin: "DeclarationTests.testCoroutineAccessors",
        syntaxVersion: "603.0.1",
        // UNFIXABLE from here, not merely unimplemented. The SE-0443 coroutine accessors need
        // `Keyword.read` / `Keyword.modify` to build the `AccessorDecl`s, and both cases are
        // `@_spi`-protected in swift-syntax — they cannot be constructed outside the package, so
        // there is no way to emit the reference shape at all. (For this input swift-syntax does
        // NOT even produce accessors: it yields a CodeBlockItemList calling `read`/`modify`,
        // which we cannot reproduce either without knowing that reclassification.)
        // Re-enable if those Keyword cases ever become public. See TODO 33.
        disabledReason: "read/modify Keyword cases are @_spi and cannot be constructed"
    ),
    SwiftSnippet(
        label: "testCoroutineAccessors#2",
        source: """
      public var i: Int {
        _read {
          yield _i
        }
        read {
          yield _i
        }
        _modify {
          yield &_i
        }
        modify {
          yield &_i
        }
      }
      """,
        origin: "DeclarationTests.testCoroutineAccessors",
        syntaxVersion: "603.0.1",
        disabledReason: "swift-syntax negative/error-recovery fixture: mixing underscored `_read`/`_modify` with SE-0474 `read`/`modify` is a duplicate-accessor error under swift-syntax 603.0.1 (parsed cleanly under the old 600.0.1 pin — the dep bump introduced the diagnostic). Not valid Swift."
    ),
    SwiftSnippet(
        label: "testBorrowAndMutateAccessors#1",
        source: """
      public class Klass {}

      public struct Wrapper {
        var _otherK: Klass

        var k1: Klass {
          borrow {
            return _otherK
          }
          mutate {
            return &_otherK
          }
        }
      }
      """,
        origin: "DeclarationTests.testBorrowAndMutateAccessors",
        syntaxVersion: "603.0.1",
        disabledReason: "experimental feature"
    ),
    SwiftSnippet(
        label: "testTrailingCommas#1",
        source: """
      protocol Baaz<
        Foo,
        Bar,
      > {
        associatedtype Foo
        associatedtype Bar
      }
      """,
        origin: "DeclarationTests.testTrailingCommas",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTrailingCommas#2",
        source: """
      struct Foo<
        T1,
        T2,
        T3,
      >: Baaz<
        T1,
        T2,
      > {}
      """,
        origin: "DeclarationTests.testTrailingCommas",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testUsing#1", source: "using @MainActor", origin: "DeclarationTests.testUsing", syntaxVersion: "603.0.1", compilerRejects: "'using' is an experimental feature that is currently disabled"),
    SwiftSnippet(label: "testUsing#2", source: "using nonisolated", origin: "DeclarationTests.testUsing", syntaxVersion: "603.0.1", compilerRejects: "'using' is an experimental feature that is currently disabled"),
    SwiftSnippet(label: "testUsing#3", source: "using @Test", origin: "DeclarationTests.testUsing", syntaxVersion: "603.0.1", compilerRejects: "'using' is an experimental feature that is currently disabled"),
    SwiftSnippet(label: "testUsing#4", source: "using test", origin: "DeclarationTests.testUsing", syntaxVersion: "603.0.1", compilerRejects: "'using' is an experimental feature that is currently disabled"),
    SwiftSnippet(
        label: "testUsing#5",
        source: """
      nonisolated
      using
      """,
        origin: "DeclarationTests.testUsing",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testUsing#6",
        source: """
      using
      nonisolated
      """,
        origin: "DeclarationTests.testUsing",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testUsing#7",
        source: """
      func
      using (x: Int) {}
      """,
        origin: "DeclarationTests.testUsing",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testUsing#8",
        source: """
      func
      using
      (x: Int) {}
      """,
        origin: "DeclarationTests.testUsing",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testUsing#9",
        source: """
      let
        using = 42
      """,
        origin: "DeclarationTests.testUsing",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testUsing#10", source: "let (x: Int, using: String) = (x: 42, using: \"\")", origin: "DeclarationTests.testUsing", syntaxVersion: "603.0.1"),

    // Stored property with BOTH an initializer and an observer. Compiler-verified valid
    // (`swiftc -typecheck`, no diagnostic). Added Sep 12 2026 with the fix for the residual
    // ambiguity these exposed: the `codeBlock` alternate of `initializedAccessorBlock` competed
    // with `willSetDidSetBlock` over the same braces. See TODO #2.
    SwiftSnippet(label: "observer-with-initializer-willSet", source: "var x: Int = 0 { willSet {} }", origin: "regression", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "observer-with-initializer-didSet", source: "var y: Int = 0 { didSet {} }", origin: "regression", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "observer-with-initializer-both", source: "var z: Int = 0 { willSet {} didSet {} }", origin: "regression", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "observer-no-annotation", source: "var w = 0 { didSet {} }", origin: "regression", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testUsing#11",
        source: """
      do {
        using @MainActor
      }
      """,
        origin: "DeclarationTests.testUsing",
        syntaxVersion: "603.0.1",
        compilerRejects: "'using' is an experimental feature that is currently disabled"
    ),
    SwiftSnippet(
        label: "testAccessorBlockDisambiguationMarker#1",
        source: """
      var value = initialValue { @_accessorBlock
        get
      }
      """,
        origin: "DeclarationTests.testAccessorBlockDisambiguationMarker",
        syntaxVersion: "603.0.1",
        compilerRejects: "expected '{' to start getter definition"
    ),
    SwiftSnippet(
        label: "testAccessorBlockAfterPatternBindingDeclWithAttribute#1",
        source: """
      var x: Int = foo()
      {
        @available(*, deprecated)
        didSet {}
      }
      """,
        origin: "DeclarationTests.testAccessorBlockAfterPatternBindingDeclWithAttribute",
        syntaxVersion: "603.0.1"
    ),
]


// MARK: - Test Suite

extension SwiftSyntax603Tests {

@Suite("Declarations")
struct DeclarationSyntaxTests {

    @Test("SwiftSyntax accepts", .tags(.swiftSyntaxReference), arguments: declarationSnippets)
    func swiftSyntaxAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let parsed = Parser.parse(source: snippet.source)
        #expect(!parsed.hasError, "SwiftSyntax parse error for: \(snippet.source)")
    }

    @Test("Advent accepts", arguments: declarationSnippets)
    func adventAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let result = try adventParse(snippet)
        #expect(result != nil, "Advent failed to parse: \(snippet.source)")
    }

    @Test("no residual ambiguity", arguments: declarationSnippets)
    func unambiguous(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        guard let result = try adventParse(snippet) else {
            Issue.record("Advent failed to parse: \(snippet.source)")
            return
        }
        #expect(result.isUnambiguous,
                "Residual ambiguity in '\(snippet.diagnosticID)': \(result.builder.diagnostics)")
    }

    @Test("trees match", arguments: declarationSnippets)
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

let declaration604Snippets: [SwiftSnippet] = [
    SwiftSnippet(label: "testImports#1", source: "import Foundation", origin: "DeclarationTests.testImports", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testImports#2", source: "@_spi(Private) import SwiftUI", origin: "DeclarationTests.testImports", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testImports#3", source: "@_exported import class Foundation.Thread", origin: "DeclarationTests.testImports", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testImports#4", source: #"@_private(sourceFile: "YetAnotherFile.swift") import Foundation"#, origin: "DeclarationTests.testImports", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testStructParsing#1", source: "struct Foo {}", origin: "DeclarationTests.testStructParsing", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testFuncParsing#1", source: "func foo() {}", origin: "DeclarationTests.testFuncParsing", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testFuncParsing#2", source: "func foo() -> Slice<MinimalMutableCollection<T>> {}", origin: "DeclarationTests.testFuncParsing", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testFuncParsing#3",
        source: """
      func onEscapingAutoclosure(_ fn: @Sendable @autoclosure @escaping () -> Int) { }
      func onEscapingAutoclosure2(_ fn: @escaping @autoclosure @Sendable () -> Int) { }
      func bar(_ : String) async -> [[String]: Array<String>] {}
      func tupleMembersFunc() -> (Type.Inner, Type2.Inner2) {}
      func myFun<S: T & U>(var1: S) {
        // do stuff
      }
      """,
        origin: "DeclarationTests.testFuncParsing",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testFuncParsing#4", source: "func /^/ (lhs: Int, rhs: Int) -> Int { 1 / 2 }", origin: "DeclarationTests.testFuncParsing", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testFuncParsing#5", source: "func /^ (lhs: Int, rhs: Int) -> Int { 1 / 2 }", origin: "DeclarationTests.testFuncParsing", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testFuncParsing#6",
        source: """
      func name(_ default: Int) {}
      """,
        origin: "DeclarationTests.testFuncParsing",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testClassParsing#1", source: "class Foo {}", origin: "DeclarationTests.testClassParsing", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testClassParsing#2",
        source: """
      @dynamicMemberLookup @available(swift 4.0)
      public class MyClass {
        let A: Int
        let B: Double
      }
      """,
        origin: "DeclarationTests.testClassParsing",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testClassParsing#3", source: "struct A<@NSApplicationMain T: AnyObject> {}", origin: "DeclarationTests.testClassParsing", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testActorParsing#1", source: "actor Foo {}", origin: "DeclarationTests.testActorParsing", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testActorParsing#2",
        source: """
      actor Foo {
        nonisolated init?() {
          for (x, y, z) in self.triples {
            precondition(isSafe)
          }
        }
        subscript(_ param: String) -> Int {
          return 42
        }
      }
      """,
        origin: "DeclarationTests.testActorParsing",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testProtocolParsing#1", source: "protocol Foo {}", origin: "DeclarationTests.testProtocolParsing", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testProtocolParsing#2", source: "protocol P { init() }", origin: "DeclarationTests.testProtocolParsing", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testProtocolParsing#3",
        source: """
      protocol P {
        associatedtype Foo: Bar where X.Y == Z.W.W.Self

        var foo: Bool { get set }
        subscript<R>(index: Int) -> R
      }
      """,
        origin: "DeclarationTests.testProtocolParsing",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testVariableDeclarations#1",
        source: """
      z

      var x: Double = z
      """,
        origin: "DeclarationTests.testVariableDeclarations",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testVariableDeclarations#2",
        source: """
      async let a = fetch("1.jpg")
      async let b: Image = fetch("2.jpg")
      async let secondPhotoToFetch = fetch("3.jpg")
      async let theVeryLastPhotoWeWant = fetch("4.jpg")
      """,
        origin: "DeclarationTests.testVariableDeclarations",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testVariableDeclarations#3", source: "private unowned(unsafe) var foo: Int", origin: "DeclarationTests.testVariableDeclarations", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testVariableDeclarations#4", source: "unowned(unsafe) let unmanagedVar: Class = c", origin: "DeclarationTests.testVariableDeclarations", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testVariableDeclarations#5", source: "_ = foo?.description", origin: "DeclarationTests.testVariableDeclarations", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testVariableDeclarations#6", source: "var a = Array<Int>?(from: decoder)", origin: "DeclarationTests.testVariableDeclarations", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testVariableDeclarations#7", source: "@Wrapper var café = 42", origin: "DeclarationTests.testVariableDeclarations", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testVariableDeclarations#8",
        source: """
      var x: T {
        get async {
          foo()
          bar()
        }
      }
      """,
        origin: "DeclarationTests.testVariableDeclarations",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testVariableDeclarations#9",
        source: """
      var foo: Int {
        _read {
          yield 1234567890
        }
        _modify {
          var someLongVariable = 0
          yield &someLongVariable
        }
      }
      """,
        origin: "DeclarationTests.testVariableDeclarations",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testVariableDeclarations#10",
        source: """
      var foo: Int {
        @available(swift 5.0)
        func myFun() -> Int {
          return 42
        }
        return myFun()
      }
      """,
        origin: "DeclarationTests.testVariableDeclarations",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testVariableDeclarations#11",
        source: """
      var foo: Int {
        mutating set {
          test += 1
        }
      }
      """,
        origin: "DeclarationTests.testVariableDeclarations",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testTypealias#1", source: "typealias Foo = Int", origin: "DeclarationTests.testTypealias", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testTypealias#2", source: "typealias MyAlias = (_ a: Int, _ b: Double, _ c: Bool, _ d: String) -> Bool", origin: "DeclarationTests.testTypealias", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testTypealias#3", source: "typealias A = @attr1 @attr2(hello) (Int) -> Void", origin: "DeclarationTests.testTypealias", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testPrecedenceGroup#1",
        source: """
      precedencegroup FooGroup {
        higherThan: Group1, Group2
        lowerThan: Group3, Group4
        associativity: left
        assignment: false
      }
      """,
        origin: "DeclarationTests.testPrecedenceGroup",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testPrecedenceGroup#2",
        source: """
      precedencegroup FunnyPrecedence {
       associativity: left
       higherThan: MultiplicationPrecedence
      }
      """,
        origin: "DeclarationTests.testPrecedenceGroup",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testOperators#1", source: "infix operator *-* : FunnyPrecedence", origin: "DeclarationTests.testOperators", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testOperators#2",
        source: """
      infix operator  <*<<< : MediumPrecedence, &
      prefix operator ^^ : PrefixMagicOperatorProtocol
      infix operator  <*< : MediumPrecedence, InfixMagicOperatorProtocol
      postfix operator ^^ : PostfixMagicOperatorProtocol
      infix operator ^^ : PostfixMagicOperatorProtocol, Class, Struct
      """,
        origin: "DeclarationTests.testOperators",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testObjCAttribute#1",
        source: """
      @objc(
        thisMethodHasAVeryLongName:
        foo:
        bar:
      )
      func f() {}
      """,
        origin: "DeclarationTests.testObjCAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDifferentiableAttribute#1",
        source: """
      @differentiable(wrt: x where T: D)
      func foo<T>(_ x: T) -> T {}

      @differentiable(wrt: x where T: Differentiable)
      func foo<T>(_ x: T) -> T {}

      @differentiable(wrt: theVariableNamedX where T: Differentiable)
      func foo<T>(_ theVariableNamedX: T) -> T {}

      @differentiable(wrt: (x, y))
      func foo<T>(_ x: T) -> T {}
      """,
        origin: "DeclarationTests.testDifferentiableAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testParsePoundError#1", source: #"#error("Unsupported platform")"#, origin: "DeclarationTests.testParsePoundError", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testParsePoundWarning#1", source: #"#warning("Unsupported platform")"#, origin: "DeclarationTests.testParsePoundWarning", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testParseSpecializeAttribute#1",
        source: #"""
      @_specialize(where T == Int, U == Float)
      mutating func exchangeSecond<U>(_ u: U, _ t: T) -> (U, T) {
        x = t
        return (u, x)
      }

      @_specialize(exported: true, kind: full, where K == Int, V == Int)
      @_specialize(exported: false, kind: partial, where K: _Trivial64)
      func dictFunction<K, V>(dict: Dictionary<K, V>) {
      }

      @_specialize(where T == Int)
      public func play() {
        for _ in 0...100_000_000 { t = t.ping() }
      }

      @_specialize(exported: true,
                   spi: SwiftSpecialization,
                   target: copy(),
                   where Key == AnyHashable, Value == Any)
      @_specialize(exported: true,
                   spi: SwiftSpecialization,
                   target: copy(),
                   where Key == AnyHashable, Value == String)
      @_specialize(exported: true,
                   spi: SwiftSpecialization,
                   target: copy(),
                   where Key == String, Value == Any)
      @_specialize(exported: true,
                   spi: SwiftSpecialization,
                   target: copy(),
                   where Key == String, Value == AnyHashable)
      @_specialize(exported: true,
                   spi: SwiftSpecialization,
                   target: copy(),
                   where Key == String, Value == String)
      @available(SwiftStdlib 5.5, *)
      @usableFromInline
      mutating func __specialize_copy() { Builtin.unreachable() }

      @_specializeExtension
      extension Sequence {
        @_specialize(exported: true,
                     spi: SwiftSpecialization,
                     target: _copyContents(initializing:),
                     where Self == [String])
        @_specialize(exported: true,
                     spi: SwiftSpecialization,
                     target: _copyContents(initializing:),
                     where Self == Set<String>)
        @available(SwiftStdlib 5.5, *)
        @usableFromInline
        __consuming func __specialize__copyContents(initializing: Swift.UnsafeMutableBufferPointer<Element>)  -> (Iterator, Int) { Builtin.unreachable() }
      }
      """#,
        origin: "DeclarationTests.testParseSpecializeAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testParseSpecializeAttribute#2",
        source: """
      @_specialize(where T: _Trivial(32), T: _Trivial(64), T: _Trivial, T: _RefCountedObject)
      @_specialize(where T: _Trivial, T: _Trivial(64))
      @_specialize(where T: _RefCountedObject, T: _NativeRefCountedObject)
      @_specialize(where Array<T> == Int)
      @_specialize(where T.Element == Int)
      public func funcWithComplexSpecializeRequirements<T: ProtocolWithDep>(t: T) -> Int {
        return 55555
      }
      """,
        origin: "DeclarationTests.testParseSpecializeAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05",
        compilerRejects: "SIL layout constraint (_Trivial(32)) not modelled"
    ),
    SwiftSnippet(
        label: "testParseSpecializeAttribute#3",
        source: """
      @specialized(where Array<T> == Int)
      @specialized(where T.Element == Int)
      public func funcWithComplexSpecializeRequirements<T: ProtocolWithDep>(t: T) -> Int {
        return 55555
      }
      """,
        origin: "DeclarationTests.testParseSpecializeAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testParseRetroactiveExtension#1",
        source: """
      extension Int: @retroactive Identifiable {}
      """,
        origin: "DeclarationTests.testParseRetroactiveExtension",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testParsePreconcurrency#1",
        source: """
      struct MyValue: @preconcurrency P {}
      """,
        origin: "DeclarationTests.testParsePreconcurrency",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testParsePreconcurrency#2",
        source: """
      extension MyValue: @preconcurrency P {}
      """,
        origin: "DeclarationTests.testParsePreconcurrency",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testParseIsolatedConformances#1",
        source: """
      extension Int: nonisolated Q {}
      """,
        origin: "DeclarationTests.testParseIsolatedConformances",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testParseIsolatedConformances#2",
        source: """
      extension Int: @MainActor P {}
      """,
        origin: "DeclarationTests.testParseIsolatedConformances",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testParseIsolatedConformances#3",
        source: """
      extension Int: @preconcurrency nonisolated Q {}
      """,
        origin: "DeclarationTests.testParseIsolatedConformances",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testParseIsolatedConformances#4",
        source: """
      extension Int: @unsafe nonisolated Q {}
      """,
        origin: "DeclarationTests.testParseIsolatedConformances",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testParseDynamicReplacement#1",
        source: """
      @_dynamicReplacement(for: dynamic_replaceable())
      func replacement() {
        dynamic_replaceable()
      }
      """,
        origin: "DeclarationTests.testParseDynamicReplacement",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testParseDynamicReplacement#2",
        source: """
      @_dynamicReplacement(for: subscript(_:))
      subscript(x y: Int) -> Int {
        get {
          return self[y]
        }
        set {
          self[y] = newValue
        }
      }
      """,
        origin: "DeclarationTests.testParseDynamicReplacement",
        syntaxVersion: "604.0.0-prerelease-2026-06-05",
        compilerRejects: "'subscript' functions may only be declared within a type"
    ),
    SwiftSnippet(
        label: "testParseDynamicReplacement#3",
        source: """
      @_dynamicReplacement(for: dynamic_replaceable_var)
      var r : Int {
        return 0
      }
      """,
        origin: "DeclarationTests.testParseDynamicReplacement",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testParseDynamicReplacement#4",
        source: """
      @_dynamicReplacement(for: init(x:))
      init(y: Int) {
        self.init(x: y + 1)
      }
      """,
        origin: "DeclarationTests.testParseDynamicReplacement",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnumParsing#1",
        source: """
      enum Foo {
        @preconcurrency case custom(@Sendable () throws -> Void)
      }
      """,
        origin: "DeclarationTests.testEnumParsing",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnumParsing#2",
        source: """
      enum Content {
        case keyPath(KeyPath<FocusedValues, Value?>)
        case keyPath(KeyPath<FocusedValues, Binding<Value>?>)
        case value(Value?)
      }
      """,
        origin: "DeclarationTests.testEnumParsing",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testTypedThrows#1", source: "func test() throws(any Error) -> Int { }", origin: "DeclarationTests.testTypedThrows", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testTypedThrows#2",
        source: """
      struct X {
        init() throws(any Error) { }
      }
      """,
        origin: "DeclarationTests.testTypedThrows",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testTypedThrows#3", source: "func test() throws(MyError) {}", origin: "DeclarationTests.testTypedThrows", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testTypedThrows#4",
        source: """
      struct S<Element, Failure: Error> {
        init(produce: @escaping () async throws(Failure) -> Element?) {
        }
      }
      """,
        origin: "DeclarationTests.testTypedThrows",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAccessors#1",
        source: """
      var bad1 : Int {
        _read async { 0 }
      }
      """,
        origin: "DeclarationTests.testAccessors",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAccessors#2",
        source: """
      public var foo: Swift.Int {
        get
        @inlinable set {}
      }
      """,
        origin: "DeclarationTests.testAccessors",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInitAccessor#1",
        source: """
      struct S {
        var value: Int {
          init {}
          get {}
          set {}
        }
      }
      """,
        origin: "DeclarationTests.testInitAccessor",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInitAccessor#2",
        source: """
      struct S {
        let _value: Int

        init() {
        }
      }
      """,
        origin: "DeclarationTests.testInitAccessor",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInitAccessor#3",
        source: """
      struct S {
        var value: Int {
          init(newValue) {}
          get {}
          set(newValue) {}
        }
      }
      """,
        origin: "DeclarationTests.testInitAccessor",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInitAccessor#4",
        source: """
      struct S {
        var value: Int {
          init(newValue) {}
          get {}
          set(newValue) {}
        }
      }
      """,
        origin: "DeclarationTests.testInitAccessor",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInitializers#1",
        source: """
      struct S0 {
        init!(int: Int) { }
        init! (uint: UInt) { }
        init !(float: Float) { }

        init?(string: String) { }
        init ?(double: Double) { }
        init ? (char: Character) { }
      }
      """,
        origin: "DeclarationTests.testInitializers",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testDeinitializers#1", source: "deinit {}", origin: "DeclarationTests.testDeinitializers", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testDeinitializers#2", source: "deinit", origin: "DeclarationTests.testDeinitializers", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testAttributedMember#1",
        source: #"""
      struct Foo {
        @Argument(help: "xxx")
        var generatedPath: String
      }
      """#,
        origin: "DeclarationTests.testAttributedMember",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testAnyAsParameterLabel#1", source: "func at(any kinds: [RawTokenKind]) {}", origin: "DeclarationTests.testAnyAsParameterLabel", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testPublicClass#1", source: "public class Foo: Superclass {}", origin: "DeclarationTests.testPublicClass", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testReturnVariableNamedAsync#1",
        source: ##"""
      if let async = self.consume(if: .keyword(.async)) {
        return async
      }

      if let reasync = self.consume(if: .keyword(.reasync)) {
        return reasync
      }
      """##,
        origin: "DeclarationTests.testReturnVariableNamedAsync",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testModifiedParameter#1",
        source: """
      func const(_const _ map: String) {}
      """,
        origin: "DeclarationTests.testModifiedParameter",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testModifiedParameter#2",
        source: """
      func isolated(isolated _ map: String) {}
      """,
        origin: "DeclarationTests.testModifiedParameter",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testModifiedParameter#3",
        source: """
      func isolatedConst(isolated _const _ map: String) {}
      """,
        origin: "DeclarationTests.testModifiedParameter",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testModifiedParameter#4",
        source: """
      func nonEphemeralIsolatedConst(@_nonEmphemeral isolated _const _ map: String) {}
      """,
        origin: "DeclarationTests.testModifiedParameter",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testModifiedParameter#5",
        source: """
      func const(_const map: String) {}
      """,
        origin: "DeclarationTests.testModifiedParameter",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testModifiedParameter#6",
        source: """
      func isolated(isolated map: String) {}
      """,
        origin: "DeclarationTests.testModifiedParameter",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testModifiedParameter#7",
        source: """
      func isolatedConst(isolated _const map: String) {}
      """,
        origin: "DeclarationTests.testModifiedParameter",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testModifiedParameter#8",
        source: """
      func const(_const x: String) {}
      func isolated(isolated: String) {}
      func isolatedConst(isolated _const: String) {}
      """,
        origin: "DeclarationTests.testModifiedParameter",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testReasyncFunctions#1",
        source: """
      class MyType {
        init(_ f: () async -> Void) reasync {
          await f()
        }

        func foo(index: Int) reasync rethrows -> String {
          await f()
        }
      }
      """,
        origin: "DeclarationTests.testReasyncFunctions",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMacroExpansionDeclaration#1",
        source: """
      struct X {
        #memberwiseInit(access: .public)
      }
      """,
        origin: "DeclarationTests.testMacroExpansionDeclaration",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMacroExpansionDeclaration#2",
        source: """
      #expand
      """,
        origin: "DeclarationTests.testMacroExpansionDeclaration",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMacroExpansionDeclarationWithKeywordName#1",
        source: """
      struct X {
        #case
      }
      """,
        origin: "DeclarationTests.testMacroExpansionDeclarationWithKeywordName",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAttributedMacroExpansionDeclaration#1",
        source: """
      @attribute #topLevelWithAttr
      """,
        origin: "DeclarationTests.testAttributedMacroExpansionDeclaration",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAttributedMacroExpansionDeclaration#2",
        source: """
      public #topLevelWithModifier
      """,
        origin: "DeclarationTests.testAttributedMacroExpansionDeclaration",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAttributedMacroExpansionDeclaration#3",
        source: """
      #topLevelBare
      """,
        origin: "DeclarationTests.testAttributedMacroExpansionDeclaration",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAttributedMacroExpansionDeclaration#4",
        source: """
      struct S {
        @attribute #memberWithAttr
      }
      """,
        origin: "DeclarationTests.testAttributedMacroExpansionDeclaration",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAttributedMacroExpansionDeclaration#5",
        source: """
      struct S {
        public #memberWithModifier
      }
      """,
        origin: "DeclarationTests.testAttributedMacroExpansionDeclaration",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAttributedMacroExpansionDeclaration#6",
        source: """
      struct S {
        #memberBare
      }
      """,
        origin: "DeclarationTests.testAttributedMacroExpansionDeclaration",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAttributedMacroExpansionDeclaration#7",
        source: """
      func test() {
        @attribute #bodyWithAttr
      }
      """,
        origin: "DeclarationTests.testAttributedMacroExpansionDeclaration",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAttributedMacroExpansionDeclaration#8",
        source: """
      func test() {
        public #bodyWithModifier
      }
      """,
        origin: "DeclarationTests.testAttributedMacroExpansionDeclaration",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAttributedMacroExpansionDeclaration#9",
        source: """
      func test() {
        #bodyBare
      }
      """,
        origin: "DeclarationTests.testAttributedMacroExpansionDeclaration",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAttributedMacroExpansionDeclaration#10",
        source: """
      func test() {
        @attrib1
        @attrib2
        public
        #declMacro
      }
      """,
        origin: "DeclarationTests.testAttributedMacroExpansionDeclaration",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAttributedMacroExpansionDeclaration#11",
        source: """
      struct S {
        @attrib #class
      }
      """,
        origin: "DeclarationTests.testAttributedMacroExpansionDeclaration",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAttributedMacroExpansionDeclaration#12",
        source: """
      struct S {
        #struct
      }
      """,
        origin: "DeclarationTests.testAttributedMacroExpansionDeclaration",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testVariableGetSetNextLine#1",
        source: """
      struct X {
        var x: Int
        { 17 }
      }
      """,
        origin: "DeclarationTests.testVariableGetSetNextLine",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testVariableFollowedByReferenceToSet#1",
        source: """
      func bar() {
          let a = b
          set.c
      }
      """,
        origin: "DeclarationTests.testVariableFollowedByReferenceToSet",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIssue1025#1",
        source: """
      struct Math {
        public static let pi = 3.14
        @available(*, unavailable) init() {}
      }
      """,
        origin: "DeclarationTests.testIssue1025",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testIssue1025#2", source: "func foo(body: (isolated String) -> Int) {}", origin: "DeclarationTests.testIssue1025", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testClassWithPrivateSet#1",
        source: """
      struct Properties {
        class private(set) var privateSetterCustomNames: Bool
      }
      """,
        origin: "DeclarationTests.testClassWithPrivateSet",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAttributeInPoundIf#1",
        source: """
      #if hasAttribute(foo)
      @foo
      #endif
      struct MyStruct {}
      """,
        origin: "DeclarationTests.testAttributeInPoundIf",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testCallToOpenThatLooksLikeDeclarationModifier#1",
        source: """
      func test() {
        open(set)
        var foo = 2
      }
      """,
        origin: "DeclarationTests.testCallToOpenThatLooksLikeDeclarationModifier",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testReferenceToOpenThatLooksLikeDeclarationModifier#1",
        source: """
      func test() {
        open
        var foo = 2
      }
      """,
        origin: "DeclarationTests.testReferenceToOpenThatLooksLikeDeclarationModifier",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOpenVarInCodeBlockItemList#1",
        source: """
      func test() {
        open var foo = 2
      }
      """,
        origin: "DeclarationTests.testOpenVarInCodeBlockItemList",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAsyncLetInLocalContext#1",
        source: """
      func foo() async {
        async let x: String = "x"
      }
      """,
        origin: "DeclarationTests.testAsyncLetInLocalContext",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testBorrowingConsumingParameterSpecifiers#1", source: "struct borrowing {}", origin: "DeclarationTests.testBorrowingConsumingParameterSpecifiers", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testBorrowingConsumingParameterSpecifiers#2", source: "struct consuming {}", origin: "DeclarationTests.testBorrowingConsumingParameterSpecifiers", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testBorrowingConsumingParameterSpecifiers#3", source: "struct Foo {}", origin: "DeclarationTests.testBorrowingConsumingParameterSpecifiers", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testBorrowingConsumingParameterSpecifiers#4", source: "func foo(x: borrowing Foo) {}", origin: "DeclarationTests.testBorrowingConsumingParameterSpecifiers", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testBorrowingConsumingParameterSpecifiers#5", source: "func bar(x: consuming Foo) {}", origin: "DeclarationTests.testBorrowingConsumingParameterSpecifiers", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testBorrowingConsumingParameterSpecifiers#6", source: "func baz(x: (borrowing Foo, consuming Foo) -> ()) {}", origin: "DeclarationTests.testBorrowingConsumingParameterSpecifiers", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testBorrowingConsumingParameterSpecifiers#7", source: "func zim(x: borrowing) {}", origin: "DeclarationTests.testBorrowingConsumingParameterSpecifiers", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testBorrowingConsumingParameterSpecifiers#8", source: "func zang(x: consuming) {}", origin: "DeclarationTests.testBorrowingConsumingParameterSpecifiers", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testBorrowingConsumingParameterSpecifiers#9", source: "func zung(x: borrowing consuming) {}", origin: "DeclarationTests.testBorrowingConsumingParameterSpecifiers", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testBorrowingConsumingParameterSpecifiers#10", source: "func zip(x: consuming borrowing) {}", origin: "DeclarationTests.testBorrowingConsumingParameterSpecifiers", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testBorrowingConsumingParameterSpecifiers#11", source: "func zap(x: (borrowing, consuming) -> ()) {}", origin: "DeclarationTests.testBorrowingConsumingParameterSpecifiers", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testBorrowingConsumingParameterSpecifiers#12", source: "func zoop(x: (borrowing consuming, consuming borrowing) -> ()) {}", origin: "DeclarationTests.testBorrowingConsumingParameterSpecifiers", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testBorrowingConsumingParameterSpecifiers#13", source: "func argumentLabelOnly(borrowing: Int) {}", origin: "DeclarationTests.testBorrowingConsumingParameterSpecifiers", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testBorrowingConsumingParameterSpecifiers#14", source: "func argumentLabelOnly(consuming: Int) {}", origin: "DeclarationTests.testBorrowingConsumingParameterSpecifiers", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testBorrowingConsumingParameterSpecifiers#15", source: "func argumentLabelOnly(__shared: Int) {}", origin: "DeclarationTests.testBorrowingConsumingParameterSpecifiers", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testBorrowingConsumingParameterSpecifiers#16", source: "func argumentLabelOnly(__owned: Int) {}", origin: "DeclarationTests.testBorrowingConsumingParameterSpecifiers", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testBorrowingConsumingParameterSpecifiers#17", source: "func argumentLabel(borrowing consuming: Int) {}", origin: "DeclarationTests.testBorrowingConsumingParameterSpecifiers", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testBorrowingConsumingParameterSpecifiers#18", source: "func argumentLabel(consuming borrowing: Int) {}", origin: "DeclarationTests.testBorrowingConsumingParameterSpecifiers", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testBorrowingConsumingParameterSpecifiers#19", source: "func argumentLabel(__shared __owned: Int) {}", origin: "DeclarationTests.testBorrowingConsumingParameterSpecifiers", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testBorrowingConsumingParameterSpecifiers#20", source: "func argumentLabel(__owned __shared: Int) {}", origin: "DeclarationTests.testBorrowingConsumingParameterSpecifiers", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testBorrowingConsumingParameterSpecifiers#21", source: "func argumentLabel(anonBorrowingInClosure: (_ borrowing: Int) -> ()) {}", origin: "DeclarationTests.testBorrowingConsumingParameterSpecifiers", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testBorrowingConsumingParameterSpecifiers#22", source: "func argumentLabel(anonConsumingInClosure: (_ consuming: Int) -> ()) {}", origin: "DeclarationTests.testBorrowingConsumingParameterSpecifiers", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testBorrowingConsumingParameterSpecifiers#23", source: "func argumentLabel(anonSharedInClosure: (_ __shared: Int) -> ()) {}", origin: "DeclarationTests.testBorrowingConsumingParameterSpecifiers", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testBorrowingConsumingParameterSpecifiers#24", source: "func argumentLabel(anonOwnedInClosure: (_ __owned: Int) -> ()) {}", origin: "DeclarationTests.testBorrowingConsumingParameterSpecifiers", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testWhereClauseWithFunctionType#1",
        source: """
      func badTypeConformance3<T>(_: T) where (T) -> () : EqualComparable { }
      """,
        origin: "DeclarationTests.testWhereClauseWithFunctionType",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSuppressedImplicitConformance#1",
        source: """
      struct Hello: ~Copyable {}
      """,
        origin: "DeclarationTests.testSuppressedImplicitConformance",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSuppressedImplicitConformance#2",
        source: """
      let _: any ~Copyable = 0
      """,
        origin: "DeclarationTests.testSuppressedImplicitConformance",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSuppressedImplicitConformance#3",
        source: """
      typealias Z = ~Copyable.Type
      """,
        origin: "DeclarationTests.testSuppressedImplicitConformance",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSuppressedImplicitConformance#4",
        source: """
      typealias Z = ~A.B.C
      """,
        origin: "DeclarationTests.testSuppressedImplicitConformance",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSuppressedImplicitConformance#5",
        source: """
      typealias Z = ~A?
      """,
        origin: "DeclarationTests.testSuppressedImplicitConformance",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSuppressedImplicitConformance#6",
        source: """
      typealias Z = ~A<T>
      """,
        origin: "DeclarationTests.testSuppressedImplicitConformance",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSuppressedImplicitConformance#7",
        source: """
      struct Hello<T: ~Copyable> {}
      """,
        origin: "DeclarationTests.testSuppressedImplicitConformance",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSuppressedImplicitConformance#8",
        source: """
      func henlo<T: ~Copyable>(_ t: T) {}
      """,
        origin: "DeclarationTests.testSuppressedImplicitConformance",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSuppressedImplicitConformance#9",
        source: """
      enum Whatever: Int, ~ Hashable, Equatable {}
      """,
        origin: "DeclarationTests.testSuppressedImplicitConformance",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSuppressedImplicitConformance#10",
        source: """
      typealias T = (~Int) -> Bool
      """,
        origin: "DeclarationTests.testSuppressedImplicitConformance",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInitAccessorsWithDefaultValues#1",
        source: """
      struct Test {
        var pair: (Int, Int) = (42, 0) {
          init(initialValue) {}

          get { (0, 42) }
          set { }
        }
      }
      """,
        origin: "DeclarationTests.testInitAccessorsWithDefaultValues",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testBorrowingGetAccessor#1",
        source: """
      struct Foo {
        var x: Int {
          borrowing get {}
        }
      }
      """,
        origin: "DeclarationTests.testBorrowingGetAccessor",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnumCaseWithGenericParameter#1",
        source: """
      enum Foo<T> {
        case five(param: T), six
      }
      """,
        origin: "DeclarationTests.testEnumCaseWithGenericParameter",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testLiteralInitializerWithTrailingClosure#1", source: "let foo = 1 { return 1 }", origin: "DeclarationTests.testLiteralInitializerWithTrailingClosure", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testInitializerWithReturnType#1", source: "init(_ ptr: UnsafeRawBufferPointer, _ a: borrowing Array<Int>) -> dependsOn(a) Self", origin: "DeclarationTests.testInitializerWithReturnType", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testInitializerWithReturnType#2", source: "public init() -> Int", origin: "DeclarationTests.testInitializerWithReturnType", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testSendingTypeSpecifier#1", source: "func testVarDeclTupleElt() -> (sending String, String) {}", origin: "DeclarationTests.testSendingTypeSpecifier", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testVarDeclTupleElt#1", source: "func testVarDeclTuple2(_ x: (sending String)) {}", origin: "DeclarationTests.testVarDeclTupleElt", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testVarDeclTuple2#1", source: "func testVarDeclTuple2(_ x: (sending String, String)) {}", origin: "DeclarationTests.testVarDeclTuple2", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testConstAsArgumentLabel#1", source: "func const(_const: String) {}", origin: "DeclarationTests.testConstAsArgumentLabel", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testConstAsArgumentLabel#2", source: "func const(_const map: String) {}", origin: "DeclarationTests.testConstAsArgumentLabel", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testConstAsArgumentLabel#3", source: "func const(_const x y: String) {}", origin: "DeclarationTests.testConstAsArgumentLabel", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testCoroutineAccessors#1",
        source: """
      var i: Int {
        yielding borrow {
          yield _i
        }
        yielding mutate {
          yield &_i
        }
      }
      """,
        origin: "DeclarationTests.testCoroutineAccessors",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testCoroutineAccessorsLegacyFormat#1",
        source: """
      var irm: Int {
        read {
          yield _i
        }
        modify {
          yield &_i
        }
      }
      """,
        origin: "DeclarationTests.testCoroutineAccessorsLegacyFormat",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testCoroutineAccessorsLegacyFormat#2",
        source: """
      public var i: Int {
        _read {
          yield _i
        }
        read {
          yield _i
        }
        _modify {
          yield &_i
        }
        modify {
          yield &_i
        }
      }
      """,
        origin: "DeclarationTests.testCoroutineAccessorsLegacyFormat",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMultipleModifiers#1",
        source: """
      public struct S {
        var v: Int {
          __consuming consuming borrowing mutating nonmutating yielding get {
            0
          }
        }
      }
      """,
        origin: "DeclarationTests.testMultipleModifiers",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testBorrowAndMutateAccessors#1",
        source: """
      public class Klass {}

      public struct Wrapper {
        var _otherK: Klass

        var k1: Klass {
          borrow {
            return _otherK
          }
          mutate {
            return &_otherK
          }
        }
      }
      """,
        origin: "DeclarationTests.testBorrowAndMutateAccessors",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTrailingCommas#1",
        source: """
      protocol Baaz<
        Foo,
        Bar,
      > {
        associatedtype Foo
        associatedtype Bar
      }
      """,
        origin: "DeclarationTests.testTrailingCommas",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTrailingCommas#2",
        source: """
      struct Foo<
        T1,
        T2,
        T3,
      >: Baaz<
        T1,
        T2,
      > {}
      """,
        origin: "DeclarationTests.testTrailingCommas",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testUsing#1", source: "using @MainActor", origin: "DeclarationTests.testUsing", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testUsing#2", source: "using nonisolated", origin: "DeclarationTests.testUsing", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testUsing#3", source: "using @Test", origin: "DeclarationTests.testUsing", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testUsing#4", source: "using test", origin: "DeclarationTests.testUsing", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testUsing#5", source: "using @warn(DiagGroupID, as: warning)", origin: "DeclarationTests.testUsing", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testUsing#6", source: "using @diagnose(DiagGroupID, as: error)", origin: "DeclarationTests.testUsing", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testUsing#7",
        source: """
      nonisolated
      using
      """,
        origin: "DeclarationTests.testUsing",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testUsing#8",
        source: """
      using
      nonisolated
      """,
        origin: "DeclarationTests.testUsing",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testUsing#9",
        source: """
      func
      using (x: Int) {}
      """,
        origin: "DeclarationTests.testUsing",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testUsing#10",
        source: """
      func
      using
      (x: Int) {}
      """,
        origin: "DeclarationTests.testUsing",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testUsing#11",
        source: """
      let
        using = 42
      """,
        origin: "DeclarationTests.testUsing",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testUsing#12", source: "let (x: Int, using: String) = (x: 42, using: \"\")", origin: "DeclarationTests.testUsing", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testUsing#13",
        source: """
      do {
        using @MainActor
      }
      """,
        origin: "DeclarationTests.testUsing",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAccessorBlockDisambiguationMarker#1",
        source: """
      var value = initialValue { @_accessorBlock
        get
      }
      """,
        origin: "DeclarationTests.testAccessorBlockDisambiguationMarker",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAccessorBlockAfterPatternBindingDeclWithAttribute#1",
        source: """
      var x: Int = foo()
      {
        @available(*, deprecated)
        didSet {}
      }
      """,
        origin: "DeclarationTests.testAccessorBlockAfterPatternBindingDeclWithAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
]

extension SwiftSyntax604Tests {

@Suite("Declarations")
struct DeclarationSyntax604Tests {

    @Test("SwiftSyntax accepts", .tags(.swiftSyntaxReference), arguments: declaration604Snippets)
    func swiftSyntaxAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        #expect(!swiftSyntaxReferenceHasError(snippet), "SwiftSyntax parse error for: \(snippet.source)")
    }

    @Test("Advent accepts", arguments: declaration604Snippets)
    func adventAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let result = try adventParse(snippet)
        #expect(result != nil, "Advent failed to parse: \(snippet.source)")
    }

    @Test("no residual ambiguity", arguments: declaration604Snippets)
    func unambiguous(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        guard let result = try adventParse(snippet) else {
            Issue.record("Advent failed to parse: \(snippet.source)")
            return
        }
        #expect(result.isUnambiguous,
                "Residual ambiguity in '\(snippet.diagnosticID)': \(result.builder.diagnostics)")
    }

    @Test("trees match", arguments: declaration604Snippets)
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

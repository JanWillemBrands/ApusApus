//
//  SwiftSyntaxAttributes.swift
//  AdventTests
//
//  Attributes snippets extracted from SwiftSyntax AttributeTests.swift (603.0.1).
//  See SwiftSyntaxTests.swift for shared infrastructure.
//

import Testing
import Foundation
import SwiftSyntax
import SwiftParser

// MARK: - Snippet Catalog

let attributeSnippets: [SwiftSnippet] = [
    SwiftSnippet(
        label: "testSpecializeAttribute#1",
        source: """
      @_specialize(where @_noMetdata T : _BridgeObject)
      func foo(_ t: T) {}
      """,
        origin: "AttributeTests.testSpecializeAttribute",
        syntaxVersion: "603.0.1", compilerRejects: "SIL layout constraint (_Trivial(32) / @_noMetdata) not modelled"
    ),
    SwiftSnippet(
        label: "testSpecializeAttribute#2",
        source: """
      @_specialize(where @_noMetdata T : _TrivialStride(64))
      func foo(_ t: T) {}
      """,
        origin: "AttributeTests.testSpecializeAttribute",
        syntaxVersion: "603.0.1", compilerRejects: "SIL layout constraint (_Trivial(32) / @_noMetdata) not modelled"
    ),
    SwiftSnippet(
        label: "testSpecializeAttribute#3",
        source: """
      @specialized(where T : Int)
      func foo(_ t: T) {}
      """,
        origin: "AttributeTests.testSpecializeAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSpecializeWithAvailability#1",
        source: """
      @_specialize(exported: true, kind: full, availability: iOS, introduced: 15.4; where T == Swift.Int)
      public func specializeWithAvailability<T>(_ t: T) { }
      """,
        origin: "AttributeTests.testSpecializeWithAvailability",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testObjCAttribute#1",
        source: """
      @objc(zeroArg)
      class A { }

      @objc(:::x::)
      func f(_: Int, _: Int, _: Int, _: Int, _: Int) { }
      """,
        origin: "AttributeTests.testObjCAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testObjCAttribute#2",
        source: """
      @objc(_:)
      func f(_: Int)
      """,
        origin: "AttributeTests.testObjCAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRethrowsAttribute#1",
        source: """
      @rethrows
      protocol P { }
      """,
        origin: "AttributeTests.testRethrowsAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAutoclosureAttribute#1",
        source: """
      func f(in: @autoclosure () -> Int) { }
      func g(in: @autoclosure @escaping () -> Int) { }
      """,
        origin: "AttributeTests.testAutoclosureAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDifferentiableAttribute#1",
        source: """
      func f(in: @differentiable(reverse) (Int) -> Int) { }
      func f(in: @differentiable(reverse, wrt: a) (Int) -> Int) { }
      """,
        origin: "AttributeTests.testDifferentiableAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testQualifiedAttribute#1",
        source: """
      @_Concurrency.MainActor(unsafe) public struct Image : SwiftUI.View {}
      """,
        origin: "AttributeTests.testQualifiedAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDerivativeAttribute#1",
        source: """
      @inlinable
      @differentiable(reverse, wrt: self)
      public func differentiableMap<Result: Differentiable>(
        _ body: @differentiable(reverse) (Element) -> Result
      ) -> [Result] {
        map(body)
      }
      """,
        origin: "AttributeTests.testDerivativeAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDerivativeAttribute#2",
        source: """
      @inlinable
      @differentiable(reverse, wrt: (self, initialResult))
      public func differentiableReduce<Result: Differentiable>(
        _ initialResult: Result,
        _ nextPartialResult: @differentiable(reverse) (Result, Element) -> Result
      ) -> Result {
        reduce(initialResult, nextPartialResult)
      }
      """,
        origin: "AttributeTests.testDerivativeAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDerivativeAttribute#3",
        source: """
      @inlinable
      @derivative(of: differentiableReduce)
      internal func _vjpDifferentiableReduce<Result: Differentiable>(
        _ initialResult: Result,
        _ nextPartialResult: @differentiable(reverse) (Result, Element) -> Result
      ) -> (
        value: Result,
        pullback: (Result.TangentVector)
          -> (Array.TangentVector, Result.TangentVector)
      ) {}
      """,
        origin: "AttributeTests.testDerivativeAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDerivativeAttribute#4",
        source: """
      @derivative(of: Self.other)
      func foo() {}
      """,
        origin: "AttributeTests.testDerivativeAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDerivativeAttribute#5",
        source: """
      @derivative(of: Foo.Self.other)
      func foo() {}
      """,
        origin: "AttributeTests.testDerivativeAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTransposeAttribute#1",
        source: """
      @transpose(of: S.instanceMethod, wrt: self)
      static func transposeInstanceMethodWrtSelf(_ other: S, t: S) -> S {
        other + t
      }
      """,
        origin: "AttributeTests.testTransposeAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTransposeAttribute#2",
        source: """
      @transpose(of: +)
      func addTranspose(_ v: Float) -> (Float, Float) {
        return (v, v)
      }
      """,
        origin: "AttributeTests.testTransposeAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTransposeAttribute#3",
        source: """
      @transpose(of: -, wrt: (0, 1))
      func subtractTranspose(_ v: Float) -> (Float, Float) {
        return (v, -v)
      }
      """,
        origin: "AttributeTests.testTransposeAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTransposeAttribute#4",
        source: """
      @transpose(of: Float.-, wrt: (0, 1))
      func subtractTranspose(_ v: Float) -> (Float, Float) {
        return (v, -v)
      }
      """,
        origin: "AttributeTests.testTransposeAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testImplementsAttribute#1",
        source: """
      @_implements(P, f0())
      func g0() -> Int {
        return 10
      }

      @_implements(P, f(x:y:))
      func g(x:Int, y:Int) -> Int {
        return 5
      }

      @_implements(Q, f(x:y:))
      func h(x:Int, y:Int) -> Int {
        return 6
      }

      @_implements(Equatable, ==(_:_:))
      public static func isEqual(_ lhs: S, _ rhs: S) -> Bool {
        return false
      }
      """,
        origin: "AttributeTests.testImplementsAttribute",
        syntaxVersion: "603.0.1",
        compilerRejects: "static methods may only be declared on a type"
    ),
    SwiftSnippet(label: "testImplementsAttributeBaseType#1", source: "@_implements(X<T>, f())", origin: "AttributeTests.testImplementsAttributeBaseType", syntaxVersion: "603.0.1", compilerRejects: "expected declaration"),
    SwiftSnippet(label: "testImplementsAttributeBaseType#2", source: "@_implements(X.Y, f())", origin: "AttributeTests.testImplementsAttributeBaseType", syntaxVersion: "603.0.1", compilerRejects: "expected declaration"),
    SwiftSnippet(label: "testImplementsAttributeBaseType#3", source: "@_implements(Any, f())", origin: "AttributeTests.testImplementsAttributeBaseType", syntaxVersion: "603.0.1", compilerRejects: "expected declaration"),
    SwiftSnippet(
        label: "testSemanticsAttribute#1",
        source: """
      @_semantics("constant_evaluable")
      func testRecursion(_ a: Int) -> Int {
        return a <= 0 ? 0 : testRecursion(a-1)
      }

      @_semantics("test_driver")
      internal func interpretRecursion() -> Int {
        return testRecursion(10)
      }
      """,
        origin: "AttributeTests.testSemanticsAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testObjcImplementationAttribute#1",
        source: """
      @_objcImplementation extension MyClass {
        func fn() {}
      }
      @_objcImplementation(Category) extension MyClass {
        func fn2() {}
      }
      """,
        origin: "AttributeTests.testObjcImplementationAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testSpiAttributeWithoutParameter#1", source: "@_spi() class Foo {}", origin: "AttributeTests.testSpiAttributeWithoutParameter", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testSpiAttributeWithUnderscore#1", source: "@_spi(_) class Foo {}", origin: "AttributeTests.testSpiAttributeWithUnderscore", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testSpiAttributeWithUnderscore#2", source: "@_spi(_) import Foo", origin: "AttributeTests.testSpiAttributeWithUnderscore", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testSilgenName#1",
        source: """
      @_silgen_name("testExclusivityBogusPC")
      private static func _testExclusivityBogusPC()
      """,
        origin: "AttributeTests.testSilgenName",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSilgenName#2",
        source: """
      @_silgen_name("") func foo() {}
      """,
        origin: "AttributeTests.testSilgenName",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSilgenName#3",
        source: """
      @_silgen_name("foo") var global: Int
      """,
        origin: "AttributeTests.testSilgenName",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSilgenName#4",
        source: """
      @_silgen_name(raw: "foo") var global: Int
      """,
        origin: "AttributeTests.testSilgenName",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testBackDeployed#1",
        source: """
      @backDeployed(before: macOS 12.0)
      struct Foo {}
      """,
        origin: "AttributeTests.testBackDeployed",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testBackDeployed#2",
        source: """
      @backDeployed(before: macos 12.0, iOS 15.0)
      struct Foo {}
      """,
        origin: "AttributeTests.testBackDeployed",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testBackDeployed#3",
        source: """
      @available(macOS 11.0, *)
      @backDeployed(before: _macOS12_1)
      public func backDeployTopLevelFunc2() -> Int { return 48 }
      """,
        origin: "AttributeTests.testBackDeployed",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testBackDeployed#4",
        source: """
      @_backDeploy(before: macOS 12.0)
      struct Foo {}
      """,
        origin: "AttributeTests.testBackDeployed",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testBackDeployed#5",
        source: """
      @_backDeploy(before: macos 12.0, iOS 15.0)
      struct Foo {}
      """,
        origin: "AttributeTests.testBackDeployed",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testBackDeployed#6",
        source: """
      @available(macOS 11.0, *)
      @_backDeploy(before: _macOS12_1)
      public func backDeployTopLevelFunc2() -> Int { return 48 }
      """,
        origin: "AttributeTests.testBackDeployed",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testExpose#1",
        source: """
      @_expose(Cxx) func foo() {}
      """,
        origin: "AttributeTests.testExpose",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testExpose#2",
        source: """
      @_expose(Cplusplus) func foo() {}
      """,
        origin: "AttributeTests.testExpose",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testExpose#3",
        source: """
      @_expose(!Cxx) func foo() {}
      """,
        origin: "AttributeTests.testExpose",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testExpose#4",
        source: """
      @_expose(Cxx, "baz") func foo() {}
      """,
        origin: "AttributeTests.testExpose",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOriginallyDefinedIn#1",
        source: """
      @_originallyDefinedIn(module: "ToasterKit", macOS 10.15)
      struct Vehicle {}
      """,
        origin: "AttributeTests.testOriginallyDefinedIn",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOriginallyDefinedIn#2",
        source: """
      @_originallyDefinedIn(module: "ToasterKit", macOS 10.15, iOS 13)
      struct Vehicle {}
      """,
        origin: "AttributeTests.testOriginallyDefinedIn",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOriginallyDefinedIn#3",
        source: """
      @_originallyDefinedIn(module: "ToasterKit", _iOS13Aligned)
      struct Vehicle {}
      """,
        origin: "AttributeTests.testOriginallyDefinedIn",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testUnavailableFromAsync#1",
        source: """
      @_unavailableFromAsync
      func foo() {}
      """,
        origin: "AttributeTests.testUnavailableFromAsync",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testUnavailableFromAsync#2",
        source: """
      @_unavailableFromAsync(message: "abc")
      func foo() {}
      """,
        origin: "AttributeTests.testUnavailableFromAsync",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testUnavailableFromAsync#3",
        source: """
      @_unavailableFromAsync(nope: "abc")
      func foo() {}
      """,
        origin: "AttributeTests.testUnavailableFromAsync",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testUnavailableFromAsync#4",
        source: """
      @_unavailableFromAsync(message: abc)
      func foo() {}
      """,
        origin: "AttributeTests.testUnavailableFromAsync",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEffects#1",
        source: """
      @_effects(notEscaping self.value**)
      func foo() {}
      """,
        origin: "AttributeTests.testEffects",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEffects#2",
        source: """
      @_effects(escaping self.value**.class*.value** => return.value**)
      func foo() {}
      """,
        origin: "AttributeTests.testEffects",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testEscapingOnClosureType#1", source: "func foo(closure: @escaping () -> Void) {}", origin: "AttributeTests.testEscapingOnClosureType", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testNonSendable#1",
        source: """
      @_nonSendable
      class NonSendableType {
      }
      """,
        origin: "AttributeTests.testNonSendable",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testDocumentationAttribute#1", source: "@_documentation(visibility: internal) @_exported import A", origin: "AttributeTests.testDocumentationAttribute", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testDocumentationAttribute#2", source: "@_documentation(visibility: package) @objc final public class Klass {}", origin: "AttributeTests.testDocumentationAttribute", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testDocumentationAttribute#3", source: "@_documentation(metadata: cool_stuff) public class SomeClass {}", origin: "AttributeTests.testDocumentationAttribute", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testDocumentationAttribute#4", source: #"@_documentation(metadata: "this is a longer string") public class OtherClass {}"#, origin: "AttributeTests.testDocumentationAttribute", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testDocumentationAttribute#5", source: #"@_documentation(visibility: internal, metadata: "this is a longer string") public class OtherClass {}"#, origin: "AttributeTests.testDocumentationAttribute", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testSendable#1", source: "func takeRepeater(_ f: @MainActor @Sendable @escaping () -> Int) {}", origin: "AttributeTests.testSendable", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testSendable#2", source: "takeRepesater { @MainActor @Sendable () -> Int in 0 }", origin: "AttributeTests.testSendable", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testLexicalLifetimes#1",
        source: """
      @_lexicalLifetimes
      func lexy(_ c: C) {}
      """,
        origin: "AttributeTests.testLexicalLifetimes",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testImportAttributes#1",
        source: """
      import A
      @_implementationOnly import B
      public import C
      package import D
      internal import E
      fileprivate import F
      private import G
      """,
        origin: "AttributeTests.testImportAttributes",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMacroRoleNames#1",
        source: """
      @attached(member, names: named(deinit))
      macro m()
      """,
        origin: "AttributeTests.testMacroRoleNames",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMacroRoleNames#2",
        source: """
      @attached(member, names: named(init))
      macro m()
      """,
        origin: "AttributeTests.testMacroRoleNames",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMacroRoleNames#3",
        source: """
      @attached(member, names: named(init(a:b:)))
      macro m()
      """,
        origin: "AttributeTests.testMacroRoleNames",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMacroRoleNames#4",
        source: """
      @attached(member, names: named(subscript))
      macro m()
      """,
        origin: "AttributeTests.testMacroRoleNames",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMacroRoleNames#5",
        source: """
      @attached(declaration, names: named(subscript(a:b:)))
      macro m()
      """,
        origin: "AttributeTests.testMacroRoleNames",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMacroRoleNames#6",
        source: """
      @freestanding(declaration, names: named(deinit))
      macro m()
      """,
        origin: "AttributeTests.testMacroRoleNames",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMacroRoleNames#7",
        source: """
      @freestanding(declaration, names: named(init))
      macro m()
      """,
        origin: "AttributeTests.testMacroRoleNames",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMacroRoleNames#8",
        source: """
      @freestanding(declaration, names: named(init(a:b:)))
      macro m()
      """,
        origin: "AttributeTests.testMacroRoleNames",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMacroRoleNames#9",
        source: """
      @freestanding(member, names: named(subscript))
      macro m()
      """,
        origin: "AttributeTests.testMacroRoleNames",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMacroRoleNames#10",
        source: """
      @freestanding(member, names: named(subscript(a:b:)))
      macro m()
      """,
        origin: "AttributeTests.testMacroRoleNames",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMacroRoleNames#11",
        source: """
      @attached(member, names: named(`class`))
      macro m()
      """,
        origin: "AttributeTests.testMacroRoleNames",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAttachedExtensionAttribute#1",
        source: """
      @attached(extension)
      macro m()
      """,
        origin: "AttributeTests.testAttachedExtensionAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAttachedExtensionAttribute#2",
        source: """
      @attached(extension, names: named(test))
      macro m()
      """,
        origin: "AttributeTests.testAttachedExtensionAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testConventionAttributeInArrayType#1",
        source: """
      _ = [@convention(c, cType: "int (*)(int)") (Int32) -> Int32]()
      """,
        origin: "AttributeTests.testConventionAttributeInArrayType",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testIsolatedTypeAttribute#1",
        source: """
      var fn: @isolated(any) () -> ()
      """,
        origin: "AttributeTests.testIsolatedTypeAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testIsolatedTypeAttribute#2",
        source: """
      var fn: @isolated(sdfhsdfi) () -> ()
      """,
        origin: "AttributeTests.testIsolatedTypeAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testIsolatedTypeAttribute#3",
        source: """
      var fn: @isolated(any) @convention(swift) () -> ()
      """,
        origin: "AttributeTests.testIsolatedTypeAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testIsolatedTypeAttribute#4",
        source: """
      var fn: @convention(swift) @isolated(any) () -> ()
      """,
        origin: "AttributeTests.testIsolatedTypeAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testIsolatedTypeAttribute#5",
        source: """
      var array = [@isolated(any) @convention(swift) () -> ()]()
      """,
        origin: "AttributeTests.testIsolatedTypeAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testIsolatedTypeAttribute#6",
        source: """
      var array = [@convention(swift) @isolated(any) () -> ()]()
      """,
        origin: "AttributeTests.testIsolatedTypeAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testABIAttribute#1",
        source: """
      @abi(func fn() -> Int)
      func fn1() -> Int { }
      """,
        origin: "AttributeTests.testABIAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testABIAttribute#2",
        source: """
      @abi(associatedtype AssocTy)
      associatedtype AssocTy
      """,
        origin: "AttributeTests.testABIAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testABIAttribute#3",
        source: """
      @abi(deinit)
      deinit {}
      """,
        origin: "AttributeTests.testABIAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testABIAttribute#4",
        source: """
      enum EnumCaseDeclNotParsedAtTopLevel {
        @abi(case someCase)
        case someCase
      }
      """,
        origin: "AttributeTests.testABIAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testABIAttribute#5",
        source: """
      @abi(func fn())
      func fn()
      """,
        origin: "AttributeTests.testABIAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testABIAttribute#6",
        source: """
      @abi(init())
      init() {}
      """,
        origin: "AttributeTests.testABIAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testABIAttribute#7",
        source: """
      @abi(subscript(i: Int) -> Element)
      subscript(i: Int) -> Element {}
      """,
        origin: "AttributeTests.testABIAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testABIAttribute#8",
        source: """
      @abi(typealias Typealias = @escaping () -> Void)
      typealias Typealias = () -> Void
      """,
        origin: "AttributeTests.testABIAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testABIAttribute#9",
        source: """
      @abi(let c1, c2)
      let c1, c2
      """,
        origin: "AttributeTests.testABIAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testABIAttribute#10",
        source: """
      @abi(var v1, v2)
      var v1, v2
      """,
        origin: "AttributeTests.testABIAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testABIAttribute#11",
        source: """
      @abi(associatedtype AssocTy = T)
      associatedtype AssocTy
      """,
        origin: "AttributeTests.testABIAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testABIAttribute#12",
        source: """
      @abi(deinit {})
      deinit {}
      """,
        origin: "AttributeTests.testABIAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testABIAttribute#13",
        source: """
      enum EnumCaseDeclNotParsedAtTopLevel {
        @abi(case someCase = 42)
        case someCase
      }
      """,
        origin: "AttributeTests.testABIAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testABIAttribute#14",
        source: """
      @abi(func fn() {})
      func fn()
      """,
        origin: "AttributeTests.testABIAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testABIAttribute#15",
        source: """
      @abi(init() {})
      init() {}
      """,
        origin: "AttributeTests.testABIAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testABIAttribute#16",
        source: """
      @abi(subscript(i: Int) -> Element { get {} set {} })
      subscript(i: Int) -> Element {}
      """,
        origin: "AttributeTests.testABIAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testABIAttribute#17",
        source: """
      @abi(let c1 = 1, c2 = 2)
      let c1, c2
      """,
        origin: "AttributeTests.testABIAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testABIAttribute#18",
        source: """
      @abi(var v1 = 1, v2 = 2)
      var v1, v2
      """,
        origin: "AttributeTests.testABIAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testABIAttribute#19",
        source: """
      @abi(var v3 { get {} set {} })
      var v3
      """,
        origin: "AttributeTests.testABIAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testLifetimeAttribute#1",
        source: """
      struct NE: ~Escapable {}

      @lifetime(ne)
      func derive1(ne: NE) -> NE { ne }

      @lifetime(borrow ne)
      func derive2(ne: borrowing NE) -> NE { ne }

      @lifetime(ne1, n2)
      func derive3(ne1: NE, ne2: NE) -> NE { ne1 }

      @lifetime(borrow ne1, n2)
      func derive4(ne1: NE, ne2: NE) -> NE { ne1 }

      @lifetime(neOut: ne)
      func derive5(ne: NE, neOut: inout NE) -> NE { neOut = ne }

      @lifetime(neOut: borrow ne)
      func derive6(ne: borrowing NE, neOut: inout NE) -> NE { neOut = ne }
      """,
        origin: "AttributeTests.testLifetimeAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAttributeMainActorClosure#1",
        source: """
      { @MainActor (arg) in }
      """,
        origin: "AttributeTests.testAttributeMainActorClosure",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypeAttributeInExprContext#1",
        source: """
      var _ = [@Sendable () -> Void]()
      """,
        origin: "AttributeTests.testTypeAttributeInExprContext",
        syntaxVersion: "603.0.1"
    ),
]


// MARK: - Test Suite

extension SwiftSyntax603Tests {

@Suite("Attributes")
struct AttributeSyntaxTests {

    @Test("SwiftSyntax accepts", .tags(.swiftSyntaxReference), arguments: attributeSnippets)
    func swiftSyntaxAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let parsed = Parser.parse(source: snippet.source)
        #expect(!parsed.hasError, "SwiftSyntax parse error for: \(snippet.source)")
    }

    @Test("Advent accepts", arguments: attributeSnippets)
    func adventAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let result = try adventParse(snippet)
        #expect(result != nil, "Advent failed to parse: \(snippet.source)")
    }

    @Test("no residual ambiguity", arguments: attributeSnippets)
    func unambiguous(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        guard let result = try adventParse(snippet) else {
            Issue.record("Advent failed to parse: \(snippet.source)")
            return
        }
        #expect(result.isUnambiguous,
                "Residual ambiguity in '\(snippet.diagnosticID)': \(result.builder.diagnostics)")
    }

    @Test("trees match", arguments: attributeSnippets)
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

let attribute604Snippets: [SwiftSnippet] = [
    SwiftSnippet(
        label: "testSpecializeAttribute#1",
        source: """
      @_specialize(where @_noMetdata T : _BridgeObject)
      func foo(_ t: T) {}
      """,
        origin: "AttributeTests.testSpecializeAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05",
        compilerRejects: "SIL layout constraint (_Trivial(32) / @_noMetdata) not modelled"
    ),
    SwiftSnippet(
        label: "testSpecializeAttribute#2",
        source: """
      @_specialize(where @_noMetdata T : _TrivialStride(64))
      func foo(_ t: T) {}
      """,
        origin: "AttributeTests.testSpecializeAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05",
        compilerRejects: "SIL layout constraint (_Trivial(32) / @_noMetdata) not modelled"
    ),
    SwiftSnippet(
        label: "testSpecializeAttribute#3",
        source: """
      @specialized(where T : Int)
      func foo(_ t: T) {}
      """,
        origin: "AttributeTests.testSpecializeAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSpecializeWithAvailability#1",
        source: """
      @_specialize(exported: true, kind: full, availability: iOS, introduced: 15.4; where T == Swift.Int)
      public func specializeWithAvailability<T>(_ t: T) { }
      """,
        origin: "AttributeTests.testSpecializeWithAvailability",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testObjCAttribute#1",
        source: """
      @objc(zeroArg)
      class A { }

      @objc(:::x::)
      func f(_: Int, _: Int, _: Int, _: Int, _: Int) { }
      """,
        origin: "AttributeTests.testObjCAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testObjCAttribute#2",
        source: """
      @objc(_:)
      func f(_: Int)
      """,
        origin: "AttributeTests.testObjCAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRethrowsAttribute#1",
        source: """
      @rethrows
      protocol P { }
      """,
        origin: "AttributeTests.testRethrowsAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAutoclosureAttribute#1",
        source: """
      func f(in: @autoclosure () -> Int) { }
      func g(in: @autoclosure @escaping () -> Int) { }
      """,
        origin: "AttributeTests.testAutoclosureAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDifferentiableAttribute#1",
        source: """
      func f(in: @differentiable(reverse) (Int) -> Int) { }
      func f(in: @differentiable(reverse, wrt: a) (Int) -> Int) { }
      """,
        origin: "AttributeTests.testDifferentiableAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testQualifiedAttribute#1",
        source: """
      @_Concurrency.MainActor(unsafe) public struct Image : SwiftUI.View {}
      """,
        origin: "AttributeTests.testQualifiedAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDerivativeAttribute#1",
        source: """
      @inlinable
      @differentiable(reverse, wrt: self)
      public func differentiableMap<Result: Differentiable>(
        _ body: @differentiable(reverse) (Element) -> Result
      ) -> [Result] {
        map(body)
      }
      """,
        origin: "AttributeTests.testDerivativeAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDerivativeAttribute#2",
        source: """
      @inlinable
      @differentiable(reverse, wrt: (self, initialResult))
      public func differentiableReduce<Result: Differentiable>(
        _ initialResult: Result,
        _ nextPartialResult: @differentiable(reverse) (Result, Element) -> Result
      ) -> Result {
        reduce(initialResult, nextPartialResult)
      }
      """,
        origin: "AttributeTests.testDerivativeAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDerivativeAttribute#3",
        source: """
      @inlinable
      @derivative(of: differentiableReduce)
      internal func _vjpDifferentiableReduce<Result: Differentiable>(
        _ initialResult: Result,
        _ nextPartialResult: @differentiable(reverse) (Result, Element) -> Result
      ) -> (
        value: Result,
        pullback: (Result.TangentVector)
          -> (Array.TangentVector, Result.TangentVector)
      ) {}
      """,
        origin: "AttributeTests.testDerivativeAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDerivativeAttribute#4",
        source: """
      @derivative(of: Self.other)
      func foo() {}
      """,
        origin: "AttributeTests.testDerivativeAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDerivativeAttribute#5",
        source: """
      @derivative(of: Foo.Self.other)
      func foo() {}
      """,
        origin: "AttributeTests.testDerivativeAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTransposeAttribute#1",
        source: """
      @transpose(of: S.instanceMethod, wrt: self)
      static func transposeInstanceMethodWrtSelf(_ other: S, t: S) -> S {
        other + t
      }
      """,
        origin: "AttributeTests.testTransposeAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTransposeAttribute#2",
        source: """
      @transpose(of: +)
      func addTranspose(_ v: Float) -> (Float, Float) {
        return (v, v)
      }
      """,
        origin: "AttributeTests.testTransposeAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTransposeAttribute#3",
        source: """
      @transpose(of: -, wrt: (0, 1))
      func subtractTranspose(_ v: Float) -> (Float, Float) {
        return (v, -v)
      }
      """,
        origin: "AttributeTests.testTransposeAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTransposeAttribute#4",
        source: """
      @transpose(of: Float.-, wrt: (0, 1))
      func subtractTranspose(_ v: Float) -> (Float, Float) {
        return (v, -v)
      }
      """,
        origin: "AttributeTests.testTransposeAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testImplementsAttribute#1",
        source: """
      @_implements(P, f0())
      func g0() -> Int {
        return 10
      }

      @_implements(P, f(x:y:))
      func g(x:Int, y:Int) -> Int {
        return 5
      }

      @_implements(Q, f(x:y:))
      func h(x:Int, y:Int) -> Int {
        return 6
      }

      @_implements(Equatable, ==(_:_:))
      public static func isEqual(_ lhs: S, _ rhs: S) -> Bool {
        return false
      }
      """,
        origin: "AttributeTests.testImplementsAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05",
        compilerRejects: "static methods may only be declared on a type"
    ),
    SwiftSnippet(label: "testImplementsAttributeBaseType#1", source: "@_implements(X<T>, f())", origin: "AttributeTests.testImplementsAttributeBaseType", syntaxVersion: "604.0.0-prerelease-2026-06-05", compilerRejects: "expected declaration"),
    SwiftSnippet(label: "testImplementsAttributeBaseType#2", source: "@_implements(X.Y, f())", origin: "AttributeTests.testImplementsAttributeBaseType", syntaxVersion: "604.0.0-prerelease-2026-06-05", compilerRejects: "expected declaration"),
    SwiftSnippet(label: "testImplementsAttributeBaseType#3", source: "@_implements(X.Y<T>, f())", origin: "AttributeTests.testImplementsAttributeBaseType", syntaxVersion: "604.0.0-prerelease-2026-06-05", compilerRejects: "expected declaration"),
    SwiftSnippet(label: "testImplementsAttributeBaseType#4", source: "@_implements(X.Type, f())", origin: "AttributeTests.testImplementsAttributeBaseType", syntaxVersion: "604.0.0-prerelease-2026-06-05", compilerRejects: "expected declaration"),
    SwiftSnippet(label: "testImplementsAttributeBaseType#5", source: "@_implements(X.Protocol, f())", origin: "AttributeTests.testImplementsAttributeBaseType", syntaxVersion: "604.0.0-prerelease-2026-06-05", compilerRejects: "expected declaration"),
    SwiftSnippet(label: "testImplementsAttributeBaseType#6", source: "@_implements(X?, f())", origin: "AttributeTests.testImplementsAttributeBaseType", syntaxVersion: "604.0.0-prerelease-2026-06-05", compilerRejects: "expected declaration"),
    SwiftSnippet(label: "testImplementsAttributeBaseType#7", source: "@_implements(X!, f())", origin: "AttributeTests.testImplementsAttributeBaseType", syntaxVersion: "604.0.0-prerelease-2026-06-05", compilerRejects: "expected declaration"),
    SwiftSnippet(label: "testImplementsAttributeBaseType#8", source: "@_implements([X], f())", origin: "AttributeTests.testImplementsAttributeBaseType", syntaxVersion: "604.0.0-prerelease-2026-06-05", compilerRejects: "expected declaration"),
    SwiftSnippet(label: "testImplementsAttributeBaseType#9", source: "@_implements([X : Y], f())", origin: "AttributeTests.testImplementsAttributeBaseType", syntaxVersion: "604.0.0-prerelease-2026-06-05", compilerRejects: "expected declaration"),
    SwiftSnippet(label: "testImplementsAttributeBaseType#10", source: "@_implements((), f())", origin: "AttributeTests.testImplementsAttributeBaseType", syntaxVersion: "604.0.0-prerelease-2026-06-05", compilerRejects: "expected declaration"),
    SwiftSnippet(label: "testImplementsAttributeBaseType#11", source: "@_implements((X), f())", origin: "AttributeTests.testImplementsAttributeBaseType", syntaxVersion: "604.0.0-prerelease-2026-06-05", compilerRejects: "expected declaration"),
    SwiftSnippet(label: "testImplementsAttributeBaseType#12", source: "@_implements((X, X), f())", origin: "AttributeTests.testImplementsAttributeBaseType", syntaxVersion: "604.0.0-prerelease-2026-06-05", compilerRejects: "expected declaration"),
    SwiftSnippet(label: "testImplementsAttributeBaseType#13", source: "@_implements(Any, f())", origin: "AttributeTests.testImplementsAttributeBaseType", syntaxVersion: "604.0.0-prerelease-2026-06-05", compilerRejects: "expected declaration"),
    SwiftSnippet(label: "testImplementsAttributeBaseType#14", source: "@_implements(Self, f())", origin: "AttributeTests.testImplementsAttributeBaseType", syntaxVersion: "604.0.0-prerelease-2026-06-05", compilerRejects: "expected declaration"),
    SwiftSnippet(label: "testImplementsAttributeBaseType#15", source: "@_implements(X & Y, f())", origin: "AttributeTests.testImplementsAttributeBaseType", syntaxVersion: "604.0.0-prerelease-2026-06-05", compilerRejects: "expected declaration"),
    SwiftSnippet(label: "testImplementsAttributeBaseType#16", source: "@_implements(any X & Y, f())", origin: "AttributeTests.testImplementsAttributeBaseType", syntaxVersion: "604.0.0-prerelease-2026-06-05", compilerRejects: "expected declaration"),
    SwiftSnippet(label: "testImplementsAttributeBaseType#17", source: "@_implements((X) -> Y, f())", origin: "AttributeTests.testImplementsAttributeBaseType", syntaxVersion: "604.0.0-prerelease-2026-06-05", compilerRejects: "expected declaration"),
    SwiftSnippet(
        label: "testSemanticsAttribute#1",
        source: """
      @_semantics("constant_evaluable")
      func testRecursion(_ a: Int) -> Int {
        return a <= 0 ? 0 : testRecursion(a-1)
      }

      @_semantics("test_driver")
      internal func interpretRecursion() -> Int {
        return testRecursion(10)
      }
      """,
        origin: "AttributeTests.testSemanticsAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testObjcImplementationAttribute#1",
        source: """
      @_objcImplementation extension MyClass {
        func fn() {}
      }
      @_objcImplementation(Category) extension MyClass {
        func fn2() {}
      }
      """,
        origin: "AttributeTests.testObjcImplementationAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testSpiAttributeWithoutParameter#1", source: "@_spi() class Foo {}", origin: "AttributeTests.testSpiAttributeWithoutParameter", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testSpiAttributeWithUnderscore#1", source: "@_spi(_) class Foo {}", origin: "AttributeTests.testSpiAttributeWithUnderscore", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testSpiAttributeWithUnderscore#2", source: "@_spi(_) import Foo", origin: "AttributeTests.testSpiAttributeWithUnderscore", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testSilgenName#1",
        source: """
      @_silgen_name("testExclusivityBogusPC")
      private static func _testExclusivityBogusPC()
      """,
        origin: "AttributeTests.testSilgenName",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSilgenName#2",
        source: """
      @_silgen_name("") func foo() {}
      """,
        origin: "AttributeTests.testSilgenName",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSilgenName#3",
        source: """
      @_silgen_name("foo") var global: Int
      """,
        origin: "AttributeTests.testSilgenName",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSilgenName#4",
        source: """
      @_silgen_name(raw: "foo") var global: Int
      """,
        origin: "AttributeTests.testSilgenName",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testBackDeployed#1",
        source: """
      @backDeployed(before: macOS 12.0)
      struct Foo {}
      """,
        origin: "AttributeTests.testBackDeployed",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testBackDeployed#2",
        source: """
      @backDeployed(before: macos 12.0, iOS 15.0)
      struct Foo {}
      """,
        origin: "AttributeTests.testBackDeployed",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testBackDeployed#3",
        source: """
      @available(macOS 11.0, *)
      @backDeployed(before: _macOS12_1)
      public func backDeployTopLevelFunc2() -> Int { return 48 }
      """,
        origin: "AttributeTests.testBackDeployed",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testBackDeployed#4",
        source: """
      @_backDeploy(before: macOS 12.0)
      struct Foo {}
      """,
        origin: "AttributeTests.testBackDeployed",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testBackDeployed#5",
        source: """
      @_backDeploy(before: macos 12.0, iOS 15.0)
      struct Foo {}
      """,
        origin: "AttributeTests.testBackDeployed",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testBackDeployed#6",
        source: """
      @available(macOS 11.0, *)
      @_backDeploy(before: _macOS12_1)
      public func backDeployTopLevelFunc2() -> Int { return 48 }
      """,
        origin: "AttributeTests.testBackDeployed",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testExpose#1",
        source: """
      @_expose(Cxx) func foo() {}
      """,
        origin: "AttributeTests.testExpose",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testExpose#2",
        source: """
      @_expose(Cplusplus) func foo() {}
      """,
        origin: "AttributeTests.testExpose",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testExpose#3",
        source: """
      @_expose(!Cxx) func foo() {}
      """,
        origin: "AttributeTests.testExpose",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testExpose#4",
        source: """
      @_expose(Cxx, "baz") func foo() {}
      """,
        origin: "AttributeTests.testExpose",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOriginallyDefinedIn#1",
        source: """
      @_originallyDefinedIn(module: "ToasterKit", macOS 10.15)
      struct Vehicle {}
      """,
        origin: "AttributeTests.testOriginallyDefinedIn",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOriginallyDefinedIn#2",
        source: """
      @_originallyDefinedIn(module: "ToasterKit", macOS 10.15, iOS 13)
      struct Vehicle {}
      """,
        origin: "AttributeTests.testOriginallyDefinedIn",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOriginallyDefinedIn#3",
        source: """
      @_originallyDefinedIn(module: "ToasterKit", _iOS13Aligned)
      struct Vehicle {}
      """,
        origin: "AttributeTests.testOriginallyDefinedIn",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testUnavailableFromAsync#1",
        source: """
      @_unavailableFromAsync
      func foo() {}
      """,
        origin: "AttributeTests.testUnavailableFromAsync",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testUnavailableFromAsync#2",
        source: """
      @_unavailableFromAsync(message: "abc")
      func foo() {}
      """,
        origin: "AttributeTests.testUnavailableFromAsync",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testUnavailableFromAsync#3",
        source: """
      @_unavailableFromAsync(nope: "abc")
      func foo() {}
      """,
        origin: "AttributeTests.testUnavailableFromAsync",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testUnavailableFromAsync#4",
        source: """
      @_unavailableFromAsync(message: abc)
      func foo() {}
      """,
        origin: "AttributeTests.testUnavailableFromAsync",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEffects#1",
        source: """
      @_effects(notEscaping self.value**)
      func foo() {}
      """,
        origin: "AttributeTests.testEffects",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEffects#2",
        source: """
      @_effects(escaping self.value**.class*.value** => return.value**)
      func foo() {}
      """,
        origin: "AttributeTests.testEffects",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testEscapingOnClosureType#1", source: "func foo(closure: @escaping () -> Void) {}", origin: "AttributeTests.testEscapingOnClosureType", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testNonSendable#1",
        source: """
      @_nonSendable
      class NonSendableType {
      }
      """,
        origin: "AttributeTests.testNonSendable",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testDocumentationAttribute#1", source: "@_documentation(visibility: internal) @_exported import A", origin: "AttributeTests.testDocumentationAttribute", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testDocumentationAttribute#2", source: "@_documentation(visibility: package) @objc final public class Klass {}", origin: "AttributeTests.testDocumentationAttribute", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testDocumentationAttribute#3", source: "@_documentation(metadata: cool_stuff) public class SomeClass {}", origin: "AttributeTests.testDocumentationAttribute", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testDocumentationAttribute#4", source: #"@_documentation(metadata: "this is a longer string") public class OtherClass {}"#, origin: "AttributeTests.testDocumentationAttribute", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testDocumentationAttribute#5", source: #"@_documentation(visibility: internal, metadata: "this is a longer string") public class OtherClass {}"#, origin: "AttributeTests.testDocumentationAttribute", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testSendable#1", source: "func takeRepeater(_ f: @MainActor @Sendable @escaping () -> Int) {}", origin: "AttributeTests.testSendable", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testSendable#2", source: "takeRepesater { @MainActor @Sendable () -> Int in 0 }", origin: "AttributeTests.testSendable", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testLexicalLifetimes#1",
        source: """
      @_lexicalLifetimes
      func lexy(_ c: C) {}
      """,
        origin: "AttributeTests.testLexicalLifetimes",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testImportAttributes#1",
        source: """
      import A
      @_implementationOnly import B
      public import C
      package import D
      internal import E
      fileprivate import F
      private import G
      """,
        origin: "AttributeTests.testImportAttributes",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMacroRoleNames#1",
        source: """
      @attached(member, names: named(deinit))
      macro m()
      """,
        origin: "AttributeTests.testMacroRoleNames",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMacroRoleNames#2",
        source: """
      @attached(member, names: named(init))
      macro m()
      """,
        origin: "AttributeTests.testMacroRoleNames",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMacroRoleNames#3",
        source: """
      @attached(member, names: named(init(a:b:)))
      macro m()
      """,
        origin: "AttributeTests.testMacroRoleNames",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMacroRoleNames#4",
        source: """
      @attached(member, names: named(subscript))
      macro m()
      """,
        origin: "AttributeTests.testMacroRoleNames",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMacroRoleNames#5",
        source: """
      @attached(declaration, names: named(subscript(a:b:)))
      macro m()
      """,
        origin: "AttributeTests.testMacroRoleNames",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMacroRoleNames#6",
        source: """
      @freestanding(declaration, names: named(deinit))
      macro m()
      """,
        origin: "AttributeTests.testMacroRoleNames",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMacroRoleNames#7",
        source: """
      @freestanding(declaration, names: named(init))
      macro m()
      """,
        origin: "AttributeTests.testMacroRoleNames",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMacroRoleNames#8",
        source: """
      @freestanding(declaration, names: named(init(a:b:)))
      macro m()
      """,
        origin: "AttributeTests.testMacroRoleNames",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMacroRoleNames#9",
        source: """
      @freestanding(member, names: named(subscript))
      macro m()
      """,
        origin: "AttributeTests.testMacroRoleNames",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMacroRoleNames#10",
        source: """
      @freestanding(member, names: named(subscript(a:b:)))
      macro m()
      """,
        origin: "AttributeTests.testMacroRoleNames",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMacroRoleNames#11",
        source: """
      @attached(member, names: named(`class`))
      macro m()
      """,
        origin: "AttributeTests.testMacroRoleNames",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAttachedExtensionAttribute#1",
        source: """
      @attached(extension)
      macro m()
      """,
        origin: "AttributeTests.testAttachedExtensionAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAttachedExtensionAttribute#2",
        source: """
      @attached(extension, names: named(test))
      macro m()
      """,
        origin: "AttributeTests.testAttachedExtensionAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testConventionAttributeInArrayType#1",
        source: """
      _ = [@convention(c, cType: "int (*)(int)") (Int32) -> Int32]()
      """,
        origin: "AttributeTests.testConventionAttributeInArrayType",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIsolatedTypeAttribute#1",
        source: """
      var fn: @isolated(any) () -> ()
      """,
        origin: "AttributeTests.testIsolatedTypeAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIsolatedTypeAttribute#2",
        source: """
      var fn: @isolated(sdfhsdfi) () -> ()
      """,
        origin: "AttributeTests.testIsolatedTypeAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIsolatedTypeAttribute#3",
        source: """
      var fn: @isolated(any) @convention(swift) () -> ()
      """,
        origin: "AttributeTests.testIsolatedTypeAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIsolatedTypeAttribute#4",
        source: """
      var fn: @convention(swift) @isolated(any) () -> ()
      """,
        origin: "AttributeTests.testIsolatedTypeAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIsolatedTypeAttribute#5",
        source: """
      var array = [@isolated(any) @convention(swift) () -> ()]()
      """,
        origin: "AttributeTests.testIsolatedTypeAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIsolatedTypeAttribute#6",
        source: """
      var array = [@convention(swift) @isolated(any) () -> ()]()
      """,
        origin: "AttributeTests.testIsolatedTypeAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testABIAttribute#1",
        source: """
      @abi(func fn() -> Int)
      func fn1() -> Int { }
      """,
        origin: "AttributeTests.testABIAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testABIAttribute#2",
        source: """
      @abi(associatedtype AssocTy)
      associatedtype AssocTy
      """,
        origin: "AttributeTests.testABIAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testABIAttribute#3",
        source: """
      @abi(deinit)
      deinit {}
      """,
        origin: "AttributeTests.testABIAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testABIAttribute#4",
        source: """
      enum EnumCaseDeclNotParsedAtTopLevel {
        @abi(case someCase)
        case someCase
      }
      """,
        origin: "AttributeTests.testABIAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testABIAttribute#5",
        source: """
      @abi(func fn())
      func fn()
      """,
        origin: "AttributeTests.testABIAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testABIAttribute#6",
        source: """
      @abi(init())
      init() {}
      """,
        origin: "AttributeTests.testABIAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testABIAttribute#7",
        source: """
      @abi(subscript(i: Int) -> Element)
      subscript(i: Int) -> Element {}
      """,
        origin: "AttributeTests.testABIAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testABIAttribute#8",
        source: """
      @abi(typealias Typealias = @escaping () -> Void)
      typealias Typealias = () -> Void
      """,
        origin: "AttributeTests.testABIAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testABIAttribute#9",
        source: """
      @abi(let c1, c2)
      let c1, c2
      """,
        origin: "AttributeTests.testABIAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testABIAttribute#10",
        source: """
      @abi(var v1, v2)
      var v1, v2
      """,
        origin: "AttributeTests.testABIAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testABIAttribute#11",
        source: """
      @abi(associatedtype AssocTy = T)
      associatedtype AssocTy
      """,
        origin: "AttributeTests.testABIAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testABIAttribute#12",
        source: """
      @abi(deinit {})
      deinit {}
      """,
        origin: "AttributeTests.testABIAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testABIAttribute#13",
        source: """
      enum EnumCaseDeclNotParsedAtTopLevel {
        @abi(case someCase = 42)
        case someCase
      }
      """,
        origin: "AttributeTests.testABIAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testABIAttribute#14",
        source: """
      @abi(func fn() {})
      func fn()
      """,
        origin: "AttributeTests.testABIAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testABIAttribute#15",
        source: """
      @abi(init() {})
      init() {}
      """,
        origin: "AttributeTests.testABIAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testABIAttribute#16",
        source: """
      @abi(subscript(i: Int) -> Element { get {} set {} })
      subscript(i: Int) -> Element {}
      """,
        origin: "AttributeTests.testABIAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testABIAttribute#17",
        source: """
      @abi(let c1 = 1, c2 = 2)
      let c1, c2
      """,
        origin: "AttributeTests.testABIAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testABIAttribute#18",
        source: """
      @abi(var v1 = 1, v2 = 2)
      var v1, v2
      """,
        origin: "AttributeTests.testABIAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testABIAttribute#19",
        source: """
      @abi(var v3 { get {} set {} })
      var v3
      """,
        origin: "AttributeTests.testABIAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testLifetimeAttribute#1",
        source: """
      struct NE: ~Escapable {}

      @lifetime(ne)
      func derive1(ne: NE) -> NE { ne }

      @lifetime(borrow ne)
      func derive2(ne: borrowing NE) -> NE { ne }

      @lifetime(ne1, n2)
      func derive3(ne1: NE, ne2: NE) -> NE { ne1 }

      @lifetime(borrow ne1, n2)
      func derive4(ne1: NE, ne2: NE) -> NE { ne1 }

      @lifetime(neOut: ne)
      func derive5(ne: NE, neOut: inout NE) -> NE { neOut = ne }

      @lifetime(neOut: borrow ne)
      func derive6(ne: borrowing NE, neOut: inout NE) -> NE { neOut = ne }
      """,
        origin: "AttributeTests.testLifetimeAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAttributeMainActorClosure#1",
        source: """
      { @MainActor (arg) in }
      """,
        origin: "AttributeTests.testAttributeMainActorClosure",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypeAttributeInExprContext#1",
        source: """
      var _ = [@Sendable () -> Void]()
      """,
        origin: "AttributeTests.testTypeAttributeInExprContext",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
]

extension SwiftSyntax604Tests {

@Suite("Attributes")
struct AttributeSyntax604Tests {

    @Test("SwiftSyntax accepts", .tags(.swiftSyntaxReference), arguments: attribute604Snippets)
    func swiftSyntaxAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        #expect(!swiftSyntaxReferenceHasError(snippet), "SwiftSyntax parse error for: \(snippet.source)")
    }

    @Test("Advent accepts", arguments: attribute604Snippets)
    func adventAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let result = try adventParse(snippet)
        #expect(result != nil, "Advent failed to parse: \(snippet.source)")
    }

    @Test("no residual ambiguity", arguments: attribute604Snippets)
    func unambiguous(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        guard let result = try adventParse(snippet) else {
            Issue.record("Advent failed to parse: \(snippet.source)")
            return
        }
        #expect(result.isUnambiguous,
                "Residual ambiguity in '\(snippet.diagnosticID)': \(result.builder.diagnostics)")
    }

    @Test("trees match", arguments: attribute604Snippets)
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

//
//  SwiftSyntaxTranslated.swift
//  AdventTests
//
//  Snippets extracted from SwiftSyntax translated/ test files (603.0.1).
//  These are 90 test files ported from the legacy Swift compiler test suite.
//  See SwiftSyntaxTests.swift for shared infrastructure.
//

import Testing
import Foundation
import SwiftSyntax
import SwiftParser

// MARK: - Snippet Catalog

let translatedSnippets: [SwiftSnippet] = [
    SwiftSnippet(
        label: "testAlwaysEmitConformanceMetadataAttr#1",
        source: """
      @_alwaysEmitConformanceMetadata
      protocol Test {}
      """,
        origin: "AlwaysEmitConformanceMetadataAttrTests.testAlwaysEmitConformanceMetadataAttr",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAsyncSyntax1#1",
        source: """
      func asyncGlobal1() async { }
      func asyncGlobal2() async throws { }
      """,
        origin: "AsyncSyntaxTests.testAsyncSyntax1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAsyncSyntax2#1",
        source: """
      typealias AsyncFunc1 = () async -> ()
      typealias AsyncFunc2 = () async throws -> ()
      typealias AsyncFunc3 = (_ a: Bool, _ b: Bool) async throws -> ()
      """,
        origin: "AsyncSyntaxTests.testAsyncSyntax2",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAsyncSyntax3#1",
        source: """
      func testTypeExprs() {
        let _ = [() async -> ()]()
        let _ = [() async throws -> ()]()
      }
      """,
        origin: "AsyncSyntaxTests.testAsyncSyntax3",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAsyncSyntax4#1",
        source: """
      func testAwaitOperator() async {
        let _ = await asyncGlobal1()
      }
      """,
        origin: "AsyncSyntaxTests.testAsyncSyntax4",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAsyncSyntax5#1",
        source: """
      func testAsyncClosure() {
        let _ = { () async in 5 }
        let _ = { () throws in 5 }
        let _ = { () async throws in 5 }
      }
      """,
        origin: "AsyncSyntaxTests.testAsyncSyntax5",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAsyncSyntax6#1",
        source: """
      func testAwait() async {
        let _ = await asyncGlobal1()
      }
      """,
        origin: "AsyncSyntaxTests.testAsyncSyntax6",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAsync1#1",
        source: """
      // Parsing function declarations with 'async'
      func asyncGlobal1() async { }
      func asyncGlobal2() async throws { }
      """,
        origin: "AsyncTests.testAsync1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAsync10a#1",
        source: """
      typealias AsyncFunc1 = () async -> ()
      """,
        origin: "AsyncTests.testAsync10a",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAsync10b#1",
        source: """
      typealias AsyncFunc2 = () async throws -> ()
      """,
        origin: "AsyncTests.testAsync10b",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAsync11a#1",
        source: """
      let _ = [() async -> ()]()
      """,
        origin: "AsyncTests.testAsync11a",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAsync11b#1",
        source: """
      let _ = [() async throws -> ()]()
      """,
        origin: "AsyncTests.testAsync11b",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAsync12#1",
        source: """
      // Parsing await syntax.
      struct MyFuture {
        func await() -> Int { 0 }
      }
      """,
        origin: "AsyncTests.testAsync12",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAsync13#1",
        source: """
      func testAwaitExpr() async {
        let _ = await asyncGlobal1()
        let myFuture = MyFuture()
        let _ = myFuture.await()
      }
      """,
        origin: "AsyncTests.testAsync13",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAsync14#1",
        source: """
      func getIntSomeday() async -> Int { 5 }
      """,
        origin: "AsyncTests.testAsync14",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAsync15#1",
        source: """
      func testAsyncLet() async {
        async let x = await getIntSomeday()
        _ = await x
      }
      """,
        origin: "AsyncTests.testAsync15",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAsync16#1",
        source: """
      async func asyncIncorrectly() { }
      """,
        origin: "AsyncTests.testAsync16",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAvailabilityQuery1#1",
        source: """
      if #available(OSX 10.51, *) {
      }
      """,
        origin: "AvailabilityQueryTests.testAvailabilityQuery1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAvailabilityQuery11#1",
        source: """
      if #available(OSX) {
      }
      """,
        origin: "AvailabilityQueryTests.testAvailabilityQuery11",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAvailabilityQuery13#1",
        source: """
      if #available(iDishwasherOS 10.51) {
      }
      """,
        origin: "AvailabilityQueryTests.testAvailabilityQuery13",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAvailabilityQuery14#1",
        source: """
      if #available(iDishwasherOS 10.51, *) {
      }
      """,
        origin: "AvailabilityQueryTests.testAvailabilityQuery14",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAvailabilityQuery15#1",
        source: """
      if #available(macos 10.51, *) {
      }
      """,
        origin: "AvailabilityQueryTests.testAvailabilityQuery15",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAvailabilityQuery16#1",
        source: """
      if #available(mscos 10.51, *) {
      }
      """,
        origin: "AvailabilityQueryTests.testAvailabilityQuery16",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAvailabilityQuery17#1",
        source: """
      if #available(macoss 10.51, *) {
      }
      """,
        origin: "AvailabilityQueryTests.testAvailabilityQuery17",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAvailabilityQuery18#1",
        source: """
      if #available(mac 10.51, *) {
      }
      """,
        origin: "AvailabilityQueryTests.testAvailabilityQuery18",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAvailabilityQuery19#1",
        source: """
      if #available(OSX 10.51, OSX 10.52, *) {
      }
      """,
        origin: "AvailabilityQueryTests.testAvailabilityQuery19",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAvailabilityQuery20#1",
        source: """
      if #available(OSX 10.52) { }
      """,
        origin: "AvailabilityQueryTests.testAvailabilityQuery20",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAvailabilityQuery21#1",
        source: """
      if #available(OSX 10.51, iOS 8.0) { }
      """,
        origin: "AvailabilityQueryTests.testAvailabilityQuery21",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAvailabilityQuery22#1",
        source: """
      if #available(iOS 8.0, *) {
      }
      """,
        origin: "AvailabilityQueryTests.testAvailabilityQuery22",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAvailabilityQuery23#1",
        source: """
      if #available(iOSApplicationExtension, unavailable) { // expected-error 2{{expected version number}}
      }
      """,
        origin: "AvailabilityQueryTests.testAvailabilityQuery23",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAvailabilityQuery24#1",
        source: """
      // Want to make sure we can parse this. Perhaps we should not let this validate, though.
      if #available(*) {
      }
      """,
        origin: "AvailabilityQueryTests.testAvailabilityQuery24",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAvailabilityQuery26#1",
        source: """
      // Multiple platforms
      if #available(OSX 10.51, iOS 8.0, *) {
      }
      """,
        origin: "AvailabilityQueryTests.testAvailabilityQuery26",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAvailabilityQuery30#1",
        source: """
      if #available(OSX 10.51, iOS 8.0, iDishwasherOS 10.51) {
      }
      """,
        origin: "AvailabilityQueryTests.testAvailabilityQuery30",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAvailabilityQuery31#1",
        source: """
      if #available(iDishwasherOS 10.51, OSX 10.51) {
      }
      """,
        origin: "AvailabilityQueryTests.testAvailabilityQuery31",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAvailabilityQuery33#1",
        source: """
      // Emit Fix-It removing un-needed >=, for the moment.
      """,
        origin: "AvailabilityQueryTests.testAvailabilityQuery33",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAvailabilityQuery35#1",
        source: """
      // Bool then #available.
      if 1 != 2, #available(iOS 8.0, *) {}
      """,
        origin: "AvailabilityQueryTests.testAvailabilityQuery35",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAvailabilityQuery36#1",
        source: """
      // Pattern then #available(iOS 8.0, *) {
      if case 42 = 42, #available(iOS 8.0, *) {}
      if let _ = Optional(42), #available(iOS 8.0, *) {}
      """,
        origin: "AvailabilityQueryTests.testAvailabilityQuery36",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAvailabilityQuery37#1",
        source: #"""
      // Allow "macOS" as well.
      if #available(macOS 10.51, *) {
      }
      """#,
        origin: "AvailabilityQueryTests.testAvailabilityQuery37",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAvailabilityQueryUnavailability1#1",
        source: """
      // This file is mostly an inverted version of availability_query.swift
      if #unavailable(OSX 10.51) {
      }
      """,
        origin: "AvailabilityQueryUnavailabilityTests.testAvailabilityQueryUnavailability1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAvailabilityQueryUnavailability8#1",
        source: """
      if #unavailable(OSX) {
      }
      """,
        origin: "AvailabilityQueryUnavailabilityTests.testAvailabilityQueryUnavailability8",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAvailabilityQueryUnavailability10#1",
        source: """
      if #unavailable(iDishwasherOS 10.51) {
      }
      """,
        origin: "AvailabilityQueryUnavailabilityTests.testAvailabilityQueryUnavailability10",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAvailabilityQueryUnavailability11#1",
        source: """
      if #unavailable(iDishwasherOS 10.51) {
      }
      """,
        origin: "AvailabilityQueryUnavailabilityTests.testAvailabilityQueryUnavailability11",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAvailabilityQueryUnavailability12#1",
        source: """
      if #unavailable(macos 10.51) {
      }
      """,
        origin: "AvailabilityQueryUnavailabilityTests.testAvailabilityQueryUnavailability12",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAvailabilityQueryUnavailability13#1",
        source: """
      if #unavailable(mscos 10.51) {
      }
      """,
        origin: "AvailabilityQueryUnavailabilityTests.testAvailabilityQueryUnavailability13",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAvailabilityQueryUnavailability14#1",
        source: """
      if #unavailable(macoss 10.51) {
      }
      """,
        origin: "AvailabilityQueryUnavailabilityTests.testAvailabilityQueryUnavailability14",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAvailabilityQueryUnavailability15#1",
        source: """
      if #unavailable(mac 10.51) {
      }
      """,
        origin: "AvailabilityQueryUnavailabilityTests.testAvailabilityQueryUnavailability15",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAvailabilityQueryUnavailability16#1",
        source: """
      if #unavailable(OSX 10.51, OSX 10.52) {
      }
      """,
        origin: "AvailabilityQueryUnavailabilityTests.testAvailabilityQueryUnavailability16",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAvailabilityQueryUnavailability17#1",
        source: """
      if #unavailable(OSX 10.51, iOS 8.0, *) { }
      if #unavailable(iOS 8.0) {
      }
      """,
        origin: "AvailabilityQueryUnavailabilityTests.testAvailabilityQueryUnavailability17",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAvailabilityQueryUnavailability18#1",
        source: """
      if #unavailable(iOSApplicationExtension, unavailable) { // expected-error 2{{expected version number}}
      }
      """,
        origin: "AvailabilityQueryUnavailabilityTests.testAvailabilityQueryUnavailability18",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAvailabilityQueryUnavailability21#1",
        source: """
      // Multiple platforms
      if #unavailable(OSX 10.51, iOS 8.0) {
      }
      """,
        origin: "AvailabilityQueryUnavailabilityTests.testAvailabilityQueryUnavailability21",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAvailabilityQueryUnavailability25#1",
        source: """
      if #unavailable(OSX 10.51, iOS 8.0, iDishwasherOS 10.51) {
      }
      """,
        origin: "AvailabilityQueryUnavailabilityTests.testAvailabilityQueryUnavailability25",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAvailabilityQueryUnavailability26#1",
        source: """
      if #unavailable(iDishwasherOS 10.51, OSX 10.51) {
      }
      """,
        origin: "AvailabilityQueryUnavailabilityTests.testAvailabilityQueryUnavailability26",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAvailabilityQueryUnavailability29#1",
        source: """
      // Bool then #unavailable.
      if 1 != 2, #unavailable(iOS 8.0) {}
      """,
        origin: "AvailabilityQueryUnavailabilityTests.testAvailabilityQueryUnavailability29",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAvailabilityQueryUnavailability30#1",
        source: """
      // Pattern then #unavailable(iOS 8.0) {
      if case 42 = 42, #unavailable(iOS 8.0) {}
      if let _ = Optional(42), #unavailable(iOS 8.0) {}
      """,
        origin: "AvailabilityQueryUnavailabilityTests.testAvailabilityQueryUnavailability30",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAvailabilityQueryUnavailability31#1",
        source: #"""
      // Allow "macOS" as well.
      if #unavailable(macOS 10.51) {
      }
      """#,
        origin: "AvailabilityQueryUnavailabilityTests.testAvailabilityQueryUnavailability31",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAvailabilityQueryUnavailability32#1",
        source: """
      // Prevent availability and unavailability being present in the same statement.
      if #unavailable(macOS 10.51), #available(macOS 10.52, *) {
      }
      if #available(macOS 10.51, *), #unavailable(macOS 10.52) {
      }
      if #available(macOS 10.51, *), #available(macOS 10.55, *), #unavailable(macOS 10.53) {
      }
      if #unavailable(macOS 10.51), #unavailable(macOS 10.55), #available(macOS 10.53, *) {
      }
      if case 42 = 42, #available(macOS 10.51, *), #unavailable(macOS 10.52) {
      }
      if #available(macOS 10.51, *), case 42 = 42, #unavailable(macOS 10.52) {
      }
      """,
        origin: "AvailabilityQueryUnavailabilityTests.testAvailabilityQueryUnavailability32",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAvailabilityQueryUnavailability33#1",
        source: """
      // Allow availability and unavailability to mix if they are not in the same statement.
      if #unavailable(macOS 11) {
        if #available(macOS 10, *) { }
      }
      if #available(macOS 10, *) {
        if #unavailable(macOS 11) { }
      }
      """,
        origin: "AvailabilityQueryUnavailabilityTests.testAvailabilityQueryUnavailability33",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testBorrowExpr1#1",
        source: """
      func useString(_ str: String) {}
      var global: String = "123"
      func testGlobal() {
        useString(_borrow global)
      }
      """,
        origin: "BorrowExprTests.testBorrowExpr1",
        syntaxVersion: "603.0.1",
        compilerRejects: "expected ',' separator"
    ),
    SwiftSnippet(
        label: "testBorrowExpr2#1",
        source: """
      func useString(_ str: String) {}
      func testVar() {
          var t = String()
          t = String()
          useString(_borrow t)
      }
      """,
        origin: "BorrowExprTests.testBorrowExpr2",
        syntaxVersion: "603.0.1",
        compilerRejects: "expected ',' separator"
    ),
    SwiftSnippet(
        label: "testBuiltinBridgeObject1#1",
        source: """
      precedencegroup AssignmentPrecedence { assignment: true }
      """,
        origin: "BuiltinBridgeObjectTests.testBuiltinBridgeObject1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testBuiltinBridgeObject2#1",
        source: """
      var word: Builtin.Word
      """,
        origin: "BuiltinBridgeObjectTests.testBuiltinBridgeObject2",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testBuiltinBridgeObject3#1",
        source: """
      class C {}
      """,
        origin: "BuiltinBridgeObjectTests.testBuiltinBridgeObject3",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testBuiltinBridgeObject4#1",
        source: """
      var c: C
      let bo = Builtin.castToBridgeObject(c, word)
      c = Builtin.castReferenceFromBridgeObject(bo)
      word = Builtin.castBitPatternFromBridgeObject(bo)
      """,
        origin: "BuiltinBridgeObjectTests.testBuiltinBridgeObject4",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testBuiltinWord1#1",
        source: """
      precedencegroup AssignmentPrecedence { assignment: true }
      """,
        origin: "BuiltinWordTests.testBuiltinWord1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testBuiltinWord2#1",
        source: """
      var word: Builtin.Word
      var i16: Builtin.Int16
      var i32: Builtin.Int32
      var i64: Builtin.Int64
      var i128: Builtin.Int128
      """,
        origin: "BuiltinWordTests.testBuiltinWord2",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testBuiltinWord3#1",
        source: """
      // Check that trunc/?ext operations are appropriately available given the
      // abstract range of potential Word sizes.
      """,
        origin: "BuiltinWordTests.testBuiltinWord3",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testBuiltinWord4#1",
        source: """
      word = Builtin.truncOrBitCast_Int128_Word(i128)
      word = Builtin.truncOrBitCast_Int64_Word(i64)
      word = Builtin.truncOrBitCast_Int32_Word(i32)
      word = Builtin.truncOrBitCast_Int16_Word(i16)
      """,
        origin: "BuiltinWordTests.testBuiltinWord4",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testBuiltinWord5#1",
        source: """
      i16 = Builtin.truncOrBitCast_Word_Int16(word)
      i32 = Builtin.truncOrBitCast_Word_Int32(word)
      i64 = Builtin.truncOrBitCast_Word_Int64(word)
      i128 = Builtin.truncOrBitCast_Word_Int128(word)
      """,
        origin: "BuiltinWordTests.testBuiltinWord5",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testBuiltinWord6#1",
        source: """
      word = Builtin.zextOrBitCast_Int128_Word(i128)
      word = Builtin.zextOrBitCast_Int64_Word(i64)
      word = Builtin.zextOrBitCast_Int32_Word(i32)
      word = Builtin.zextOrBitCast_Int16_Word(i16)
      """,
        origin: "BuiltinWordTests.testBuiltinWord6",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testBuiltinWord7#1",
        source: """
      i16 = Builtin.zextOrBitCast_Word_Int16(word)
      i32 = Builtin.zextOrBitCast_Word_Int32(word)
      i64 = Builtin.zextOrBitCast_Word_Int64(word)
      i128 = Builtin.zextOrBitCast_Word_Int128(word)
      """,
        origin: "BuiltinWordTests.testBuiltinWord7",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testBuiltinWord8#1",
        source: """
      word = Builtin.trunc_Int128_Word(i128)
      word = Builtin.trunc_Int64_Word(i64)
      word = Builtin.trunc_Int32_Word(i32)
      word = Builtin.trunc_Int16_Word(i16)
      """,
        origin: "BuiltinWordTests.testBuiltinWord8",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testBuiltinWord9#1",
        source: """
      i16 = Builtin.trunc_Word_Int16(word)
      i32 = Builtin.trunc_Word_Int32(word)
      i64 = Builtin.trunc_Word_Int64(word)
      i128 = Builtin.trunc_Word_Int128(word)
      """,
        origin: "BuiltinWordTests.testBuiltinWord9",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testBuiltinWord10#1",
        source: """
      word = Builtin.zext_Int128_Word(i128)
      word = Builtin.zext_Int64_Word(i64)
      word = Builtin.zext_Int32_Word(i32)
      word = Builtin.zext_Int16_Word(i16)
      """,
        origin: "BuiltinWordTests.testBuiltinWord10",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testBuiltinWord11#1",
        source: """
      i16 = Builtin.zext_Word_Int16(word)
      i32 = Builtin.zext_Word_Int32(word)
      i64 = Builtin.zext_Word_Int64(word)
      i128 = Builtin.zext_Word_Int128(word)
      """,
        origin: "BuiltinWordTests.testBuiltinWord11",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testConflictMarkers1#1",
        source: """
      // Conflict marker parsing should never conflict with operator parsing.
      """,
        origin: "ConflictMarkersTests.testConflictMarkers1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testConflictMarkers2#1",
        source: """
      prefix operator <<<<<<<
      infix operator <<<<<<<
      """,
        origin: "ConflictMarkersTests.testConflictMarkers2",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testConflictMarkers3#1",
        source: """
      prefix func <<<<<<< (x : String) {}
      func <<<<<<< (x : String, y : String) {}
      """,
        origin: "ConflictMarkersTests.testConflictMarkers3",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testConflictMarkers4#1",
        source: """
      prefix operator >>>>>>>
      infix operator >>>>>>>
      """,
        origin: "ConflictMarkersTests.testConflictMarkers4",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testConflictMarkers5#1",
        source: """
      prefix func >>>>>>> (x : String) {}
      func >>>>>>> (x : String, y : String) {}
      """,
        origin: "ConflictMarkersTests.testConflictMarkers5",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testConflictMarkers6#1",
        source: """
      // diff3-style conflict markers
      """,
        origin: "ConflictMarkersTests.testConflictMarkers6",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testConflictMarkers9#1",
        source: #"""
      <<<<<<<"HEAD:fake_conflict_markers.swift" // No error
      >>>>>>>"18844bc65229786b96b89a9fc7739c0fc897905e:fake_conflict_markers.swift" // No error
      """#,
        origin: "ConflictMarkersTests.testConflictMarkers9",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testConflictMarkers11#1",
        source: """
      // Disambiguating conflict markers from operator applications.
      """,
        origin: "ConflictMarkersTests.testConflictMarkers11",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testConflictMarkers13#1",
        source: """
      // Perforce-style conflict markers
      """,
        origin: "ConflictMarkersTests.testConflictMarkers13",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testConsecutiveStatements1#1",
        source: """
      func statement_starts() {
        var f : (Int) -> ()
        f = { (x : Int) -> () in }
        f(0)
        f (0)
        f
        (0)
        var a = [1,2,3]
        a[0] = 1
        a [0] = 1
        a
        [0, 1, 2]
      }
      """,
        origin: "ConsecutiveStatementsTests.testConsecutiveStatements1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testGlobal#1",
        source: """
      var global: Int = 5
      func testGlobal() {
          let _ = copy global
      }
      """,
        origin: "CopyExprTests.testGlobal",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testLet#1",
        source: """
      func testLet() {
          let t = String()
          let _ = copy t
      }
      """,
        origin: "CopyExprTests.testLet",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testVar#1",
        source: """
      func testVar() {
          var t = String()
          t = String()
          let _ = copy t
      }
      """,
        origin: "CopyExprTests.testVar",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testStillAbleToCallFunctionCalledCopy#1",
        source: """
      func copy() {}
      func copy(_: String) {}
      func copy(_: String, _: Int) {}
      func copy(x: String, y: Int) {}

      func useCopyFunc() {
          var s = String()
          var i = global

          copy()
          copy(s)
          copy(i) // expected-error{{cannot convert value of type 'Int' to expected argument type 'String'}}
          copy(s, i)
          copy(i, s) // expected-error{{unnamed argument #2 must precede unnamed argument #1}}
          copy(x: s, y: i)
          copy(y: i, x: s) // expected-error{{argument 'x' must precede argument 'y'}}
      }
      """,
        origin: "CopyExprTests.testStillAbleToCallFunctionCalledCopy",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testUseCopyVariable#1",
        source: """
      func useCopyVar(copy: inout String) {
          let s = copy
          copy = s

          // We can copy from a variable named `copy`
          let t = copy copy
          copy = t

          // We can do member access and subscript a variable named `copy`
          let i = copy.startIndex
          let _ = copy[i]
      }
      """,
        origin: "CopyExprTests.testUseCopyVariable",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testPropertyWrapperWithCopy#1",
        source: """
      @propertyWrapper
      struct FooWrapper<T> {
          var value: T

          init(wrappedValue: T) { value = wrappedValue }

          var wrappedValue: T {
              get { value }
              nonmutating set {}
          }
          var projectedValue: T {
              get { value }
              nonmutating set {}
          }
      }

      struct Foo {
          @FooWrapper var wrapperTest: String

          func copySelf() {
              _ = copy self
          }

          func copyPropertyWrapper() {
              // should still parse, even if it doesn't semantically work out
              _ = copy wrapperTest // expected-error{{can only be applied to lvalues}}
              _ = copy _wrapperTest // expected-error{{can only be applied to lvalues}}
              _ = copy $wrapperTest // expected-error{{can only be applied to lvalues}}
          }
      }
      """,
        origin: "CopyExprTests.testPropertyWrapperWithCopy",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAsCaseStmt#1",
        source: """
      class ParentKlass {}
      class SubKlass : ParentKlass {}

      func test(_ s: SubKlass) {
        switch s {
        case let copy as ParentKlass:
          fallthrough
        }
      }
      """,
        origin: "CopyExprTests.testAsCaseStmt",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testParseCanCopyClosureDollarIdentifier#1",
        source: """
      class Klass {}
      let f: (Klass) -> () = {
        let _ = copy $0
      }
      """,
        origin: "CopyExprTests.testParseCanCopyClosureDollarIdentifier",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForLoop#1",
        source: """
      func test() {
        for copy in 1..<1024 {
        }
      }
      """,
        origin: "CopyExprTests.testForLoop",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testCopySelf#1",
        source: """
      class Klass {
        func test() {
          let _ = copy self
        }
      }
      """,
        origin: "CopyExprTests.testCopySelf",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDebugger1#1",
        source: """
      import Nonexistent_Module
      """,
        origin: "DebuggerTests.testDebugger1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDebugger2#1",
        source: """
      var ($x0, $x1) = (4, 3)
      var z = $x0 + $x1
      """,
        origin: "DebuggerTests.testDebugger2",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDebugger3#1",
        source: """
      z // no error.
      """,
        origin: "DebuggerTests.testDebugger3",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDebugger4#1",
        source: """
      var x: Double = z
      """,
        origin: "DebuggerTests.testDebugger4",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDelayedExtension1#1",
        source: """
      extension X { }
      _ = 1
      f()
      """,
        origin: "DelayedExtensionTests.testDelayedExtension1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDeprecatedWhere1#1",
        source: """
      protocol Mashable { }
      protocol Womparable { }
      """,
        origin: "DeprecatedWhereTests.testDeprecatedWhere1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDeprecatedWhere2#1",
        source: """
      // FuncDecl: Choose 0
      func f1<T>(x: T) {}
      """,
        origin: "DeprecatedWhereTests.testDeprecatedWhere2",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDeprecatedWhere3#1",
        source: """
      // FuncDecl: Choose 1
      // 1: Inherited constraint
      func f2<T: Mashable>(x: T) {} // no-warning
      // 2: Non-trailing where
      func f3<T where T: Womparable>(x: T) {}
      // 3: Has return type
      func f4<T>(x: T) -> Int { return 2 } // no-warning
      // 4: Trailing where
      func f5<T>(x: T) where T : Equatable {} // no-warning
      """,
        origin: "DeprecatedWhereTests.testDeprecatedWhere3",
        syntaxVersion: "603.0.1",
        compilerRejects: "'where' clause next to generic parameters is obsolete, must be written"
    ),
    SwiftSnippet(
        label: "testDeprecatedWhere4#1",
        source: """
      // FuncDecl: Choose 2
      // 1,2
      func f12<T: Mashable where T: Womparable>(x: T) {}
      // 1,3
      func f13<T: Mashable>(x: T) -> Int { return 2 } // no-warning
      // 1,4
      func f14<T: Mashable>(x: T) where T: Equatable {} // no-warning
      // 2,3
      func f23<T where T: Womparable>(x: T) -> Int { return 2 }
      // 2,4
      func f24<T where T: Womparable>(x: T) where T: Equatable {}
      // 3,4
      func f34<T>(x: T) -> Int where T: Equatable { return 2 } // no-warning
      """,
        origin: "DeprecatedWhereTests.testDeprecatedWhere4",
        syntaxVersion: "603.0.1",
        compilerRejects: "'where' clause next to generic parameters is obsolete, must be written"
    ),
    SwiftSnippet(
        label: "testDeprecatedWhere5#1",
        source: """
      // FuncDecl: Choose 3
      // 1,2,3
      func f123<T: Mashable where T: Womparable>(x: T) -> Int { return 2 }
      // 1,2,4
      func f124<T: Mashable where T: Womparable>(x: T) where T: Equatable {}
      // 2,3,4
      func f234<T where T: Womparable>(x: T) -> Int where T: Equatable { return 2 }
      """,
        origin: "DeprecatedWhereTests.testDeprecatedWhere5",
        syntaxVersion: "603.0.1",
        compilerRejects: "'where' clause next to generic parameters is obsolete, must be written"
    ),
    SwiftSnippet(
        label: "testDeprecatedWhere6#1",
        source: """
      // FuncDecl: Choose 4
      // 1,2,3,4
      func f1234<T: Mashable where T: Womparable>(x: T) -> Int where T: Equatable { return 2 }
      """,
        origin: "DeprecatedWhereTests.testDeprecatedWhere6",
        syntaxVersion: "603.0.1",
        compilerRejects: "'where' clause next to generic parameters is obsolete, must be written"
    ),
    SwiftSnippet(
        label: "testDeprecatedWhere7#1",
        source: """
      // NominalTypeDecl: Choose 0
      struct S0<T> {}
      """,
        origin: "DeprecatedWhereTests.testDeprecatedWhere7",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDeprecatedWhere8#1",
        source: """
      // NominalTypeDecl: Choose 1
      // 1: Inherited constraint
      struct S1<T: Mashable> {} // no-warning
      // 2: Non-trailing where
      struct S2<T where T: Womparable> {}
      // 3: Trailing where
      struct S3<T> where T : Equatable {} // no-warning
      """,
        origin: "DeprecatedWhereTests.testDeprecatedWhere8",
        syntaxVersion: "603.0.1",
        compilerRejects: "'where' clause next to generic parameters is obsolete, must be written"
    ),
    SwiftSnippet(
        label: "testDeprecatedWhere9#1",
        source: """
      // NominalTypeDecl: Choose 2
      // 1,2
      struct S12<T: Mashable where T: Womparable> {}
      // 1,3
      struct S13<T: Mashable> where T: Equatable {} // no-warning
      // 2,3
      struct S23<T where T: Womparable> where T: Equatable {}
      """,
        origin: "DeprecatedWhereTests.testDeprecatedWhere9",
        syntaxVersion: "603.0.1",
        compilerRejects: "'where' clause next to generic parameters is obsolete, must be written"
    ),
    SwiftSnippet(
        label: "testDeprecatedWhere10#1",
        source: """
      // NominalTypeDecl: Choose 3
      // 1,2,3
      struct S123<T: Mashable where T: Womparable> where T: Equatable {}
      """,
        origin: "DeprecatedWhereTests.testDeprecatedWhere10",
        syntaxVersion: "603.0.1",
        compilerRejects: "'where' clause next to generic parameters is obsolete, must be written"
    ),
    SwiftSnippet(
        label: "testDeprecatedWhere11#1",
        source: """
      protocol ProtoA {}
      protocol ProtoB {}
      protocol ProtoC {}
      protocol ProtoD {}
      func testCombinedConstraints<T: ProtoA & ProtoB where T: ProtoC>(x: T) {}
      func testCombinedConstraints<T: ProtoA & ProtoB where T: ProtoC>(x: T) where T: ProtoD {}
      """,
        origin: "DeprecatedWhereTests.testDeprecatedWhere11",
        syntaxVersion: "603.0.1",
        compilerRejects: "'where' clause next to generic parameters is obsolete, must be written"
    ),
    SwiftSnippet(
        label: "testDiagnoseAvailability1#1",
        source: """
      // https://github.com/apple/swift/issues/46814
      // Misleading/wrong error message for malformed '@available'
      """,
        origin: "DiagnoseAvailabilityTests.testDiagnoseAvailability1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDiagnoseAvailability2#1",
        source: """
      @available(OSX 10.6, *) // no error
      func availableSince10_6() {}
      """,
        origin: "DiagnoseAvailabilityTests.testDiagnoseAvailability2",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDiagnoseAvailability3#1",
        source: """
      @available(OSX, introduced: 10.0, deprecated: 10.12) // no error
      func introducedFollowedByDeprecated() {}
      """,
        origin: "DiagnoseAvailabilityTests.testDiagnoseAvailability3",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDiagnoseAvailability4#1",
        source: """
      @available(OSX 10.0, deprecated: 10.12)
      func shorthandFollowedByDeprecated() {}
      """,
        origin: "DiagnoseAvailabilityTests.testDiagnoseAvailability4",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDiagnoseAvailability5#1",
        source: """
      @available(OSX 10.0, introduced: 10.12)
      func shorthandFollowedByIntroduced() {}
      """,
        origin: "DiagnoseAvailabilityTests.testDiagnoseAvailability5",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDiagnoseAvailability6#1",
        source: """
      @available(iOS 6.0, OSX 10.8, *) // no error
      func availableOnMultiplePlatforms() {}
      """,
        origin: "DiagnoseAvailabilityTests.testDiagnoseAvailability6",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDiagnoseAvailability7#1",
        source: """
      @available(iOS 6.0, OSX 10.0, deprecated: 10.12)
      func twoShorthandsFollowedByDeprecated() {}
      """,
        origin: "DiagnoseAvailabilityTests.testDiagnoseAvailability7",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDiagnoseAvailability9#1",
        source: """
      @available(*, deprecated: 4.2)
      func allPlatformsDeprecatedVersion() {}
      """,
        origin: "DiagnoseAvailabilityTests.testDiagnoseAvailability9",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDiagnoseAvailability10#1",
        source: """
      @available(*, deprecated, obsoleted: 4.2)
      func allPlatformsDeprecatedAndObsoleted() {}
      """,
        origin: "DiagnoseAvailabilityTests.testDiagnoseAvailability10",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDiagnoseAvailability11#1",
        source: """
      @available(*, introduced: 4.0, deprecated: 4.1, obsoleted: 4.2)
      func allPlatformsDeprecatedAndObsoleted2() {}
      """,
        origin: "DiagnoseAvailabilityTests.testDiagnoseAvailability11",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDiagnoseAvailability12#1",
        source: """
      @available(swift, unavailable)
      func swiftUnavailable() {}
      """,
        origin: "DiagnoseAvailabilityTests.testDiagnoseAvailability12",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDiagnoseAvailability13#1",
        source: """
      @available(swift, unavailable, introduced: 4.2)
      func swiftUnavailableIntroduced() {}
      """,
        origin: "DiagnoseAvailabilityTests.testDiagnoseAvailability13",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDiagnoseAvailability14#1",
        source: """
      @available(swift, deprecated)
      func swiftDeprecated() {}
      """,
        origin: "DiagnoseAvailabilityTests.testDiagnoseAvailability14",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDiagnoseAvailability15#1",
        source: """
      @available(swift, deprecated, obsoleted: 4.2)
      func swiftDeprecatedObsoleted() {}
      """,
        origin: "DiagnoseAvailabilityTests.testDiagnoseAvailability15",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDiagnoseAvailability16#1",
        source: #"""
      @available(swift, message: "missing valid option")
      func swiftMessage() {}
      """#,
        origin: "DiagnoseAvailabilityTests.testDiagnoseAvailability16",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDiagnoseAvailability18#1",
        source: #"""
      @available(*, unavailable, message: """
        foobar message.
        """)
      func multilineMessage() {}
      """#,
        origin: "DiagnoseAvailabilityTests.testDiagnoseAvailability18",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDiagnoseAvailability19#1",
        source: #"""
      @available(*, unavailable, message: " ")
      func emptyMessage() {}
      emptyMessage()
      """#,
        origin: "DiagnoseAvailabilityTests.testDiagnoseAvailability19",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDiagnoseAvailabilityWindows1#1",
        source: #"""
      @available(Windows, unavailable, message: "unsupported")
      func unavailable() {}
      """#,
        origin: "DiagnoseAvailabilityWindowsTests.testDiagnoseAvailabilityWindows1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDiagnoseAvailabilityWindows2#1",
        source: """
      unavailable()
      """,
        origin: "DiagnoseAvailabilityWindowsTests.testDiagnoseAvailabilityWindows2",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDiagnoseAvailabilityWindows3#1",
        source: """
      @available(Windows, introduced: 10.0.17763, deprecated: 10.0.19140)
      func introduced_deprecated() {}
      """,
        origin: "DiagnoseAvailabilityWindowsTests.testDiagnoseAvailabilityWindows3",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDiagnoseAvailabilityWindows4#1",
        source: """
      introduced_deprecated()
      """,
        origin: "DiagnoseAvailabilityWindowsTests.testDiagnoseAvailabilityWindows4",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDiagnoseAvailabilityWindows5#1",
        source: """
      @available(Windows 10, *)
      func windows10() {}
      """,
        origin: "DiagnoseAvailabilityWindowsTests.testDiagnoseAvailabilityWindows5",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDiagnoseAvailabilityWindows6#1",
        source: """
      windows10()
      """,
        origin: "DiagnoseAvailabilityWindowsTests.testDiagnoseAvailabilityWindows6",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDiagnoseAvailabilityWindows7#1",
        source: """
      func conditional_compilation() {
        if #available(Windows 10, *) {
        }
      }
      """,
        origin: "DiagnoseAvailabilityWindowsTests.testDiagnoseAvailabilityWindows7",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDiagnoseDynamicReplacement1#1",
        source: """
      dynamic func dynamic_replaceable() {
      }
      """,
        origin: "DiagnoseDynamicReplacementTests.testDiagnoseDynamicReplacement1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDiagnoseInitializerAsTypedPattern6#1",
        source: """
      var _1 = 1, _2 = 2
      """,
        origin: "DiagnoseInitializerAsTypedPatternTests.testDiagnoseInitializerAsTypedPattern6",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDiagnoseInitializerAsTypedPattern7#1",
        source: """
      let ff: X
      (_1, _2) = (_2, _1)
      let fff: X
       (_1, _2) = (_2, _1)
      """,
        origin: "DiagnoseInitializerAsTypedPatternTests.testDiagnoseInitializerAsTypedPattern7",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDiagnoseInitializerAsTypedPattern9e#1",
        source: """
      func nonTopLevel() {
        _ = (a, i, j, k)
      }
      """,
        origin: "DiagnoseInitializerAsTypedPatternTests.testDiagnoseInitializerAsTypedPattern9e",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDiagnosticMissingFuncKeyword3#1",
        source: """
      infix operator %%
      """,
        origin: "DiagnosticMissingFuncKeywordTests.testDiagnosticMissingFuncKeyword3",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDollarIdentifier1#1",
        source: """
      // https://github.com/apple/swift/issues/44270
      // Dollar was accidentally allowed as an identifier in Swift 3.
      // SE-0144: Reject this behavior in the future.
      """,
        origin: "DollarIdentifierTests.testDollarIdentifier1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDollarIdentifier4#1",
        source: """
      func escapedDollarVar() {
        var `$` : Int = 42 // no error
        `$` += 1
        print(`$`)
      }
      func escapedDollarLet() {
        let `$` = 42 // no error
        print(`$`)
      }
      func escapedDollarClass() {
        class `$` {} // no error
      }
      func escapedDollarEnum() {
        enum `$` {} // no error
      }
      func escapedDollarStruct() {
        struct `$` {} // no error
      }
      """,
        origin: "DollarIdentifierTests.testDollarIdentifier4",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDollarIdentifier5#1",
        source: """
      func escapedDollarFunc() {
        func `$`(`$`: Int) {} // no error
        `$`(`$`: 25) // no error
      }
      """,
        origin: "DollarIdentifierTests.testDollarIdentifier5",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDollarIdentifier6#1",
        source: """
      func escapedDollarAnd() {
        `$0` = 1
        `$$` = 2
        `$abc` = 3
      }
      """,
        origin: "DollarIdentifierTests.testDollarIdentifier6",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDollarIdentifier7#1",
        source: """
      // Test that we disallow user-defined $-prefixed identifiers. However, the error
      // should not be emitted on $-prefixed identifiers that are not considered
      // declarations.
      """,
        origin: "DollarIdentifierTests.testDollarIdentifier7",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDollarIdentifier8#1",
        source: """
      func $declareWithDollar() {
        var $foo: Int {
          get { 0 }
          set($value) {}
        }
        func $bar() { }
        func wibble(
          $a: Int,
          $b c: Int) { }
        let _: (Int) -> Int = {
          [$capture = 0]
          $a in
          $capture
        }
        let ($a: _, _) = (0, 0)
        $label: if true {
          break $label
        }
        switch 0 {
        @$dollar case _:
          break
        }
        if #available($Dummy 9999, *) {}
        @_swift_native_objc_runtime_base($Dollar)
        class $Class {}
        enum $Enum {}
        struct $Struct {
          @_projectedValueProperty($dummy)
          let property: Never
        }
      }
      protocol $Protocol {}
      precedencegroup $Precedence {
        higherThan: $Precedence
      }
      infix operator **: $Precedence
      #$UnknownDirective()
      """,
        origin: "DollarIdentifierTests.testDollarIdentifier8",
        syntaxVersion: "603.0.1",
        compilerRejects: "cannot declare entity named '$declareWithDollar'; the '$' prefix is re"
    ),
    SwiftSnippet(
        label: "testDollarIdentifier9#1",
        source: """
      // https://github.com/apple/swift/issues/55672
      """,
        origin: "DollarIdentifierTests.testDollarIdentifier9",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDollarIdentifier10#1",
        source: """
      @propertyWrapper
      struct Wrapper {
        var wrappedValue: Int
        var projectedValue: String { String(wrappedValue) }
      }
      """,
        origin: "DollarIdentifierTests.testDollarIdentifier10",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDollarIdentifier11#1",
        source: """
      struct S {
        @Wrapper var café = 42
      }
      """,
        origin: "DollarIdentifierTests.testDollarIdentifier11",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDollarIdentifier12#1",
        source: """
      let _ = S().$café // Okay
      """,
        origin: "DollarIdentifierTests.testDollarIdentifier12",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEffectfulProperties1#1",
        source: """
      struct MyProps {
        var prop1 : Int {
          get async { }
        }
        var prop2 : Int {
          get throws { }
        }
        var prop3 : Int {
          get async throws { }
        }
        var prop1mut : Int {
          mutating get async { }
        }
        var prop2mut : Int {
          mutating get throws { }
        }
        var prop3mut : Int {
          mutating get async throws { }
        }
      }
      """,
        origin: "EffectfulPropertiesTests.testEffectfulProperties1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEffectfulProperties2#1",
        source: """
      struct X1 {
        subscript(_ i : Int) -> Int {
            get async {}
          }
      }
      """,
        origin: "EffectfulPropertiesTests.testEffectfulProperties2",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEffectfulProperties3#1",
        source: """
      class X2 {
        subscript(_ i : Int) -> Int {
            get throws {}
          }
      }
      """,
        origin: "EffectfulPropertiesTests.testEffectfulProperties3",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEffectfulProperties4#1",
        source: """
      struct X3 {
        subscript(_ i : Int) -> Int {
            get async throws {}
          }
      }
      """,
        origin: "EffectfulPropertiesTests.testEffectfulProperties4",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEffectfulProperties5#1",
        source: """
      struct BadSubscript1 {
        subscript(_ i : Int) -> Int {
            get async throws {}
            set {}
          }
      }
      """,
        origin: "EffectfulPropertiesTests.testEffectfulProperties5",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEffectfulProperties6#1",
        source: """
      struct BadSubscript2 {
        subscript(_ i : Int) -> Int {
            get throws {}
            set throws {}
          }
      }
      """,
        origin: "EffectfulPropertiesTests.testEffectfulProperties6",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEffectfulProperties7#1",
        source: """
      struct S {
        var prop2 : Int {
          mutating get async throws { 0 }
          nonmutating set {}
        }
      }
      """,
        origin: "EffectfulPropertiesTests.testEffectfulProperties7",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEffectfulProperties8#1",
        source: """
      var prop3 : Bool {
        _read { yield prop3 }
        get throws { false }
        get async { true }
        get {}
      }
      """,
        origin: "EffectfulPropertiesTests.testEffectfulProperties8",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEffectfulProperties9#1",
        source: """
      enum E {
        private(set) var prop4 : Double {
          set {}
          get async throws { 1.1 }
          _modify { yield &prop4 }
        }
      }
      """,
        origin: "EffectfulPropertiesTests.testEffectfulProperties9",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEffectfulProperties10#1",
        source: """
      protocol P {
        associatedtype T
        var prop1 : T { get async throws }
        var prop2 : T { get async throws set }
        var prop3 : T { get throws set }
        var prop4 : T { get async }
        var prop5 : T { mutating get async throws }
        var prop6 : T { mutating get throws }
        var prop7 : T { mutating get async nonmutating set }
      }
      """,
        origin: "EffectfulPropertiesTests.testEffectfulProperties10",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEffectfulProperties11#1",
        source: """
      ///////////////////
      // invalid syntax
      """,
        origin: "EffectfulPropertiesTests.testEffectfulProperties11",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEffectfulProperties14#1",
        source: """
      var bad3 : Int {
        _read async { yield 0 }
        set(theValue) async { }
      }
      """,
        origin: "EffectfulPropertiesTests.testEffectfulProperties14",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnumElementPatternSwift42#1",
        source: """
      enum E {
        case A, B, C, D
        static func testE(e: E) {
          switch e {
          case A<UndefinedTy>():
            break
          case B<Int>():
            break
          default:
            break;
          }
        }
      }
      """,
        origin: "EnumElementPatternSwift4Tests.testEnumElementPatternSwift42",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnumElementPatternSwift43#1",
        source: """
      func testE(e: E) {
        switch e {
        case E.A<UndefinedTy>():
          break
        case E.B<Int>():
          break
        case .C():
          break
        case .D(let payload):
          let _: () = payload
          break
        default:
          break
        }
        guard
          case .C() = e,
          case .D(let payload) = e
        else { return }
      }
      """,
        origin: "EnumElementPatternSwift4Tests.testEnumElementPatternSwift43",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnumElementPatternSwift44#1",
        source: """
      extension E : Error {}
      func canThrow() throws {
        throw E.A
      }
      """,
        origin: "EnumElementPatternSwift4Tests.testEnumElementPatternSwift44",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnumElementPatternSwift45#1",
        source: """
      do {
        try canThrow()
      } catch E.A() {
        // ..
      } catch E.B(let payload) {
        let _: () = payload
      }
      """,
        origin: "EnumElementPatternSwift4Tests.testEnumElementPatternSwift45",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum2#1",
        source: """
      // Windows does not support FP80
      // XFAIL: OS=windows-msvc
      """,
        origin: "EnumTests.testEnum2",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum3#1",
        source: """
      enum Empty {}
      """,
        origin: "EnumTests.testEnum3",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum4#1",
        source: """
      enum Boolish {
        case falsy
        case truthy
        init() { self = .falsy }
      }
      """,
        origin: "EnumTests.testEnum4",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum5#1",
        source: """
      var b = Boolish.falsy
      b = .truthy
      """,
        origin: "EnumTests.testEnum5",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum6#1",
        source: """
      enum Optionable<T> {
        case Nought
        case Mere(T)
      }
      """,
        origin: "EnumTests.testEnum6",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum7#1",
        source: """
      var o = Optionable<Int>.Nought
      o = .Mere(0)
      """,
        origin: "EnumTests.testEnum7",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum8#1",
        source: """
      enum Color { case Red, Green, Grayscale(Int), Blue }
      """,
        origin: "EnumTests.testEnum8",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum9#1",
        source: """
      var c = Color.Red
      c = .Green
      c = .Grayscale(255)
      c = .Blue
      """,
        origin: "EnumTests.testEnum9",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum10#1",
        source: """
      let partialApplication = Color.Grayscale
      """,
        origin: "EnumTests.testEnum10",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum12#1",
        source: """
      struct SomeStruct {
        case StructCase
      }
      """,
        origin: "EnumTests.testEnum12",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum13#1",
        source: """
      class SomeClass {
        case ClassCase
      }
      """,
        origin: "EnumTests.testEnum13",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum14#1",
        source: """
      enum EnumWithExtension1 {
        case A1
      }
      extension EnumWithExtension1 {
        case A2
      }
      """,
        origin: "EnumTests.testEnum14",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum15#1",
        source: """
      // Attributes for enum cases.
      """,
        origin: "EnumTests.testEnum15",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum16#1",
        source: """
      enum EnumCaseAttributes {
        @xyz case EmptyAttributes
      }
      """,
        origin: "EnumTests.testEnum16",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum18#1",
        source: """
      enum HasMethodsPropertiesAndCtors {
        case TweedleDee
        case TweedleDum
        func method() {}
        func staticMethod() {}
        init() {}
        subscript(x:Int) -> Int {
          return 0
        }
        var property : Int {
          return 0
        }
      }
      """,
        origin: "EnumTests.testEnum18",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum19#1",
        source: """
      enum ImproperlyHasIVars {
        case Flopsy
        case Mopsy
        var ivar : Int
      }
      """,
        origin: "EnumTests.testEnum19",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum22#1",
        source: """
      enum RawTypeEmpty : Int {}
      """,
        origin: "EnumTests.testEnum22",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum23#1",
        source: """
      enum Raw : Int {
        case Ankeny, Burnside
      }
      """,
        origin: "EnumTests.testEnum23",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum24#1",
        source: """
      enum MultiRawType : Int64, Int32 {
        case Couch, Davis
      }
      """,
        origin: "EnumTests.testEnum24",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum25#1",
        source: """
      protocol RawTypeNotFirstProtocol {}
      enum RawTypeNotFirst : RawTypeNotFirstProtocol, Int {
        case E
      }
      """,
        origin: "EnumTests.testEnum25",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum26#1",
        source: """
      enum ExpressibleByRawTypeNotLiteral : Array<Int> {
        case Ladd, Elliott, Sixteenth, Harrison
      }
      """,
        origin: "EnumTests.testEnum26",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum27#1",
        source: """
      enum RawTypeCircularityA : RawTypeCircularityB, ExpressibleByIntegerLiteral {
        case Morrison, Belmont, Madison, Hawthorne
        init(integerLiteral value: Int) {
          self = .Morrison
        }
      }
      """,
        origin: "EnumTests.testEnum27",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum28#1",
        source: """
      enum RawTypeCircularityB : RawTypeCircularityA, ExpressibleByIntegerLiteral {
        case Willamette, Columbia, Sandy, Multnomah
        init(integerLiteral value: Int) {
          self = .Willamette
        }
      }
      """,
        origin: "EnumTests.testEnum28",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum29#1",
        source: """
      struct ExpressibleByFloatLiteralOnly : ExpressibleByFloatLiteral {
          init(floatLiteral: Double) {}
      }
      enum ExpressibleByRawTypeNotIntegerLiteral : ExpressibleByFloatLiteralOnly {
        case Everett
        case Flanders
      }
      """,
        origin: "EnumTests.testEnum29",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum30#1",
        source: """
      enum RawTypeWithIntValues : Int {
        case Glisan = 17, Hoyt = 219, Irving, Johnson = 97209
      }
      """,
        origin: "EnumTests.testEnum30",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum31#1",
        source: """
      enum RawTypeWithNegativeValues : Int {
        case Glisan = -17, Hoyt = -219, Irving, Johnson = -97209
        case AutoIncAcrossZero = -1, Zero, One
      }
      """,
        origin: "EnumTests.testEnum31",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum32#1",
        source: #"""
      enum RawTypeWithUnicodeScalarValues : UnicodeScalar {
        case Kearney = "K"
        case Lovejoy
        case Marshall = "M"
      }
      """#,
        origin: "EnumTests.testEnum32",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum33#1",
        source: #"""
      enum RawTypeWithCharacterValues : Character {
        case First = "い"
        case Second
        case Third = "は"
      }
      """#,
        origin: "EnumTests.testEnum33",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum34#1",
        source: #"""
      enum RawTypeWithCharacterValues_Correct : Character {
        case First = "😅" // ok
        case Second = "👩‍👩‍👧‍👦" // ok
        case Third = "👋🏽" // ok
        case Fourth = "\u{1F3F4}\u{E0067}\u{E0062}\u{E0065}\u{E006E}\u{E0067}\u{E007F}" // ok
      }
      """#,
        origin: "EnumTests.testEnum34",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum35#1",
        source: #"""
      enum RawTypeWithCharacterValues_Error1 : Character {
        case First = "abc"
      }
      """#,
        origin: "EnumTests.testEnum35",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum36#1",
        source: """
      enum RawTypeWithFloatValues : Float {
        case Northrup = 1.5
        case Overton
        case Pettygrove = 2.25
      }
      """,
        origin: "EnumTests.testEnum36",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum37#1",
        source: #"""
      enum RawTypeWithStringValues : String {
        case Primrose // okay
        case Quimby = "Lucky Lab"
        case Raleigh // okay
        case Savier = "McMenamin's", Thurman = "Kenny and Zuke's"
      }
      """#,
        origin: "EnumTests.testEnum37",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum38#1",
        source: """
      enum RawValuesWithoutRawType {
        case Upshur = 22
      }
      """,
        origin: "EnumTests.testEnum38",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum39#1",
        source: """
      enum RawTypeWithRepeatValues : Int {
        case Vaughn = 22
        case Wilson = 22
      }
      """,
        origin: "EnumTests.testEnum39",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum40#1",
        source: """
      enum RawTypeWithRepeatValues2 : Double {
        case Vaughn = 22
        case Wilson = 22.0
      }
      """,
        origin: "EnumTests.testEnum40",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum41#1",
        source: """
      enum RawTypeWithRepeatValues3 : Double {
        // 2^63-1
        case Vaughn = 9223372036854775807
        case Wilson = 9223372036854775807.0
      }
      """,
        origin: "EnumTests.testEnum41",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum42#1",
        source: """
      enum RawTypeWithRepeatValues4 : Double {
        // 2^64-1
        case Vaughn = 18446744073709551615
        case Wilson = 18446744073709551615.0
      }
      """,
        origin: "EnumTests.testEnum42",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum43#1",
        source: """
      enum RawTypeWithRepeatValues5 : Double {
        // 2^65-1
        case Vaughn = 36893488147419103231
        case Wilson = 36893488147419103231.0
      }
      """,
        origin: "EnumTests.testEnum43",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum44#1",
        source: """
      enum RawTypeWithRepeatValues6 : Double {
        // 2^127-1
        case Vaughn = 170141183460469231731687303715884105727
        case Wilson = 170141183460469231731687303715884105727.0
      }
      """,
        origin: "EnumTests.testEnum44",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum45#1",
        source: """
      enum RawTypeWithRepeatValues7 : Double {
        // 2^128-1
        case Vaughn = 340282366920938463463374607431768211455
        case Wilson = 340282366920938463463374607431768211455.0
      }
      """,
        origin: "EnumTests.testEnum45",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum46#1",
        source: #"""
      enum RawTypeWithRepeatValues8 : String {
        case Vaughn = "XYZ"
        case Wilson = "XYZ"
      }
      """#,
        origin: "EnumTests.testEnum46",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum47#1",
        source: """
      enum RawTypeWithNonRepeatValues : Double {
        case SantaClara = 3.7
        case SanFernando = 7.4
        case SanAntonio = -3.7
        case SanCarlos = -7.4
      }
      """,
        origin: "EnumTests.testEnum47",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum48#1",
        source: """
      enum RawTypeWithRepeatValuesAutoInc : Double {
        case Vaughn = 22
        case Wilson
        case Yeon = 23
      }
      """,
        origin: "EnumTests.testEnum48",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum49#1",
        source: """
      enum RawTypeWithRepeatValuesAutoInc2 : Double {
        case Vaughn = 23
        case Wilson = 22
        case Yeon
      }
      """,
        origin: "EnumTests.testEnum49",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum50#1",
        source: """
      enum RawTypeWithRepeatValuesAutoInc3 : Double {
        case Vaughn
        case Wilson
        case Yeon = 1
      }
      """,
        origin: "EnumTests.testEnum50",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum51#1",
        source: #"""
      enum RawTypeWithRepeatValuesAutoInc4 : String {
        case A = "B"
        case B
      }
      """#,
        origin: "EnumTests.testEnum51",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum52#1",
        source: #"""
      enum RawTypeWithRepeatValuesAutoInc5 : String {
        case A
        case B = "A"
      }
      """#,
        origin: "EnumTests.testEnum52",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum53#1",
        source: #"""
      enum RawTypeWithRepeatValuesAutoInc6 : String {
        case A
        case B
        case C = "B"
      }
      """#,
        origin: "EnumTests.testEnum53",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum54#1",
        source: """
      enum NonliteralRawValue : Int {
        case Yeon = 100 + 20 + 3
      }
      """,
        origin: "EnumTests.testEnum54",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum55#1",
        source: """
      enum RawTypeWithPayload : Int {
        case Powell(Int)
        case Terwilliger(Int) = 17
      }
      """,
        origin: "EnumTests.testEnum55",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum56#1",
        source: #"""
      enum RawTypeMismatch : Int {
        case Barbur = "foo"
      }
      """#,
        origin: "EnumTests.testEnum56",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum57#1",
        source: """
      enum DuplicateMembers1 {
        case Foo
        case Foo
      }
      """,
        origin: "EnumTests.testEnum57",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum58#1",
        source: """
      enum DuplicateMembers2 {
        case Foo, Bar
        case Foo
        case Bar
      }
      """,
        origin: "EnumTests.testEnum58",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum59#1",
        source: """
      enum DuplicateMembers3 {
        case Foo
        case Foo(Int)
      }
      """,
        origin: "EnumTests.testEnum59",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum60#1",
        source: """
      enum DuplicateMembers4 : Int {
        case Foo = 1
        case Foo = 2
      }
      """,
        origin: "EnumTests.testEnum60",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum61#1",
        source: """
      enum DuplicateMembers5 : Int {
        case Foo = 1
        case Foo = 1 + 1
      }
      """,
        origin: "EnumTests.testEnum61",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum62#1",
        source: """
      enum DuplicateMembers6 {
        case Foo // expected-note 2{{'Foo' previously declared here}}
        case Foo
        case Foo
      }
      """,
        origin: "EnumTests.testEnum62",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum63#1",
        source: #"""
      enum DuplicateMembers7 : String {
        case Foo
        case Foo = "Bar"
      }
      """#,
        origin: "EnumTests.testEnum63",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum64#1",
        source: #"""
      // Refs to duplicated enum cases shouldn't crash the compiler.
      // rdar://problem/20922401
      func check20922401() -> String {
        let x: DuplicateMembers1 = .Foo
        switch x {
          case .Foo:
            return "Foo"
        }
      }
      """#,
        origin: "EnumTests.testEnum64",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum65#1",
        source: """
      enum PlaygroundRepresentation : UInt8 {
        case Class = 1
        case Struct = 2
        case Tuple = 3
        case Enum = 4
        case Aggregate = 5
        case Container = 6
        case IDERepr = 7
        case Gap = 8
        case ScopeEntry = 9
        case ScopeExit = 10
        case Error = 11
        case IndexContainer = 12
        case KeyContainer = 13
        case MembershipContainer = 14
        case Unknown = 0xFF
        static func fromByte(byte : UInt8) -> PlaygroundRepresentation {
          let repr = PlaygroundRepresentation(rawValue: byte)
          if repr == .none { return .Unknown } else { return repr! }
        }
      }
      """,
        origin: "EnumTests.testEnum65",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum66#1",
        source: """
      struct ManyLiteralable : ExpressibleByIntegerLiteral, ExpressibleByStringLiteral, Equatable {
        init(stringLiteral: String) {}
        init(integerLiteral: Int) {}
        init(unicodeScalarLiteral: String) {}
        init(extendedGraphemeClusterLiteral: String) {}
      }
      func ==(lhs: ManyLiteralable, rhs: ManyLiteralable) -> Bool { return true }
      """,
        origin: "EnumTests.testEnum66",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum67#1",
        source: """
      enum ManyLiteralA : ManyLiteralable {
        case A
        case B = 0
      }
      """,
        origin: "EnumTests.testEnum67",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum68#1",
        source: #"""
      enum ManyLiteralB : ManyLiteralable {
        case A = "abc"
        case B
      }
      """#,
        origin: "EnumTests.testEnum68",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum69#1",
        source: #"""
      enum ManyLiteralC : ManyLiteralable {
        case A
        case B = "0"
      }
      """#,
        origin: "EnumTests.testEnum69",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum70#1",
        source: """
      // rdar://problem/22476643
      public protocol RawValueA: RawRepresentable
      {
        var rawValue: Double { get }
      }
      """,
        origin: "EnumTests.testEnum70",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum71#1",
        source: """
      enum RawValueATest: Double, RawValueA {
        case A, B
      }
      """,
        origin: "EnumTests.testEnum71",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum72#1",
        source: """
      public protocol RawValueB
      {
        var rawValue: Double { get }
      }
      """,
        origin: "EnumTests.testEnum72",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum73#1",
        source: """
      enum RawValueBTest: Double, RawValueB {
        case A, B
      }
      """,
        origin: "EnumTests.testEnum73",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum74#1",
        source: """
      enum foo : String {
        case bar = nil
      }
      """,
        origin: "EnumTests.testEnum74",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum75#1",
        source: """
      // Static member lookup from instance methods
      """,
        origin: "EnumTests.testEnum75",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum76#1",
        source: """
      struct EmptyStruct {}
      """,
        origin: "EnumTests.testEnum76",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum77#1",
        source: """
      enum EnumWithStaticMember {
        static let staticVar = EmptyStruct()
        func foo() {
          let _ = staticVar
        }
      }
      """,
        origin: "EnumTests.testEnum77",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum78#1",
        source: """
      // SE-0036:
      """,
        origin: "EnumTests.testEnum78",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum79#1",
        source: """
      struct SE0036_Auxiliary {}
      """,
        origin: "EnumTests.testEnum79",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum80#1",
        source: """
      enum SE0036 {
        case A
        case B(SE0036_Auxiliary)
        case C(SE0036_Auxiliary)
        static func staticReference() {
          _ = A
          _ = self.A
          _ = SE0036.A
        }
        func staticReferenceInInstanceMethod() {
          _ = A
          _ = self.A
          _ = SE0036.A
        }
        static func staticReferenceInSwitchInStaticMethod() {
          switch SE0036.A {
          case A: break
          case B(_): break
          case C(let x): _ = x; break
          }
        }
        func staticReferenceInSwitchInInstanceMethod() {
          switch self {
          case A: break
          case B(_): break
          case C(let x): _ = x; break
          }
        }
        func explicitReferenceInSwitch() {
          switch SE0036.A {
          case SE0036.A: break
          case SE0036.B(_): break
          case SE0036.C(let x): _ = x; break
          }
        }
        func dotReferenceInSwitchInInstanceMethod() {
          switch self {
          case .A: break
          case .B(_): break
          case .C(let x): _ = x; break
          }
        }
        static func dotReferenceInSwitchInStaticMethod() {
          switch SE0036.A {
          case .A: break
          case .B(_): break
          case .C(let x): _ = x; break
          }
        }
        init() {
          self = .A
          self = A
          self = SE0036.A
          self = .B(SE0036_Auxiliary())
          self = B(SE0036_Auxiliary())
          self = SE0036.B(SE0036_Auxiliary())
        }
      }
      """,
        origin: "EnumTests.testEnum80",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum81#1",
        source: """
      enum SE0036_Generic<T> {
        case A(x: T)
        func foo() {
          switch self {
          case A(_): break
          }
          switch self {
          case .A(let a): print(a)
          }
          switch self {
          case SE0036_Generic.A(let a): print(a)
          }
        }
      }
      """,
        origin: "EnumTests.testEnum81",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum81b#1",
        source: """
      switch self {
        case A(_): break
      }
      """,
        origin: "EnumTests.testEnum81b",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnum83#1",
        source: """
      enum SE0155 {
        case emptyArgs()
      }
      """,
        origin: "EnumTests.testEnum83",
        syntaxVersion: "603.0.1",
        compilerRejects: "enum element with associated values must have at least one associated"
    ),
    SwiftSnippet(
        label: "testEnum84#1",
        source: """
      // https://github.com/apple/swift/issues/53662
      """,
        origin: "EnumTests.testEnum84",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnumCaseWithWildcardAsFirstName#1",
        source: #"""
      enum Foo {
        case a(_ x: Int)
      }
      """#,
        origin: "EnumTests.testEnumCaseWithWildcardAsFirstName",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEnumCaseWithWildcardAsFirstName#2",
        source: """
      enum E {
        case a
          (Int)
      }
      """,
        origin: "EnumTests.testEnumCaseWithWildcardAsFirstName",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testErrors1#1",
        source: #"""
      enum MSV : Error {
        case Foo, Bar, Baz
        case CarriesInt(Int)
        var _domain: String { return "" }
        var _code: Int { return 0 }
      }
      """#,
        origin: "ErrorsTests.testErrors1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testErrors2#1",
        source: """
      func opaque_error() -> Error { return MSV.Foo }
      """,
        origin: "ErrorsTests.testErrors2",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testErrors3#1",
        source: """
      do {
        throw opaque_error()
      } catch MSV.Foo, MSV.CarriesInt(let num) {
      } catch {
      }
      """,
        origin: "ErrorsTests.testErrors3",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testErrors4#1",
        source: """
      func takesAutoclosure(_ fn : @autoclosure () -> Int) {}
      func takesThrowingAutoclosure(_ fn : @autoclosure () throws -> Int) {}
      """,
        origin: "ErrorsTests.testErrors4",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testErrors5#1",
        source: """
      func genError() throws -> Int { throw MSV.Foo }
      func genNoError() -> Int { return 0 }
      """,
        origin: "ErrorsTests.testErrors5",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testErrors6#1",
        source: """
      func testAutoclosures() throws {
        takesAutoclosure(genError())
        takesAutoclosure(genNoError())
        try takesAutoclosure(genError())
        try takesAutoclosure(genNoError())
        takesAutoclosure(try genError())
        takesAutoclosure(try genNoError())
        takesThrowingAutoclosure(try genError())
        takesThrowingAutoclosure(try genNoError())
        try takesThrowingAutoclosure(genError())
        try takesThrowingAutoclosure(genNoError())
        takesThrowingAutoclosure(genError())
        takesThrowingAutoclosure(genNoError())
      }
      """,
        origin: "ErrorsTests.testErrors6",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testErrors19#1",
        source: """
      // https://github.com/apple/swift/issues/53979
      """,
        origin: "ErrorsTests.testErrors19",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testErrors28#1",
        source: """
      do {
      } catch {
        let error2 = error
      }
      """,
        origin: "ErrorsTests.testErrors28",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testErrors29#1",
        source: """
      do {
      } catch where true {
        let error2 = error
      } catch {
      }
      """,
        origin: "ErrorsTests.testErrors29",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testErrors30#1",
        source: """
      do {
        throw opaque_error()
      } catch MSV {
      } catch {
      }
      """,
        origin: "ErrorsTests.testErrors30",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testErrors31#1",
        source: """
      do {
        throw opaque_error()
      } catch is Error {
      }
      """,
        origin: "ErrorsTests.testErrors31",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testErrors32#1",
        source: """
      func foo() throws {}
        do {
      #if false
          try foo()
      #endif
        } catch {    // don't warn, #if code should be scanned.
        }
        do {
      #if false
          throw opaque_error()
      #endif
        } catch {    // don't warn, #if code should be scanned.
        }
      """,
        origin: "ErrorsTests.testErrors32",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEscapedIdentifiers1#1",
        source: """
      func `protocol`() {}
      """,
        origin: "EscapedIdentifiersTests.testEscapedIdentifiers1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEscapedIdentifiers2#1",
        source: """
      `protocol`()
      """,
        origin: "EscapedIdentifiersTests.testEscapedIdentifiers2",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEscapedIdentifiers3#1",
        source: """
      class `Type` {}
      """,
        origin: "EscapedIdentifiersTests.testEscapedIdentifiers3",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEscapedIdentifiers4#1",
        source: """
      var `class` = `Type`.self
      """,
        origin: "EscapedIdentifiersTests.testEscapedIdentifiers4",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEscapedIdentifiers5#1",
        source: """
      func foo() {}
      """,
        origin: "EscapedIdentifiersTests.testEscapedIdentifiers5",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEscapedIdentifiers6#1",
        source: """
      `foo`()
      """,
        origin: "EscapedIdentifiersTests.testEscapedIdentifiers6",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEscapedIdentifiers7#1",
        source: """
      // Escaping suppresses identifier contextualization.
      var get: (() -> ()) -> () = { $0() }
      """,
        origin: "EscapedIdentifiersTests.testEscapedIdentifiers7",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEscapedIdentifiers8#1",
        source: """
      var applyGet: Int {
        `get` { }
        return 0
      }
      """,
        origin: "EscapedIdentifiersTests.testEscapedIdentifiers8",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEscapedIdentifiers9#1",
        source: """
      enum `switch` {}
      """,
        origin: "EscapedIdentifiersTests.testEscapedIdentifiers9",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEscapedIdentifiers10#1",
        source: """
      typealias `Self` = Int
      """,
        origin: "EscapedIdentifiersTests.testEscapedIdentifiers10",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEscapedIdentifiers11#1",
        source: """
      func `method with space and .:/`() {}
      `method with space and .:/`()

      class `Class with space and .:/` {}
      var `var with space and .:/` = `Class with space and .:/`.self

      enum `Enum with space and .:/` {
        case `space cases`
        case `case with payload`(`some label`: `Class with space and .:/`)
      }
      let `enum value`: `Enum with space and .:/` =
        .`case with payload`(`some label`: `var with space and .:/`)

      struct `Escaped Type` {}
      func `escaped function`(`escaped label` `escaped arg`: `Escaped Type`) {}
      `escaped function`(`escaped label`: `Escaped Type`())
      let `escaped reference` = `escaped function`(`escaped label`:)
      `escaped reference`(`Escaped Type`())
      """,
        origin: "EscapedIdentifiersTests.testEscapedIdentifiers11",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEscapedIdentifiers12#1",
        source: """
      func `+ start with operator`() {}
      func `end with operator +`() {}
      func ` + `() {}
      """,
        origin: "EscapedIdentifiersTests.testEscapedIdentifiers12",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEscapedIdentifiers13#1",
        source: """
      func `// not a comment`() {}
      func `/* also not a comment */`() {}
      func `func dontDoThis() {}`() {}
      """,
        origin: "EscapedIdentifiersTests.testEscapedIdentifiers13",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEscapedIdentifiers14#1",
        source: """
      let `@atSign` = 0
      let `#octothorpe` = 0
      """,
        origin: "EscapedIdentifiersTests.testEscapedIdentifiers14",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEscapedIdentifiers15#1",
        source: """
      @propertyWrapper
      struct `@PoorlyNamedWrapper`<`The Value`> {
        var wrappedValue: `The Value`
      }
      struct WithWrappedProperty {
        @`@PoorlyNamedWrapper` var x: Int
      }
      """,
        origin: "EscapedIdentifiersTests.testEscapedIdentifiers15",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForeachAsync1#1",
        source: """
      import _Concurrency
      """,
        origin: "ForeachAsyncTests.testForeachAsync1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForeachAsync2#1",
        source: """
      struct AsyncRange<Bound: Comparable & Strideable>: AsyncSequence, AsyncIteratorProtocol where Bound.Stride : SignedInteger {
        var range: Range<Bound>.Iterator
        typealias Element = Bound
        mutating func next() async -> Element? { return range.next() }
        func cancel() { }
        func makeAsyncIterator() -> Self { return self }
      }
      """,
        origin: "ForeachAsyncTests.testForeachAsync2",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForeachAsync3#1",
        source: """
      struct AsyncIntRange<Int> : AsyncSequence, AsyncIteratorProtocol {
        typealias Element = (Int, Int)
        func next() async -> (Int, Int)? {}
        func cancel() { }
        typealias AsyncIterator = AsyncIntRange<Int>
        func makeAsyncIterator() -> AsyncIntRange<Int> { return self }
      }
      """,
        origin: "ForeachAsyncTests.testForeachAsync3",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForeachAsync4#1",
        source: """
      func for_each(r: AsyncRange<Int>, iir: AsyncIntRange<Int>) async {
        var sum = 0
        // Simple foreach loop, using the variable in the body
        for await i in r {
          sum = sum + i
        }
      }
      """,
        origin: "ForeachAsyncTests.testForeachAsync4",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForeachAsync5#1",
        source: """
      func for_each(r: AsyncRange<Int>, iir: AsyncIntRange<Int>) async {
        var sum = 0
        for await (i, j) in iir {
          sum = sum + i + j
        }
      }
      """,
        origin: "ForeachAsyncTests.testForeachAsync5",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForeachAsync5#2",
        source: """
      func for_each(r: AsyncRange<Int>, iir: AsyncIntRange<Int>) async {
        var sum = 0
        for await (i, j) in iir {
          sum = sum + i + j
        }
      }
      """,
        origin: "ForeachAsyncTests.testForeachAsync5",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForeachAsync5#3",
        source: """
      func for_each(r: AsyncRange<Int>, iir: AsyncIntRange<Int>) async {
        var sum = 0
        for await (i, j) : (Int, Int) in iir {
          sum = sum + i + j
        }
      }
      """,
        origin: "ForeachAsyncTests.testForeachAsync5",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForeach1#1",
        source: """
      struct IntRange<Int> : Sequence, IteratorProtocol {
        typealias Element = (Int, Int)
        func next() -> (Int, Int)? {}
        typealias Iterator = IntRange<Int>
        func makeIterator() -> IntRange<Int> { return self }
      }
      """,
        origin: "ForeachTests.testForeach1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForeach2#1",
        source: """
      func for_each(r: Range<Int>, iir: IntRange<Int>) {
        var sum = 0
        for i in r {
          sum = sum + i
        }
      }
      """,
        origin: "ForeachTests.testForeach2",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForeach2#2",
        source: """
      func for_each(r: Range<Int>, iir: IntRange<Int>) {
        var sum = 0
        for (i, j) in iir {
          sum = sum + i + j
        }
      }
      """,
        origin: "ForeachTests.testForeach2",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForeach2#3",
        source: """
      func for_each(r: Range<Int>, iir: IntRange<Int>) {
        var sum = 0
        for (i, j) : (Int, Int) in iir {
          sum = sum + i + j
        }
      }
      """,
        origin: "ForeachTests.testForeach2",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkippingAllowed7#1",
        source: """
      func d() {
        _ = 1 / 2 + 3 * 4
        _ = 1 / 2 / 3 / 4
      }
      """,
        origin: "ForwardSlashRegexSkippingAllowedTests.testForwardSlashRegexSkippingAllowed7",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkippingAllowed8#1",
        source: #"""
      func e() {
        let arr = [1, 2, 3]
        _ = arr.reduce(0, /) / 2
        func foo(_ i: Int, _ fn: () -> Void) {}
        foo(1 / 2 / 3, { print("}}}{{{") })
      }
      """#,
        origin: "ForwardSlashRegexSkippingAllowedTests.testForwardSlashRegexSkippingAllowed8",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkippingAllowed9#1",
        source: """
      prefix operator /
      prefix func / <T> (_ x: T) -> T { x }
      """,
        origin: "ForwardSlashRegexSkippingAllowedTests.testForwardSlashRegexSkippingAllowed9",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkippingAllowed11#1",
        source: """
      func f() {
        _ = /E.e
        (/E.e).foo(/0)
        func foo<T, U>(_ x: T, _ y: U) {}
        foo(/E.e, /E.e)
        foo((/E.e), /E.e)
        foo((/)(E.e), /E.e)
        func bar<T>(_ x: T) -> Int { 0 }
        _ = bar(/E.e) / 2
      }
      """,
        origin: "ForwardSlashRegexSkippingAllowedTests.testForwardSlashRegexSkippingAllowed11",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkippingAllowed12#1",
        source: """
      postfix operator /
      prefix func / <T> (_ x: T) -> T { x }
      """,
        origin: "ForwardSlashRegexSkippingAllowedTests.testForwardSlashRegexSkippingAllowed12",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkippingAllowed13#1",
        source: """
      func g() {
          _ = 0/
          _ = 0/ / 1/
          _ = 1/ + 1/
          _ = 1 + 2/
      }
      """,
        origin: "ForwardSlashRegexSkippingAllowedTests.testForwardSlashRegexSkippingAllowed13",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkippingInvalid7#1",
        source: """
      func h() {
        _ = /x         {
        }
      }
      """,
        origin: "ForwardSlashRegexSkippingInvalidTests.testForwardSlashRegexSkippingInvalid7",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping3#1",
        source: #"""
      struct A {
        static let r = /test":"(.*?)"/
      }
      """#,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping3",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping4#1",
        source: """
      struct B {
        static let r = /x*/
      }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping4",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping5#1",
        source: """
      struct C {
        func foo() {
          let r = /x*/
        }
      }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping5",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping6#1",
        source: """
      struct D {
        func foo() {
          func bar() {
            let r = /x}}*/
          }
        }
      }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping6",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping7#1",
        source: """
      func a() { _ = /abc}}*/ }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping7",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping8#1",
        source: #"""
      func b() { _ = /\// }
      """#,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping8",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping9#1",
        source: #"""
      func c() { _ = /\\/ }
      """#,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping9",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping10#1",
        source: """
      func d() { _ = ^^/x}}*/ }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping10",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping11#1",
        source: """
      func e() { _ = (^^/x}}*/) }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping11",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping12#1",
        source: """
      func f() { _ = ^^/^x}}*/ }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping12",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping13#1",
        source: #"""
      func g() { _ = "\(/x}}*/)" }
      """#,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping13",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping14#1",
        source: #"""
      func h() { _ = "\(^^/x}}*/)" }
      """#,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping14",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping15#1",
        source: #"""
      func i() {
        func foo<T>(_ x: T, y: T) {}
        foo(/}}*/, y: /"/)
      }
      """#,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping15",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping16#1",
        source: """
      func j() {
        _ = {
          0
          /x}}}/ 
          2
        }
      }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping16",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping17#1",
        source: """
      func k() {
        _ = 2
        / 1 / .bitWidth
      }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping17",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping18#1",
        source: """
      func l() {
        _ = 2
        /x}*/ .self
      }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping18",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping20#1",
        source: """
      func m() {
        _ = 2
        / 1 /
          .bitWidth
      }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping20",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping21#1",
        source: """
      func n() {
        _ = 2
        /x}/
          .bitWidth
      }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping21",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping23#1",
        source: """
      func o() {
        _ = /x// comment
      }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping23",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping24#1",
        source: """
      func p() {
        _ = /x // comment
      }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping24",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping25#1",
        source: """
      func q() {
        _ = /x/*comment*/
      }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping25",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping26#1",
        source: """
      func r() { _ = /[(0)]/ }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping26",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping27#1",
        source: """
      func s() { _ = /(x)/ }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping27",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping28#1",
        source: """
      func t() { _ = /[)]/ }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping28",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping29#1",
        source: #"""
      func u() { _ = /[a\])]/ }
      """#,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping29",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping30#1",
        source: """
      func v() { _ = /([)])/ }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping30",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping31#1",
        source: """
      func w() { _ = /]]][)]/ }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping31",
        syntaxVersion: "603.0.1",
        compilerRejects: "expected expression after unary operator"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping32#1",
        source: """
      func x() { _ = /,/ }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping32",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping33#1",
        source: """
      func y() { _ = /}/ }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping33",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping34#1",
        source: """
      func z() { _ = /]/ }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping34",
        syntaxVersion: "603.0.1",
        compilerRejects: "expected expression after unary operator"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping35#1",
        source: """
      func a1() { _ = /:/ }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping35",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping36#1",
        source: """
      func a2() { _ = /;/ }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping36",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping37#1",
        source: """
      func a3() { _ = /)/ }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping37",
        syntaxVersion: "603.0.1",
        compilerRejects: "expected expression after unary operator"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping39#1",
        source: #"""
      func a5() { _ = /\ / }
      """#,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping39",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping42#1",
        source: #"""
      func a7() { _ = /\/}/ }
      """#,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping42",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping43#1",
        source: """
      func err1() { _ = /0xG/ }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping43",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping44#1",
        source: """
      func err2() { _ = /0oG/ }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping44",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping45#1",
        source: #"""
      func err3() { _ = /"/ }
      """#,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping45",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping46#1",
        source: """
      func err4() { _ = /'/ }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping46",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping47#1",
        source: """
      func err5() { _ = /<#placeholder#>/ }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping47",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping48#1",
        source: """
      func err6() { _ = ^^/0xG/ }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping48",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping49#1",
        source: """
      func err7() { _ = ^^/0oG/ }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping49",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping50#1",
        source: #"""
      func err8() { _ = ^^/"/ }
      """#,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping50",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping51#1",
        source: """
      func err9() { _ = ^^/'/ }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping51",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping52#1",
        source: """
      func err10() { _ = ^^/<#placeholder#>/ }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping52",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping53#1",
        source: """
      func err11() { _ = (^^/0xG/) }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping53",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping54#1",
        source: """
      func err12() { _ = (^^/0oG/) }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping54",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping55#1",
        source: #"""
      func err13() { _ = (^^/"/) }
      """#,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping55",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping56#1",
        source: """
      func err14() { _ = (^^/'/) }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping56",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping57#1",
        source: """
      func err15() { _ = (^^/<#placeholder#>/) }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping57",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex1#1",
        source: """
      prefix operator /
      prefix operator ^/
      prefix operator /^/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex2#1",
        source: """
      prefix func ^/ <T> (_ x: T) -> T { x }
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex2",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex8#1",
        source: """
      infix operator /^/ : P
      func /^/ (lhs: Int, rhs: Int) -> Int { 1 / 2 }
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex8",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex9#1",
        source: """
      infix operator /^ : P
      func /^ (lhs: Int, rhs: Int) -> Int { 1 / 2 }
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex9",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex10#1",
        source: """
      infix operator ^^/ : P
      func ^^/ (lhs: Int, rhs: Int) -> Int { 1 / 2 }
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex10",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex11#1",
        source: """
      let i = 0 /^/ 1/^/3
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex11",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex12#1",
        source: """
      let x = /abc/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex12",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex13#1",
        source: """
      _ = /abc/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex13",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex14#1",
        source: """
      _ = /x/.self
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex14",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex15#1",
        source: #"""
      _ = /\//
      """#,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex15",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex16#1",
        source: #"""
      _ = /\\/
      """#,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex16",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex19#1",
        source: """
      do {
        _=/0/
      }
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex19",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex21#1",
        source: """
      _ = /x
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex21",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex22#1",
        source: """
      _ = !/x/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex22",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex23#1",
        source: """
      _ = (!/x/)
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex23",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex26#1",
        source: """
      _ = !!/x/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex26",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex27#1",
        source: """
      _ = (!!/x/)
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex27",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex29#1",
        source: """
      _ = /x/!
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex29",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex30#1",
        source: """
      _ = /x/ + /y/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex30",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex31#1",
        source: """
      _ = /x/+/y/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex31",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex32#1",
        source: """
      _ = /x/?.blah
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex32",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex33#1",
        source: """
      _ = /x/!.blah
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex33",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex34#1",
        source: """
      do {
        _ = /x /?
          .blah
      }
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex34",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex35#1",
        source: """
      _ = /x/? 
        .blah
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex35",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex36#1",
        source: """
      _ = 0; /x/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex36",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex39#1",
        source: """
      _ = .random() ? /x/ : .blah
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex39",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex41#1",
        source: """
      _ = /x/??/x/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex41",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex42#1",
        source: """
      _ = /x/ ... /y/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex42",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex43#1",
        source: """
      _ = /x/.../y/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex43",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex44#1",
        source: """
      _ = /x/...
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex44",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex47#1",
        source: #"""
      _ = "\(/x/)"
      """#,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex47",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex48#1",
        source: """
      func defaulted(x: Regex<Substring> = /x/) {}
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex48",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex50#1",
        source: """
      foo(/abc/, y: /abc/)
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex50",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex53#1",
        source: """
      bar(&/x/)
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex53",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex57#1",
        source: """
      func testThrow() throws {
        throw /x/ 
      }
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex57",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex60#1",
        source: """
      _ = [/abc/:/abc/]
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex60",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex61#1",
        source: """
      _ = [/abc/ : /abc/]
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex61",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex62#1",
        source: """
      _ = [/abc/ :/abc/]
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex62",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex63#1",
        source: """
      _ = [/abc/: /abc/]
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex63",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex64#1",
        source: """
      _ = (/abc/, /abc/)
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex64",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex65#1",
        source: """
      _ = ((/abc/))
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex65",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex67#1",
        source: """
      _ = { /abc/ }
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex67",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex68#1",
        source: """
      _ = {
        /abc/
      }
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex68",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex69#1",
        source: """
      let _: () -> Int = {
        0
        / 1 /
        2
      }
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex69",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex70#1",
        source: """
      let _: () -> Int = {
        0
        /1 / 
        2
      }
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex70",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex71#1",
        source: """
      _ = {
        0 
        /1/ 
        2 
      }
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex71",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex73#1",
        source: """
      _ = 2
      / 1 / .bitWidth
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex73",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex74#1",
        source: """
      _ = 2
      /1/ .bitWidth
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex74",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex75#1",
        source: """
      _ = 2
      / 1 /
        .bitWidth
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex75",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex76#1",
        source: """
      _ = 2
      /1 /
        .bitWidth
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex76",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex77#1",
        source: """
      _ = !!/1/ .bitWidth
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex77",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex78#1",
        source: """
      _ = !!/1 / .bitWidth
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex78",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex79#1",
        source: """
      let z =
      /y/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex79",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex83#1",
        source: #"""
      switch "" {
      case _ where /x/:
        break
      default:
        break
      }
      """#,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex83",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex84#1",
        source: """
      do {} catch /x/ {}
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex84",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex86#1",
        source: """
      switch /x/ {
      default:
        break
      }
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex86",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex87#1",
        source: """
      if /x/ {}
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex87",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex88#1",
        source: """
      if /x/.smth {}
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex88",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex89#1",
        source: """
      func testGuard() {
        guard /x/ else { return } 
      }
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex89",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex90#1",
        source: """
      for x in [0] where /x/ {}
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex90",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex92#1",
        source: """
      _ = /x/ as Magic
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex92",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex93#1",
        source: """
      _ = /x/ as! String
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex93",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex94#1",
        source: """
      _ = type(of: /x/)
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex94",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex99#1",
        source: """
      _ = await /x/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex99",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex100#1",
        source: """
      /x/ = 0 
      /x/()
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex100",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex102#1",
        source: """
      _ = /x// comment
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex102",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex103#1",
        source: """
      _ = /x // comment
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex103",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex104#1",
        source: """
      _ = /x/*comment*/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex104",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex108#1",
        source: """
      baz(/, /)
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex108",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex108#2",
        source: """
      baz(/,/)
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex108",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex109#1",
        source: """
      baz((/), /)
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex109",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex110#1",
        source: """
      baz(/^, /)
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex110",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex110#2",
        source: """
      baz(/^,/)
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex110",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex111#1",
        source: """
      baz((/^), /)
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex111",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex112#1",
        source: """
      baz(^^/, /)
      baz(^^/,/) 
      baz((^^/), /)
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex112",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex114#1",
        source: """
      bazbaz(/, 0)
      bazbaz(^^/, 0)
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex114",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex117#1",
        source: #"""
      _ = qux((/), "(") / 2
      """#,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex117",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex118#1",
        source: """
      _ = qux(/, 1) // this comment tests to make sure we don't try and end the regex on the starting '/' of '//'.
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex118",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex119#1",
        source: """
      _ = qux(/, 1) /* same thing with a block comment */
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex119",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex122#1",
        source: """
      quxqux(/^/) 
      quxqux((/^/)) 
      quxqux({ $0 /^/ $1 })
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex122",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex123#1",
        source: """
      quxqux(!/^/)
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex123",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex124#1",
        source: """
      quxqux(/^)
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex124",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex125#1",
        source: """
      _ = quxqux(/^) / 1
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex125",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex127#1",
        source: """
      _ = arr.reduce(1, /) / 3
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex127",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex128#1",
        source: """
      _ = arr.reduce(1, /) + arr.reduce(1, /)
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex128",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex130#1",
        source: """
      _ = (/x)
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex130",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex131#1",
        source: """
      _ = (/x)/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex131",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex132#1",
        source: """
      _ = (/[(0)])/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex132",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex133#1",
        source: """
      _ = /[(0)]/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex133",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex134#1",
        source: """
      _ = /(x)/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex134",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex135#1",
        source: """
      _ = /[)]/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex135",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex136#1",
        source: #"""
      _ = /[a\])]/
      """#,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex136",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex137#1",
        source: """
      _ = /([)])/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex137",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex138#1",
        source: """
      _ = /]]][)]/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex138",
        syntaxVersion: "603.0.1",
        compilerRejects: "expected expression after unary operator"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex141#1",
        source: """
      let fn: (Int, Int) -> Int = (/)
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex141",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex147#1",
        source: """
      _ = ^/x/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex147",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex148#1",
        source: """
      _ = (^/x)/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex148",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex149#1",
        source: """
      _ = (!!/x/)
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex149",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex152#1",
        source: #"""
      _ = (^/)("/")
      """#,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex152",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex155#1",
        source: """
      _ = /./
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex155",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex157#1",
        source: #"""
      _ = /\ /
      """#,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex157",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex160#1",
        source: """
      _ = #/  /#
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex160",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex161#1",
        source: #"""
      _ = /x\ /
      """#,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex161",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex162#1",
        source: #"""
      _ = /\ \ /
      """#,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex162",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex163#1",
        source: """

      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex163",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex167#1",
        source: #"""
      _ = /\)/
      """#,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex167",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex168#1",
        source: """
      _ = /)/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex168",
        syntaxVersion: "603.0.1",
        compilerRejects: "expected expression after unary operator"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex169#1",
        source: """
      _ = /,/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex169",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex170#1",
        source: """
      _ = /}/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex170",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex171#1",
        source: """
      _ = /]/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex171",
        syntaxVersion: "603.0.1",
        compilerRejects: "expected expression after unary operator"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex172#1",
        source: """
      _ = /:/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex172",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex173#1",
        source: """
      _ = /;/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex173",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex175#1",
        source: """
      _ = /0xG/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex175",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex176#1",
        source: """
      _ = /0oG/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex176",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex177#1",
        source: #"""
      _ = /"/
      """#,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex177",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex178#1",
        source: """
      _ = /'/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex178",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex179#1",
        source: """
      _ = /<#placeholder#>/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex179",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex180#1",
        source: """
      _ = ^^/0xG/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex180",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex181#1",
        source: """
      _ = ^^/0oG/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex181",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex182#1",
        source: #"""
      _ = ^^/"/
      """#,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex182",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex183#1",
        source: """
      _ = ^^/'/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex183",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex184#1",
        source: """
      _ = ^^/<#placeholder#>/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex184",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex185#1",
        source: """
      _ = (^^/0xG/)
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex185",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex186#1",
        source: """
      _ = (^^/0oG/)
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex186",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex187#1",
        source: #"""
      _ = (^^/"/)
      """#,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex187",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex188#1",
        source: """
      _ = (^^/'/)
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex188",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex189#1",
        source: """
      _ = (^^/<#placeholder#>/)
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex189",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testGenericDisambiguation1#1",
        source: """
      struct A<B> {
        init(x:Int) {}
        static func c() {}
        struct C<D> {
          static func e() {}
        }
        struct F {}
      }
      struct B {}
      struct D {}
      """,
        origin: "GenericDisambiguationTests.testGenericDisambiguation1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testGenericDisambiguation2#1",
        source: """
      protocol Runcible {}
      protocol Fungible {}
      """,
        origin: "GenericDisambiguationTests.testGenericDisambiguation2",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testGenericDisambiguation3#1",
        source: """
      func meta<T>(_ m: T.Type) {}
      func meta2<T>(_ m: T.Type, _ x: Int) {}
      """,
        origin: "GenericDisambiguationTests.testGenericDisambiguation3",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testGenericDisambiguation4#1",
        source: """
      func generic<T>(_ x: T) {}
      """,
        origin: "GenericDisambiguationTests.testGenericDisambiguation4",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testGenericDisambiguation5#1",
        source: """
      var a, b, c, d : Int
      """,
        origin: "GenericDisambiguationTests.testGenericDisambiguation5",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testGenericDisambiguation6a#1",
        source: """
      _ = a < b
      """,
        origin: "GenericDisambiguationTests.testGenericDisambiguation6a",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testGenericDisambiguation6b#1",
        source: """
      _ = (a < b, c > d)
      """,
        origin: "GenericDisambiguationTests.testGenericDisambiguation6b",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testGenericDisambiguation6c#1",
        source: """
      (a < b, c > (d))
      """,
        origin: "GenericDisambiguationTests.testGenericDisambiguation6c",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testGenericDisambiguation6d#1",
        source: """
      (a<b, c>(d))
      """,
        origin: "GenericDisambiguationTests.testGenericDisambiguation6d",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testGenericDisambiguation6e#1",
        source: """
      _ = a>(b)
      """,
        origin: "GenericDisambiguationTests.testGenericDisambiguation6e",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testGenericDisambiguation6f#1",
        source: """
      _ = a > (b)
      """,
        origin: "GenericDisambiguationTests.testGenericDisambiguation6f",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testGenericDisambiguation7#1",
        source: """
      generic<Int>(0)
      """,
        origin: "GenericDisambiguationTests.testGenericDisambiguation7",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testGenericDisambiguation8#1",
        source: """
      A<B>.c()
      A<A<B>>.c()
      A<A<B>.F>.c()
      A<(A<B>) -> B>.c()
      A<[[Int]]>.c()
      A<[[A<B>]]>.c()
      A<(Int, UnicodeScalar)>.c()
      A<(a:Int, b:UnicodeScalar)>.c()
      A<Runcible & Fungible>.c()
      A<@convention(c) () -> Int32>.c()
      A<(@autoclosure @escaping () -> Int, Int) -> Void>.c()
      _ = [@convention(block) ()  -> Int]().count
      _ = [String: (@escaping (A<B>) -> Int) -> Void]().keys
      """,
        origin: "GenericDisambiguationTests.testGenericDisambiguation8",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testGenericDisambiguation9#1",
        source: """
      A<B>(x: 0)
      """,
        origin: "GenericDisambiguationTests.testGenericDisambiguation9",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testGenericDisambiguation10#1",
        source: """
      meta(A<B>.self)
      """,
        origin: "GenericDisambiguationTests.testGenericDisambiguation10",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testGenericDisambiguation11#1",
        source: """
      meta2(A<B>.self, 0)
      """,
        origin: "GenericDisambiguationTests.testGenericDisambiguation11",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testGenericDisambiguation12#1",
        source: """
      A<B>.C<D>.e()
      """,
        origin: "GenericDisambiguationTests.testGenericDisambiguation12",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testGenericDisambiguation13#1",
        source: """
      A<B>.C<D>(0)
      """,
        origin: "GenericDisambiguationTests.testGenericDisambiguation13",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testGenericDisambiguation14#1",
        source: """
      meta(A<B>.C<D>.self)
      meta2(A<B>.C<D>.self, 0)
      """,
        origin: "GenericDisambiguationTests.testGenericDisambiguation14",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testGenericDisambiguation15#1",
        source: """
      A<>.c()
      """,
        origin: "GenericDisambiguationTests.testGenericDisambiguation15",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testGenericDisambiguation16#1",
        source: """
      A<B, D>.c()
      """,
        origin: "GenericDisambiguationTests.testGenericDisambiguation16",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testGenericDisambiguation17#1",
        source: """
      A<B?>(x: 0) // parses as type
      _ = a < b ? c : d
      """,
        origin: "GenericDisambiguationTests.testGenericDisambiguation17",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testGenericDisambiguation18#1",
        source: """
      A<(B) throws -> D>(x: 0)
      """,
        origin: "GenericDisambiguationTests.testGenericDisambiguation18",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testGuardTopLevel1#1",
        source: """
      let a: Int? = 1
      guard let b = a else {
      }
      """,
        origin: "GuardTopLevelTests.testGuardTopLevel1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testGuardTopLevel2#1",
        source: """
      func foo() {} // to interrupt the TopLevelCodeDecl
      """,
        origin: "GuardTopLevelTests.testGuardTopLevel2",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testGuardTopLevel3#1",
        source: """
      let c = b
      """,
        origin: "GuardTopLevelTests.testGuardTopLevel3",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testHashbangLibrary1#1",
        source: """
      #!/usr/bin/swift
      class Foo {}
      """,
        origin: "HashbangLibraryTests.testHashbangLibrary1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testHashbangMain1#1",
        source: """
      #!/usr/bin/swift
      let x = 42
      x + x
      // Check that we skip the hashbang at the beginning of the file.
      """,
        origin: "HashbangMainTests.testHashbangMain1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testIdentifiers1#1",
        source: """
      func my_print<T>(_ t: T) {}
      """,
        origin: "IdentifiersTests.testIdentifiers1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testIdentifiers2#1",
        source: #"""
      class 你好 {
        class שלום {
          class வணக்கம் {
            class Γειά {
              class func привет() {
                my_print("hello")
              }
            }
          }
        }
      }
      """#,
        origin: "IdentifiersTests.testIdentifiers2",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testIdentifiers3#1",
        source: """
      你好.שלום.வணக்கம்.Γειά.привет()
      """,
        origin: "IdentifiersTests.testIdentifiers3",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testIdentifiers4#1",
        source: """
      // Identifiers cannot start with combining chars.
      _ = .́duh()
      """,
        origin: "IdentifiersTests.testIdentifiers4",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testIdentifiers5#1",
        source: """
      // Combining characters can be used within identifiers.
      func s̈pin̈al_tap̈() {}
      """,
        origin: "IdentifiersTests.testIdentifiers5",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testStructNamedLowercaseAny#1",
        source: """
      struct any {}
      """,
        origin: "IdentifiersTests.testStructNamedLowercaseAny",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testIdentifiers9#1",
        source: """
      // SIL keywords are tokenized as normal identifiers in non-SIL mode.
      _ = undef
      _ = sil
      _ = sil_stage
      _ = sil_vtable
      _ = sil_global
      _ = sil_witness_table
      _ = sil_default_witness_table
      _ = sil_coverage_map
      _ = sil_scope
      """,
        origin: "IdentifiersTests.testIdentifiers9",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testIdentifiers10#1",
        source: """
      // https://github.com/apple/swift/issues/57542
      // Make sure we do not parse the '_' on the newline as being part of the 'variable' identifier on the line before.
      """,
        origin: "IdentifiersTests.testIdentifiers10",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testIdentifiers11#1",
        source: """
      @propertyWrapper
      struct Wrapper {
        var wrappedValue = 0
      }
      """,
        origin: "IdentifiersTests.testIdentifiers11",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testIdentifiers12#1",
        source: """
      func localScope() {
        @Wrapper var variable
        _ = 0
      }
      """,
        origin: "IdentifiersTests.testIdentifiers12",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr1#1",
        source: """
      postfix operator ++
      postfix func ++ (_: Int) -> Int { 0 }
      """,
        origin: "IfconfigExprTests.testIfconfigExpr1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr2#1",
        source: """
      struct OneResult {}
      struct TwoResult {}
      """,
        origin: "IfconfigExprTests.testIfconfigExpr2",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr3#1",
        source: """
      protocol MyProto {
          func optionalMethod() -> [Int]?
      }
      struct MyStruct {
          var optionalMember: MyProto? { nil }
          func methodOne() -> OneResult { OneResult() }
          func methodTwo() -> TwoResult { TwoResult() }
      }
      """,
        origin: "IfconfigExprTests.testIfconfigExpr3",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr4#1",
        source: """
      func globalFunc<T>(_ arg: T) -> T { arg }
      """,
        origin: "IfconfigExprTests.testIfconfigExpr4",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr5#1",
        source: """
      func testBasic(baseExpr: MyStruct) {
          baseExpr
      #if CONDITION_1
            .methodOne()
      #else
            .methodTwo()
      #endif
      }
      """,
        origin: "IfconfigExprTests.testIfconfigExpr5",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr6#1",
        source: """
      MyStruct()
      #if CONDITION_1
        .methodOne()
      #else
        .methodTwo()
      #endif
      """,
        origin: "IfconfigExprTests.testIfconfigExpr6",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr10#1",
        source: """
      func consecutiveIfConfig(baseExpr: MyStruct) {
          baseExpr
      #if CONDITION_1
        .methodOne()
      #endif
      #if CONDITION_2
        .methodTwo()
      #endif
        .unknownMethod()
      }
      """,
        origin: "IfconfigExprTests.testIfconfigExpr10",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr11#1",
        source: """
      func nestedIfConfig(baseExpr: MyStruct) {
        baseExpr
      #if CONDITION_1
        #if CONDITION_2
          .methodOne()
        #endif
        #if CONDITION_1
          .methodTwo()
        #endif
      #else
        .unknownMethod1()
        #if CONDITION_2
          .unknownMethod2()
        #endif
      #endif
      }
      """,
        origin: "IfconfigExprTests.testIfconfigExpr11",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr12#1",
        source: """
      func ifconfigExprInExpr(baseExpr: MyStruct) {
        globalFunc(
          baseExpr
      #if CONDITION_1
            .methodOne()
      #else
            .methodTwo()
      #endif
        )
      }
      """,
        origin: "IfconfigExprTests.testIfconfigExpr12",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr13#1",
        source: """
      #if canImport(A, _version: 2)
        let a = 1
      #endif
      """,
        origin: "IfconfigExprTests.testIfconfigExpr13",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr14#1",
        source: """
      #if canImport(A, _version: 2.2)
        let a = 1
      #endif
      """,
        origin: "IfconfigExprTests.testIfconfigExpr14",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr15#1",
        source: """
      #if canImport(A, _version: 2.2.2)
        let a = 1
      #endif
      """,
        origin: "IfconfigExprTests.testIfconfigExpr15",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr16#1",
        source: """
      #if canImport(A, _version: 2.2.2.2)
        let a = 1
      #endif
      """,
        origin: "IfconfigExprTests.testIfconfigExpr16",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr17#1",
        source: """
      #if canImport(A, _version: 2.2.2.2.2)
        let a = 1
      #endif
      """,
        origin: "IfconfigExprTests.testIfconfigExpr17",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr18#1",
        source: """
      #if canImport(A, _underlyingVersion: 4)
        let a = 1
      #endif
      """,
        origin: "IfconfigExprTests.testIfconfigExpr18",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr19#1",
        source: """
      #if canImport(A, _underlyingVersion: 2.200)
        let a = 1
      #endif
      """,
        origin: "IfconfigExprTests.testIfconfigExpr19",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr20#1",
        source: """
      #if canImport(A, _underlyingVersion: 2.200.1)
        let a = 1
      #endif
      """,
        origin: "IfconfigExprTests.testIfconfigExpr20",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr21#1",
        source: """
      #if canImport(A, _underlyingVersion: 2.200.1.3)
        let a = 1
      #endif
      """,
        origin: "IfconfigExprTests.testIfconfigExpr21",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr22#1",
        source: """
      #if canImport(A, unknown: 2.2)
        let a = 1
      #endif
      """,
        origin: "IfconfigExprTests.testIfconfigExpr22",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr23#1",
        source: """
      #if canImport(A,)
        let a = 1
      #endif
      """,
        origin: "IfconfigExprTests.testIfconfigExpr23",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr24#1",
        source: """
      #if canImport(A, 2.2)
        let a = 1
      #endif
      """,
        origin: "IfconfigExprTests.testIfconfigExpr24",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr25#1",
        source: """
      #if canImport(A, 2.2, 1.1)
        let a = 1
      #endif
      """,
        origin: "IfconfigExprTests.testIfconfigExpr25",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr27#1",
        source: #"""
      #if canImport(A, _version: "")
        let a = 1
      #endif
      """#,
        origin: "IfconfigExprTests.testIfconfigExpr27",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr28#1",
        source: """
      #if canImport(A, _version: >=2.2)
        let a = 1
      #endif
      """,
        origin: "IfconfigExprTests.testIfconfigExpr28",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr30#1",
        source: #"""
      #if canImport(A, _version: "20A301")
        let a = 1
      #endif
      """#,
        origin: "IfconfigExprTests.testIfconfigExpr30",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testIfConfigExpr33#1",
        source: """
      #if arch(x86_64)
      #line
      #endif
      """,
        origin: "IfconfigExprTests.testIfConfigExpr33",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testCanImportFuncCall#1",
        source: """
      canImport(a, b, c)
      """,
        origin: "IfconfigExprTests.testCanImportFuncCall",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testArchFuncCall#1",
        source: """
      arch()
      """,
        origin: "IfconfigExprTests.testArchFuncCall",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOsFuncCall#1",
        source: """
      os(bogus)
      """,
        origin: "IfconfigExprTests.testOsFuncCall",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTargetEnvironmentFuncCall#1",
        source: """
      targetEnvironment(foo, bar)
      """,
        origin: "IfconfigExprTests.testTargetEnvironmentFuncCall",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testCompilerFuncCall#1",
        source: """
      compiler(a)
      """,
        origin: "IfconfigExprTests.testCompilerFuncCall",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwiftFuncCall#1",
        source: """
      swift(foo)
      """,
        origin: "IfconfigExprTests.testSwiftFuncCall",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testUnknownPlatform1#1",
        source: """
      #if hasGreeble(blah)
      #endif
      """,
        origin: "IfconfigExprTests.testUnknownPlatform1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testUnknownPlatform2#1",
        source: """
      // Future compiler, short-circuit right-hand side
      #if compiler(>=10.0) && hasGreeble(blah)
      #endif
      """,
        origin: "IfconfigExprTests.testUnknownPlatform2",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testUnknownPlatform3#1",
        source: """
      // Current compiler, short-circuit right-hand side
      #if compiler(<10.0) || hasGreeble(blah)
      #endif
      """,
        origin: "IfconfigExprTests.testUnknownPlatform3",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testUnknownPlatform4#1",
        source: """
      // This compiler, don't short-circuit.
      #if compiler(>=5.7) && hasGreeble(blah)
      #endif
      """,
        origin: "IfconfigExprTests.testUnknownPlatform4",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testUnknownPlatform5#1",
        source: """
      // This compiler, don't short-circuit.
      #if compiler(<5.8) || hasGreeble(blah)
      #endif
      """,
        origin: "IfconfigExprTests.testUnknownPlatform5",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testUnknownPlatform6#1",
        source: #"""
      // Not a "version" check, so don't short-circuit.
      #if os(macOS) && hasGreeble(blah)
      #endif
      """#,
        origin: "IfconfigExprTests.testUnknownPlatform6",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testUpcomingFeature1#1",
        source: """
      #if hasFeature(17)
      #endif
      """,
        origin: "IfconfigExprTests.testUpcomingFeature1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testCanImportWithStringVersion#1",
        source: """
      #if canImport(MyModule, _version: "1.2.3")
      #endif
      """,
        origin: "IfconfigExprTests.testCanImportWithStringVersion",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testImplicitGetterIncomplete1#1",
        source: """
      func test1() {
        var a : Int {
      #if arch(x86_64)
          return 0
      #else
          return 1
      #endif
        }
      }
      """,
        origin: "ImplicitGetterIncompleteTests.testImplicitGetterIncomplete1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInitDeinit2#1",
        source: """
      struct FooStructConstructorB {
        init()
      }
      """,
        origin: "InitDeinitTests.testInitDeinit2",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInitDeinit4#1",
        source: """
      struct FooStructConstructorD {
        init() -> FooStructConstructorD { }
      }
      """,
        origin: "InitDeinitTests.testInitDeinit4",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInitDeinit5a#1",
        source: """
      struct FooStructDeinitializerA {
        deinit
      }
      """,
        origin: "InitDeinitTests.testInitDeinit5a",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInitDeinit6#1",
        source: """
      struct FooStructDeinitializerB {
        deinit
      }
      """,
        origin: "InitDeinitTests.testInitDeinit6",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInitDeinit7#1",
        source: """
      struct FooStructDeinitializerC {
        deinit {}
      }
      """,
        origin: "InitDeinitTests.testInitDeinit7",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInitDeinit9#1",
        source: """
      class FooClassDeinitializerB {
        deinit { }
      }
      """,
        origin: "InitDeinitTests.testInitDeinit9",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInitDeinit12#1",
        source: """
      deinit {}
      deinit
      deinit {}
      """,
        origin: "InitDeinitTests.testInitDeinit12",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInitDeinit13#1",
        source: """
      struct BarStruct {
        init() {}
        deinit {}
      }
      """,
        origin: "InitDeinitTests.testInitDeinit13",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInitDeinit14#1",
        source: """
      extension BarStruct {
        init(x : Int) {}
        // When/if we allow 'var' in extensions, then we should also allow dtors
        deinit {}
      }
      """,
        origin: "InitDeinitTests.testInitDeinit14",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInitDeinit15#1",
        source: """
      enum BarUnion {
        init() {}
        deinit {}
      }
      """,
        origin: "InitDeinitTests.testInitDeinit15",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInitDeinit16#1",
        source: """
      extension BarUnion {
        init(x : Int) {}
        deinit {}
      }
      """,
        origin: "InitDeinitTests.testInitDeinit16",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInitDeinit17#1",
        source: """
      class BarClass {
        init() {}
        deinit {}
      }
      """,
        origin: "InitDeinitTests.testInitDeinit17",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInitDeinit18#1",
        source: """
      extension BarClass {
        convenience init(x : Int) { self.init() }
        deinit {}
      }
      """,
        origin: "InitDeinitTests.testInitDeinit18",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInitDeinit19#1",
        source: """
      protocol BarProtocol {
        init() {}
        deinit {}
      }
      """,
        origin: "InitDeinitTests.testInitDeinit19",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInitDeinit20#1",
        source: """
      extension BarProtocol {
        init(x : Int) {}
        deinit {}
      }
      """,
        origin: "InitDeinitTests.testInitDeinit20",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInitDeinit21#1",
        source: """
      func fooFunc() {
        init() {}
        deinit {}
      }
      """,
        origin: "InitDeinitTests.testInitDeinit21",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInitDeinit22#1",
        source: """
      func barFunc() {
        var x : () = { () -> () in
          init() {}
          return
        } ()
        var y : () = { () -> () in
          deinit {}
          return
        } ()
      }
      """,
        origin: "InitDeinitTests.testInitDeinit22",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInitDeinit24#1",
        source: """
      class Aaron {
        convenience init() { init(x: 1) }
      }
      """,
        origin: "InitDeinitTests.testInitDeinit24",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInitDeinit25#1",
        source: """
      class Theodosia: Aaron {
        init() {
          init(x: 2)
        }
      }
      """,
        origin: "InitDeinitTests.testInitDeinit25",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInitDeinit26#1",
        source: """
      struct AaronStruct {
        init(x: Int) {}
        init() { init(x: 1) }
      }
      """,
        origin: "InitDeinitTests.testInitDeinit26",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInitDeinit27#1",
        source: """
      enum AaronEnum: Int {
        case A = 1
        init(x: Int) { init(rawValue: x)! }
      }
      """,
        origin: "InitDeinitTests.testInitDeinit27",
        syntaxVersion: "603.0.1",
        disabledReason: "parser produces no root yield for initializer body containing implicit init(rawValue:)!"
    ),
    SwiftSnippet(
        label: "testInitDeinit28#1",
        source: """
      init(_ foo: T) -> Int where T: Comparable {}
      """,
        origin: "InitDeinitTests.testInitDeinit28",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDeinitInSwiftinterfaceIsFollowedByFinalFunc#1",
        source: """
      class Foo {
        deinit
        final func foo()
      }
      """,
        origin: "InitDeinitTests.testDeinitInSwiftinterfaceIsFollowedByFinalFunc",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testDeinitAsync#1",
        source: """
      class FooClassDeinitializerA {
        deinit async {}
      }
      """,
        origin: "InitDeinitTests.testDeinitAsync",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAsyncDeinit#1",
        source: """
      class FooClassDeinitializerA {
        async deinit {}
      }
      """,
        origin: "InitDeinitTests.testAsyncDeinit",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInvalidStringInterpolationProtocol1#1",
        source: """
      // Has a lot of invalid 'appendInterpolation' methods
      public struct BadStringInterpolation: StringInterpolationProtocol {
        //  {{educational-notes=string-interpolation-conformance}}
        public init(literalCapacity: Int, interpolationCount: Int) {}
        public mutating func appendLiteral(_: String) {}
        public static func appendInterpolation(static: ()) {
          //  {{educational-notes=string-interpolation-conformance}}
        }
        private func appendInterpolation(private: ()) {
        }
        func appendInterpolation(default: ()) {
        }
        public func appendInterpolation(intResult: ()) -> Int {
          //  {{educational-notes=string-interpolation-conformance}}
        }
      }
      """,
        origin: "InvalidStringInterpolationProtocolTests.testInvalidStringInterpolationProtocol1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInvalidStringInterpolationProtocol2#1",
        source: """
      // Has no 'appendInterpolation' methods at all
      public struct IncompleteStringInterpolation: StringInterpolationProtocol {
        public init(literalCapacity: Int, interpolationCount: Int) {}
        public mutating func appendLiteral(_: String) {}
      }
      """,
        origin: "InvalidStringInterpolationProtocolTests.testInvalidStringInterpolationProtocol2",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInvalidStringInterpolationProtocol3#1",
        source: """
      // Has only good 'appendInterpolation' methods.
      public struct GoodStringInterpolation: StringInterpolationProtocol {
        public init(literalCapacity: Int, interpolationCount: Int) {}
        public mutating func appendLiteral(_: String) {}
        public func appendInterpolation(noResult: ()) {}
        public func appendInterpolation(voidResult: ()) -> Void {}
        @discardableResult
        public func appendInterpolation(discardableResult: ()) -> Int {}
      }
      """,
        origin: "InvalidStringInterpolationProtocolTests.testInvalidStringInterpolationProtocol3",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInvalidStringInterpolationProtocol4#1",
        source: """
      // Has only good 'appendInterpolation' methods, but they're in an extension.
      public struct GoodSplitStringInterpolation: StringInterpolationProtocol {
        public init(literalCapacity: Int, interpolationCount: Int) {}
        public mutating func appendLiteral(_: String) {}
      }
      """,
        origin: "InvalidStringInterpolationProtocolTests.testInvalidStringInterpolationProtocol4",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInvalidStringInterpolationProtocol5#1",
        source: """
      extension GoodSplitStringInterpolation {
        public func appendInterpolation(noResult: ()) {}
        public func appendInterpolation(voidResult: ()) -> Void {}
        @discardableResult
        public func appendInterpolation(discardableResult: ()) -> Int {}
      }
      """,
        origin: "InvalidStringInterpolationProtocolTests.testInvalidStringInterpolationProtocol5",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInvalidStringInterpolationProtocol6#1",
        source: """
      // Has only good 'appendInterpolation' methods, and is not public.
      struct GoodNonPublicStringInterpolation: StringInterpolationProtocol {
        init(literalCapacity: Int, interpolationCount: Int) {}
        mutating func appendLiteral(_: String) {}
        func appendInterpolation(noResult: ()) {}
        public func appendInterpolation(voidResult: ()) -> Void {}
        @discardableResult
        func appendInterpolation(discardableResult: ()) -> Int {}
      }
      """,
        origin: "InvalidStringInterpolationProtocolTests.testInvalidStringInterpolationProtocol6",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInvalidStringInterpolationProtocol7#1",
        source: """
      // Has a mixture of good and bad 'appendInterpolation' methods.
      // We don't emit any errors in this case--we assume the others
      // are implementation details or something.
      public struct GoodStringInterpolationWithBadOnesToo: StringInterpolationProtocol {
        public init(literalCapacity: Int, interpolationCount: Int) {}
        public mutating func appendLiteral(_: String) {}
        public func appendInterpolation(noResult: ()) {}
        public static func appendInterpolation(static: ()) {}
        private func appendInterpolation(private: ()) {}
        func appendInterpolation(default: ()) {}
        public func appendInterpolation(intResult: ()) -> Int {}
      }
      """,
        origin: "InvalidStringInterpolationProtocolTests.testInvalidStringInterpolationProtocol7",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInvalid5#1",
        source: """
      func runAction() {}
      """,
        origin: "InvalidTests.testInvalid5",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInvalid7#1",
        source: """
      super.init()
      """,
        origin: "InvalidTests.testInvalid7",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInvalid12#1",
        source: """
      protocol Animal<Food> {
        func feed(_ food: Food)
      }
      """,
        origin: "InvalidTests.testInvalid12",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInvalid16a#1",
        source: """
      func f1_43591(a : inout inout Int) {}
      """,
        origin: "InvalidTests.testInvalid16a",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInvalid28#1",
        source: """
      prefix operator %
      prefix func %<T>(x: T) -> T { return x } // No error expected - the < is considered an identifier but is peeled off by the parser.
      """,
        origin: "InvalidTests.testInvalid28",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInvalid30#1",
        source: """
      let x: () = ()
      !()
      !(())
      !(x)
      !x
      """,
        origin: "InvalidTests.testInvalid30",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInvalid32#1",
        source: """
      func f1_50734(@NSApplicationMain x: Int) {}
      """,
        origin: "InvalidTests.testInvalid32",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInvalid33#1",
        source: """
      func f2_50734(@available(iOS, deprecated: 0) x: Int) {}
      """,
        origin: "InvalidTests.testInvalid33",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInvalid34#1",
        source: """
      func f3_50734(@discardableResult x: Int) {}
      """,
        origin: "InvalidTests.testInvalid34",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInvalid35#1",
        source: """
      func f4_50734(@objcMembers x: String) {}
      """,
        origin: "InvalidTests.testInvalid35",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInvalid36#1",
        source: """
      func f5_50734(@weak x: String) {}
      """,
        origin: "InvalidTests.testInvalid36",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInvalid37#1",
        source: """
      class C_50734<@NSApplicationMain T: AnyObject> {}
      """,
        origin: "InvalidTests.testInvalid37",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInvalid38#1",
        source: """
      func f6_50734<@discardableResult T>(x: T) {}
      """,
        origin: "InvalidTests.testInvalid38",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInvalid39#1",
        source: """
      enum E_50734<@indirect T> {}
      """,
        origin: "InvalidTests.testInvalid39",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInvalid40#1",
        source: """
      protocol P {
        @available(swift, introduced: 4.2) associatedtype Assoc
      }
      """,
        origin: "InvalidTests.testInvalid40",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns1#1",
        source: """
      import imported_enums
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns3#1",
        source: """
      var x:Int
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns3",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns4#1",
        source: """
      func square(_ x: Int) -> Int { return x*x }
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns4",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns5#1",
        source: """
      struct A<B> {
        struct C<D> { }
      }
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns5",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns6#1",
        source: #"""
      switch x {
      // Expressions as patterns.
      case 0:
        ()
      case 1 + 2:
        ()
      case square(9):
        ()
      // 'var' and 'let' patterns.
      case var a:
        a = 1
      case let a:
        a = 1
      case inout a:
        a = 1
      case _mutating a:
        a = 1
      case _borrowing a:
        a = 1
      case _consuming a:
        a = 1
      case var var a:
        a += 1
      case var let a:
        print(a, terminator: "")
      case var (var b):
        b += 1
      // 'Any' pattern.
      case _:
        ()
      // patterns are resolved in expression-only positions are errors.
      case 1 + (_):
        ()
      }
      """#,
        origin: "MatchingPatternsTests.testMatchingPatterns6",
        syntaxVersion: "603.0.1",
        disabledReason: "experimental feature"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns7#1",
        source: """
      switch (x,x) {
      case (var a, var a):
        fallthrough
      case _:
        ()
      }
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns7",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns8#1",
        source: """
      var e : Any = 0
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns8",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns7a#1",
        source: """
      switch (x,x) {
      case _borrowing a:
        ()
      }
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns7a",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns7b#1",
        source: """
      switch (x,x) {
      case _mutating a:
        ()
      }
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns7b",
        syntaxVersion: "603.0.1",
        disabledReason: "experimental feature"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns7c#1",
        source: """
      switch (x,x) {
      case _consuming a:
        ()
      }
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns7c",
        syntaxVersion: "603.0.1",
        disabledReason: "experimental feature"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns9#1",
        source: """
      switch e {
      // 'is' pattern.
      case is Int,
           is A<Int>,
           is A<Int>.C<Int>,
           is (Int, Int),
           is (a: Int, b: Int):
        ()
      }
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns9",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns10#1",
        source: """
      // Enum patterns.
      enum Foo { case A, B, C }
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns10",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns11#1",
        source: """
      func == <T>(_: Voluntary<T>, _: Voluntary<T>) -> Bool { return true }
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns11",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns12#1",
        source: """
      enum Voluntary<T> : Equatable {
        case Naught
        case Mere(T)
        case Twain(T, T)
        func enumMethod(_ other: Voluntary<T>, foo: Foo) {
          switch self {
          case other:
            ()
          case .Naught,
               .Naught(),
               .Naught(_),
               .Naught(_, _):
            ()
          case .Mere,
               .Mere(),
               .Mere(_),
               .Mere(_, _):
            ()
          case .Twain(),
               .Twain(_),
               .Twain(_, _),
               .Twain(_, _, _):
            ()
          }
          switch foo {
          case .Naught:
            ()
          case .A, .B, .C:
            ()
          }
        }
      }
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns12",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns13#1",
        source: """
      var n : Voluntary<Int> = .Naught
      if case let .Naught(value) = n {}
      if case let .Naught(value1, value2, value3) = n {}
      if case inout .Naught(value) = n {}
      if case _mutating .Naught(value) = n {}
      if case _borrowing .Naught(value) = n {}
      if case _consuming .Naught(value) = n {}
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns13",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns14#1",
        source: """
      switch n {
      case Foo.A:
        ()
      case Voluntary<Int>.Naught,
           Voluntary<Int>.Naught(),
           Voluntary<Int>.Naught(_, _),
           Voluntary.Naught,
           .Naught:
        ()
      case Voluntary<Int>.Mere,
           Voluntary<Int>.Mere(_),
           Voluntary<Int>.Mere(_, _),
           Voluntary.Mere,
           Voluntary.Mere(_),
           .Mere,
           .Mere(_):
        ()
      case .Twain,
           .Twain(_),
           .Twain(_, _),
           .Twain(_, _, _):
        ()
      }
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns14",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns15#1",
        source: """
      var notAnEnum = 0
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns15",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns16#1",
        source: """
      switch notAnEnum {
      case .Foo:
        ()
      }
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns16",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns17#1",
        source: """
      struct ContainsEnum {
        enum Possible<T> {
          case Naught
          case Mere(T)
          case Twain(T, T)
        }
        func member(_ n: Possible<Int>) {
          switch n {
          case ContainsEnum.Possible<Int>.Naught,
               ContainsEnum.Possible.Naught,
               Possible<Int>.Naught,
               Possible.Naught,
               .Naught:
            ()
          }
        }
      }
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns17",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns18#1",
        source: """
      func nonmemberAccessesMemberType(_ n: ContainsEnum.Possible<Int>) {
        switch n {
        case ContainsEnum.Possible<Int>.Naught,
             .Naught:
          ()
        }
      }
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns18",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns19#1",
        source: """
      var m : ImportedEnum = .Simple
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns19",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns20#1",
        source: """
      switch m {
      case imported_enums.ImportedEnum.Simple,
           ImportedEnum.Simple,
           .Simple:
        ()
      case imported_enums.ImportedEnum.Compound,
           imported_enums.ImportedEnum.Compound(_),
           ImportedEnum.Compound,
           ImportedEnum.Compound(_),
           .Compound,
           .Compound(_):
        ()
      }
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns20",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns21#1",
        source: """
      // Check that single-element tuple payloads work sensibly in patterns.
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns21",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns22#1",
        source: """
      enum LabeledScalarPayload {
        case Payload(name: Int)
      }
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns22",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns23#1",
        source: """
      var lsp: LabeledScalarPayload = .Payload(name: 0)
      func acceptInt(_: Int) {}
      func acceptString(_: String) {}
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns23",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns24#1",
        source: #"""
      switch lsp {
      case .Payload(0):
        ()
      case .Payload(name: 0):
        ()
      case let .Payload(x):
        acceptInt(x)
        acceptString("\(x)")
      case let .Payload(name: x):
        acceptInt(x)
        acceptString("\(x)")
      case let .Payload((name: x)):
        acceptInt(x)
        acceptString("\(x)")
      case .Payload(let (name: x)):
        acceptInt(x)
        acceptString("\(x)")
      case .Payload(let (name: x)):
        acceptInt(x)
        acceptString("\(x)")
      case .Payload(let x):
        acceptInt(x)
        acceptString("\(x)")
      case .Payload((let x)):
        acceptInt(x)
        acceptString("\(x)")
      case .Payload(inout x):
        acceptInt(x)
      case .Payload(_mutating x):
        acceptInt(x)
      case .Payload(_borrowing x):
        acceptInt(x)
      case .Payload(_consuming x):
        acceptInt(x)
      }
      """#,
        origin: "MatchingPatternsTests.testMatchingPatterns24",
        syntaxVersion: "603.0.1",
        disabledReason: "experimental feature"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns25#1",
        source: """
      // Property patterns.
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns25",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns26#1",
        source: """
      struct S {
        static var stat: Int = 0
        var x, y : Int
        var comp : Int {
          return x + y
        }
        func nonProperty() {}
      }
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns26",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns27#1",
        source: """
      // Tuple patterns.
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns27",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns28#1",
        source: """
      var t = (1, 2, 3)
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns28",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns29#1",
        source: """
      prefix operator +++
      infix operator +++
      prefix func +++(x: (Int,Int,Int)) -> (Int,Int,Int) { return x }
      func +++(x: (Int,Int,Int), y: (Int,Int,Int)) -> (Int,Int,Int) {
        return (x.0+y.0, x.1+y.1, x.2+y.2)
      }
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns29",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns30#1",
        source: """
      switch t {
      case (_, var a, 3):
        a += 1
      case (_, inout a, 3):
        a += 1
      case (_, _mutating a, 3):
        a += 1
      case (_, _borrowing a, 3):
        a += 1
      case (_, _consuming a, 3):
        a += 1
      case var (_, b, 3):
        b += 1
      case var (_, var c, 3):
        c += 1
      case (1, 2, 3):
        ()
      // patterns in expression-only positions are errors.
      case +++(_, var d, 3):
        ()
      case (_, var e, 3) +++ (1, 2, 3):
        ()
      case (let (_, _, _)) + 1:
        ()
      }
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns30",
        syntaxVersion: "603.0.1",
        compilerRejects: "expected ',' separator"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns31#1",
        source: #"""
      class Base { }
      class Derived : Base { }
      """#,
        origin: "MatchingPatternsTests.testMatchingPatterns31",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns32#1",
        source: """
      switch [Derived(), Derived(), Base()] {
      case let ds as [Derived]:
        ()
      case is [Derived]:
        ()
      default:
        ()
      }
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns32",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns33#1",
        source: """
      // Optional patterns.
      let op1 : Int?
      let op2 : Int??
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns33",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns34#1",
        source: """
      switch op1 {
      case nil: break
      case 1?: break
      case _?: break
      }
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns34",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns35#1",
        source: """
      switch op2 {
      case nil: break
      case _?: break
      case (1?)?: break
      case (_?)?: break
      }
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns35",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testIfCaseMatchMutating#1",
        source: """
      if case _mutating x = y {}
      guard case _mutating z = y else {}
      """,
        origin: "MatchingPatternsTests.testIfCaseMatchMutating",
        syntaxVersion: "603.0.1",
        disabledReason: "experimental feature"
    ),
    SwiftSnippet(
        label: "testIfCaseMatchConsuming#1",
        source: """
      if case _consuming x = y {}
      guard case _consuming z = y else {}
      """,
        origin: "MatchingPatternsTests.testIfCaseMatchConsuming",
        syntaxVersion: "603.0.1",
        disabledReason: "experimental feature"
    ),
    SwiftSnippet(
        label: "testIfCaseMatchBorrowing#1",
        source: """
      if case _borrowing x = y {}
      guard case _borrowing z = y else {}
      """,
        origin: "MatchingPatternsTests.testIfCaseMatchBorrowing",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testBorrowingContextualParsing#1",
        source: """
      switch 42 {
      case borrowing .foo(): // parses as `borrowing.foo()` as before
        break
      }
      """,
        origin: "MatchingPatternsTests.testBorrowingContextualParsing",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testBorrowingContextualParsing#2",
        source: """
      switch 42 {
      case borrowing (): // parses as `borrowing()` as before
        break
      }
      """,
        origin: "MatchingPatternsTests.testBorrowingContextualParsing",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testBorrowingContextualParsing#3",
        source: """
      switch 42 {
      case borrowing x: // parses as binding
        break
      }
      """,
        origin: "MatchingPatternsTests.testBorrowingContextualParsing",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testBorrowingContextualParsing#4",
        source: """
      switch bar {
      case .payload(borrowing x): // parses as binding
        break
      }
      """,
        origin: "MatchingPatternsTests.testBorrowingContextualParsing",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testBorrowingContextualParsing#5",
        source: """
      switch bar {
      case borrowing x.member: // parses as var introducer surrounding postfix expression (which never is valid)
        break
      }
      """,
        origin: "MatchingPatternsTests.testBorrowingContextualParsing",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testBorrowingContextualParsing#6",
        source: """
      switch 42 {
      case let borrowing: // parses as let binding named 'borrowing'
        break
      }
      """,
        origin: "MatchingPatternsTests.testBorrowingContextualParsing",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testBorrowingContextualParsing#7",
        source: """
      switch 42 {
      case borrowing + borrowing: // parses as expr pattern
        break
      }
      """,
        origin: "MatchingPatternsTests.testBorrowingContextualParsing",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testBorrowingContextualParsing#8",
        source: """
      switch 42 {
      case borrowing(let borrowing): // parses as let binding named 'borrowing' inside a case pattern named 'borrowing'
        break
      }
      """,
        origin: "MatchingPatternsTests.testBorrowingContextualParsing",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testBorrowingContextualParsing#9",
        source: """
      switch 42 {
      case {}(borrowing + borrowing): // parses as expr pattern
        break
      }
      """,
        origin: "MatchingPatternsTests.testBorrowingContextualParsing",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMetatypeObjectConversion1#1",
        source: """
      class C {}
      struct S {}
      """,
        origin: "MetatypeObjectConversionTests.testMetatypeObjectConversion1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMetatypeObjectConversion2#1",
        source: """
      protocol NonClassProto {}
      protocol ClassConstrainedProto : class {}
      """,
        origin: "MetatypeObjectConversionTests.testMetatypeObjectConversion2",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMetatypeObjectConversion3#1",
        source: """
      func takesAnyObject(_ x: AnyObject) {}
      """,
        origin: "MetatypeObjectConversionTests.testMetatypeObjectConversion3",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMetatypeObjectConversion4#1",
        source: """
      func concreteTypes() {
        takesAnyObject(C.self)
        takesAnyObject(S.self)
        takesAnyObject(ClassConstrainedProto.self)
      }
      """,
        origin: "MetatypeObjectConversionTests.testMetatypeObjectConversion4",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMetatypeObjectConversion5#1",
        source: """
      func existentialMetatypes(nonClass: NonClassProto.Type,
                                classConstrained: ClassConstrainedProto.Type,
                                compo: (NonClassProto & ClassConstrainedProto).Type) {
        takesAnyObject(nonClass)
        takesAnyObject(classConstrained)
        takesAnyObject(compo)
      }
      """,
        origin: "MetatypeObjectConversionTests.testMetatypeObjectConversion5",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testModuleSelectorImports#1",
        source: """
      import struct ModuleSelectorTestingKit::A
      """,
        origin: "ModuleSelectorTests.testModuleSelectorImports",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testModuleSelectorCorrectCode#1",
        source: """
      extension ModuleSelectorTestingKit::A {}
      """,
        origin: "ModuleSelectorTests.testModuleSelectorCorrectCode",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testModuleSelectorCorrectCode#2",
        source: """
      extension A: @retroactive Swift::Equatable {}
      """,
        origin: "ModuleSelectorTests.testModuleSelectorCorrectCode",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testModuleSelectorCorrectCode#3",
        source: """
      @_implements(Swift::Equatable, ==(_:_:))
      public static func equals(_: ModuleSelectorTestingKit::A, _: ModuleSelectorTestingKit::A) -> Swift::Bool {
        Swift::fatalError()
      }
      """,
        origin: "ModuleSelectorTests.testModuleSelectorCorrectCode",
        syntaxVersion: "603.0.1",
        compilerRejects: "static methods may only be declared on a type"
    ),
    SwiftSnippet(
        label: "testModuleSelectorCorrectCode#4",
        source: """
      @_dynamicReplacement(for: ModuleSelectorTestingKit::negate())
      mutating func myNegate() {}
      """,
        origin: "ModuleSelectorTests.testModuleSelectorCorrectCode",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testModuleSelectorCorrectCode#5",
        source: """
      let fn: (Swift::Int, Swift::Int) -> Swift::Int = (Swift::+)
      """,
        origin: "ModuleSelectorTests.testModuleSelectorCorrectCode",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testModuleSelectorCorrectCode#6",
        source: """
      let magnitude: Int.Swift::Magnitude = main::magnitude
      """,
        origin: "ModuleSelectorTests.testModuleSelectorCorrectCode",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testModuleSelectorCorrectCode#7",
        source: """
      if Swift::Bool.Swift::random() {
      }
      """,
        origin: "ModuleSelectorTests.testModuleSelectorCorrectCode",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testModuleSelectorCorrectCode#8",
        source: """
      self.ModuleSelectorTestingKit::negate()
      """,
        origin: "ModuleSelectorTests.testModuleSelectorCorrectCode",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testModuleSelectorCorrectCode#9",
        source: """
      self = ModuleSelectorTestingKit::A(value: .Swift::min)
      """,
        origin: "ModuleSelectorTests.testModuleSelectorCorrectCode",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testModuleSelectorCorrectCode#10",
        source: """
      self = A.ModuleSelectorTestingKit::init(value: .min)
      """,
        origin: "ModuleSelectorTests.testModuleSelectorCorrectCode",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testModuleSelectorCorrectCode#11",
        source: """
      self.main::myNegate()
      """,
        origin: "ModuleSelectorTests.testModuleSelectorCorrectCode",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testModuleSelectorIncorrectAttrNames#1",
        source: """
      @main::available var use2
      """,
        origin: "ModuleSelectorTests.testModuleSelectorIncorrectAttrNames",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testModuleSelectorIncorrectAttrNames#2",
        source: """
      @main::available(foo: bar) var use3
      """,
        origin: "ModuleSelectorTests.testModuleSelectorIncorrectAttrNames",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testModuleSelectorIncorrectAttrNames#3",
        source: """
      func builderUser2(@main::MyBuilder fn: () -> Void) {}
      """,
        origin: "ModuleSelectorTests.testModuleSelectorIncorrectAttrNames",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testModuleSelectorWhitespace#1",
        source: """
      _ = Swift::print
      """,
        origin: "ModuleSelectorTests.testModuleSelectorWhitespace",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testModuleSelectorWhitespace#2",
        source: """
      _ = Swift:: print
      """,
        origin: "ModuleSelectorTests.testModuleSelectorWhitespace",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testModuleSelectorWhitespace#3",
        source: """
      _ = Swift ::print
      """,
        origin: "ModuleSelectorTests.testModuleSelectorWhitespace",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testModuleSelectorWhitespace#4",
        source: """
      _ = Swift :: print
      """,
        origin: "ModuleSelectorTests.testModuleSelectorWhitespace",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testModuleSelectorWhitespace#5",
        source: """
      _ = Swift
      ::print
      """,
        origin: "ModuleSelectorTests.testModuleSelectorWhitespace",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testModuleSelectorWhitespace#6",
        source: """
      _ = Swift
      :: print
      """,
        origin: "ModuleSelectorTests.testModuleSelectorWhitespace",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testModuleSelectorMacroDecls#1",
        source: """
      struct CreatesDeclExpectation {
        #main::myMacro()
      }
      """,
        origin: "ModuleSelectorTests.testModuleSelectorMacroDecls",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testModuleSelectorIncorrectRuntimeBaseAttr#1",
        source: """
      @_swift_native_objc_runtime_base(main::BaseClass)
      class C1 {}
      """,
        origin: "ModuleSelectorTests.testModuleSelectorIncorrectRuntimeBaseAttr",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testModuleSelectorAttrs#1",
        source: """
      @_spi(main::Private)
      public struct BadImplementsAttr: CustomStringConvertible {}
      """,
        origin: "ModuleSelectorTests.testModuleSelectorAttrs",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testModuleSelectorAttrs#2",
        source: """
      @_implements(main::CustomStringConvertible, Swift::description)
      public var stringValue: String { fatalError() }
      """,
        origin: "ModuleSelectorTests.testModuleSelectorAttrs",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testModuleSelectorAttrs#3",
        source: """
      @derivative(of: Swift::Foo.Swift::Bar.Swift::baz(), wrt: quux)
      func fn() {}
      """,
        origin: "ModuleSelectorTests.testModuleSelectorAttrs",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testModuleSelectorExpr#1", source: "let x = Swift::do { 1 }", origin: "ModuleSelectorTests.testModuleSelectorExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testModuleSelectorExpr#2", source: #"_ = \main::Foo.BarKit::bar"#, origin: "ModuleSelectorTests.testModuleSelectorExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testModuleSelectorExpr#3", source: "_ = Swift::nil", origin: "ModuleSelectorTests.testModuleSelectorExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testModuleSelectorExpr#4", source: "_ = Swift::true", origin: "ModuleSelectorTests.testModuleSelectorExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testModuleSelectorExpr#5", source: "_ = Swift::identifier", origin: "ModuleSelectorTests.testModuleSelectorExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testModuleSelectorExpr#6", source: "_ = Swift::self", origin: "ModuleSelectorTests.testModuleSelectorExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testModuleSelectorExpr#7", source: "_ = Swift::init", origin: "ModuleSelectorTests.testModuleSelectorExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testModuleSelectorExpr#8", source: "@attached(extension, names: Swift::deinit) macro m()", origin: "ModuleSelectorTests.testModuleSelectorExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testModuleSelectorExpr#9", source: "@attached(extension, names: Swift::subscript) macro m()", origin: "ModuleSelectorTests.testModuleSelectorExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testModuleSelectorExpr#10", source: "_ = Swift::Self", origin: "ModuleSelectorTests.testModuleSelectorExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testModuleSelectorExpr#11", source: "_ = Swift::Any", origin: "ModuleSelectorTests.testModuleSelectorExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testModuleSelectorExpr#12", source: "_ = Swift::$foo", origin: "ModuleSelectorTests.testModuleSelectorExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testModuleSelectorExpr#13", source: "_ = #Swift::foo", origin: "ModuleSelectorTests.testModuleSelectorExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testModuleSelectorExpr#14", source: "_ = .main::random()", origin: "ModuleSelectorTests.testModuleSelectorExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testModuleSelectorExpr#15", source: "_ = Swift::super.foo()", origin: "ModuleSelectorTests.testModuleSelectorExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testModuleSelectorExpr#16", source: "_ = x.Swift::y", origin: "ModuleSelectorTests.testModuleSelectorExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testModuleSelectorExpr#17", source: "_ = x.Swift::self", origin: "ModuleSelectorTests.testModuleSelectorExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testModuleSelectorExpr#18", source: "_ = x.Swift::Self.self", origin: "ModuleSelectorTests.testModuleSelectorExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testModuleSelectorExpr#19", source: "_ = x.Swift::Type.self", origin: "ModuleSelectorTests.testModuleSelectorExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testModuleSelectorExpr#20", source: "_ = x.Swift::Protocol.self", origin: "ModuleSelectorTests.testModuleSelectorExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testModuleSelectorExpr#21", source: "_ = myArray.reduce(0, Swift::+)", origin: "ModuleSelectorTests.testModuleSelectorExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testModuleSelectorType#1", source: "func fn(_: Swift::Self) {}", origin: "ModuleSelectorTests.testModuleSelectorType", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testModuleSelectorType#2", source: "func fn(_: Swift::Any) {}", origin: "ModuleSelectorTests.testModuleSelectorType", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testModuleSelectorType#3", source: "func fn(_: Swift::Foo) {}", origin: "ModuleSelectorTests.testModuleSelectorType", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testModuleSelectorType#4", source: "func fn(_: Foo.Swift::Type) {}", origin: "ModuleSelectorTests.testModuleSelectorType", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testModuleSelectorType#5", source: "func fn(_: Foo.Swift::Protocol) {}", origin: "ModuleSelectorTests.testModuleSelectorType", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testModuleSelectorType#6", source: "func fn(_: Foo.Swift::Bar) {}", origin: "ModuleSelectorTests.testModuleSelectorType", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testModuleSelectorType#7", source: "func fn(_: Foo.Swift::self) {}", origin: "ModuleSelectorTests.testModuleSelectorType", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testMoveExpr1#1",
        source: """
      var global: Int = 5
      func testGlobal() {
          let _ = _move global
      }
      """,
        origin: "MoveExprTests.testMoveExpr1",
        syntaxVersion: "603.0.1",
        compilerRejects: "consecutive statements on a line must be separated by ';'"
    ),
    SwiftSnippet(
        label: "testMoveExpr2#1",
        source: """
      func testLet() {
          let t = String()
          let _ = _move t
      }
      """,
        origin: "MoveExprTests.testMoveExpr2",
        syntaxVersion: "603.0.1",
        compilerRejects: "consecutive statements on a line must be separated by ';'"
    ),
    SwiftSnippet(
        label: "testMoveExpr3#1",
        source: """
      func testVar() {
          var t = String()
          t = String()
          let _ = _move t
      }
      """,
        origin: "MoveExprTests.testMoveExpr3",
        syntaxVersion: "603.0.1",
        compilerRejects: "consecutive statements on a line must be separated by ';'"
    ),
    SwiftSnippet(
        label: "testMoveExpr4#1",
        source: """
      _move(t)
      """,
        origin: "MoveExprTests.testMoveExpr4",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMoveExpr5#1",
        source: """
      _move(t)
      """,
        origin: "MoveExprTests.testMoveExpr5",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testConsumeExpr1#1",
        source: """
      var global: Int = 5
      func testGlobal() {
          let _ = consume global
      }
      """,
        origin: "MoveExprTests.testConsumeExpr1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testConsumeExpr2#1",
        source: """
      func testLet() {
          let t = String()
          let _ = consume t
      }
      """,
        origin: "MoveExprTests.testConsumeExpr2",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testConsumeExpr3#1",
        source: """
      func testVar() {
          var t = String()
          t = String()
          let _ = consume t
      }
      """,
        origin: "MoveExprTests.testConsumeExpr3",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testConsumeVariableNameInCast#1",
        source: """
      class ParentKlass {}
      class SubKlass : ParentKlass {}

      func test(_ x: SubKlass) {
        switch x {
        case let consume as ParentKlass:
          fallthrough
        }
      }
      """,
        origin: "MoveExprTests.testConsumeVariableNameInCast",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMultilineString1#1",
        source: """
      import Swift
      """,
        origin: "MultilineStringTests.testMultilineString1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMultilineString2#1",
        source: """
      // ===---------- Multiline --------===
      """,
        origin: "MultilineStringTests.testMultilineString2",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMultilineString3#1",
        source: #"""
      _ = """
          One
          ""Alpha""
          """
      """#,
        origin: "MultilineStringTests.testMultilineString3",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMultilineString4#1",
        source: #"""
      _ = """
          Two
        Beta
        """
      """#,
        origin: "MultilineStringTests.testMultilineString4",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMultilineString5#1",
        source: #"""
      _ = """
          Three
          Gamma.
        """
      """#,
        origin: "MultilineStringTests.testMultilineString5",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMultilineString6#1",
        source: #"""
      _ = """
          Four
          Delta
      """
      """#,
        origin: "MultilineStringTests.testMultilineString6",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMultilineString7#1",
        source: #"""
      _ = """
          Five\n

          Epsilon
          """
      """#,
        origin: "MultilineStringTests.testMultilineString7",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMultilineString9#1",
        source: #"""
      _ = """
          Six
          Zeta

          """
      """#,
        origin: "MultilineStringTests.testMultilineString9",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMultilineString11#1",
        source: #"""
      _ = """
          Seven
          Eta\n
          """
      """#,
        origin: "MultilineStringTests.testMultilineString11",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMultilineString12#1",
        source: #"""
      _ = """
          \"""
          "\""
          ""\"
          Iota
          """
      """#,
        origin: "MultilineStringTests.testMultilineString12",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMultilineString13#1",
        source: #"""
      _ = """
           \("Nine")
          Kappa
          """
      """#,
        origin: "MultilineStringTests.testMultilineString13",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMultilineString14#1",
        source: #"""
      _ = """
      	first
      	 second
      	third
      	"""
      """#,
        origin: "MultilineStringTests.testMultilineString14",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMultilineString15#1",
        source: #"""
      _ = """
       first
       	second
       third
       """
      """#,
        origin: "MultilineStringTests.testMultilineString15",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMultilineString16#1",
        source: #"""
      _ = """
      \\
      """
      """#,
        origin: "MultilineStringTests.testMultilineString16",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMultilineString17#1",
        source: #"""
      _ = """
        \\
        """
      """#,
        origin: "MultilineStringTests.testMultilineString17",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMultilineString18#1",
        source: #"""
      _ = """

        ABC
        """
      """#,
        origin: "MultilineStringTests.testMultilineString18",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMultilineString20#1",
        source: #"""
      _ = """

      ABC
      """
      """#,
        origin: "MultilineStringTests.testMultilineString20",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMultilineString22#1",
        source: #"""
      _ = """

        ABC
        """
      """#,
        origin: "MultilineStringTests.testMultilineString22",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMultilineString24#1",
        source: #"""
      // contains tabs
      _ = """
      	Twelve
      	Nu
      	"""
      """#,
        origin: "MultilineStringTests.testMultilineString24",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMultilineString25#1",
        source: #"""
      _ = """
        newline \
        elided
        """
      """#,
        origin: "MultilineStringTests.testMultilineString25",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMultilineString26#1",
        source: #"""
      _ = """
        trailing \
        \("""
          substring1 \
          \("""
            substring2 \         \#u{20}
            substring3
            """)
          """) \
        whitespace
        """
      """#,
        origin: "MultilineStringTests.testMultilineString26",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMultilineString27#1",
        source: #"""
      _ = """
          foo

          bar
          """
      """#,
        origin: "MultilineStringTests.testMultilineString27",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMultilineString29#1",
        source: #"""
      _ = """
          foo\\#u{20}
         \#u{20}
          bar
          """
      """#,
        origin: "MultilineStringTests.testMultilineString29",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMultilineString31#1",
        source: #"""
      _ = """
          foo \
            bar
          """
      """#,
        origin: "MultilineStringTests.testMultilineString31",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMultilineString32#1",
        source: #"""
      _ = """

        ABC
        """
      """#,
        origin: "MultilineStringTests.testMultilineString32",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMultilineString34#1",
        source: #"""
      _ = """

          ABC

          """
      """#,
        origin: "MultilineStringTests.testMultilineString34",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMultilineString37#1",
        source: #"""
      _ = """


          """
      """#,
        origin: "MultilineStringTests.testMultilineString37",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMultilineString39#1",
        source: #"""
      _ = """

          """
      """#,
        origin: "MultilineStringTests.testMultilineString39",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMultilineString41#1",
        source: #"""
      _ = """
          """
      """#,
        origin: "MultilineStringTests.testMultilineString41",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMultilineString42#1",
        source: #"""
      _ = "\("""
        \("a" + """
         valid
        """)
        """) literal"
      """#,
        origin: "MultilineStringTests.testMultilineString42",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMultilineString43#1",
        source: #"""
      _ = "hello\("""
        world
        """)"
      """#,
        origin: "MultilineStringTests.testMultilineString43",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMultilineString44#1",
        source: #"""
      _ = """
        hello\("""
           world
           """)
        abc
        """
      """#,
        origin: "MultilineStringTests.testMultilineString44",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMultilineString45#1",
        source: #"""
      _ = "hello\("""
                  "world'
                  """)abc"
      """#,
        origin: "MultilineStringTests.testMultilineString45",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMultilineString46#1",
        source: #"""
      _ = """
          welcome
          \(
            /*
              ')' or '"""' in comment.
              """
            */
            "to\("""
                 Swift
                 """)"
            // ) or """ in comment.
          )
          !
          """
      """#,
        origin: "MultilineStringTests.testMultilineString46",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEscapeNewlineInRawString#1",
        source: ##"""
      #"""
      Three \#
      Gamma
      """#
      """##,
        origin: "MultilineStringTests.testEscapeNewlineInRawString",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEscapeLastNewlineInRawString#1",
        source: ##"""
      #"""
      Three \#
      Gamma \#
      """#
      """##,
        origin: "MultilineStringTests.testEscapeLastNewlineInRawString",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testNoimplicitcopyAttr1#1",
        source: """
      f// RUN: %target-typecheck-verify-swift -parse -parse-stdlib -disable-availability-checking -verify-syntax-tree
      """,
        origin: "NoimplicitcopyAttrTests.testNoimplicitcopyAttr1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testNoimplicitcopyAttr2#1",
        source: """
      import Swift
      """,
        origin: "NoimplicitcopyAttrTests.testNoimplicitcopyAttr2",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testNoimplicitcopyAttr3#1",
        source: """
      class Klass {}
      """,
        origin: "NoimplicitcopyAttrTests.testNoimplicitcopyAttr3",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testNoimplicitcopyAttr4#1",
        source: """
      func argumentsAndReturns(@_noImplicitCopy _ x: Klass) -> Klass {
          return x
      }
      """,
        origin: "NoimplicitcopyAttrTests.testNoimplicitcopyAttr4",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testNoimplicitcopyAttr5#1",
        source: """
      func letDecls(@_noImplicitCopy  _ x: Klass) -> () {
          @_noImplicitCopy let y: Klass = x
          print(y)
      }
      """,
        origin: "NoimplicitcopyAttrTests.testNoimplicitcopyAttr5",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testNoimplicitcopyAttr6#1",
        source: """
      func varDecls(@_noImplicitCopy _ x: Klass, @_noImplicitCopy _ x2: Klass) -> () {
          @_noImplicitCopy var y: Klass = x
          y = x2
          print(y)
      }
      """,
        origin: "NoimplicitcopyAttrTests.testNoimplicitcopyAttr6",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testNoimplicitcopyAttr7#1",
        source: """
      func getKlass() -> Builtin.NativeObject {
          let k = Klass()
          let b = Builtin.unsafeCastToNativeObject(k)
          return Builtin.move(b)
      }
      """,
        origin: "NoimplicitcopyAttrTests.testNoimplicitcopyAttr7",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testNoimplicitcopyAttr8#1",
        source: """
      @_noImplicitCopy var g: Builtin.NativeObject = getKlass()
      @_noImplicitCopy let g2: Builtin.NativeObject = getKlass()
      """,
        origin: "NoimplicitcopyAttrTests.testNoimplicitcopyAttr8",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testNumberIdentifierErrors1#1",
        source: """
      // Per rdar://problem/32316666 , it is a common mistake for beginners
      // to start a function name with a number, so it's worth
      // special-casing the diagnostic to make it clearer.
      """,
        origin: "NumberIdentifierErrorsTests.testNumberIdentifierErrors1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testObjcEnum1#1",
        source: """
      @objc enum Foo: Int32 {
        case Zim, Zang, Zung
      }
      """,
        origin: "ObjcEnumTests.testObjcEnum1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testObjcEnum2#1",
        source: """
      @objc enum Generic<T>: Int32 {
        case Zim, Zang, Zung
      }
      """,
        origin: "ObjcEnumTests.testObjcEnum2",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testObjcEnum3#1",
        source: """
      @objc(EnumRuntimeName) enum RuntimeNamed: Int32 {
        case Zim, Zang, Zung
      }
      """,
        origin: "ObjcEnumTests.testObjcEnum3",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testObjcEnum4#1",
        source: """
      @objc enum NoRawType {
        case Zim, Zang, Zung
      }
      """,
        origin: "ObjcEnumTests.testObjcEnum4",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testObjcEnum5#1",
        source: """
      @objc enum NonIntegerRawType: Float {
        case Zim = 1.0, Zang = 1.5, Zung = 2.0
      }
      """,
        origin: "ObjcEnumTests.testObjcEnum5",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testObjcEnum6#1",
        source: """
      enum NonObjCEnum: Int {
        case Zim, Zang, Zung
      }
      """,
        origin: "ObjcEnumTests.testObjcEnum6",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testObjcEnum7#1",
        source: """
      class Bar {
        @objc func foo(x: Foo) {}
        @objc func nonObjC(x: NonObjCEnum) {}
      }
      """,
        origin: "ObjcEnumTests.testObjcEnum7",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testObjcEnum8#1",
        source: """
      // <rdar://problem/23681566> @objc enums with payloads rejected with no source location info
      @objc enum r23681566 : Int32 {
        case Foo(progress: Int)
      }
      """,
        origin: "ObjcEnumTests.testObjcEnum8",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testObjectLiterals2a#1",
        source: """
      let _ = #Color(colorLiteralRed: red, green: green, blue: blue, alpha: alpha)
      """,
        origin: "ObjectLiteralsTests.testObjectLiterals2a",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testObjectLiterals2b#1",
        source: """
      let _ = #Image(imageLiteral: localResourceNameAsString)
      """,
        origin: "ObjectLiteralsTests.testObjectLiterals2b",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testObjectLiterals2c#1",
        source: """
      let _ = #FileReference(fileReferenceLiteral: localResourceNameAsString)
      """,
        origin: "ObjectLiteralsTests.testObjectLiterals2c",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testObjectLiterals3a#1",
        source: """
      let _ = #notAPound
      """,
        origin: "ObjectLiteralsTests.testObjectLiterals3a",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testObjectLiterals3b#1",
        source: """
      let _ = #notAPound(1, 2)
      """,
        origin: "ObjectLiteralsTests.testObjectLiterals3b",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testObjectLiterals3c#1",
        source: """
      let _ = #Color
      """,
        origin: "ObjectLiteralsTests.testObjectLiterals3c",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testObjectLiterals8#1",
        source: """
      let _ = #Color(_: 1, green: 1)
      """,
        origin: "ObjectLiteralsTests.testObjectLiterals8",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperatorDeclDesignatedTypes1#1",
        source: """
      precedencegroup LowPrecedence {
        associativity: right
      }
      """,
        origin: "OperatorDeclDesignatedTypesTests.testOperatorDeclDesignatedTypes1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperatorDeclDesignatedTypes2#1",
        source: """
      precedencegroup MediumPrecedence {
        associativity: left
        higherThan: LowPrecedence
      }
      """,
        origin: "OperatorDeclDesignatedTypesTests.testOperatorDeclDesignatedTypes2",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperatorDeclDesignatedTypes3#1",
        source: """
      protocol PrefixMagicOperatorProtocol {
      }
      """,
        origin: "OperatorDeclDesignatedTypesTests.testOperatorDeclDesignatedTypes3",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperatorDeclDesignatedTypes4#1",
        source: """
      protocol PostfixMagicOperatorProtocol {
      }
      """,
        origin: "OperatorDeclDesignatedTypesTests.testOperatorDeclDesignatedTypes4",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperatorDeclDesignatedTypes5#1",
        source: """
      protocol InfixMagicOperatorProtocol {
      }
      """,
        origin: "OperatorDeclDesignatedTypesTests.testOperatorDeclDesignatedTypes5",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperatorDeclDesignatedTypes6#1",
        source: """
      prefix operator ^^ : PrefixMagicOperatorProtocol
      infix operator  <*< : MediumPrecedence, InfixMagicOperatorProtocol
      postfix operator ^^ : PostfixMagicOperatorProtocol
      """,
        origin: "OperatorDeclDesignatedTypesTests.testOperatorDeclDesignatedTypes6",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperatorDeclDesignatedTypes7#1",
        source: """
      infix operator ^*^
      prefix operator *^^
      postfix operator ^^*
      """,
        origin: "OperatorDeclDesignatedTypesTests.testOperatorDeclDesignatedTypes7",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperatorDeclDesignatedTypes8#1",
        source: """
      infix operator **>> : UndeclaredPrecedence
      """,
        origin: "OperatorDeclDesignatedTypesTests.testOperatorDeclDesignatedTypes8",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperatorDeclDesignatedTypes9#1",
        source: """
      infix operator **+> : MediumPrecedence, UndeclaredProtocol
      """,
        origin: "OperatorDeclDesignatedTypesTests.testOperatorDeclDesignatedTypes9",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperatorDeclDesignatedTypes10#1",
        source: """
      prefix operator *+*> : MediumPrecedence
      """,
        origin: "OperatorDeclDesignatedTypesTests.testOperatorDeclDesignatedTypes10",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperatorDeclDesignatedTypes11#1",
        source: """
      postfix operator ++*> : MediumPrecedence
      """,
        origin: "OperatorDeclDesignatedTypesTests.testOperatorDeclDesignatedTypes11",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperatorDeclDesignatedTypes12#1",
        source: """
      prefix operator *++> : UndeclaredProtocol
      postfix operator +*+> : UndeclaredProtocol
      """,
        origin: "OperatorDeclDesignatedTypesTests.testOperatorDeclDesignatedTypes12",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperatorDeclDesignatedTypes13#1",
        source: """
      struct Struct {}
      class Class {}
      infix operator *>*> : Struct
      infix operator >**> : Class
      """,
        origin: "OperatorDeclDesignatedTypesTests.testOperatorDeclDesignatedTypes13",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperatorDeclDesignatedTypes14#1",
        source: """
      prefix operator **>> : Struct
      prefix operator *>*> : Class
      """,
        origin: "OperatorDeclDesignatedTypesTests.testOperatorDeclDesignatedTypes14",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperatorDeclDesignatedTypes15#1",
        source: """
      postfix operator >*>* : Struct
      postfix operator >>** : Class
      """,
        origin: "OperatorDeclDesignatedTypesTests.testOperatorDeclDesignatedTypes15",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperatorDeclDesignatedTypes16#1",
        source: """
      infix operator  <*<<< : MediumPrecedence, &
      """,
        origin: "OperatorDeclDesignatedTypesTests.testOperatorDeclDesignatedTypes16",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperatorDeclDesignatedTypes17#1",
        source: """
      infix operator **^^ : MediumPrecedence
      infix operator **^^ : InfixMagicOperatorProtocol
      """,
        origin: "OperatorDeclDesignatedTypesTests.testOperatorDeclDesignatedTypes17",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperatorDeclDesignatedTypes18#1",
        source: """
      infix operator ^%*%^ : MediumPrecedence, Struct, Class
      infix operator ^%*%% : Struct, Class
      prefix operator %^*^^ : Struct, Class
      postfix operator ^^*^% : Struct, Class
      prefix operator %%*^^ : LowPrecedence, Class
      postfix operator ^^*%% : MediumPrecedence, Class
      """,
        origin: "OperatorDeclDesignatedTypesTests.testOperatorDeclDesignatedTypes18",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperatorDeclDesignatedTypes19#1",
        source: """
      infix operator <*<>*> : AdditionPrecedence,
      """,
        origin: "OperatorDeclDesignatedTypesTests.testOperatorDeclDesignatedTypes19",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperatorDecl3#1",
        source: """
      prefix operator ++*++ : A
      """,
        origin: "OperatorDeclTests.testOperatorDecl3",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperatorDecl5#1",
        source: """
      postfix operator ++**+ : A
      """,
        origin: "OperatorDeclTests.testOperatorDecl5",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperatorDecl11a#1",
        source: """
      prefix operator ??
      """,
        origin: "OperatorDeclTests.testOperatorDecl11a",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperatorDecl11b#1",
        source: """
      postfix operator ??
      """,
        origin: "OperatorDeclTests.testOperatorDecl11b",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperatorDecl11c#1",
        source: """
      prefix operator !!
      """,
        origin: "OperatorDeclTests.testOperatorDecl11c",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperatorDecl11d#1",
        source: """
      postfix operator !!
      """,
        origin: "OperatorDeclTests.testOperatorDecl11d",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperatorDecl16#1",
        source: """
      precedencegroup F {
        higherThan: A, B, C
      }
      """,
        origin: "OperatorDeclTests.testOperatorDecl16",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperatorDecl17#1",
        source: """
      precedencegroup BangBangBang {
        associativity: none
        associativity: left
      }
      """,
        origin: "OperatorDeclTests.testOperatorDecl17",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperatorDecl18#1",
        source: """
      precedencegroup CaretCaretCaret {
        assignment: true
        assignment: false
      }
      """,
        origin: "OperatorDeclTests.testOperatorDecl18",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperatorDecl19#1",
        source: """
      class Foo {
        infix operator |||
      }
      """,
        origin: "OperatorDeclTests.testOperatorDecl19",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperatorDecl20#1",
        source: """
      infix operator **<< : UndeclaredPrecedenceGroup
      """,
        origin: "OperatorDeclTests.testOperatorDecl20",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperatorDecl21#1",
        source: """
      protocol Proto {}
      infix operator *<*< : F, Proto
      """,
        origin: "OperatorDeclTests.testOperatorDecl21",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperatorDecl22#1",
        source: """
      // https://github.com/apple/swift/issues/60932
      """,
        origin: "OperatorDeclTests.testOperatorDecl22",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testRegexLikeOperator#1", source: "prefix operator /^/", origin: "OperatorDeclTests.testRegexLikeOperator", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testOperators1#1",
        source: """
      // This disables importing the stdlib intentionally.
      """,
        origin: "OperatorsTests.testOperators1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperators2#1",
        source: """
      infix operator == : Equal
      precedencegroup Equal {
        associativity: left
        higherThan: FatArrow
      }
      """,
        origin: "OperatorsTests.testOperators2",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperators3#1",
        source: """
      infix operator & : BitAnd
      precedencegroup BitAnd {
        associativity: left
        higherThan: Equal
      }
      """,
        origin: "OperatorsTests.testOperators3",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperators4#1",
        source: """
      infix operator => : FatArrow
      precedencegroup FatArrow {
        associativity: right
        higherThan: AssignmentPrecedence
      }
      precedencegroup AssignmentPrecedence {
        assignment: true
      }
      """,
        origin: "OperatorsTests.testOperators4",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperators5#1",
        source: """
      precedencegroup DefaultPrecedence {}
      """,
        origin: "OperatorsTests.testOperators5",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperators6#1",
        source: """
      struct Man {}
      struct TheDevil {}
      struct God {}
      """,
        origin: "OperatorsTests.testOperators6",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperators7#1",
        source: """
      struct Five {}
      struct Six {}
      struct Seven {}
      """,
        origin: "OperatorsTests.testOperators7",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperators8#1",
        source: """
      struct ManIsFive {}
      struct TheDevilIsSix {}
      struct GodIsSeven {}
      """,
        origin: "OperatorsTests.testOperators8",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperators9#1",
        source: """
      struct TheDevilIsSixThenGodIsSeven {}
      """,
        origin: "OperatorsTests.testOperators9",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperators10#1",
        source: """
      func == (x: Man, y: Five) -> ManIsFive {}
      func == (x: TheDevil, y: Six) -> TheDevilIsSix {}
      func == (x: God, y: Seven) -> GodIsSeven {}
      """,
        origin: "OperatorsTests.testOperators10",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperators11#1",
        source: """
      func => (x: TheDevilIsSix, y: GodIsSeven) -> TheDevilIsSixThenGodIsSeven {}
      func => (x: ManIsFive, y: TheDevilIsSixThenGodIsSeven) {}
      """,
        origin: "OperatorsTests.testOperators11",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperators12#1",
        source: """
      func test1() {
        Man() == Five() => TheDevil() == Six() => God() == Seven()
      }
      """,
        origin: "OperatorsTests.testOperators12",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperators13#1",
        source: """
      postfix operator *!*
      prefix operator *!*
      """,
        origin: "OperatorsTests.testOperators13",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperators14#1",
        source: """
      struct LOOK {}
      struct LOOKBang {
        func exclaim() {}
      }
      """,
        origin: "OperatorsTests.testOperators14",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperators15#1",
        source: """
      postfix func *!* (x: LOOK) -> LOOKBang {}
      prefix func *!* (x: LOOKBang) {}
      """,
        origin: "OperatorsTests.testOperators15",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperators16#1",
        source: """
      func test2() {
        *!*LOOK()*!*
      }
      """,
        origin: "OperatorsTests.testOperators16",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperators17#1",
        source: """
      // This should be parsed as (x*!*).exclaim()
      LOOK()*!*.exclaim()
      """,
        origin: "OperatorsTests.testOperators17",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperators18#1",
        source: """
      prefix operator ^
      infix operator ^
      postfix operator ^
      """,
        origin: "OperatorsTests.testOperators18",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperators19#1",
        source: """
      postfix func ^ (x: God) -> TheDevil {}
      prefix func ^ (x: TheDevil) -> God {}
      """,
        origin: "OperatorsTests.testOperators19",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperators20#1",
        source: """
      func ^ (x: TheDevil, y: God) -> Man {}
      """,
        origin: "OperatorsTests.testOperators20",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperators21#1",
        source: """
      var _ : TheDevil = God()^
      var _ : God = ^TheDevil()
      var _ : Man = TheDevil() ^ God()
      var _ : Man = God()^ ^ ^TheDevil()
      let _ = God()^TheDevil()
      """,
        origin: "OperatorsTests.testOperators21",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperators22#1",
        source: """
      postfix func ^ (x: Man) -> () -> God {
        return { return God() }
      }
      """,
        origin: "OperatorsTests.testOperators22",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperators23#1",
        source: """
      var _ : God = Man()^()
      """,
        origin: "OperatorsTests.testOperators23",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperators24#1",
        source: """
      func &(x : Man, y : Man) -> Man { return x } // forgive amp_prefix token
      """,
        origin: "OperatorsTests.testOperators24",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperators25#1",
        source: """
      prefix operator ⚽️
      """,
        origin: "OperatorsTests.testOperators25",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperators26#1",
        source: """
      prefix func ⚽️(x: Man) { }
      """,
        origin: "OperatorsTests.testOperators26",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperators27#1",
        source: """
      infix operator ?? : OptTest
      precedencegroup OptTest {
        associativity: right
      }
      """,
        origin: "OperatorsTests.testOperators27",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperators28#1",
        source: """
      func ??(x: Man, y: TheDevil) -> TheDevil {
        return y
      }
      """,
        origin: "OperatorsTests.testOperators28",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperators29#1",
        source: """
      func test3(a: Man, b: Man, c: TheDevil) -> TheDevil {
        return a ?? b ?? c
      }
      """,
        origin: "OperatorsTests.testOperators29",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperators30#1",
        source: """
      // <rdar://problem/17821399> We don't parse infix operators bound on both
      // sides that begin with ! or ? correctly yet.
      infix operator !!
      """,
        origin: "OperatorsTests.testOperators30",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperators31#1",
        source: """
      func !!(x: Man, y: Man) {}
      """,
        origin: "OperatorsTests.testOperators31",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperators32#1",
        source: """
      let foo = Man()
      """,
        origin: "OperatorsTests.testOperators32",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOperators33#1",
        source: """
      let bar = TheDevil()
      """,
        origin: "OperatorsTests.testOperators33",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOptionalChainLvalues1#1",
        source: """
      struct S {
        var x: Int = 0
        let y: Int = 0  // expected-note 3 {{change 'let' to 'var' to make it mutable}} {{3-6=var}} {{3-6=var}} {{3-6=var}}
        mutating func mutateS() {}
        init() {}
      }
      """,
        origin: "OptionalChainLvaluesTests.testOptionalChainLvalues1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOptionalChainLvalues2#1",
        source: """
      struct T {
        var mutS: S? = nil
        let immS: S? = nil  // expected-note 4 {{change 'let' to 'var' to make it mutable}} {{3-6=var}} {{3-6=var}} {{3-6=var}} {{3-6=var}}
        mutating func mutateT() {}
        init() {}
      }
      """,
        origin: "OptionalChainLvaluesTests.testOptionalChainLvalues2",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOptionalChainLvalues3#1",
        source: """
      var mutT: T?
      let immT: T? = nil
      """,
        origin: "OptionalChainLvaluesTests.testOptionalChainLvalues3",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOptionalChainLvalues4#1",
        source: """
      postfix operator ++
      prefix operator ++
      """,
        origin: "OptionalChainLvaluesTests.testOptionalChainLvalues4",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOptionalChainLvalues5#1",
        source: """
      public postfix func ++ <T>(rhs: inout T) -> T { fatalError() }
      public prefix func ++ <T>(rhs: inout T) -> T { fatalError() }
      """,
        origin: "OptionalChainLvaluesTests.testOptionalChainLvalues5",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOptionalChainLvalues6#1",
        source: """
      mutT?.mutateT()
      immT?.mutateT()
      mutT?.mutS?.mutateS()
      mutT?.immS?.mutateS()
      mutT?.mutS?.x += 1
      mutT?.mutS?.y++
      """,
        origin: "OptionalChainLvaluesTests.testOptionalChainLvalues6",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOptionalChainLvalues7#1",
        source: """
      // Prefix operators don't chain
      ++mutT?.mutS?.x
      ++mutT?.mutS?.y
      """,
        origin: "OptionalChainLvaluesTests.testOptionalChainLvalues7",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOptionalChainLvalues8#1",
        source: """
      mutT? = T()
      mutT?.mutS = S()
      mutT?.mutS? = S()
      mutT?.mutS?.x += 0
      _ = mutT?.mutS?.x + 0
      mutT?.mutS?.y -= 0
      mutT?.immS = S()
      mutT?.immS? = S()
      mutT?.immS?.x += 0
      mutT?.immS?.y -= 0
      """,
        origin: "OptionalChainLvaluesTests.testOptionalChainLvalues8",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOptionalLvalues1#1",
        source: """
      struct S {
        var x: Int = 0
        let y: Int = 0 // expected-note 4 {{change 'let' to 'var' to make it mutable}} {{3-6=var}} {{3-6=var}} {{3-6=var}} {{3-6=var}}
        init() {}
      }
      """,
        origin: "OptionalLvaluesTests.testOptionalLvalues1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOptionalLvalues2#1",
        source: """
      struct T {
        var mutS: S? = nil
        let immS: S? = nil // expected-note 10 {{change 'let' to 'var' to make it mutable}} {{3-6=var}} {{3-6=var}} {{3-6=var}} {{3-6=var}} {{3-6=var}} {{3-6=var}} {{3-6=var}} {{3-6=var}} {{3-6=var}} {{3-6=var}}
        init() {}
      }
      """,
        origin: "OptionalLvaluesTests.testOptionalLvalues2",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOptionalLvalues3#1",
        source: """
      var mutT: T?
      let immT: T? = nil  // expected-note 4 {{change 'let' to 'var' to make it mutable}} {{1-4=var}} {{1-4=var}} {{1-4=var}} {{1-4=var}}
      """,
        origin: "OptionalLvaluesTests.testOptionalLvalues3",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOptionalLvalues4#1",
        source: """
      let mutTPayload = mutT!
      """,
        origin: "OptionalLvaluesTests.testOptionalLvalues4",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOptionalLvalues5#1",
        source: """
      mutT! = T()
      mutT!.mutS = S()
      mutT!.mutS! = S()
      mutT!.mutS!.x = 0
      mutT!.mutS!.y = 0
      mutT!.immS = S()
      mutT!.immS! = S()
      mutT!.immS!.x = 0
      mutT!.immS!.y = 0
      """,
        origin: "OptionalLvaluesTests.testOptionalLvalues5",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOptionalLvalues6#1",
        source: """
      immT! = T()
      immT!.mutS = S()
      immT!.mutS! = S()
      immT!.mutS!.x = 0
      immT!.mutS!.y = 0
      immT!.immS = S()
      immT!.immS! = S()
      immT!.immS!.x = 0
      immT!.immS!.y = 0
      """,
        origin: "OptionalLvaluesTests.testOptionalLvalues6",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOptionalLvalues7#1",
        source: """
      var mutIUO: T! = nil
      let immIUO: T! = nil // expected-note 2 {{change 'let' to 'var' to make it mutable}} {{1-4=var}} {{1-4=var}}
      """,
        origin: "OptionalLvaluesTests.testOptionalLvalues7",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOptionalLvalues8#1",
        source: """
      mutIUO!.mutS = S()
      mutIUO!.immS = S()
      immIUO!.mutS = S()
      immIUO!.immS = S()
      """,
        origin: "OptionalLvaluesTests.testOptionalLvalues8",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOptionalLvalues9#1",
        source: """
      mutIUO.mutS = S()
      mutIUO.immS = S()
      immIUO.mutS = S()
      immIUO.immS = S()
      """,
        origin: "OptionalLvaluesTests.testOptionalLvalues9",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOptionalLvalues10#1",
        source: """
      func foo(x: Int) {}
      """,
        origin: "OptionalLvaluesTests.testOptionalLvalues10",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOptionalLvalues11#1",
        source: """
      var nonOptional: S = S()
      _ = nonOptional!
      _ = nonOptional!.x
      """,
        origin: "OptionalLvaluesTests.testOptionalLvalues11",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOptionalLvalues12#1",
        source: """
      class C {}
      class D: C {}
      """,
        origin: "OptionalLvaluesTests.testOptionalLvalues12",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOptionalLvalues13#1",
        source: """
      let c = C()
      let d = (c as! D)!
      """,
        origin: "OptionalLvaluesTests.testOptionalLvalues13",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOptional1#1",
        source: """
      struct A {
        func foo() {}
      }
      """,
        origin: "OptionalTests.testOptional1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOptional3a#1",
        source: """
      var c = a?
      """,
        origin: "OptionalTests.testOptional3a",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOptional3b#1",
        source: """
      var d : ()? = a?.foo()
      """,
        origin: "OptionalTests.testOptional3b",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOptional4#1",
        source: """
      var e : (() -> A)?
      var f = e?()
      """,
        origin: "OptionalTests.testOptional4",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOptional5#1",
        source: """
      struct B<T> {}
      var g = B<A?>()
      """,
        origin: "OptionalTests.testOptional5",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOriginalDefinedInAttr1#1",
        source: #"""
      @_originallyDefinedIn(module: "foo", OSX 13.13)
      public func foo() {}
      """#,
        origin: "OriginalDefinedInAttrTests.testOriginalDefinedInAttr1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOriginalDefinedInAttr3#1",
        source: #"""
      @_originallyDefinedIn(module: "foo", OSX 13.13.3)
      public class ToplevelClass {}
      """#,
        origin: "OriginalDefinedInAttrTests.testOriginalDefinedInAttr3",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOriginalDefinedInAttr7#1",
        source: #"""
      @available(OSX 13.10, *)
      @_originallyDefinedIn(module: "foo", * 13.13)
      public class ToplevelClass4 {}
      """#,
        origin: "OriginalDefinedInAttrTests.testOriginalDefinedInAttr7",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOriginalDefinedInAttr7#2",
        source: #"""
      @available(OSX 13.10, *)
      @_originallyDefinedIn(module: "foo", OSX 13.13, iOS 7.0)
      public class ToplevelClass4 {}
      """#,
        origin: "OriginalDefinedInAttrTests.testOriginalDefinedInAttr7",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOriginalDefinedInAttr7#3",
        source: #"""
      @available(OSX 13.10, *)
      @_originallyDefinedIn(module: "foo", OSX 13.14, * 7.0)
      public class ToplevelClass4 {}
      """#,
        origin: "OriginalDefinedInAttrTests.testOriginalDefinedInAttr7",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOriginalDefinedInAttr7#4",
        source: #"""
      public class ToplevelClass4 {
        @_originallyDefinedIn(module: "foo", OSX 13.13)
        subscript(index: Int) -> Int {
              get { return 1 }
              set(newValue) {}
        }
      }
      """#,
        origin: "OriginalDefinedInAttrTests.testOriginalDefinedInAttr7",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOriginalDefinedInAttr8#1",
        source: #"""
      @available(OSX 13.10, *)
      @_originallyDefinedIn(module: "foo", OSX 13.13)
      @_originallyDefinedIn(module: "foo", iOS 7.0)
      internal class ToplevelClass5 {}
      """#,
        origin: "OriginalDefinedInAttrTests.testOriginalDefinedInAttr8",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOriginalDefinedInAttr9#1",
        source: #"""
      @available(OSX 13.10, *)
      @_originallyDefinedIn(module: "foo", OSX 13.13)
      @_originallyDefinedIn(module: "foo", iOS 7.0)
      private class ToplevelClass6 {}
      """#,
        origin: "OriginalDefinedInAttrTests.testOriginalDefinedInAttr9",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOriginalDefinedInAttr10#1",
        source: #"""
      @available(OSX 13.10, *)
      @_originallyDefinedIn(module: "foo", OSX 13.13)
      @_originallyDefinedIn(module: "foo", iOS 7.0)
      fileprivate class ToplevelClass7 {}
      """#,
        origin: "OriginalDefinedInAttrTests.testOriginalDefinedInAttr10",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOriginalDefinedInAttr11#1",
        source: #"""
      @available(OSX 13.10, *)
      @_originallyDefinedIn(module: "foo", OSX 13.13, iOS 7.0)
      internal class ToplevelClass8 {}
      """#,
        origin: "OriginalDefinedInAttrTests.testOriginalDefinedInAttr11",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testOrinalDefinedInAttr12#1",
        source: """
      @_originallyDefinedIn(module: "ToasterKit", _iOS13Aligned)
      struct Vehicle {}
      """,
        origin: "OriginalDefinedInAttrTests.testOrinalDefinedInAttr12",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testPatternWithoutVariablesScript1#1",
        source: """
      _ = 1
      """,
        origin: "PatternWithoutVariablesScriptTests.testPatternWithoutVariablesScript1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testPatternWithoutVariables1#1",
        source: """
      let _ = 1
      inout _ = 1
      _mutating _ = 1
      _borrowing _ = 1
      _consuming _ = 1
      """,
        origin: "PatternWithoutVariablesTests.testPatternWithoutVariables1",
        syntaxVersion: "603.0.1",
        compilerRejects: "consecutive statements on a line must be separated by ';'"
    ),
    SwiftSnippet(
        label: "testPatternWithoutVariables2#1",
        source: """
      func foo() {
        let _ = 1 // OK
        inout _ = 1
        _mutating _ = 1
        _borrowing _ = 1
        _consuming _ = 1
      }
      """,
        origin: "PatternWithoutVariablesTests.testPatternWithoutVariables2",
        syntaxVersion: "603.0.1",
        compilerRejects: "consecutive statements on a line must be separated by ';'"
    ),
    SwiftSnippet(
        label: "testPatternWithoutVariables3#1",
        source: """
      struct Foo {
        let _ = 1
        var (_, _) = (1, 2)
        func foo() {
          let _ = 1 // OK
        }
        inout (_, _) = (1, 2)
        _mutating (_, _) = (1, 2)
        _borrowing (_, _) = (1, 2)
        _consuming (_, _) = (1, 2)
      }
      """,
        origin: "PatternWithoutVariablesTests.testPatternWithoutVariables3",
        syntaxVersion: "603.0.1",
        compilerRejects: "expected declaration"
    ),
    SwiftSnippet(
        label: "testPatternWithoutVariables4#1",
        source: #"""
      // <rdar://problem/19786845> Warn on "let" and "var" when no data is bound in a pattern
      enum SimpleEnum { case Bar }
      """#,
        origin: "PatternWithoutVariablesTests.testPatternWithoutVariables4",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testPatternWithoutVariables5#1",
        source: #"""
      func testVarLetPattern(a : SimpleEnum) {
        switch a {
        case let .Bar: break
        }
        switch a {
        case let x: _ = x; break         // Ok.
        }
        switch a {
        case let _: break
        }
        switch (a, 42) {
        case let (_, x): _ = x; break    // ok
        }
        if case let _ = "str" {}
        switch a {
        case inout .Bar: break
        }
        switch a {
        case _mutating .Bar: break
        }
        switch a {
        case _borrowing .Bar: break
        }
        switch a {
        case _consuming .Bar: break
        }
      }
      """#,
        origin: "PatternWithoutVariablesTests.testPatternWithoutVariables5",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testPatternWithoutVariables6#1",
        source: """
      // https://github.com/apple/swift/issues/53293
      class C_53293 {
        static var _: Int { 0 }
      }
      """,
        origin: "PatternWithoutVariablesTests.testPatternWithoutVariables6",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testMutatingNotADeclarationStartIfNotEnabled#1", source: "_mutating = 2", origin: "PatternWithoutVariablesTests.testMutatingNotADeclarationStartIfNotEnabled", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testPlaygroundLvalues1#1",
        source: """
      var a = 1, b = 2
      let z = 3
      """,
        origin: "PlaygroundLvaluesTests.testPlaygroundLvalues1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testPlaygroundLvalues2#1",
        source: """
      a
      (a, b)
      (a, z)
      """,
        origin: "PlaygroundLvaluesTests.testPlaygroundLvalues2",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testPoundAssert1#1",
        source: """
      #assert(true, 123)
      """,
        origin: "PoundAssertTests.testPoundAssert1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testPoundAssert2#1",
        source: #"""
      #assert(true, "error \(1) message")
      """#,
        origin: "PoundAssertTests.testPoundAssert2",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testPrefixSlash2#1",
        source: """
      prefix operator /
      prefix func / <T> (_ x: T) -> T { x }
      """,
        origin: "PrefixSlashTests.testPrefixSlash2",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testPrefixSlash4#1",
        source: """
      _ = /E.e
      (/E.e).foo(/0)
      """,
        origin: "PrefixSlashTests.testPrefixSlash4",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testPrefixSlash6#1",
        source: """
      foo(/E.e, /E.e)
      foo((/E.e), /E.e)
      foo((/)(E.e), /E.e)
      """,
        origin: "PrefixSlashTests.testPrefixSlash6",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testPrefixSlash8#1",
        source: """
      _ = bar(/E.e) / 2
      """,
        origin: "PrefixSlashTests.testPrefixSlash8",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRawString1#1",
        source: """
      import Swift
      """,
        origin: "RawStringTests.testRawString1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRawString2#1",
        source: ##"""
      _ = #"""
      ###################################################################
      ## This source file is part of the Swift.org open source project ##
      ###################################################################
      """#
      """##,
        origin: "RawStringTests.testRawString2",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRawString3#1",
        source: ####"""
      _ = #"""
          # H1 #
          ## H2 ##
          ### H3 ###
          """#
      """####,
        origin: "RawStringTests.testRawString3",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRawString5#1",
        source: ###"""
      _ = ##"""
          One
          ""Alpha""
          """##
      """###,
        origin: "RawStringTests.testRawString5",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRawString6#1",
        source: ###"""
      _ = ##"""
          Two
        Beta
        """##
      """###,
        origin: "RawStringTests.testRawString6",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRawString7#1",
        source: ##"""
      _ = #"""
          Three\r
          Gamma\
        """#
      """##,
        origin: "RawStringTests.testRawString7",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRawString8#1",
        source: ####"""
      _ = ###"""
          Four \(foo)
          Delta
      """###
      """####,
        origin: "RawStringTests.testRawString8",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRawString9#1",
        source: ###"""
      _ = ##"""
        print("""
          Five\##n\##n\##nEpsilon
          """)
        """##
      """###,
        origin: "RawStringTests.testRawString9",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRawString10#1",
        source: """
      // ===---------- Single line --------===
      """,
        origin: "RawStringTests.testRawString10",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRawString11#1",
        source: ##"""
      _ = #""Zeta""#
      """##,
        origin: "RawStringTests.testRawString11",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRawString12#1",
        source: ##"""
      _ = #""Eta"\#n\#n\#n\#""#
      """##,
        origin: "RawStringTests.testRawString12",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRawString13#1",
        source: ##"""
      _ = #""Iota"\n\n\n\""#
      """##,
        origin: "RawStringTests.testRawString13",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRawString14#1",
        source: ##"""
      _ = #"a raw string with \" in it"#
      """##,
        origin: "RawStringTests.testRawString14",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRawString15#1",
        source: ###"""
      _ = ##"""
            a raw string with """ in it
            """##
      """###,
        origin: "RawStringTests.testRawString15",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRawString16#1",
        source: """
      // ===---------- False Multiline Delimiters --------===
      """,
        origin: "RawStringTests.testRawString16",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRawString17#1",
        source: ##"""
      /// Source code contains zero-width character in this format: `#"[U+200B]"[U+200B]"#`
      /// The check contains zero-width character in this format: `"[U+200B]\"[U+200B]"`
      /// If this check fails after you implement `diagnoseZeroWidthMatchAndAdvance`,
      /// then you may need to tweak how to test for single-line string literals that
      /// resemble a multiline delimiter in `advanceIfMultilineDelimiter` so that it
      /// passes again.
      /// See https://github.com/apple/swift/issues/51192.
      _ = #"​"​"#
      """##,
        origin: "RawStringTests.testRawString17",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRawString18#1",
        source: ##"""
      _ = #""""#
      """##,
        origin: "RawStringTests.testRawString18",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRawString19#1",
        source: ##"""
      _ = #"""""#
      """##,
        origin: "RawStringTests.testRawString19",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRawString20#1",
        source: ##"""
      _ = #""""""#
      """##,
        origin: "RawStringTests.testRawString20",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRawString21#1",
        source: ##"""
      _ = #"""#
      """##,
        origin: "RawStringTests.testRawString21",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRawString22#1",
        source: ###"""
      _ = ##""" foo # "# "##
      """###,
        origin: "RawStringTests.testRawString22",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRawString23#1",
        source: ####"""
      _ = ###""" "# "## "###
      """####,
        origin: "RawStringTests.testRawString23",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRawString24#1",
        source: ####"""
      _ = ###"""##"###
      """####,
        origin: "RawStringTests.testRawString24",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRawString25#1",
        source: ##"""
      _ = "interpolating \(#"""false delimiter"#)"
      """##,
        origin: "RawStringTests.testRawString25",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRawString26#1",
        source: ##"""
      _ = """
        interpolating \(#"""false delimiters"""#)
        """
      """##,
        origin: "RawStringTests.testRawString26",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRawString27#1",
        source: ##"""
      let foo = "Interpolation"
      _ = #"\b\b \#(foo)\#(foo) Kappa"#
      """##,
        origin: "RawStringTests.testRawString27",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRawString28#1",
        source: ###"""
      _ = """
        interpolating \(##"""
          delimited \##("string")\#n\##n
          """##)
        """
      """###,
        origin: "RawStringTests.testRawString28",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRawString30#1",
        source: ##"""
      #"unused literal"#
      """##,
        origin: "RawStringTests.testRawString30",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRawString32#1",
        source: ##"""
      _ = #"This is a string"#
      """##,
        origin: "RawStringTests.testRawString32",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRawString33#1",
        source: ######"""
      _ = #####"This is a string"#####
      """######,
        origin: "RawStringTests.testRawString33",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRawString34#1",
        source: ###"""
      _ = #"enum\s+.+\{.*case\s+[:upper:]"#
      _ = #"Alice: "How long is forever?" White Rabbit: "Sometimes, just one second.""#
      _ = #"\#\#1"#
      _ = ##"\#1"##
      _ = #"c:\windows\system32"#
      _ = #"\d{3) \d{3} \d{4}"#
      _ = #"""
          a string with
          """
          in it
          """#
      _ = #"a raw string containing \r\n"#
      _ = #"""
          [
              {
                  "id": "12345",
                  "title": "A title that \"contains\" \\\""
              }
          ]
          """#
      _ = #"# #"#
      """###,
        origin: "RawStringTests.testRawString34",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRecovery6#1",
        source: """
      class Container<T> {
        func exists() -> Bool { return true }
      }
      """,
        origin: "RecoveryTests.testRecovery6",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRecovery8#1",
        source: """
      @xyz class BadAttributes {
        func exists() -> Bool { return true }
      }
      """,
        origin: "RecoveryTests.testRecovery8",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRecovery9#1",
        source: """
      func test(a: BadAttributes) -> () {
        _ = a.exists() // no-warning
      }
      """,
        origin: "RecoveryTests.testRecovery9",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRecovery11#1",
        source: """
      func braceStmt2() {
        { () in braceStmt2(); }
      }
      """,
        origin: "RecoveryTests.testRecovery11",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRecovery12#1",
        source: """
      func braceStmt3() {
        {
          undefinedIdentifier {}
        }
      }
      """,
        origin: "RecoveryTests.testRecovery12",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRecovery13#1",
        source: """
      static func toplevelStaticFunc() {}
      static struct StaticStruct {}
      static class StaticClass {}
      static protocol StaticProtocol {}
      static typealias StaticTypealias = Int
      class ClassWithStaticDecls {
        class var a = 42
      }
      """,
        origin: "RecoveryTests.testRecovery13",
        syntaxVersion: "603.0.1",
        compilerRejects: "static methods may only be declared on a type"
    ),
    SwiftSnippet(
        label: "testRecovery27#1",
        source: """
      {
        missingControllingExprInRepeatWhile();
      }
      """,
        origin: "RecoveryTests.testRecovery27",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRecovery65#1",
        source: """
      _ = foobar // OK.
      """,
        origin: "RecoveryTests.testRecovery65",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRecovery111#1",
        source: """
      //===---
      """,
        origin: "RecoveryTests.testRecovery111",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRecovery112#1",
        source: """
      class Base {}
      """,
        origin: "RecoveryTests.testRecovery112",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRecovery113#1",
        source: """
      class ExprSuper1 {
        init() {
          super
        }
      }
      """,
        origin: "RecoveryTests.testRecovery113",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRecovery115#1",
        source: """
      //===--- Recovery for braces inside a nominal decl.
      """,
        origin: "RecoveryTests.testRecovery115",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRecovery117#1",
        source: """
      func use_BracesInsideNominalDecl1() {
        // Ensure that the typealias decl is not skipped.
        var _ : BracesInsideNominalDecl1.A // no-error
      }
      """,
        origin: "RecoveryTests.testRecovery117",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRecovery123#1",
        source: """
      class Base2<T> {
      }
      """,
        origin: "RecoveryTests.testRecovery123",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRecovery124#1",
        source: """
      class SubModule {
          class Base1 {}
          class Base2<T> {}
      }
      """,
        origin: "RecoveryTests.testRecovery124",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRecovery132#1",
        source: """
      Base=1 as Base=1
      """,
        origin: "RecoveryTests.testRecovery132",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRecovery152#1",
        source: """
      if var y = x, y == 0, var z = x {
        z = y; y = z
      }
      """,
        origin: "RecoveryTests.testRecovery152",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRecovery154#1",
        source: #"""
      // <rdar://problem/20883210> QoI: Following a "let" condition with boolean condition spouts nonsensical errors
      guard let x: Int? = 1, x == 1 else {  }
      """#,
        origin: "RecoveryTests.testRecovery154",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRecovery161#1",
        source: """
      // <rdar://problem/21369926> Malformed Swift Enums crash playground service
      enum Rank: Int {
        case Ace = 1
        case Two = 2.1
      }
      """,
        origin: "RecoveryTests.testRecovery161",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRecovery162#1",
        source: """
      // rdar://22240342 - Crash in diagRecursivePropertyAccess
      class r22240342 {
        lazy var xx: Int = {
          foo {
            let issueView = 42
            issueView.delegate = 12
          }
          return 42
          }()
      }
      """,
        origin: "RecoveryTests.testRecovery162",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRecovery165#1",
        source: """
      // <rdar://problem/23086402> Swift compiler crash in CSDiag
      protocol A23086402 {
        var b: B23086402 { get }
      }
      """,
        origin: "RecoveryTests.testRecovery165",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRecovery166#1",
        source: """
      protocol B23086402 {
        var c: [String] { get }
      }
      """,
        origin: "RecoveryTests.testRecovery166",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRecovery167#1",
        source: #"""
      func test23086402(a: A23086402) {
        print(a.b.c + "") // should not crash but: expected-error {{}}
      }
      """#,
        origin: "RecoveryTests.testRecovery167",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRecovery168#1",
        source: #"""
      // <rdar://problem/23550816> QoI: Poor diagnostic in argument list of "print" (varargs related)
      // The situation has changed. String now conforms to the RangeReplaceableCollection protocol
      // and `ss + s` becomes ambiguous. Disambiguation is provided with the unavailable overload
      // in order to produce a meaningful diagnostics. (Related: <rdar://problem/31763930>)
      func test23550816(ss: [String], s: String) {
        print(ss + s)
      }
      """#,
        origin: "RecoveryTests.testRecovery168",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRecovery169#1",
        source: """
      // <rdar://problem/23719432> [practicalswift] Compiler crashes on &(Int:_)
      func test23719432() {
        var x = 42
          &(Int:x)
      }
      """,
        origin: "RecoveryTests.testRecovery169",
        syntaxVersion: "603.0.1",
        compilerRejects: "'&' may only be used to pass an argument to inout parameter"
    ),
    SwiftSnippet(
        label: "testRegexParseError1#1",
        source: """
      _ = /(/
      """,
        origin: "RegexParseErrorTests.testRegexParseError1",
        syntaxVersion: "603.0.1",
        compilerRejects: "expected expression after unary operator"
    ),
    SwiftSnippet(
        label: "testRegexParseError2#1",
        source: """
      _ = #/(/#
      """,
        origin: "RegexParseErrorTests.testRegexParseError2",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRegexParseError4#1",
        source: """
      _ = /)/
      """,
        origin: "RegexParseErrorTests.testRegexParseError4",
        syntaxVersion: "603.0.1",
        compilerRejects: "expected expression after unary operator"
    ),
    SwiftSnippet(
        label: "testRegexParseError5#1",
        source: """
      _ = #/)/#
      """,
        origin: "RegexParseErrorTests.testRegexParseError5",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRegexParseError10#1",
        source: """
      _ = #/(?/#
      """,
        origin: "RegexParseErrorTests.testRegexParseError10",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRegexParseError11#1",
        source: """
      _ = #/(?'/#
      """,
        origin: "RegexParseErrorTests.testRegexParseError11",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRegexParseError12#1",
        source: """
      _ = #/(?'abc/#
      """,
        origin: "RegexParseErrorTests.testRegexParseError12",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRegexParseError13#1",
        source: """
      _ = #/(?'abc /#
      """,
        origin: "RegexParseErrorTests.testRegexParseError13",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRegexParseError15#1",
        source: #"""
      _ = #/\(?'abc/#
      """#,
        origin: "RegexParseErrorTests.testRegexParseError15",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRegexParseError19#1",
        source: """
      foo(#/(?/#, #/abc/#) 
      foo(#/(?C/#, #/abc/#)
      """,
        origin: "RegexParseErrorTests.testRegexParseError19",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRegexParseError20#1",
        source: """
      foo(#/(?'/#, #/abc/#)
      """,
        origin: "RegexParseErrorTests.testRegexParseError20",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRegex1#1",
        source: """
      _ = /abc/
      _ = #/abc/#
      _ = ##/abc/##
      """,
        origin: "RegexTests.testRegex1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRegex3#1",
        source: """
      foo(/abc/, #/abc/#, ##/abc/##)
      """,
        origin: "RegexTests.testRegex3",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRegex4#1",
        source: """
      let arr = [/abc/, #/abc/#, ##/abc/##]
      """,
        origin: "RegexTests.testRegex4",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRegex5#1",
        source: #"""
      _ = /\w+/.self
      _ = #/\w+/#.self
      _ = ##/\w+/##.self
      """#,
        origin: "RegexTests.testRegex5",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRegex6#1",
        source: ##"""
      _ = /#\/\#\\/
      _ = #/#/\/\#\\/#
      _ = ##/#|\|\#\\/##
      """##,
        origin: "RegexTests.testRegex6",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testRegex7#1",
        source: """
      _ = (#/[*/#, #/+]/#, #/.]/#)
      """,
        origin: "RegexTests.testRegex7",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testResultBuilder1#1",
        source: """
      // rdar://70158735
      """,
        origin: "ResultBuilderTests.testResultBuilder1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testResultBuilder2#1",
        source: """
      @resultBuilder
      struct A<T> {
        static func buildBlock(_ values: Int...) -> Int { return 0 }
      }
      """,
        origin: "ResultBuilderTests.testResultBuilder2",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testResultBuilder3#1",
        source: """
      struct B<T> {}
      """,
        origin: "ResultBuilderTests.testResultBuilder3",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testResultBuilder4#1",
        source: """
      extension B {
        @resultBuilder
        struct Generic<U> {
          static func buildBlock(_ values: Int...) -> Int { return 0 }
        }
        @resultBuilder
        struct NonGeneric {
          static func buildBlock(_ values: Int...) -> Int { return 0 }
        }
      }
      """,
        origin: "ResultBuilderTests.testResultBuilder4",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testResultBuilder5#1",
        source: """
      @A<Float> var test0: Int {
        1
        2
        3
      }
      """,
        origin: "ResultBuilderTests.testResultBuilder5",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testResultBuilder6#1",
        source: """
      @B<Float>.NonGeneric var test1: Int {
        1
        2
        3
      }
      """,
        origin: "ResultBuilderTests.testResultBuilder6",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testResultBuilder7#1",
        source: """
      @B<Float>.Generic<Float> var test2: Int {
        1
        2
        3
      }
      """,
        origin: "ResultBuilderTests.testResultBuilder7",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSelfRebinding1#1",
        source: #"""
      class Writer {
          private var articleWritten = 47
          func stop() {
              let rest: () -> Void = { [weak self] in
                  let articleWritten = self?.articleWritten ?? 0
                  guard let `self` = self else {
                      return
                  }
                  self.articleWritten = articleWritten
              }
              fatalError("I'm running out of time")
              rest()
          }
          func nonStop() {
              let write: () -> Void = { [weak self] in
                  self?.articleWritten += 1
                  if let self = self {
                      self.articleWritten += 1
                  }
                  if let `self` = self {
                      self.articleWritten += 1
                  }
                  guard let self = self else {
                      return
                  }
                  self.articleWritten += 1
              }
              write()
          }
      }
      """#,
        origin: "SelfRebindingTests.testSelfRebinding1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSelfRebinding3#1",
        source: """
      class MyCls {
          func something() {}
          func test() {
              let `self` = Writer() // Even if `self` is shadowed,
              something() // this should still refer `MyCls.something`.
          }
      }
      """,
        origin: "SelfRebindingTests.testSelfRebinding3",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSelfRebinding4#1",
        source: """
      // https://github.com/apple/swift/issues/47136
      // Method called 'self' can be confused with regular 'self'
      """,
        origin: "SelfRebindingTests.testSelfRebinding4",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSelfRebinding5#1",
        source: """
      func funcThatReturnsSomething(_ any: Any) -> Any {
          any
      }
      """,
        origin: "SelfRebindingTests.testSelfRebinding5",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSelfRebinding6#1",
        source: """
      struct TypeWithSelfMethod {
          let property = self
          // Existing warning expected, not confusable
          let property2 = self()
          let propertyFromClosure: () = {
              print(self)
          }()
          let propertyFromFunc = funcThatReturnsSomething(self)
          let propertyFromFunc2 = funcThatReturnsSomething(TypeWithSelfMethod.self) // OK
          func `self`() {
          }
      }
      """,
        origin: "SelfRebindingTests.testSelfRebinding6",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSelfRebinding7#1",
        source: """
      /// Test fix_unqualified_access_member_named_self doesn't appear for computed var called `self`
      /// it can't currently be referenced as a static member -- unlike a method with the same name
      struct TypeWithSelfComputedVar {
          let property = self
          let propertyFromClosure: () = {
              print(self)
          }()
          let propertyFromFunc = funcThatReturnsSomething(self)
          var `self`: () {
              ()
          }
      }
      """,
        origin: "SelfRebindingTests.testSelfRebinding7",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSelfRebinding8#1",
        source: """
      /// Test fix_unqualified_access_member_named_self doesn't appear for property called `self`
      /// it can't currently be referenced as a static member -- unlike a method with the same name
      struct TypeWithSelfProperty {
          let property = self
          let propertyFromClosure: () = {
              print(self)
          }()
          let propertyFromFunc = funcThatReturnsSomething(self)
          let `self`: () = ()
      }
      """,
        origin: "SelfRebindingTests.testSelfRebinding8",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSelfRebinding9#1",
        source: """
      enum EnumCaseNamedSelf {
          case `self`
          init() {
              self = .self // OK
              self = .`self` // OK
              self = EnumCaseNamedSelf.`self` // OK
          }
      }
      """,
        origin: "SelfRebindingTests.testSelfRebinding9",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSelfRebinding10#1",
        source: """
      // rdar://90624344 - warning about `self` which cannot be fixed because it's located in implicitly generated code.
      struct TestImplicitSelfUse : Codable {
        let `self`: Int // Ok
      }
      """,
        origin: "SelfRebindingTests.testSelfRebinding10",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSemicolon1#1",
        source: #"""
      let a = 42;
      var b = "b";
      """#,
        origin: "SemicolonTests.testSemicolon1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSemicolon2#1",
        source: """
      struct A {
          var a1: Int;
          let a2: Int ;
          var a3: Int;let a4: Int
          var a5: Int; let a6: Int;
      };
      """,
        origin: "SemicolonTests.testSemicolon2",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSemicolon3#1",
        source: """
      enum B {
          case B1;
          case B2(value: Int);
          case B3
          case B4; case B5 ; case B6;
      };
      """,
        origin: "SemicolonTests.testSemicolon3",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSemicolon4#1",
        source: """
      class C {
          var x: Int;
          let y = 3.14159;
          init(x: Int) { self.x = x; }
      };
      """,
        origin: "SemicolonTests.testSemicolon4",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSemicolon5#1",
        source: """
      typealias C1 = C;
      """,
        origin: "SemicolonTests.testSemicolon5",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSemicolon6#1",
        source: """
      protocol D {
          var foo: () -> Int { get };
      }
      """,
        origin: "SemicolonTests.testSemicolon6",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSemicolon7#1",
        source: """
      struct D1: D {
          let foo = { return 42; };
      }
      func e() -> Bool {
          return false;
      }
      """,
        origin: "SemicolonTests.testSemicolon7",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSemicolon8#1",
        source: """
      import Swift;
      """,
        origin: "SemicolonTests.testSemicolon8",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSemicolon9#1",
        source: """
      for i in 1..<1000 {
          if i % 2 == 1 {
              break;
          };
      }
      """,
        origin: "SemicolonTests.testSemicolon9",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSemicolon10#1",
        source: """
      let six = (1..<3).reduce(0, +);
      """,
        origin: "SemicolonTests.testSemicolon10",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSemicolon11#1",
        source: """
      func lessThanTwo(input: UInt) -> Bool {
          switch input {
          case 0:     return true;
          case 1, 2:  return true;
          default:
              return false;
          }
      }
      """,
        origin: "SemicolonTests.testSemicolon11",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSemicolon12#1",
        source: """
      enum StarWars {
          enum Quality { case 😀; case 🙂; case 😐; case 😏; case 😞 };
          case Ep4; case Ep5; case Ep6
          case Ep1, Ep2; case Ep3;
      };
      """,
        origin: "SemicolonTests.testSemicolon12",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSubscripting1#1",
        source: """
      struct X { }
      """,
        origin: "SubscriptingTests.testSubscripting1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSubscripting2#1",
        source: """
      // Simple examples
      struct X1 {
        var stored: Int
        subscript(i: Int) -> Int {
          get {
            return stored
          }
          mutating
          set {
            stored = newValue
          }
        }
      }
      """,
        origin: "SubscriptingTests.testSubscripting2",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSubscripting3#1",
        source: """
      struct X2 {
        var stored: Int
        subscript(i: Int) -> Int {
          get {
            return stored + i
          }
          set(v) {
            stored = v - i
          }
        }
      }
      """,
        origin: "SubscriptingTests.testSubscripting3",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSubscripting4#1",
        source: """
      struct X3 {
        var stored: Int
        subscript(_: Int) -> Int {
          get {
            return stored
          }
          set(v) {
            stored = v
          }
        }
      }
      """,
        origin: "SubscriptingTests.testSubscripting4",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSubscripting5#1",
        source: """
      struct X4 {
        var stored: Int
        subscript(i: Int, j: Int) -> Int {
          get {
            return stored + i + j
          }
          mutating
          set(v) {
            stored = v + i - j
          }
        }
      }
      """,
        origin: "SubscriptingTests.testSubscripting5",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSubscripting6#1",
        source: """
      struct X5 {
        static var stored: Int = 1
        static subscript(i: Int) -> Int {
          get {
            return stored + i
          }
          set {
            stored = newValue - i
          }
        }
      }
      """,
        origin: "SubscriptingTests.testSubscripting6",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSubscripting7#1",
        source: """
      class X6 {
        static var stored: Int = 1
        class subscript(i: Int) -> Int {
          get {
            return stored + i
          }
          set {
            stored = newValue - i
          }
        }
      }
      """,
        origin: "SubscriptingTests.testSubscripting7",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSubscripting8#1",
        source: """
      struct Y1 {
        var stored: Int
        subscript(_: i, j: Int) -> Int {
          get {
            return stored + j
          }
          set {
            stored = j
          }
        }
      }
      """,
        origin: "SubscriptingTests.testSubscripting8",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSubscripting9#1",
        source: """
      // Mutating getters on constants
      // https://github.com/apple/swift/issues/43457
      """,
        origin: "SubscriptingTests.testSubscripting9",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSubscripting10#1",
        source: """
      struct Y2 {
        subscript(_: Int) -> Int {
          mutating get { return 0 }
        }
      }
      """,
        origin: "SubscriptingTests.testSubscripting10",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSubscripting11#1",
        source: """
      let y2 = Y2()
      _ = y2[0]
      """,
        origin: "SubscriptingTests.testSubscripting11",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSubscripting17#1",
        source: """
      struct A5 {
        subscript(i : Int) -> Int
      }
      """,
        origin: "SubscriptingTests.testSubscripting17",
        syntaxVersion: "603.0.1",
        compilerRejects: "expected '{' in subscript to specify getter and setter implementation"
    ),
    SwiftSnippet(
        label: "testSubscripting19#1",
        source: """
      struct A7 {
        class subscript(a: Float) -> Int {
          get {
            return 42
          }
        }
      }
      """,
        origin: "SubscriptingTests.testSubscripting19",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSubscripting20#1",
        source: """
      class A7b {
        class static subscript(a: Float) -> Int {
          get {
            return 42
          }
        }
      }
      """,
        origin: "SubscriptingTests.testSubscripting20",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSuper1#1",
        source: """
      class B {
        var foo: Int
        func bar() {}
        init() {}
        init(x: Int) {}
        subscript(x: Int) -> Int {
          get {}
          set {}
        }
      }
      """,
        origin: "SuperTests.testSuper1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSuper2a#1",
        source: #"""
      class D : B {
        override init() {
          super.init()
          super.init(42)
        }
      }
      """#,
        origin: "SuperTests.testSuper2a",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSuper2b#1",
        source: #"""
      class D : B {
        override init(x:Int) {
          let _: () -> B = super.init
        }
      }
      """#,
        origin: "SuperTests.testSuper2b",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSuper2c#1",
        source: #"""
      class D : B {
        convenience init(y:Int) {
          let _: () -> D = self.init
        }
      }
      """#,
        origin: "SuperTests.testSuper2c",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSuper2d#1",
        source: #"""
      class D : B {
        init(z: Int) {
          super
            .init(x: z)
        }
      }
      """#,
        origin: "SuperTests.testSuper2d",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSuper2e#1",
        source: #"""
      class D : B {
        func super_calls() {
          super.foo
          super.foo.bar
          super.bar
          super.bar()
          super.init
          super.init()
          super.init(0)
          super[0]
          super
            .bar()
        }
      }
      """#,
        origin: "SuperTests.testSuper2e",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSuper2g#1",
        source: #"""
      class D : B {
        func bad_super_2() {
          super(0)
        }
      }
      """#,
        origin: "SuperTests.testSuper2g",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSuper2h#1",
        source: #"""
      class D : B {
        func bad_super_3() {
          super
            [1]
        }
      }
      """#,
        origin: "SuperTests.testSuper2h",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSuper3#1",
        source: """
      class Closures : B {
        func captureWeak() {
          let g = { [weak self] () -> Void in // expected-note * {{'self' explicitly captured here}}
            super.foo()
          }
          g()
        }
        func captureUnowned() {
          let g = { [unowned self] () -> Void in // expected-note * {{'self' explicitly captured here}}
            super.foo()
          }
          g()
        }
        func nestedInner() {
          let g = { () -> Void in
            let h = { [weak self] () -> Void in // expected-note * {{'self' explicitly captured here}}
              super.foo()
              nil ?? super.foo()
            }
            h()
          }
          g()
        }
        func nestedOuter() {
          let g = { [weak self] () -> Void in // expected-note * {{'self' explicitly captured here}}
            let h = { () -> Void in
              super.foo()
              nil ?? super.foo()
            }
            h()
          }
          g()
        }
      }
      """,
        origin: "SuperTests.testSuper3",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch1#1",
        source: """
      func ~= (x: (Int,Int), y: (Int,Int)) -> Bool {
        return true
      }
      """,
        origin: "SwitchTests.testSwitch1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch8#1",
        source: """
      var x: Int
      """,
        origin: "SwitchTests.testSwitch8",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch9#1",
        source: """
      switch x {}
      """,
        origin: "SwitchTests.testSwitch9",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch10#1",
        source: """
      switch x {
      case 0:
        x = 0
      // Multiple patterns per case
      case 1, 2, 3:
        x = 0
      // 'where' guard
      case _ where x % 2 == 0:
        x = 1
        x = 2
        x = 3
      case _ where x % 2 == 0,
           _ where x % 3 == 0:
        x = 1
      case 10,
           _ where x % 3 == 0:
        x = 1
      case _ where x % 2 == 0,
           20:
        x = 1
      case var y where y % 2 == 0:
        x = y + 1
      case _ where 0:
        x = 0
      default:
        x = 1
      }
      """,
        origin: "SwitchTests.testSwitch10",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch11#1",
        source: """
      // Multiple cases per case block
      switch x {
      case 0:
      case 1:
        x = 0
      }
      """,
        origin: "SwitchTests.testSwitch11",
        syntaxVersion: "603.0.1",
        compilerRejects: "'case' label in a 'switch' must have at least one executable statement"
    ),
    SwiftSnippet(
        label: "testSwitch12#1",
        source: """
      switch x {
      case 0:
      default:
        x = 0
      }
      """,
        origin: "SwitchTests.testSwitch12",
        syntaxVersion: "603.0.1",
        compilerRejects: "'case' label in a 'switch' must have at least one executable statement"
    ),
    SwiftSnippet(
        label: "testSwitch13#1",
        source: """
      switch x {
      case 0:
        x = 0
      case 1:
      }
      """,
        origin: "SwitchTests.testSwitch13",
        syntaxVersion: "603.0.1",
        compilerRejects: "'case' label in a 'switch' must have at least one executable statement"
    ),
    SwiftSnippet(
        label: "testSwitch14#1",
        source: """
      switch x {
      case 0:
        x = 0
      default:
      }
      """,
        origin: "SwitchTests.testSwitch14",
        syntaxVersion: "603.0.1",
        compilerRejects: "'default' label in a 'switch' must have at least one executable statem"
    ),
    SwiftSnippet(
        label: "testSwitch17#1",
        source: """
      switch x {
      default:
        x = 0
      default:
        x = 0
      }
      """,
        origin: "SwitchTests.testSwitch17",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch20#1",
        source: """
      switch x {
      default:
      case 0:
        x = 0
      }
      """,
        origin: "SwitchTests.testSwitch20",
        syntaxVersion: "603.0.1",
        compilerRejects: "'default' label in a 'switch' must have at least one executable statem"
    ),
    SwiftSnippet(
        label: "testSwitch21#1",
        source: """
      switch x {
      default:
      default:
        x = 0
      }
      """,
        origin: "SwitchTests.testSwitch21",
        syntaxVersion: "603.0.1",
        compilerRejects: "'default' label in a 'switch' must have at least one executable statem"
    ),
    SwiftSnippet(
        label: "testSwitch23#1",
        source: """
      switch x {
      case 0:
      }
      """,
        origin: "SwitchTests.testSwitch23",
        syntaxVersion: "603.0.1",
        compilerRejects: "'case' label in a 'switch' must have at least one executable statement"
    ),
    SwiftSnippet(
        label: "testSwitch24#1",
        source: """
      switch x {
      case 0:
      case 1:
        x = 0
      }
      """,
        origin: "SwitchTests.testSwitch24",
        syntaxVersion: "603.0.1",
        compilerRejects: "'case' label in a 'switch' must have at least one executable statement"
    ),
    SwiftSnippet(
        label: "testSwitch25#1",
        source: """
      switch x {
      case 0:
        x = 0
      case 1:
      }
      """,
        origin: "SwitchTests.testSwitch25",
        syntaxVersion: "603.0.1",
        compilerRejects: "'case' label in a 'switch' must have at least one executable statement"
    ),
    SwiftSnippet(
        label: "testSwitch27#1",
        source: """
      fallthrough
      """,
        origin: "SwitchTests.testSwitch27",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch28#1",
        source: """
      switch x {
      case 0:
        fallthrough
      case 1:
        fallthrough
      default:
        fallthrough
      }
      """,
        origin: "SwitchTests.testSwitch28",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch29#1",
        source: """
      // Fallthrough can transfer control anywhere within a case and can appear
      // multiple times in the same case.
      switch x {
      case 0:
        if true { fallthrough }
        if false { fallthrough }
        x += 1
      default:
        x += 1
      }
      """,
        origin: "SwitchTests.testSwitch29",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch30#1",
        source: """
      // Cases cannot contain 'var' bindings if there are multiple matching patterns
      // attached to a block. They may however contain other non-binding patterns.
      """,
        origin: "SwitchTests.testSwitch30",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch31#1",
        source: """
      var t = (1, 2)
      """,
        origin: "SwitchTests.testSwitch31",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch32#1",
        source: """
      switch t {
      case (var a, 2), (1, _):
        ()
      case (_, 2), (var a, _):
        ()
      case (var a, 2), (1, var b):
        ()
      case (var a, 2):
      case (1, _):
        ()
      case (_, 2):
      case (1, var a):
        ()
      case (var a, 2):
      case (1, var b):
        ()
      case (1, let b): // let bindings expected-warning {{immutable value 'b' was never used; consider replacing with '_' or removing it}}
        ()
      case (_, 2), (let a, _):
        ()
      // OK
      case (_, 2), (1, _):
        ()
      case (_, var a), (_, var a):
        ()
      case (var a, var b), (var b, var a):
        ()
      case (_, 2):
      case (1, _):
        ()
      }
      """,
        origin: "SwitchTests.testSwitch32",
        syntaxVersion: "603.0.1",
        compilerRejects: "'a' must be bound in every pattern"
    ),
    SwiftSnippet(
        label: "testSwitch33#1",
        source: """
      func patternVarUsedInAnotherPattern(x: Int) {
        switch x {
        case let a,
             value:
          break
        }
      }
      """,
        origin: "SwitchTests.testSwitch33",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch34#1",
        source: """
      // Fallthroughs can only transfer control into a case label with bindings if the previous case binds a superset of those vars.
      switch t {
      case (1, 2):
        fallthrough
      case (var a, var b):
        t = (b, a)
      }
      """,
        origin: "SwitchTests.testSwitch34",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch35#1",
        source: """
      switch t { // specifically notice on next line that we shouldn't complain that a is unused - just never mutated
      case (var a, let b):
        t = (b, b)
        fallthrough // ok - notice that subset of bound variables falling through is fine
      case (2, let a):
        t = (a, a)
      }
      """,
        origin: "SwitchTests.testSwitch35",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch36#1",
        source: """
      func patternVarDiffType(x: Int, y: Double) {
        switch (x, y) {
        case (1, let a):
          fallthrough
        case (let a, _):
          break
        }
      }
      """,
        origin: "SwitchTests.testSwitch36",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch37#1",
        source: """
      func patternVarDiffMutability(x: Int, y: Double) {
        switch x {
        case let a where a < 5, var a where a > 10:
          break
        default:
          break
        }
        switch (x, y) {
        // Would be nice to have a fixit in the following line if we detect that all bindings in the same pattern have the same problem.
        case let (a, b) where a < 5, var (a, b) where a > 10: // expected-error 2{{'var' pattern binding must match previous 'let' pattern binding}}{{none}}
          break
        case (let a, var b) where a < 5, (let a, let b) where a > 10:
          break
        case (let a, let b) where a < 5, (var a, let b) where a > 10, (let a, var b) where a == 8:
          break
        default:
          break
        }
      }
      """,
        origin: "SwitchTests.testSwitch37",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch38#1",
        source: """
      func test_label(x : Int) {
      Gronk:
        switch x {
        case 42: return
        }
      }
      """,
        origin: "SwitchTests.testSwitch38",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch39#1",
        source: """
      func enumElementSyntaxOnTuple() {
        switch (1, 1) {
        case .Bar:
          break
        default:
          break
        }
      }
      """,
        origin: "SwitchTests.testSwitch39",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch40#1",
        source: """
      // https://github.com/apple/swift/issues/42798
      enum Whatever { case Thing }
      func f0(values: [Whatever]) {
          switch value {
          case .Thing: // Ok. Don't emit diagnostics about enum case not found in type <<error type>>.
              break
          }
      }
      """,
        origin: "SwitchTests.testSwitch40",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch41#1",
        source: #"""
      // https://github.com/apple/swift/issues/43334
      // https://github.com/apple/swift/issues/43335
      enum Whichever {
        case Thing
        static let title = "title"
        static let alias: Whichever = .Thing
      }
      func f1(x: String, y: Whichever) {
        switch x {
          case Whichever.title: // Ok. Don't emit diagnostics for static member of enum.
              break
          case Whichever.buzz:
              break
          case Whichever.alias:
          default:
            break
        }
        switch y {
          case Whichever.Thing: // Ok.
              break
          case Whichever.alias: // Ok. Don't emit diagnostics for static member of enum.
              break
          case Whichever.title:
              break
        }
        switch y {
          case .alias:
            break
          default:
            break
        }
      }
      """#,
        origin: "SwitchTests.testSwitch41",
        syntaxVersion: "603.0.1",
        compilerRejects: "'case' label in a 'switch' must have at least one executable statement"
    ),
    SwiftSnippet(
        label: "testSwitch42#1",
        source: """
      switch Whatever.Thing {
      case .Thing:
      @unknown case _:
        x = 0
      }
      """,
        origin: "SwitchTests.testSwitch42",
        syntaxVersion: "603.0.1",
        compilerRejects: "'case' label in a 'switch' must have at least one executable statement"
    ),
    SwiftSnippet(
        label: "testSwitch43#1",
        source: """
      switch Whatever.Thing {
      case .Thing:
      @unknown default:
        x = 0
      }
      """,
        origin: "SwitchTests.testSwitch43",
        syntaxVersion: "603.0.1",
        compilerRejects: "'case' label in a 'switch' must have at least one executable statement"
    ),
    SwiftSnippet(
        label: "testSwitch44#1",
        source: """
      switch Whatever.Thing {
      case .Thing:
        x = 0
      @unknown case _:
      }
      """,
        origin: "SwitchTests.testSwitch44",
        syntaxVersion: "603.0.1",
        compilerRejects: "'case' label in a 'switch' must have at least one executable statement"
    ),
    SwiftSnippet(
        label: "testSwitch45#1",
        source: """
      switch Whatever.Thing {
      case .Thing:
        x = 0
      @unknown default:
      }
      """,
        origin: "SwitchTests.testSwitch45",
        syntaxVersion: "603.0.1",
        compilerRejects: "'default' label in a 'switch' must have at least one executable statem"
    ),
    SwiftSnippet(
        label: "testSwitch46#1",
        source: """
      switch Whatever.Thing {
      @unknown default:
        x = 0
      default:
        x = 0
      case .Thing:
        x = 0
      }
      """,
        origin: "SwitchTests.testSwitch46",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch47#1",
        source: """
      switch Whatever.Thing {
      default:
        x = 0
      @unknown case _:
        x = 0
      case .Thing:
        x = 0
      }
      """,
        origin: "SwitchTests.testSwitch47",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch48#1",
        source: """
      switch Whatever.Thing {
      default:
        x = 0
      @unknown default:
        x = 0
      case .Thing:
        x = 0
      }
      """,
        origin: "SwitchTests.testSwitch48",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch50#1",
        source: """
      switch Whatever.Thing {
      @unknown case _:
        fallthrough
      }
      """,
        origin: "SwitchTests.testSwitch50",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch51#1",
        source: """
      switch Whatever.Thing {
      @unknown case _:
        fallthrough
      case .Thing:
        break
      }
      """,
        origin: "SwitchTests.testSwitch51",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch52#1",
        source: """
      switch Whatever.Thing {
      @unknown default:
        fallthrough
      case .Thing:
        break
      }
      """,
        origin: "SwitchTests.testSwitch52",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch53#1",
        source: """
      switch Whatever.Thing {
      @unknown case _, _:
        break
      }
      """,
        origin: "SwitchTests.testSwitch53",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch54#1",
        source: """
      switch Whatever.Thing {
      @unknown case _, _, _:
        break
      }
      """,
        origin: "SwitchTests.testSwitch54",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch55#1",
        source: """
      switch Whatever.Thing {
      @unknown case let value:
        _ = value
      }
      """,
        origin: "SwitchTests.testSwitch55",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch56#1",
        source: """
      switch (Whatever.Thing, Whatever.Thing) {
      @unknown case (_, _):
        break
      }
      """,
        origin: "SwitchTests.testSwitch56",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch57#1",
        source: """
      switch Whatever.Thing {
      @unknown case is Whatever:
        break
      }
      """,
        origin: "SwitchTests.testSwitch57",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch58#1",
        source: """
      switch Whatever.Thing {
      @unknown case .Thing:
        break
      }
      """,
        origin: "SwitchTests.testSwitch58",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch59#1",
        source: """
      switch Whatever.Thing {
      @unknown case (_): // okay
        break
      }
      """,
        origin: "SwitchTests.testSwitch59",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch60#1",
        source: """
      switch Whatever.Thing {
      @unknown case _ where x == 0:
        break
      }
      """,
        origin: "SwitchTests.testSwitch60",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch62#1",
        source: """
      switch Whatever.Thing {
      case .Thing:
        x = 0
      #if true
      @unknown case _:
        x = 0
      #endif
      }
      """,
        origin: "SwitchTests.testSwitch62",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch63#1",
        source: """
      switch x {
      case 0:
        break
      @garbage case _:
        break
      }
      """,
        origin: "SwitchTests.testSwitch63",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch65#1",
        source: """
      @unknown let _ = 1
      """,
        origin: "SwitchTests.testSwitch65",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch66#1",
        source: """
      switch x {
      case _:
        @unknown let _ = 1
      }
      """,
        origin: "SwitchTests.testSwitch66",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch68#1",
        source: """
      switch x {
      case 1:
        break
      @unknown case _:
        break
      }
      """,
        origin: "SwitchTests.testSwitch68",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch69#1",
        source: """
      switch x {
      @unknown case _:
        break
      }
      """,
        origin: "SwitchTests.testSwitch69",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch70#1",
        source: """
      switch x {
      @unknown default:
        break
      }
      """,
        origin: "SwitchTests.testSwitch70",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch71#1",
        source: """
      switch Whatever.Thing {
      case .Thing:
        break
      @unknown case _:
        break
      @unknown case _:
        break
      }
      """,
        origin: "SwitchTests.testSwitch71",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch72#1",
        source: """
      switch Whatever.Thing {
      case .Thing:
        break
      @unknown case _:
        break
      @unknown default:
        break
      }
      """,
        origin: "SwitchTests.testSwitch72",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch73#1",
        source: """
      switch Whatever.Thing {
      case .Thing:
        break
      @unknown default:
        break
      @unknown default:
        break
      }
      """,
        origin: "SwitchTests.testSwitch73",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch74#1",
        source: """
      switch Whatever.Thing {
      @unknown case _:
        break
      @unknown case _:
        break
      }
      """,
        origin: "SwitchTests.testSwitch74",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch75#1",
        source: """
      switch Whatever.Thing {
      @unknown case _:
        break
      @unknown default:
        break
      }
      """,
        origin: "SwitchTests.testSwitch75",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch76#1",
        source: """
      switch Whatever.Thing {
      @unknown default:
        break
      @unknown default:
        break
      }
      """,
        origin: "SwitchTests.testSwitch76",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch77#1",
        source: """
      switch x {
      @unknown case _:
        break
      @unknown case _:
        break
      }
      """,
        origin: "SwitchTests.testSwitch77",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch78#1",
        source: """
      switch x {
      @unknown case _:
        break
      @unknown default:
        break
      }
      """,
        origin: "SwitchTests.testSwitch78",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch79#1",
        source: """
      switch x {
      @unknown default:
        break
      @unknown default:
        break
      }
      """,
        origin: "SwitchTests.testSwitch79",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitch80#1",
        source: """
      func testReturnBeforeUnknownDefault() {
        switch x {
        case 1:
          return
        @unknown default:
          break
        }
      }
      """,
        origin: "SwitchTests.testSwitch80",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testToplevelLibrary1#1",
        source: """
      // make sure trailing semicolons are valid syntax in toplevel library code.
      var x = 4;
      """,
        origin: "ToplevelLibraryTests.testToplevelLibrary1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testToplevelLibraryInvalid1#1",
        source: """
      let x = 42
      x + x;
      x + x;
      // Make sure we don't crash on closures at the top level
      ({ })
      ({ 5 }())
      """,
        origin: "ToplevelLibraryTests.testToplevelLibraryInvalid1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTrailingClosures1#1",
        source: """
      func foo<T, U>(a: () -> T, b: () -> U) {}
      """,
        origin: "TrailingClosuresTests.testTrailingClosures1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTrailingClosures2#1",
        source: #"""
      foo { 42 }
      b: { "" }
      """#,
        origin: "TrailingClosuresTests.testTrailingClosures2",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTrailingClosures3#1",
        source: #"""
      foo { 42 } b: { "" }
      """#,
        origin: "TrailingClosuresTests.testTrailingClosures3",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTrailingClosures4#1",
        source: """
      func when<T>(_ condition: @autoclosure () -> Bool,
                   `then` trueBranch: () -> T,
                   `else` falseBranch: () -> T) -> T {
        return condition() ? trueBranch() : falseBranch()
      }
      """,
        origin: "TrailingClosuresTests.testTrailingClosures4",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTrailingClosures5#1",
        source: """
      let _ = when (2 < 3) { 3 } else: { 4 }
      """,
        origin: "TrailingClosuresTests.testTrailingClosures5",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTrailingClosures6#1",
        source: """
      struct S {
        static func foo(a: Int = 42, b: (inout Int) -> Void) -> S {
          return S()
        }
        static func foo(a: Int = 42, ab: () -> Void, b: (inout Int) -> Void) -> S {
          return S()
        }
        subscript(v v: () -> Int) -> Int {
          get { return v() }
        }
        subscript(u u: () -> Int, v v: () -> Int) -> Int {
          get { return u() + v() }
        }
        subscript(cond: Bool, v v: () -> Int) -> Int {
          get { return cond ? 0 : v() }
        }
        subscript(cond: Bool, u u: () -> Int, v v: () -> Int) -> Int {
          get { return cond ? u() : v() }
        }
      }
      """,
        origin: "TrailingClosuresTests.testTrailingClosures6",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTrailingClosures7#1",
        source: """
      let _: S = .foo {
        $0 = $0 + 1
      }
      """,
        origin: "TrailingClosuresTests.testTrailingClosures7",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTrailingClosures8#1",
        source: """
      let _: S = .foo {} b: { $0 = $0 + 1 }
      """,
        origin: "TrailingClosuresTests.testTrailingClosures8",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTrailingClosures9#1",
        source: """
      func bar(_ s: S) {
        _ = s[] {
          42
        }
        _ = s[] {
          21
        } v: {
          42
        }
        _ = s[true] {
          42
        }
        _ = s[true] {
          21
        } v: {
          42
        }
      }
      """,
        origin: "TrailingClosuresTests.testTrailingClosures9",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTrailingClosures10#1",
        source: """
      func multiple_trailing_with_defaults(
        duration: Int,
        animations: (() -> Void)? = nil,
        completion: (() -> Void)? = nil) {}
      """,
        origin: "TrailingClosuresTests.testTrailingClosures10",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTrailingClosures11#1",
        source: """
      multiple_trailing_with_defaults(duration: 42) {}
      """,
        origin: "TrailingClosuresTests.testTrailingClosures11",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTrailingClosures12#1",
        source: """
      multiple_trailing_with_defaults(duration: 42) {} completion: {}
      """,
        origin: "TrailingClosuresTests.testTrailingClosures12",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTrailingClosures13a#1",
        source: """
      fn {} g: {}
      fn {} _: {}
      multiple {} _: { }
      mixed_args_1 {} _: {}
      mixed_args_1 {} a: {}  //  {{none}}
      mixed_args_2 {} a: {} _: {}
      mixed_args_2 {} _: {} //  {{none}}
      mixed_args_2 {} _: {} _: {} //  {{none}}
      """,
        origin: "TrailingClosuresTests.testTrailingClosures13a",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTrailingClosures15#1",
        source: """
      func f() -> Int { 42 }
      """,
        origin: "TrailingClosuresTests.testTrailingClosures15",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTrailingClosures16#1",
        source: """
      // This should be interpreted as a trailing closure, instead of being
      // interpreted as a computed property with undesired initial value.
      struct TrickyTest {
          var x : Int = f () {
              3
          }
      }
      """,
        origin: "TrailingClosuresTests.testTrailingClosures16",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTrailingSemi1#1",
        source: """
      struct S {
        var a : Int ;
        func b () {};
        static func c () {};
      }
      """,
        origin: "TrailingSemiTests.testTrailingSemi1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTrailingSemi5#1",
        source: """
      protocol P {
        var a : Int { get };
        func b ();
        static func c ();
      }
      """,
        origin: "TrailingSemiTests.testTrailingSemi5",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTry1#1",
        source: """
      // Intentionally has lower precedence than assignments and ?:
      infix operator %%%% : LowPrecedence
      precedencegroup LowPrecedence {
        associativity: none
        lowerThan: AssignmentPrecedence
      }
      func %%%%<T, U>(x: T, y: U) -> Int { return 0 }
      """,
        origin: "TryTests.testTry1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTry2#1",
        source: """
      // Intentionally has lower precedence between assignments and ?:
      infix operator %%% : MiddlingPrecedence
      precedencegroup MiddlingPrecedence {
        associativity: none
        higherThan: AssignmentPrecedence
        lowerThan: TernaryPrecedence
      }
      func %%%<T, U>(x: T, y: U) -> Int { return 1 }
      """,
        origin: "TryTests.testTry2",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTry3#1",
        source: """
      func foo() throws -> Int { return 0 }
      func bar() throws -> Int { return 0 }
      """,
        origin: "TryTests.testTry3",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTry4#1",
        source: """
      var x = try foo() + bar()
      x = try foo() + bar()
      x += try foo() + bar()
      x += try foo() %%%% bar()
      x += try foo() %%% bar()
      x = foo() + try bar()
      """,
        origin: "TryTests.testTry4",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTry5#1",
        source: """
      var y = true ? try foo() : try bar() + 0
      var z = true ? try foo() : try bar() %%% 0
      """,
        origin: "TryTests.testTry5",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTry6#1",
        source: """
      var a = try! foo() + bar()
      a = try! foo() + bar()
      a += try! foo() + bar()
      a += try! foo() %%%% bar()
      a += try! foo() %%% bar()
      a = foo() + try! bar()
      """,
        origin: "TryTests.testTry6",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTry7#1",
        source: """
      var b = true ? try! foo() : try! bar() + 0
      var c = true ? try! foo() : try! bar() %%% 0
      """,
        origin: "TryTests.testTry7",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTry8#1",
        source: """
      infix operator ?+= : AssignmentPrecedence
      func ?+=(lhs: inout Int?, rhs: Int?) {
        lhs = lhs! + rhs!
      }
      """,
        origin: "TryTests.testTry8",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTry9#1",
        source: """
      var i = try? foo() + bar()
      let _: Double = i
      i = try? foo() + bar()
      i ?+= try? foo() + bar()
      i ?+= try? foo() %%%% bar()
      i ?+= try? foo() %%% bar()
      _ = foo() == try? bar()
      _ = (try? foo()) == bar()
      _ = foo() == (try? bar())
      _ = (try? foo()) == (try? bar())
      """,
        origin: "TryTests.testTry9",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTry10#1",
        source: """
      let j = true ? try? foo() : try? bar() + 0
      let k = true ? try? foo() : try? bar() %%% 0
      """,
        origin: "TryTests.testTry10",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTry13#1",
        source: #"""
      // Test operators.
      func *(a : String, b : String) throws -> Int { return 42 }
      let _ = "foo"
              *
              "bar"
      let _ = try! "foo"*"bar"
      let _ = try? "foo"*"bar"
      let _ = (try? "foo"*"bar") ?? 0
      """#,
        origin: "TryTests.testTry13",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTry14#1",
        source: """
      // <rdar://problem/21414023> Assertion failure when compiling function that takes throwing functions and rethrows
      func rethrowsDispatchError(handleError: ((Error) throws -> ()), body: () throws -> ()) rethrows {
        do {
          body()
        } catch {
        }
      }
      """,
        origin: "TryTests.testTry14",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTry15#1",
        source: """
      // <rdar://problem/21432429> Calling rethrows from rethrows crashes Swift compiler
      struct r21432429 {
        func x(_ f: () throws -> ()) rethrows {}
        func y(_ f: () throws -> ()) rethrows {
          x(f)
        }
      }
      """,
        origin: "TryTests.testTry15",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTry16#1",
        source: """
      // <rdar://problem/21427855> Swift 2: Omitting try from call to throwing closure in rethrowing function crashes compiler
      func callThrowingClosureWithoutTry(closure: (Int) throws -> Int) rethrows {
        closure(0)
      }
      """,
        origin: "TryTests.testTry16",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTry17#1",
        source: """
      func producesOptional() throws -> Int? { return nil }
      let _: String = try? producesOptional()
      """,
        origin: "TryTests.testTry17",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTry18#1",
        source: """
      let _ = (try? foo())!!
      """,
        origin: "TryTests.testTry18",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTry19#1",
        source: """
      func producesDoubleOptional() throws -> Int?? { return 3 }
      let _: String = try? producesDoubleOptional()
      """,
        origin: "TryTests.testTry19",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTry20#1",
        source: """
      func maybeThrow() throws {}
      try maybeThrow() // okay
      try! maybeThrow() // okay
      try? maybeThrow() // okay since return type of maybeThrow is Void
      _ = try? maybeThrow() // okay
      """,
        origin: "TryTests.testTry20",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTry21#1",
        source: """
      let _: () -> Void = { try! maybeThrow() } // okay
      let _: () -> Void = { try? maybeThrow() } // okay since return type of maybeThrow is Void
      """,
        origin: "TryTests.testTry21",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTry22#1",
        source: """
      if try? maybeThrow() {
      }
      let _: Int = try? foo()
      """,
        origin: "TryTests.testTry22",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTry23#1",
        source: """
      class X {}
      func test(_: X) {}
      func producesObject() throws -> AnyObject { return X() }
      test(try producesObject())
      """,
        origin: "TryTests.testTry23",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTry24#1",
        source: #"""
      _ = "a\(try maybeThrow())b"
      _ = try "a\(maybeThrow())b"
      _ = "a\(maybeThrow())"
      """#,
        origin: "TryTests.testTry24",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTry25#1",
        source: """
      extension DefaultStringInterpolation {
        mutating func appendInterpolation() throws {}
      }
      """,
        origin: "TryTests.testTry25",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTry26#1",
        source: #"""
      _ = try "a\()b"
      _ = "a\()b"
      _ = try "\() \(1)"
      """#,
        origin: "TryTests.testTry26",
        syntaxVersion: "603.0.1",
        compilerRejects: "missing argument for parameter #1 in call"
    ),
    SwiftSnippet(
        label: "testTry27#1",
        source: """
      func testGenericOptionalTry<T>(_ call: () throws -> T ) {
        let _: String = try? call()
      }
      """,
        origin: "TryTests.testTry27",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTry28#1",
        source: """
      func genericOptionalTry<T>(_ call: () throws -> T ) -> T? {
        let x = try? call() // no error expected
        return x
      }
      """,
        origin: "TryTests.testTry28",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTry29#1",
        source: """
      // Test with a non-optional type
      let _: String = genericOptionalTry({ () throws -> Int in return 3 })
      """,
        origin: "TryTests.testTry29",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTry30#1",
        source: """
      // Test with an optional type
      let _: String = genericOptionalTry({ () throws -> Int? in return nil })
      """,
        origin: "TryTests.testTry30",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTry31#1",
        source: """
      func produceAny() throws -> Any {
        return 3
      }
      """,
        origin: "TryTests.testTry31",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTry32#1",
        source: """
      let _: Int? = try? produceAny() as? Int
      let _: Int?? = (try? produceAny()) as? Int // good
      let _: String = try? produceAny() as? Int
      let _: String = (try? produceAny()) as? Int
      """,
        origin: "TryTests.testTry32",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTry33#1",
        source: """
      struct ThingProducer {
        func produceInt() throws -> Int { return 3 }
        func produceIntNoThrowing() -> Int { return 3 }
        func produceAny() throws -> Any { return 3 }
        func produceOptionalAny() throws -> Any? { return 3 }
        func produceDoubleOptionalInt() throws -> Int?? { return 3 }
      }
      """,
        origin: "TryTests.testTry33",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTry34#1",
        source: """
      let optProducer: ThingProducer? = ThingProducer()
      let _: Int? = try? optProducer?.produceInt()
      let _: Int = try? optProducer?.produceInt()
      let _: String = try? optProducer?.produceInt()
      let _: Int?? = try? optProducer?.produceInt() // good
      """,
        origin: "TryTests.testTry34",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTry35#1",
        source: """
      let _: Int? = try? optProducer?.produceIntNoThrowing()
      let _: Int?? = try? optProducer?.produceIntNoThrowing()
      """,
        origin: "TryTests.testTry35",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTry36#1",
        source: """
      let _: Int? = (try? optProducer?.produceAny()) as? Int // good
      let _: Int? = try? optProducer?.produceAny() as? Int
      let _: Int?? = try? optProducer?.produceAny() as? Int // good
      let _: String = try? optProducer?.produceAny() as? Int
      """,
        origin: "TryTests.testTry36",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTry37#1",
        source: """
      let _: String = try? optProducer?.produceDoubleOptionalInt()
      """,
        origin: "TryTests.testTry37",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTry38#1",
        source: """
      let producer = ThingProducer()
      """,
        origin: "TryTests.testTry38",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTry39#1",
        source: """
      let _: Int = try? producer.produceDoubleOptionalInt()
      let _: Int? = try? producer.produceDoubleOptionalInt()
      let _: Int?? = try? producer.produceDoubleOptionalInt()
      let _: Int??? = try? producer.produceDoubleOptionalInt() // good
      let _: String = try? producer.produceDoubleOptionalInt()
      """,
        origin: "TryTests.testTry39",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTry40#1",
        source: """
      // rdar://problem/46742002
      protocol Dummy : class {}
      """,
        origin: "TryTests.testTry40",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTry41#1",
        source: """
      class F<T> {
        func wait() throws -> T { fatalError() }
      }
      """,
        origin: "TryTests.testTry41",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTry42#1",
        source: """
      func bar(_ a: F<Dummy>, _ b: F<Dummy>) {
        _ = (try? a.wait()) === (try? b.wait())
      }
      """,
        origin: "TryTests.testTry42",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypeExpr3#1",
        source: """
      struct Foo {
        struct Bar {
          init() {}
          static var prop: Int = 0
          static func meth() {}
          func instMeth() {}
        }
        init() {}
        static var prop: Int = 0
        static func meth() {}
        func instMeth() {}
      }
      """,
        origin: "TypeExprTests.testTypeExpr3",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypeExpr4#1",
        source: """
      protocol Zim {
        associatedtype Zang
        init()
        static func meth() {}
        func instMeth() {}
      }
      """,
        origin: "TypeExprTests.testTypeExpr4",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypeExpr5#1",
        source: """
      protocol Bad {
        init() {}
      }
      """,
        origin: "TypeExprTests.testTypeExpr5",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypeExpr6#1",
        source: """
      struct Gen<T> {
        struct Bar {
          init() {}
          static var prop: Int { return 0 }
          static func meth() {}
          func instMeth() {}
        }
        init() {}
        static var prop: Int { return 0 }
        static func meth() {}
        func instMeth() {}
      }
      """,
        origin: "TypeExprTests.testTypeExpr6",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypeExpr7#1",
        source: """
      func unqualifiedType() {
        _ = Foo.self
        _ = Foo.self
        _ = Foo()
        _ = Foo.prop
        _ = Foo.meth
        let _ : () = Foo.meth()
        _ = Foo.instMeth
        _ = Foo
        _ = Foo.dynamicType
        _ = Bad
      }
      """,
        origin: "TypeExprTests.testTypeExpr7",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypeExpr8#1",
        source: """
      func qualifiedType() {
        _ = Foo.Bar.self
        let _ : Foo.Bar.Type = Foo.Bar.self
        let _ : Foo.Protocol = Foo.self
        _ = Foo.Bar()
        _ = Foo.Bar.prop
        _ = Foo.Bar.meth
        let _ : () = Foo.Bar.meth()
        _ = Foo.Bar.instMeth
        _ = Foo.Bar
        _ = Foo.Bar.dynamicType
      }
      """,
        origin: "TypeExprTests.testTypeExpr8",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testTypeExpr8#2", source: "(X).Y.self", origin: "TypeExprTests.testTypeExpr8", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testTypeExpr8#3", source: "(X.Y).Z.self", origin: "TypeExprTests.testTypeExpr8", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testTypeExpr8#4", source: "((X).Y).Z.self", origin: "TypeExprTests.testTypeExpr8", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testTypeExpr9#1",
        source: """
      // We allow '.Type' in expr context
      func metaType() {
        let _ = Foo.Type.self
        let _ = Foo.Type.self
        let _ = Foo.Type
        let _ = type(of: Foo.Type)
      }
      """,
        origin: "TypeExprTests.testTypeExpr9",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypeExpr10#1",
        source: """
      func genType() {
        _ = Gen<Foo>.self
        _ = Gen<Foo>()
        _ = Gen<Foo>.prop
        _ = Gen<Foo>.meth
        let _ : () = Gen<Foo>.meth()
        _ = Gen<Foo>.instMeth
        _ = Gen<Foo>

        _ = X?.self
        _ = [X].self
        _ = [X : Y].self
      }
      """,
        origin: "TypeExprTests.testTypeExpr10",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testTypeExpr10#2", source: "X?.self", origin: "TypeExprTests.testTypeExpr10", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testTypeExpr10#3", source: "[X].self", origin: "TypeExprTests.testTypeExpr10", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testTypeExpr10#4", source: "[X : Y].self", origin: "TypeExprTests.testTypeExpr10", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testTypeExpr11#1",
        source: """
      func genQualifiedType() {
        _ = Gen<Foo>.Bar.self
        _ = Gen<Foo>.Bar()
        _ = Gen<Foo>.Bar.prop
        _ = Gen<Foo>.Bar.meth
        let _ : () = Gen<Foo>.Bar.meth()
        _ = Gen<Foo>.Bar.instMeth
        _ = Gen<Foo>.Bar
        _ = Gen<Foo>.Bar.dynamicType

        _ = (G<X>).Y.self
        _ = X?.Y.self
        _ = (X)?.Y.self
        _ = (X?).Y.self
        _ = [X].Y.self
        _ = [X : Y].Z.self
      }
      """,
        origin: "TypeExprTests.testTypeExpr11",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testTypeExpr11#2", source: "(G<X>).Y.self", origin: "TypeExprTests.testTypeExpr11", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testTypeExpr11#3", source: "X?.Y.self", origin: "TypeExprTests.testTypeExpr11", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testTypeExpr11#4", source: "(X)?.Y.self", origin: "TypeExprTests.testTypeExpr11", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testTypeExpr11#5", source: "(X?).Y.self", origin: "TypeExprTests.testTypeExpr11", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testTypeExpr11#6", source: "[X].Y.self", origin: "TypeExprTests.testTypeExpr11", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testTypeExpr11#7", source: "[X : Y].Z.self", origin: "TypeExprTests.testTypeExpr11", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testTypeExpr12#1",
        source: """
      func typeOfShadowing() {
        // Try to shadow type(of:)
        func type<T>(of t: T.Type, flag: Bool) -> T.Type {
          return t
        }
        func type<T, U>(of t: T.Type, _ : U) -> T.Type {
          return t
        }
        func type<T>(_ t: T.Type) -> T.Type {
          return t
        }
        func type<T>(fo t: T.Type) -> T.Type {
          return t
        }
        _ = type(of: Gen<Foo>.Bar)
        _ = type(Gen<Foo>.Bar)
        _ = type(of: Gen<Foo>.Bar.self, flag: false) // No error here.
        _ = type(fo: Foo.Bar.self) // No error here.
        _ = type(of: Foo.Bar.self, [1, 2, 3]) // No error here.
      }
      """,
        origin: "TypeExprTests.testTypeExpr12",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypeExpr13#1",
        source: """
      func archetype<T: Zim>(_: T) {
        _ = T.self
        _ = T()
        _ = T.meth
        let _ : () = T.meth()
        _ = T
      }
      """,
        origin: "TypeExprTests.testTypeExpr13",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypeExpr14#1",
        source: """
      func assocType<T: Zim>(_: T) where T.Zang: Zim {
        _ = T.Zang.self
        _ = T.Zang()
        _ = T.Zang.meth
        let _ : () = T.Zang.meth()
        _ = T.Zang
      }
      """,
        origin: "TypeExprTests.testTypeExpr14",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypeExpr15#1",
        source: """
      class B {
        class func baseMethod() {}
      }
      class D: B {
        class func derivedMethod() {}
      }
      """,
        origin: "TypeExprTests.testTypeExpr15",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypeExpr16#1",
        source: """
      func derivedType() {
        let _: B.Type = D.self
        _ = D.baseMethod
        let _ : () = D.baseMethod()
        let _: D.Type = D.self
        _ = D.derivedMethod
        let _ : () = D.derivedMethod()
        let _: B.Type = D
        let _: D.Type = D
      }
      """,
        origin: "TypeExprTests.testTypeExpr16",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypeExpr17#1",
        source: #"""
      // Referencing a nonexistent member or constructor should not trigger errors
      // about the type expression.
      func nonexistentMember() {
        let cons = Foo("this constructor does not exist")
        let prop = Foo.nonexistent
        let meth = Foo.nonexistent()
      }
      """#,
        origin: "TypeExprTests.testTypeExpr17",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypeExpr18#1",
        source: """
      protocol P {}
      """,
        origin: "TypeExprTests.testTypeExpr18",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypeExpr19#1",
        source: """
      func meta_metatypes() {
        let _: P.Protocol = P.self
        _ = P.Type.self
        _ = P.Protocol.self
        _ = P.Protocol.Protocol.self
        _ = P.Protocol.Type.self
        _ = B.Type.self
      }
      """,
        origin: "TypeExprTests.testTypeExpr19",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypeExpr20#1",
        source: """
      class E {
        private init() {}
      }
      """,
        origin: "TypeExprTests.testTypeExpr20",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypeExpr21#1",
        source: """
      func inAccessibleInit() {
        _ = E
      }
      """,
        origin: "TypeExprTests.testTypeExpr21",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypeExpr22#1",
        source: """
      enum F: Int {
        case A, B
      }
      """,
        origin: "TypeExprTests.testTypeExpr22",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypeExpr23#1",
        source: """
      struct G {
        var x: Int
      }
      """,
        origin: "TypeExprTests.testTypeExpr23",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypeExpr24#1",
        source: """
      func implicitInit() {
        _ = F
        _ = G
      }
      """,
        origin: "TypeExprTests.testTypeExpr24",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypeExpr25a#1",
        source: """
      _ = [(Int) -> Int]()
      """,
        origin: "TypeExprTests.testTypeExpr25a",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypeExpr25b#1",
        source: """
      _ = [(Int, Int) -> Int]()
      """,
        origin: "TypeExprTests.testTypeExpr25b",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypeExpr25c#1",
        source: """
      _ = [(x: Int, y: Int) -> Int]()
      """,
        origin: "TypeExprTests.testTypeExpr25c",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypeExpr25d#1",
        source: """
      // Make sure associativity is correct
      let a = [(Int) -> (Int) -> Int]()
      """,
        origin: "TypeExprTests.testTypeExpr25d",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypeExpr25e#1",
        source: """
      let b: Int = a[0](5)(4)
      """,
        origin: "TypeExprTests.testTypeExpr25e",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypeExpr25f#1",
        source: """
      _ = [String: (Int) -> Int]()
      """,
        origin: "TypeExprTests.testTypeExpr25f",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypeExpr25g#1",
        source: """
      _ = [String: (Int, Int) -> Int]()
      """,
        origin: "TypeExprTests.testTypeExpr25g",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypeExpr25h#1",
        source: """
      _ = [1 -> Int]()
      """,
        origin: "TypeExprTests.testTypeExpr25h",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypeExpr25i#1",
        source: """
      _ = [Int -> 1]()
      """,
        origin: "TypeExprTests.testTypeExpr25i",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypeExpr25j#1",
        source: """
      // Should parse () as void type when before or after arrow
      _ = [() -> Int]()
      """,
        origin: "TypeExprTests.testTypeExpr25j",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypeExpr25k#1",
        source: """
      _ = [(Int) -> ()]()
      """,
        origin: "TypeExprTests.testTypeExpr25k",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypeExpr25l#1",
        source: """
      _ = 2 + () -> Int
      """,
        origin: "TypeExprTests.testTypeExpr25l",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypeExpr25m#1",
        source: """
      _ = () -> (Int, Int).2
      """,
        origin: "TypeExprTests.testTypeExpr25m",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypeExpr25n#1",
        source: """
      _ = (Int) -> Int
      """,
        origin: "TypeExprTests.testTypeExpr25n",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypeExpr25o#1",
        source: """
      _ = @convention(c) () -> Int
      """,
        origin: "TypeExprTests.testTypeExpr25o",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypeExpr25p#1",
        source: """
      _ = 1 + (@convention(c) () -> Int).self
      """,
        origin: "TypeExprTests.testTypeExpr25p",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypeExpr25q#1",
        source: """
      _ = (@autoclosure () -> Int) -> (Int, Int).2
      """,
        origin: "TypeExprTests.testTypeExpr25q",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypeExpr25r#1",
        source: """
      _ = ((@autoclosure () -> Int) -> (Int, Int)).1
      """,
        origin: "TypeExprTests.testTypeExpr25r",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypeExpr25s#1",
        source: """
      _ = ((inout Int) -> Void).self
      """,
        origin: "TypeExprTests.testTypeExpr25s",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypeExpr25t#1",
        source: """
      _ = [(Int) throws -> Int]()
      """,
        origin: "TypeExprTests.testTypeExpr25t",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypeExpr25u#1",
        source: """
      _ = [@convention(swift) (Int) throws -> Int]().count
      """,
        origin: "TypeExprTests.testTypeExpr25u",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypeExpr25v#1",
        source: """
      _ = [(inout Int) throws -> (inout () -> Void) -> Void]().count
      """,
        origin: "TypeExprTests.testTypeExpr25v",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypeExpr25w#1",
        source: """
      _ = [String: (@autoclosure (Int) -> Int32) -> Void]().keys
      """,
        origin: "TypeExprTests.testTypeExpr25w",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testCompositionTypeExpr#1", source: "P & Q", origin: "TypeExprTests.testCompositionTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testCompositionTypeExpr#2", source: "P & Q.self", origin: "TypeExprTests.testCompositionTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testCompositionTypeExpr#3", source: "any P & Q", origin: "TypeExprTests.testCompositionTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testCompositionTypeExpr#4", source: "(P & Q).self", origin: "TypeExprTests.testCompositionTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testCompositionTypeExpr#5", source: "((P) & (Q)).self", origin: "TypeExprTests.testCompositionTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testCompositionTypeExpr#6", source: "(A.B & C.D).self", origin: "TypeExprTests.testCompositionTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testCompositionTypeExpr#7", source: "((A).B & (C).D).self", origin: "TypeExprTests.testCompositionTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testCompositionTypeExpr#8", source: "(G<X> & G<Y>).self", origin: "TypeExprTests.testCompositionTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testCompositionTypeExpr#9", source: "(X? & Y?).self", origin: "TypeExprTests.testCompositionTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testCompositionTypeExpr#10", source: "([X] & [Y]).self", origin: "TypeExprTests.testCompositionTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testCompositionTypeExpr#11", source: "([A : B] & [C : D]).self", origin: "TypeExprTests.testCompositionTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testCompositionTypeExpr#12", source: "(G<A>.B & G<C>.D).self", origin: "TypeExprTests.testCompositionTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testCompositionTypeExpr#13", source: "(A?.B & C?.D).self", origin: "TypeExprTests.testCompositionTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testCompositionTypeExpr#14", source: "([A].B & [A].B).self", origin: "TypeExprTests.testCompositionTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testCompositionTypeExpr#15", source: "([A : B].C & [D : E].F).self", origin: "TypeExprTests.testCompositionTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testCompositionTypeExpr#16", source: "(X.Type & Y.Type).self", origin: "TypeExprTests.testCompositionTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testCompositionTypeExpr#17", source: "(X.Protocol & Y.Protocol).self", origin: "TypeExprTests.testCompositionTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testCompositionTypeExpr#18", source: "((A, B) & (C, D)).self", origin: "TypeExprTests.testCompositionTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testTupleTypeExpr#1", source: "(X).self", origin: "TypeExprTests.testTupleTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testTupleTypeExpr#2", source: "(X, Y)", origin: "TypeExprTests.testTupleTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testTupleTypeExpr#3", source: "(X, Y).self", origin: "TypeExprTests.testTupleTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testTupleTypeExpr#4", source: "((X), (Y)).self", origin: "TypeExprTests.testTupleTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testTupleTypeExpr#5", source: "(A.B, C.D).self", origin: "TypeExprTests.testTupleTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testTupleTypeExpr#6", source: "((A).B, (C).D).self", origin: "TypeExprTests.testTupleTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testTupleTypeExpr#7", source: "(G<X>, G<Y>).self", origin: "TypeExprTests.testTupleTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testTupleTypeExpr#8", source: "(X?, Y?).self", origin: "TypeExprTests.testTupleTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testTupleTypeExpr#9", source: "([X], [Y]).self", origin: "TypeExprTests.testTupleTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testTupleTypeExpr#10", source: "([A : B], [C : D]).self", origin: "TypeExprTests.testTupleTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testTupleTypeExpr#11", source: "(G<A>.B, G<C>.D).self", origin: "TypeExprTests.testTupleTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testTupleTypeExpr#12", source: "(A?.B, C?.D).self", origin: "TypeExprTests.testTupleTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testTupleTypeExpr#13", source: "([A].B, [C].D).self", origin: "TypeExprTests.testTupleTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testTupleTypeExpr#14", source: "([A : B].C, [D : E].F).self", origin: "TypeExprTests.testTupleTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testTupleTypeExpr#15", source: "(X.Type, Y.Type).self", origin: "TypeExprTests.testTupleTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testTupleTypeExpr#16", source: "(X.Protocol, Y.Protocol).self", origin: "TypeExprTests.testTupleTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testTupleTypeExpr#17", source: "(P & Q, P & Q).self", origin: "TypeExprTests.testTupleTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testTupleTypeExpr#18",
        source: """
      (
        (G<X>.Y) -> (P) & X?.Y, (X.Y, [X : Y?].Type), [(G<X>).Y], [A.B.C].D
      ).self
      """,
        origin: "TypeExprTests.testTupleTypeExpr",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testFunctionTypeExpr#1", source: "X -> Y", origin: "TypeExprTests.testFunctionTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testFunctionTypeExpr#2", source: "(X) -> Y", origin: "TypeExprTests.testFunctionTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testFunctionTypeExpr#3", source: "(X) -> Y -> Z", origin: "TypeExprTests.testFunctionTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testFunctionTypeExpr#4", source: "P & Q -> X", origin: "TypeExprTests.testFunctionTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testFunctionTypeExpr#5", source: "A & B -> C & D -> X", origin: "TypeExprTests.testFunctionTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testFunctionTypeExpr#6", source: "(X -> Y).self", origin: "TypeExprTests.testFunctionTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testFunctionTypeExpr#7", source: "(A & B -> C & D).self", origin: "TypeExprTests.testFunctionTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testFunctionTypeExpr#8", source: "((X) -> Y).self", origin: "TypeExprTests.testFunctionTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testFunctionTypeExpr#9", source: "(((X)) -> (Y)).self", origin: "TypeExprTests.testFunctionTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testFunctionTypeExpr#10", source: "((A.B) -> C.D).self", origin: "TypeExprTests.testFunctionTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testFunctionTypeExpr#11", source: "(((A).B) -> (C).D).self", origin: "TypeExprTests.testFunctionTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testFunctionTypeExpr#12", source: "((G<X>) -> G<Y>).self", origin: "TypeExprTests.testFunctionTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testFunctionTypeExpr#13", source: "((X?) -> Y?).self", origin: "TypeExprTests.testFunctionTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testFunctionTypeExpr#14", source: "(([X]) -> [Y]).self", origin: "TypeExprTests.testFunctionTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testFunctionTypeExpr#15", source: "(([A : B]) -> [C : D]).self", origin: "TypeExprTests.testFunctionTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testFunctionTypeExpr#16", source: "((Gen<Foo>.Bar) -> Gen<Foo>.Bar).self", origin: "TypeExprTests.testFunctionTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testFunctionTypeExpr#17", source: "((Foo?.Bar) -> Foo?.Bar).self", origin: "TypeExprTests.testFunctionTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testFunctionTypeExpr#18", source: "(([Foo].Element) -> [Foo].Element).self", origin: "TypeExprTests.testFunctionTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testFunctionTypeExpr#19", source: "(([Int : Foo].Element) -> [Int : Foo].Element).self", origin: "TypeExprTests.testFunctionTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testFunctionTypeExpr#20", source: "((X.Type) -> Y.Type).self", origin: "TypeExprTests.testFunctionTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testFunctionTypeExpr#21", source: "((X.Protocol) -> Y.Protocol).self", origin: "TypeExprTests.testFunctionTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testFunctionTypeExpr#22", source: "(() -> X & Y).self", origin: "TypeExprTests.testFunctionTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testFunctionTypeExpr#23", source: "((A & B) -> C & D).self", origin: "TypeExprTests.testFunctionTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testFunctionTypeExpr#24", source: "((A & B) -> (C & D) -> E & Any).self", origin: "TypeExprTests.testFunctionTypeExpr", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testFunctionTypeExpr#25",
        source: """
      (
        ((P) & X?.Y, G<X>.Y, (X, [A : B?].Type)) -> ([(X).Y]) -> [X].Y
      ).self
      """,
        origin: "TypeExprTests.testFunctionTypeExpr",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypeExpr27#1",
        source: """
      func complexSequence() {
        // (assign_expr
        //   (discard_assignment_expr)
        //   (try_expr
        //     (type_expr typerepr='P1 & P2 throws -> P3 & P1')))
        _ = try P1 & P2 throws -> P3 & P1
      }
      """,
        origin: "TypeExprTests.testTypeExpr27",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypeExpr29#1",
        source: """
      func takesOneArg<T>(_: T.Type) {}
      func takesTwoArgs<T>(_: T.Type, _: Int) {}
      """,
        origin: "TypeExprTests.testTypeExpr29",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypeExpr30#1",
        source: """
      func testMissingSelf() {
        // None of these were not caught in Swift 3.
        // See test/Compatibility/type_expr.swift.
        takesOneArg(Int)
        takesOneArg(Swift.Int)
        takesTwoArgs(Int, 0)
        takesTwoArgs(Swift.Int, 0)
        Swift.Int
        _ = Swift.Int
      }
      """,
        origin: "TypeExprTests.testTypeExpr30",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypealias2a#1",
        source: """
      typealias IntPair = (Int, Int)
      """,
        origin: "TypealiasTests.testTypealias2a",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypealias2b#1",
        source: """
      typealias IntTriple = (Int, Int, Int)
      """,
        origin: "TypealiasTests.testTypealias2b",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypealias2c#1",
        source: """
      typealias FiveInts = (IntPair, IntTriple)
      """,
        origin: "TypealiasTests.testTypealias2c",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypealias2d#1",
        source: """
      var fiveInts : FiveInts = ((4,2), (1,2,3))
      """,
        origin: "TypealiasTests.testTypealias2d",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testUnclosedStringInterpolation1#1",
        source: #"""
      let mid = "pete"
      """#,
        origin: "UnclosedStringInterpolationTests.testUnclosedStringInterpolation1",
        syntaxVersion: "603.0.1"
    ),
]

// MARK: - Test Suite

extension SwiftSyntax603Tests {

@Suite("Translated")
struct TranslatedSyntaxTests {

    @Test("SwiftSyntax accepts", .tags(.swiftSyntaxReference), arguments: translatedSnippets)
    func swiftSyntaxAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let parsed = Parser.parse(source: snippet.source)
        #expect(!parsed.hasError, "SwiftSyntax parse error for: \(snippet.source)")
    }

    @Test("Advent accepts", arguments: translatedSnippets)
    func adventAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let result = try adventParse(snippet)
        #expect(result != nil, "Advent failed to parse: \(snippet.source)")
    }

    @Test("no residual ambiguity", arguments: translatedSnippets)
    func unambiguous(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        guard let result = try adventParse(snippet) else {
            Issue.record("Advent failed to parse: \(snippet.source)")
            return
        }
        #expect(result.isUnambiguous,
                "Residual ambiguity in '\(snippet.diagnosticID)': \(result.builder.diagnostics)")
    }

    @Test("trees match", arguments: translatedSnippets)
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

let translated604Snippets: [SwiftSnippet] = [
    SwiftSnippet(
        label: "testAlwaysEmitConformanceMetadataAttr#1",
        source: """
      @_alwaysEmitConformanceMetadata
      protocol Test {}
      """,
        origin: "AlwaysEmitConformanceMetadataAttrTests.testAlwaysEmitConformanceMetadataAttr",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAsyncSyntax1#1",
        source: """
      func asyncGlobal1() async { }
      func asyncGlobal2() async throws { }
      """,
        origin: "AsyncSyntaxTests.testAsyncSyntax1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAsyncSyntax2#1",
        source: """
      typealias AsyncFunc1 = () async -> ()
      typealias AsyncFunc2 = () async throws -> ()
      typealias AsyncFunc3 = (_ a: Bool, _ b: Bool) async throws -> ()
      """,
        origin: "AsyncSyntaxTests.testAsyncSyntax2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAsyncSyntax3#1",
        source: """
      func testTypeExprs() {
        let _ = [() async -> ()]()
        let _ = [() async throws -> ()]()
      }
      """,
        origin: "AsyncSyntaxTests.testAsyncSyntax3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAsyncSyntax4#1",
        source: """
      func testAwaitOperator() async {
        let _ = await asyncGlobal1()
      }
      """,
        origin: "AsyncSyntaxTests.testAsyncSyntax4",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAsyncSyntax5#1",
        source: """
      func testAsyncClosure() {
        let _ = { () async in 5 }
        let _ = { () throws in 5 }
        let _ = { () async throws in 5 }
      }
      """,
        origin: "AsyncSyntaxTests.testAsyncSyntax5",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAsyncSyntax6#1",
        source: """
      func testAwait() async {
        let _ = await asyncGlobal1()
      }
      """,
        origin: "AsyncSyntaxTests.testAsyncSyntax6",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAsync1#1",
        source: """
      // Parsing function declarations with 'async'
      func asyncGlobal1() async { }
      func asyncGlobal2() async throws { }
      """,
        origin: "AsyncTests.testAsync1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAsync10a#1",
        source: """
      typealias AsyncFunc1 = () async -> ()
      """,
        origin: "AsyncTests.testAsync10a",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAsync10b#1",
        source: """
      typealias AsyncFunc2 = () async throws -> ()
      """,
        origin: "AsyncTests.testAsync10b",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAsync11a#1",
        source: """
      let _ = [() async -> ()]()
      """,
        origin: "AsyncTests.testAsync11a",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAsync11b#1",
        source: """
      let _ = [() async throws -> ()]()
      """,
        origin: "AsyncTests.testAsync11b",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAsync12#1",
        source: """
      // Parsing await syntax.
      struct MyFuture {
        func await() -> Int { 0 }
      }
      """,
        origin: "AsyncTests.testAsync12",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAsync13#1",
        source: """
      func testAwaitExpr() async {
        let _ = await asyncGlobal1()
        let myFuture = MyFuture()
        let _ = myFuture.await()
      }
      """,
        origin: "AsyncTests.testAsync13",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAsync14#1",
        source: """
      func getIntSomeday() async -> Int { 5 }
      """,
        origin: "AsyncTests.testAsync14",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAsync15#1",
        source: """
      func testAsyncLet() async {
        async let x = await getIntSomeday()
        _ = await x
      }
      """,
        origin: "AsyncTests.testAsync15",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAsync16#1",
        source: """
      async func asyncIncorrectly() { }
      """,
        origin: "AsyncTests.testAsync16",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAvailabilityQuery1#1",
        source: """
      if #available(OSX 10.51, *) {
      }
      """,
        origin: "AvailabilityQueryTests.testAvailabilityQuery1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAvailabilityQuery11#1",
        source: """
      if #available(OSX) {
      }
      """,
        origin: "AvailabilityQueryTests.testAvailabilityQuery11",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAvailabilityQuery13#1",
        source: """
      if #available(iDishwasherOS 10.51) {
      }
      """,
        origin: "AvailabilityQueryTests.testAvailabilityQuery13",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAvailabilityQuery14#1",
        source: """
      if #available(iDishwasherOS 10.51, *) {
      }
      """,
        origin: "AvailabilityQueryTests.testAvailabilityQuery14",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAvailabilityQuery15#1",
        source: """
      if #available(macos 10.51, *) {
      }
      """,
        origin: "AvailabilityQueryTests.testAvailabilityQuery15",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAvailabilityQuery16#1",
        source: """
      if #available(mscos 10.51, *) {
      }
      """,
        origin: "AvailabilityQueryTests.testAvailabilityQuery16",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAvailabilityQuery17#1",
        source: """
      if #available(macoss 10.51, *) {
      }
      """,
        origin: "AvailabilityQueryTests.testAvailabilityQuery17",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAvailabilityQuery18#1",
        source: """
      if #available(mac 10.51, *) {
      }
      """,
        origin: "AvailabilityQueryTests.testAvailabilityQuery18",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAvailabilityQuery19#1",
        source: """
      if #available(OSX 10.51, OSX 10.52, *) {
      }
      """,
        origin: "AvailabilityQueryTests.testAvailabilityQuery19",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAvailabilityQuery20#1",
        source: """
      if #available(OSX 10.52) { }
      """,
        origin: "AvailabilityQueryTests.testAvailabilityQuery20",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAvailabilityQuery21#1",
        source: """
      if #available(OSX 10.51, iOS 8.0) { }
      """,
        origin: "AvailabilityQueryTests.testAvailabilityQuery21",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAvailabilityQuery22#1",
        source: """
      if #available(iOS 8.0, *) {
      }
      """,
        origin: "AvailabilityQueryTests.testAvailabilityQuery22",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAvailabilityQuery23#1",
        source: """
      if #available(iOSApplicationExtension, unavailable) { // expected-error 2{{expected version number}}
      }
      """,
        origin: "AvailabilityQueryTests.testAvailabilityQuery23",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAvailabilityQuery24#1",
        source: """
      // Want to make sure we can parse this. Perhaps we should not let this validate, though.
      if #available(*) {
      }
      """,
        origin: "AvailabilityQueryTests.testAvailabilityQuery24",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAvailabilityQuery26#1",
        source: """
      // Multiple platforms
      if #available(OSX 10.51, iOS 8.0, *) {
      }
      """,
        origin: "AvailabilityQueryTests.testAvailabilityQuery26",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAvailabilityQuery30#1",
        source: """
      if #available(OSX 10.51, iOS 8.0, iDishwasherOS 10.51) {
      }
      """,
        origin: "AvailabilityQueryTests.testAvailabilityQuery30",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAvailabilityQuery31#1",
        source: """
      if #available(iDishwasherOS 10.51, OSX 10.51) {
      }
      """,
        origin: "AvailabilityQueryTests.testAvailabilityQuery31",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAvailabilityQuery33#1",
        source: """
      // Emit Fix-It removing un-needed >=, for the moment.
      """,
        origin: "AvailabilityQueryTests.testAvailabilityQuery33",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAvailabilityQuery35#1",
        source: """
      // Bool then #available.
      if 1 != 2, #available(iOS 8.0, *) {}
      """,
        origin: "AvailabilityQueryTests.testAvailabilityQuery35",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAvailabilityQuery36#1",
        source: """
      // Pattern then #available(iOS 8.0, *) {
      if case 42 = 42, #available(iOS 8.0, *) {}
      if let _ = Optional(42), #available(iOS 8.0, *) {}
      """,
        origin: "AvailabilityQueryTests.testAvailabilityQuery36",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAvailabilityQuery37#1",
        source: #"""
      // Allow "macOS" as well.
      if #available(macOS 10.51, *) {
      }
      """#,
        origin: "AvailabilityQueryTests.testAvailabilityQuery37",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAvailabilityQueryUnavailability1#1",
        source: """
      // This file is mostly an inverted version of availability_query.swift
      if #unavailable(OSX 10.51) {
      }
      """,
        origin: "AvailabilityQueryUnavailabilityTests.testAvailabilityQueryUnavailability1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAvailabilityQueryUnavailability8#1",
        source: """
      if #unavailable(OSX) {
      }
      """,
        origin: "AvailabilityQueryUnavailabilityTests.testAvailabilityQueryUnavailability8",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAvailabilityQueryUnavailability10#1",
        source: """
      if #unavailable(iDishwasherOS 10.51) {
      }
      """,
        origin: "AvailabilityQueryUnavailabilityTests.testAvailabilityQueryUnavailability10",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAvailabilityQueryUnavailability11#1",
        source: """
      if #unavailable(iDishwasherOS 10.51) {
      }
      """,
        origin: "AvailabilityQueryUnavailabilityTests.testAvailabilityQueryUnavailability11",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAvailabilityQueryUnavailability12#1",
        source: """
      if #unavailable(macos 10.51) {
      }
      """,
        origin: "AvailabilityQueryUnavailabilityTests.testAvailabilityQueryUnavailability12",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAvailabilityQueryUnavailability13#1",
        source: """
      if #unavailable(mscos 10.51) {
      }
      """,
        origin: "AvailabilityQueryUnavailabilityTests.testAvailabilityQueryUnavailability13",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAvailabilityQueryUnavailability14#1",
        source: """
      if #unavailable(macoss 10.51) {
      }
      """,
        origin: "AvailabilityQueryUnavailabilityTests.testAvailabilityQueryUnavailability14",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAvailabilityQueryUnavailability15#1",
        source: """
      if #unavailable(mac 10.51) {
      }
      """,
        origin: "AvailabilityQueryUnavailabilityTests.testAvailabilityQueryUnavailability15",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAvailabilityQueryUnavailability16#1",
        source: """
      if #unavailable(OSX 10.51, OSX 10.52) {
      }
      """,
        origin: "AvailabilityQueryUnavailabilityTests.testAvailabilityQueryUnavailability16",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAvailabilityQueryUnavailability17#1",
        source: """
      if #unavailable(OSX 10.51, iOS 8.0, *) { }
      if #unavailable(iOS 8.0) {
      }
      """,
        origin: "AvailabilityQueryUnavailabilityTests.testAvailabilityQueryUnavailability17",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAvailabilityQueryUnavailability18#1",
        source: """
      if #unavailable(iOSApplicationExtension, unavailable) { // expected-error 2{{expected version number}}
      }
      """,
        origin: "AvailabilityQueryUnavailabilityTests.testAvailabilityQueryUnavailability18",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAvailabilityQueryUnavailability21#1",
        source: """
      // Multiple platforms
      if #unavailable(OSX 10.51, iOS 8.0) {
      }
      """,
        origin: "AvailabilityQueryUnavailabilityTests.testAvailabilityQueryUnavailability21",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAvailabilityQueryUnavailability25#1",
        source: """
      if #unavailable(OSX 10.51, iOS 8.0, iDishwasherOS 10.51) {
      }
      """,
        origin: "AvailabilityQueryUnavailabilityTests.testAvailabilityQueryUnavailability25",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAvailabilityQueryUnavailability26#1",
        source: """
      if #unavailable(iDishwasherOS 10.51, OSX 10.51) {
      }
      """,
        origin: "AvailabilityQueryUnavailabilityTests.testAvailabilityQueryUnavailability26",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAvailabilityQueryUnavailability29#1",
        source: """
      // Bool then #unavailable.
      if 1 != 2, #unavailable(iOS 8.0) {}
      """,
        origin: "AvailabilityQueryUnavailabilityTests.testAvailabilityQueryUnavailability29",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAvailabilityQueryUnavailability30#1",
        source: """
      // Pattern then #unavailable(iOS 8.0) {
      if case 42 = 42, #unavailable(iOS 8.0) {}
      if let _ = Optional(42), #unavailable(iOS 8.0) {}
      """,
        origin: "AvailabilityQueryUnavailabilityTests.testAvailabilityQueryUnavailability30",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAvailabilityQueryUnavailability31#1",
        source: #"""
      // Allow "macOS" as well.
      if #unavailable(macOS 10.51) {
      }
      """#,
        origin: "AvailabilityQueryUnavailabilityTests.testAvailabilityQueryUnavailability31",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAvailabilityQueryUnavailability32#1",
        source: """
      // Prevent availability and unavailability being present in the same statement.
      if #unavailable(macOS 10.51), #available(macOS 10.52, *) {
      }
      if #available(macOS 10.51, *), #unavailable(macOS 10.52) {
      }
      if #available(macOS 10.51, *), #available(macOS 10.55, *), #unavailable(macOS 10.53) {
      }
      if #unavailable(macOS 10.51), #unavailable(macOS 10.55), #available(macOS 10.53, *) {
      }
      if case 42 = 42, #available(macOS 10.51, *), #unavailable(macOS 10.52) {
      }
      if #available(macOS 10.51, *), case 42 = 42, #unavailable(macOS 10.52) {
      }
      """,
        origin: "AvailabilityQueryUnavailabilityTests.testAvailabilityQueryUnavailability32",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAvailabilityQueryUnavailability33#1",
        source: """
      // Allow availability and unavailability to mix if they are not in the same statement.
      if #unavailable(macOS 11) {
        if #available(macOS 10, *) { }
      }
      if #available(macOS 10, *) {
        if #unavailable(macOS 11) { }
      }
      """,
        origin: "AvailabilityQueryUnavailabilityTests.testAvailabilityQueryUnavailability33",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testBorrowExpr1#1",
        source: """
      func useString(_ str: String) {}
      var global: String = "123"
      func testGlobal() {
        useString(_borrow global)
      }
      """,
        origin: "BorrowExprTests.testBorrowExpr1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testBorrowExpr2#1",
        source: """
      func useString(_ str: String) {}
      func testVar() {
          var t = String()
          t = String()
          useString(_borrow t)
      }
      """,
        origin: "BorrowExprTests.testBorrowExpr2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testBuiltinBridgeObject1#1",
        source: """
      precedencegroup AssignmentPrecedence { assignment: true }
      """,
        origin: "BuiltinBridgeObjectTests.testBuiltinBridgeObject1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testBuiltinBridgeObject2#1",
        source: """
      var word: Builtin.Word
      """,
        origin: "BuiltinBridgeObjectTests.testBuiltinBridgeObject2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testBuiltinBridgeObject3#1",
        source: """
      class C {}
      """,
        origin: "BuiltinBridgeObjectTests.testBuiltinBridgeObject3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testBuiltinBridgeObject4#1",
        source: """
      var c: C
      let bo = Builtin.castToBridgeObject(c, word)
      c = Builtin.castReferenceFromBridgeObject(bo)
      word = Builtin.castBitPatternFromBridgeObject(bo)
      """,
        origin: "BuiltinBridgeObjectTests.testBuiltinBridgeObject4",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testBuiltinWord1#1",
        source: """
      precedencegroup AssignmentPrecedence { assignment: true }
      """,
        origin: "BuiltinWordTests.testBuiltinWord1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testBuiltinWord2#1",
        source: """
      var word: Builtin.Word
      var i16: Builtin.Int16
      var i32: Builtin.Int32
      var i64: Builtin.Int64
      var i128: Builtin.Int128
      """,
        origin: "BuiltinWordTests.testBuiltinWord2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testBuiltinWord3#1",
        source: """
      // Check that trunc/?ext operations are appropriately available given the
      // abstract range of potential Word sizes.
      """,
        origin: "BuiltinWordTests.testBuiltinWord3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testBuiltinWord4#1",
        source: """
      word = Builtin.truncOrBitCast_Int128_Word(i128)
      word = Builtin.truncOrBitCast_Int64_Word(i64)
      word = Builtin.truncOrBitCast_Int32_Word(i32)
      word = Builtin.truncOrBitCast_Int16_Word(i16)
      """,
        origin: "BuiltinWordTests.testBuiltinWord4",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testBuiltinWord5#1",
        source: """
      i16 = Builtin.truncOrBitCast_Word_Int16(word)
      i32 = Builtin.truncOrBitCast_Word_Int32(word)
      i64 = Builtin.truncOrBitCast_Word_Int64(word)
      i128 = Builtin.truncOrBitCast_Word_Int128(word)
      """,
        origin: "BuiltinWordTests.testBuiltinWord5",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testBuiltinWord6#1",
        source: """
      word = Builtin.zextOrBitCast_Int128_Word(i128)
      word = Builtin.zextOrBitCast_Int64_Word(i64)
      word = Builtin.zextOrBitCast_Int32_Word(i32)
      word = Builtin.zextOrBitCast_Int16_Word(i16)
      """,
        origin: "BuiltinWordTests.testBuiltinWord6",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testBuiltinWord7#1",
        source: """
      i16 = Builtin.zextOrBitCast_Word_Int16(word)
      i32 = Builtin.zextOrBitCast_Word_Int32(word)
      i64 = Builtin.zextOrBitCast_Word_Int64(word)
      i128 = Builtin.zextOrBitCast_Word_Int128(word)
      """,
        origin: "BuiltinWordTests.testBuiltinWord7",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testBuiltinWord8#1",
        source: """
      word = Builtin.trunc_Int128_Word(i128)
      word = Builtin.trunc_Int64_Word(i64)
      word = Builtin.trunc_Int32_Word(i32)
      word = Builtin.trunc_Int16_Word(i16)
      """,
        origin: "BuiltinWordTests.testBuiltinWord8",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testBuiltinWord9#1",
        source: """
      i16 = Builtin.trunc_Word_Int16(word)
      i32 = Builtin.trunc_Word_Int32(word)
      i64 = Builtin.trunc_Word_Int64(word)
      i128 = Builtin.trunc_Word_Int128(word)
      """,
        origin: "BuiltinWordTests.testBuiltinWord9",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testBuiltinWord10#1",
        source: """
      word = Builtin.zext_Int128_Word(i128)
      word = Builtin.zext_Int64_Word(i64)
      word = Builtin.zext_Int32_Word(i32)
      word = Builtin.zext_Int16_Word(i16)
      """,
        origin: "BuiltinWordTests.testBuiltinWord10",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testBuiltinWord11#1",
        source: """
      i16 = Builtin.zext_Word_Int16(word)
      i32 = Builtin.zext_Word_Int32(word)
      i64 = Builtin.zext_Word_Int64(word)
      i128 = Builtin.zext_Word_Int128(word)
      """,
        origin: "BuiltinWordTests.testBuiltinWord11",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testConflictMarkers1#1",
        source: """
      // Conflict marker parsing should never conflict with operator parsing.
      """,
        origin: "ConflictMarkersTests.testConflictMarkers1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testConflictMarkers2#1",
        source: """
      prefix operator <<<<<<<
      infix operator <<<<<<<
      """,
        origin: "ConflictMarkersTests.testConflictMarkers2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testConflictMarkers3#1",
        source: """
      prefix func <<<<<<< (x : String) {}
      func <<<<<<< (x : String, y : String) {}
      """,
        origin: "ConflictMarkersTests.testConflictMarkers3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testConflictMarkers4#1",
        source: """
      prefix operator >>>>>>>
      infix operator >>>>>>>
      """,
        origin: "ConflictMarkersTests.testConflictMarkers4",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testConflictMarkers5#1",
        source: """
      prefix func >>>>>>> (x : String) {}
      func >>>>>>> (x : String, y : String) {}
      """,
        origin: "ConflictMarkersTests.testConflictMarkers5",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testConflictMarkers6#1",
        source: """
      // diff3-style conflict markers
      """,
        origin: "ConflictMarkersTests.testConflictMarkers6",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testConflictMarkers9#1",
        source: #"""
      <<<<<<<"HEAD:fake_conflict_markers.swift" // No error
      >>>>>>>"18844bc65229786b96b89a9fc7739c0fc897905e:fake_conflict_markers.swift" // No error
      """#,
        origin: "ConflictMarkersTests.testConflictMarkers9",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testConflictMarkers11#1",
        source: """
      // Disambiguating conflict markers from operator applications.
      """,
        origin: "ConflictMarkersTests.testConflictMarkers11",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testConflictMarkers13#1",
        source: """
      // Perforce-style conflict markers
      """,
        origin: "ConflictMarkersTests.testConflictMarkers13",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testConsecutiveStatements1#1",
        source: """
      func statement_starts() {
        var f : (Int) -> ()
        f = { (x : Int) -> () in }
        f(0)
        f (0)
        f
        (0)
        var a = [1,2,3]
        a[0] = 1
        a [0] = 1
        a
        [0, 1, 2]
      }
      """,
        origin: "ConsecutiveStatementsTests.testConsecutiveStatements1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testGlobal#1",
        source: """
      var global: Int = 5
      func testGlobal() {
          let _ = copy global
      }
      """,
        origin: "CopyExprTests.testGlobal",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testLet#1",
        source: """
      func testLet() {
          let t = String()
          let _ = copy t
      }
      """,
        origin: "CopyExprTests.testLet",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testVar#1",
        source: """
      func testVar() {
          var t = String()
          t = String()
          let _ = copy t
      }
      """,
        origin: "CopyExprTests.testVar",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testStillAbleToCallFunctionCalledCopy#1",
        source: """
      func copy() {}
      func copy(_: String) {}
      func copy(_: String, _: Int) {}
      func copy(x: String, y: Int) {}

      func useCopyFunc() {
          var s = String()
          var i = global

          copy()
          copy(s)
          copy(i) // expected-error{{cannot convert value of type 'Int' to expected argument type 'String'}}
          copy(s, i)
          copy(i, s) // expected-error{{unnamed argument #2 must precede unnamed argument #1}}
          copy(x: s, y: i)
          copy(y: i, x: s) // expected-error{{argument 'x' must precede argument 'y'}}
      }
      """,
        origin: "CopyExprTests.testStillAbleToCallFunctionCalledCopy",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testUseCopyVariable#1",
        source: """
      func useCopyVar(copy: inout String) {
          let s = copy
          copy = s

          // We can copy from a variable named `copy`
          let t = copy copy
          copy = t

          // We can do member access and subscript a variable named `copy`
          let i = copy.startIndex
          let _ = copy[i]
      }
      """,
        origin: "CopyExprTests.testUseCopyVariable",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testPropertyWrapperWithCopy#1",
        source: """
      @propertyWrapper
      struct FooWrapper<T> {
          var value: T

          init(wrappedValue: T) { value = wrappedValue }

          var wrappedValue: T {
              get { value }
              nonmutating set {}
          }
          var projectedValue: T {
              get { value }
              nonmutating set {}
          }
      }

      struct Foo {
          @FooWrapper var wrapperTest: String

          func copySelf() {
              _ = copy self
          }

          func copyPropertyWrapper() {
              // should still parse, even if it doesn't semantically work out
              _ = copy wrapperTest // expected-error{{can only be applied to lvalues}}
              _ = copy _wrapperTest // expected-error{{can only be applied to lvalues}}
              _ = copy $wrapperTest // expected-error{{can only be applied to lvalues}}
          }
      }
      """,
        origin: "CopyExprTests.testPropertyWrapperWithCopy",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAsCaseStmt#1",
        source: """
      class ParentKlass {}
      class SubKlass : ParentKlass {}

      func test(_ s: SubKlass) {
        switch s {
        case let copy as ParentKlass:
          fallthrough
        }
      }
      """,
        origin: "CopyExprTests.testAsCaseStmt",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testParseCanCopyClosureDollarIdentifier#1",
        source: """
      class Klass {}
      let f: (Klass) -> () = {
        let _ = copy $0
      }
      """,
        origin: "CopyExprTests.testParseCanCopyClosureDollarIdentifier",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForLoop#1",
        source: """
      func test() {
        for copy in 1..<1024 {
        }
      }
      """,
        origin: "CopyExprTests.testForLoop",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testCopySelf#1",
        source: """
      class Klass {
        func test() {
          let _ = copy self
        }
      }
      """,
        origin: "CopyExprTests.testCopySelf",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDebugger1#1",
        source: """
      import Nonexistent_Module
      """,
        origin: "DebuggerTests.testDebugger1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDebugger2#1",
        source: """
      var ($x0, $x1) = (4, 3)
      var z = $x0 + $x1
      """,
        origin: "DebuggerTests.testDebugger2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDebugger3#1",
        source: """
      z // no error.
      """,
        origin: "DebuggerTests.testDebugger3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDebugger4#1",
        source: """
      var x: Double = z
      """,
        origin: "DebuggerTests.testDebugger4",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDelayedExtension1#1",
        source: """
      extension X { }
      _ = 1
      f()
      """,
        origin: "DelayedExtensionTests.testDelayedExtension1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDeprecatedWhere1#1",
        source: """
      protocol Mashable { }
      protocol Womparable { }
      """,
        origin: "DeprecatedWhereTests.testDeprecatedWhere1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDeprecatedWhere2#1",
        source: """
      // FuncDecl: Choose 0
      func f1<T>(x: T) {}
      """,
        origin: "DeprecatedWhereTests.testDeprecatedWhere2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDeprecatedWhere3#1",
        source: """
      // FuncDecl: Choose 1
      // 1: Inherited constraint
      func f2<T: Mashable>(x: T) {} // no-warning
      // 2: Non-trailing where
      func f3<T where T: Womparable>(x: T) {}
      // 3: Has return type
      func f4<T>(x: T) -> Int { return 2 } // no-warning
      // 4: Trailing where
      func f5<T>(x: T) where T : Equatable {} // no-warning
      """,
        origin: "DeprecatedWhereTests.testDeprecatedWhere3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05",
        compilerRejects: "'where' clause next to generic parameters is obsolete, must be written"
    ),
    SwiftSnippet(
        label: "testDeprecatedWhere4#1",
        source: """
      // FuncDecl: Choose 2
      // 1,2
      func f12<T: Mashable where T: Womparable>(x: T) {}
      // 1,3
      func f13<T: Mashable>(x: T) -> Int { return 2 } // no-warning
      // 1,4
      func f14<T: Mashable>(x: T) where T: Equatable {} // no-warning
      // 2,3
      func f23<T where T: Womparable>(x: T) -> Int { return 2 }
      // 2,4
      func f24<T where T: Womparable>(x: T) where T: Equatable {}
      // 3,4
      func f34<T>(x: T) -> Int where T: Equatable { return 2 } // no-warning
      """,
        origin: "DeprecatedWhereTests.testDeprecatedWhere4",
        syntaxVersion: "604.0.0-prerelease-2026-06-05",
        compilerRejects: "'where' clause next to generic parameters is obsolete, must be written"
    ),
    SwiftSnippet(
        label: "testDeprecatedWhere5#1",
        source: """
      // FuncDecl: Choose 3
      // 1,2,3
      func f123<T: Mashable where T: Womparable>(x: T) -> Int { return 2 }
      // 1,2,4
      func f124<T: Mashable where T: Womparable>(x: T) where T: Equatable {}
      // 2,3,4
      func f234<T where T: Womparable>(x: T) -> Int where T: Equatable { return 2 }
      """,
        origin: "DeprecatedWhereTests.testDeprecatedWhere5",
        syntaxVersion: "604.0.0-prerelease-2026-06-05",
        compilerRejects: "'where' clause next to generic parameters is obsolete, must be written"
    ),
    SwiftSnippet(
        label: "testDeprecatedWhere6#1",
        source: """
      // FuncDecl: Choose 4
      // 1,2,3,4
      func f1234<T: Mashable where T: Womparable>(x: T) -> Int where T: Equatable { return 2 }
      """,
        origin: "DeprecatedWhereTests.testDeprecatedWhere6",
        syntaxVersion: "604.0.0-prerelease-2026-06-05",
        compilerRejects: "'where' clause next to generic parameters is obsolete, must be written"
    ),
    SwiftSnippet(
        label: "testDeprecatedWhere7#1",
        source: """
      // NominalTypeDecl: Choose 0
      struct S0<T> {}
      """,
        origin: "DeprecatedWhereTests.testDeprecatedWhere7",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDeprecatedWhere8#1",
        source: """
      // NominalTypeDecl: Choose 1
      // 1: Inherited constraint
      struct S1<T: Mashable> {} // no-warning
      // 2: Non-trailing where
      struct S2<T where T: Womparable> {}
      // 3: Trailing where
      struct S3<T> where T : Equatable {} // no-warning
      """,
        origin: "DeprecatedWhereTests.testDeprecatedWhere8",
        syntaxVersion: "604.0.0-prerelease-2026-06-05",
        compilerRejects: "'where' clause next to generic parameters is obsolete, must be written"
    ),
    SwiftSnippet(
        label: "testDeprecatedWhere9#1",
        source: """
      // NominalTypeDecl: Choose 2
      // 1,2
      struct S12<T: Mashable where T: Womparable> {}
      // 1,3
      struct S13<T: Mashable> where T: Equatable {} // no-warning
      // 2,3
      struct S23<T where T: Womparable> where T: Equatable {}
      """,
        origin: "DeprecatedWhereTests.testDeprecatedWhere9",
        syntaxVersion: "604.0.0-prerelease-2026-06-05",
        compilerRejects: "'where' clause next to generic parameters is obsolete, must be written"
    ),
    SwiftSnippet(
        label: "testDeprecatedWhere10#1",
        source: """
      // NominalTypeDecl: Choose 3
      // 1,2,3
      struct S123<T: Mashable where T: Womparable> where T: Equatable {}
      """,
        origin: "DeprecatedWhereTests.testDeprecatedWhere10",
        syntaxVersion: "604.0.0-prerelease-2026-06-05",
        compilerRejects: "'where' clause next to generic parameters is obsolete, must be written"
    ),
    SwiftSnippet(
        label: "testDeprecatedWhere11#1",
        source: """
      protocol ProtoA {}
      protocol ProtoB {}
      protocol ProtoC {}
      protocol ProtoD {}
      func testCombinedConstraints<T: ProtoA & ProtoB where T: ProtoC>(x: T) {}
      func testCombinedConstraints<T: ProtoA & ProtoB where T: ProtoC>(x: T) where T: ProtoD {}
      """,
        origin: "DeprecatedWhereTests.testDeprecatedWhere11",
        syntaxVersion: "604.0.0-prerelease-2026-06-05",
        compilerRejects: "'where' clause next to generic parameters is obsolete, must be written"
    ),
    SwiftSnippet(
        label: "testDiagnoseAvailability1#1",
        source: """
      // https://github.com/apple/swift/issues/46814
      // Misleading/wrong error message for malformed '@available'
      """,
        origin: "DiagnoseAvailabilityTests.testDiagnoseAvailability1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDiagnoseAvailability2#1",
        source: """
      @available(OSX 10.6, *) // no error
      func availableSince10_6() {}
      """,
        origin: "DiagnoseAvailabilityTests.testDiagnoseAvailability2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDiagnoseAvailability3#1",
        source: """
      @available(OSX, introduced: 10.0, deprecated: 10.12) // no error
      func introducedFollowedByDeprecated() {}
      """,
        origin: "DiagnoseAvailabilityTests.testDiagnoseAvailability3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDiagnoseAvailability4#1",
        source: """
      @available(OSX 10.0, deprecated: 10.12)
      func shorthandFollowedByDeprecated() {}
      """,
        origin: "DiagnoseAvailabilityTests.testDiagnoseAvailability4",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDiagnoseAvailability5#1",
        source: """
      @available(OSX 10.0, introduced: 10.12)
      func shorthandFollowedByIntroduced() {}
      """,
        origin: "DiagnoseAvailabilityTests.testDiagnoseAvailability5",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDiagnoseAvailability6#1",
        source: """
      @available(iOS 6.0, OSX 10.8, *) // no error
      func availableOnMultiplePlatforms() {}
      """,
        origin: "DiagnoseAvailabilityTests.testDiagnoseAvailability6",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDiagnoseAvailability7#1",
        source: """
      @available(iOS 6.0, OSX 10.0, deprecated: 10.12)
      func twoShorthandsFollowedByDeprecated() {}
      """,
        origin: "DiagnoseAvailabilityTests.testDiagnoseAvailability7",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDiagnoseAvailability9#1",
        source: """
      @available(*, deprecated: 4.2)
      func allPlatformsDeprecatedVersion() {}
      """,
        origin: "DiagnoseAvailabilityTests.testDiagnoseAvailability9",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDiagnoseAvailability10#1",
        source: """
      @available(*, deprecated, obsoleted: 4.2)
      func allPlatformsDeprecatedAndObsoleted() {}
      """,
        origin: "DiagnoseAvailabilityTests.testDiagnoseAvailability10",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDiagnoseAvailability11#1",
        source: """
      @available(*, introduced: 4.0, deprecated: 4.1, obsoleted: 4.2)
      func allPlatformsDeprecatedAndObsoleted2() {}
      """,
        origin: "DiagnoseAvailabilityTests.testDiagnoseAvailability11",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDiagnoseAvailability12#1",
        source: """
      @available(swift, unavailable)
      func swiftUnavailable() {}
      """,
        origin: "DiagnoseAvailabilityTests.testDiagnoseAvailability12",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDiagnoseAvailability13#1",
        source: """
      @available(swift, unavailable, introduced: 4.2)
      func swiftUnavailableIntroduced() {}
      """,
        origin: "DiagnoseAvailabilityTests.testDiagnoseAvailability13",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDiagnoseAvailability14#1",
        source: """
      @available(swift, deprecated)
      func swiftDeprecated() {}
      """,
        origin: "DiagnoseAvailabilityTests.testDiagnoseAvailability14",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDiagnoseAvailability15#1",
        source: """
      @available(swift, deprecated, obsoleted: 4.2)
      func swiftDeprecatedObsoleted() {}
      """,
        origin: "DiagnoseAvailabilityTests.testDiagnoseAvailability15",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDiagnoseAvailability16#1",
        source: #"""
      @available(swift, message: "missing valid option")
      func swiftMessage() {}
      """#,
        origin: "DiagnoseAvailabilityTests.testDiagnoseAvailability16",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDiagnoseAvailability18#1",
        source: #"""
      @available(*, unavailable, message: """
        foobar message.
        """)
      func multilineMessage() {}
      """#,
        origin: "DiagnoseAvailabilityTests.testDiagnoseAvailability18",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDiagnoseAvailability19#1",
        source: #"""
      @available(*, unavailable, message: " ")
      func emptyMessage() {}
      emptyMessage()
      """#,
        origin: "DiagnoseAvailabilityTests.testDiagnoseAvailability19",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDiagnoseAvailabilityWindows1#1",
        source: #"""
      @available(Windows, unavailable, message: "unsupported")
      func unavailable() {}
      """#,
        origin: "DiagnoseAvailabilityWindowsTests.testDiagnoseAvailabilityWindows1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDiagnoseAvailabilityWindows2#1",
        source: """
      unavailable()
      """,
        origin: "DiagnoseAvailabilityWindowsTests.testDiagnoseAvailabilityWindows2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDiagnoseAvailabilityWindows3#1",
        source: """
      @available(Windows, introduced: 10.0.17763, deprecated: 10.0.19140)
      func introduced_deprecated() {}
      """,
        origin: "DiagnoseAvailabilityWindowsTests.testDiagnoseAvailabilityWindows3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDiagnoseAvailabilityWindows4#1",
        source: """
      introduced_deprecated()
      """,
        origin: "DiagnoseAvailabilityWindowsTests.testDiagnoseAvailabilityWindows4",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDiagnoseAvailabilityWindows5#1",
        source: """
      @available(Windows 10, *)
      func windows10() {}
      """,
        origin: "DiagnoseAvailabilityWindowsTests.testDiagnoseAvailabilityWindows5",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDiagnoseAvailabilityWindows6#1",
        source: """
      windows10()
      """,
        origin: "DiagnoseAvailabilityWindowsTests.testDiagnoseAvailabilityWindows6",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDiagnoseAvailabilityWindows7#1",
        source: """
      func conditional_compilation() {
        if #available(Windows 10, *) {
        }
      }
      """,
        origin: "DiagnoseAvailabilityWindowsTests.testDiagnoseAvailabilityWindows7",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDiagnoseDynamicReplacement1#1",
        source: """
      dynamic func dynamic_replaceable() {
      }
      """,
        origin: "DiagnoseDynamicReplacementTests.testDiagnoseDynamicReplacement1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDiagnoseInitializerAsTypedPattern6#1",
        source: """
      var _1 = 1, _2 = 2
      """,
        origin: "DiagnoseInitializerAsTypedPatternTests.testDiagnoseInitializerAsTypedPattern6",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDiagnoseInitializerAsTypedPattern7#1",
        source: """
      let ff: X
      (_1, _2) = (_2, _1)
      let fff: X
       (_1, _2) = (_2, _1)
      """,
        origin: "DiagnoseInitializerAsTypedPatternTests.testDiagnoseInitializerAsTypedPattern7",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDiagnoseInitializerAsTypedPattern9e#1",
        source: """
      func nonTopLevel() {
        _ = (a, i, j, k)
      }
      """,
        origin: "DiagnoseInitializerAsTypedPatternTests.testDiagnoseInitializerAsTypedPattern9e",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDiagnosticMissingFuncKeyword3#1",
        source: """
      infix operator %%
      """,
        origin: "DiagnosticMissingFuncKeywordTests.testDiagnosticMissingFuncKeyword3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDollarIdentifier1#1",
        source: """
      // https://github.com/apple/swift/issues/44270
      // Dollar was accidentally allowed as an identifier in Swift 3.
      // SE-0144: Reject this behavior in the future.
      """,
        origin: "DollarIdentifierTests.testDollarIdentifier1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDollarIdentifier4#1",
        source: """
      func escapedDollarVar() {
        var `$` : Int = 42 // no error
        `$` += 1
        print(`$`)
      }
      func escapedDollarLet() {
        let `$` = 42 // no error
        print(`$`)
      }
      func escapedDollarClass() {
        class `$` {} // no error
      }
      func escapedDollarEnum() {
        enum `$` {} // no error
      }
      func escapedDollarStruct() {
        struct `$` {} // no error
      }
      """,
        origin: "DollarIdentifierTests.testDollarIdentifier4",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDollarIdentifier5#1",
        source: """
      func escapedDollarFunc() {
        func `$`(`$`: Int) {} // no error
        `$`(`$`: 25) // no error
      }
      """,
        origin: "DollarIdentifierTests.testDollarIdentifier5",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDollarIdentifier6#1",
        source: """
      func escapedDollarAnd() {
        `$0` = 1
        `$$` = 2
        `$abc` = 3
      }
      """,
        origin: "DollarIdentifierTests.testDollarIdentifier6",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDollarIdentifier7#1",
        source: """
      // Test that we disallow user-defined $-prefixed identifiers. However, the error
      // should not be emitted on $-prefixed identifiers that are not considered
      // declarations.
      """,
        origin: "DollarIdentifierTests.testDollarIdentifier7",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDollarIdentifier8#1",
        source: """
      func $declareWithDollar() {
        var $foo: Int {
          get { 0 }
          set($value) {}
        }
        func $bar() { }
        func wibble(
          $a: Int,
          $b c: Int) { }
        let _: (Int) -> Int = {
          [$capture = 0]
          $a in
          $capture
        }
        let ($a: _, _) = (0, 0)
        $label: if true {
          break $label
        }
        switch 0 {
        @$dollar case _:
          break
        }
        if #available($Dummy 9999, *) {}
        @_swift_native_objc_runtime_base($Dollar)
        class $Class {}
        enum $Enum {}
        struct $Struct {
          @_projectedValueProperty($dummy)
          let property: Never
        }
      }
      protocol $Protocol {}
      precedencegroup $Precedence {
        higherThan: $Precedence
      }
      infix operator **: $Precedence
      #$UnknownDirective()
      """,
        origin: "DollarIdentifierTests.testDollarIdentifier8",
        syntaxVersion: "604.0.0-prerelease-2026-06-05",
        compilerRejects: "cannot declare entity named '$declareWithDollar'; the '$' prefix is re"
    ),
    SwiftSnippet(
        label: "testDollarIdentifier9#1",
        source: """
      // https://github.com/apple/swift/issues/55672
      """,
        origin: "DollarIdentifierTests.testDollarIdentifier9",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDollarIdentifier10#1",
        source: """
      @propertyWrapper
      struct Wrapper {
        var wrappedValue: Int
        var projectedValue: String { String(wrappedValue) }
      }
      """,
        origin: "DollarIdentifierTests.testDollarIdentifier10",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDollarIdentifier11#1",
        source: """
      struct S {
        @Wrapper var café = 42
      }
      """,
        origin: "DollarIdentifierTests.testDollarIdentifier11",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDollarIdentifier12#1",
        source: """
      let _ = S().$café // Okay
      """,
        origin: "DollarIdentifierTests.testDollarIdentifier12",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEffectfulProperties1#1",
        source: """
      struct MyProps {
        var prop1 : Int {
          get async { }
        }
        var prop2 : Int {
          get throws { }
        }
        var prop3 : Int {
          get async throws { }
        }
        var prop1mut : Int {
          mutating get async { }
        }
        var prop2mut : Int {
          mutating get throws { }
        }
        var prop3mut : Int {
          mutating get async throws { }
        }
      }
      """,
        origin: "EffectfulPropertiesTests.testEffectfulProperties1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEffectfulProperties2#1",
        source: """
      struct X1 {
        subscript(_ i : Int) -> Int {
            get async {}
          }
      }
      """,
        origin: "EffectfulPropertiesTests.testEffectfulProperties2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEffectfulProperties3#1",
        source: """
      class X2 {
        subscript(_ i : Int) -> Int {
            get throws {}
          }
      }
      """,
        origin: "EffectfulPropertiesTests.testEffectfulProperties3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEffectfulProperties4#1",
        source: """
      struct X3 {
        subscript(_ i : Int) -> Int {
            get async throws {}
          }
      }
      """,
        origin: "EffectfulPropertiesTests.testEffectfulProperties4",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEffectfulProperties5#1",
        source: """
      struct BadSubscript1 {
        subscript(_ i : Int) -> Int {
            get async throws {}
            set {}
          }
      }
      """,
        origin: "EffectfulPropertiesTests.testEffectfulProperties5",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEffectfulProperties6#1",
        source: """
      struct BadSubscript2 {
        subscript(_ i : Int) -> Int {
            get throws {}
            set throws {}
          }
      }
      """,
        origin: "EffectfulPropertiesTests.testEffectfulProperties6",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEffectfulProperties7#1",
        source: """
      struct S {
        var prop2 : Int {
          mutating get async throws { 0 }
          nonmutating set {}
        }
      }
      """,
        origin: "EffectfulPropertiesTests.testEffectfulProperties7",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEffectfulProperties8#1",
        source: """
      var prop3 : Bool {
        _read { yield prop3 }
        get throws { false }
        get async { true }
        get {}
      }
      """,
        origin: "EffectfulPropertiesTests.testEffectfulProperties8",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEffectfulProperties9#1",
        source: """
      enum E {
        private(set) var prop4 : Double {
          set {}
          get async throws { 1.1 }
          _modify { yield &prop4 }
        }
      }
      """,
        origin: "EffectfulPropertiesTests.testEffectfulProperties9",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEffectfulProperties10#1",
        source: """
      protocol P {
        associatedtype T
        var prop1 : T { get async throws }
        var prop2 : T { get async throws set }
        var prop3 : T { get throws set }
        var prop4 : T { get async }
        var prop5 : T { mutating get async throws }
        var prop6 : T { mutating get throws }
        var prop7 : T { mutating get async nonmutating set }
      }
      """,
        origin: "EffectfulPropertiesTests.testEffectfulProperties10",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEffectfulProperties11#1",
        source: """
      ///////////////////
      // invalid syntax
      """,
        origin: "EffectfulPropertiesTests.testEffectfulProperties11",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEffectfulProperties14#1",
        source: """
      var bad3 : Int {
        _read async { yield 0 }
        set(theValue) async { }
      }
      """,
        origin: "EffectfulPropertiesTests.testEffectfulProperties14",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnumElementPatternSwift42#1",
        source: """
      enum E {
        case A, B, C, D
        static func testE(e: E) {
          switch e {
          case A<UndefinedTy>():
            break
          case B<Int>():
            break
          default:
            break;
          }
        }
      }
      """,
        origin: "EnumElementPatternSwift4Tests.testEnumElementPatternSwift42",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnumElementPatternSwift43#1",
        source: """
      func testE(e: E) {
        switch e {
        case E.A<UndefinedTy>():
          break
        case E.B<Int>():
          break
        case .C():
          break
        case .D(let payload):
          let _: () = payload
          break
        default:
          break
        }
        guard
          case .C() = e,
          case .D(let payload) = e
        else { return }
      }
      """,
        origin: "EnumElementPatternSwift4Tests.testEnumElementPatternSwift43",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnumElementPatternSwift44#1",
        source: """
      extension E : Error {}
      func canThrow() throws {
        throw E.A
      }
      """,
        origin: "EnumElementPatternSwift4Tests.testEnumElementPatternSwift44",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnumElementPatternSwift45#1",
        source: """
      do {
        try canThrow()
      } catch E.A() {
        // ..
      } catch E.B(let payload) {
        let _: () = payload
      }
      """,
        origin: "EnumElementPatternSwift4Tests.testEnumElementPatternSwift45",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum2#1",
        source: """
      // Windows does not support FP80
      // XFAIL: OS=windows-msvc
      """,
        origin: "EnumTests.testEnum2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum3#1",
        source: """
      enum Empty {}
      """,
        origin: "EnumTests.testEnum3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum4#1",
        source: """
      enum Boolish {
        case falsy
        case truthy
        init() { self = .falsy }
      }
      """,
        origin: "EnumTests.testEnum4",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum5#1",
        source: """
      var b = Boolish.falsy
      b = .truthy
      """,
        origin: "EnumTests.testEnum5",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum6#1",
        source: """
      enum Optionable<T> {
        case Nought
        case Mere(T)
      }
      """,
        origin: "EnumTests.testEnum6",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum7#1",
        source: """
      var o = Optionable<Int>.Nought
      o = .Mere(0)
      """,
        origin: "EnumTests.testEnum7",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum8#1",
        source: """
      enum Color { case Red, Green, Grayscale(Int), Blue }
      """,
        origin: "EnumTests.testEnum8",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum9#1",
        source: """
      var c = Color.Red
      c = .Green
      c = .Grayscale(255)
      c = .Blue
      """,
        origin: "EnumTests.testEnum9",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum10#1",
        source: """
      let partialApplication = Color.Grayscale
      """,
        origin: "EnumTests.testEnum10",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum12#1",
        source: """
      struct SomeStruct {
        case StructCase
      }
      """,
        origin: "EnumTests.testEnum12",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum13#1",
        source: """
      class SomeClass {
        case ClassCase
      }
      """,
        origin: "EnumTests.testEnum13",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum14#1",
        source: """
      enum EnumWithExtension1 {
        case A1
      }
      extension EnumWithExtension1 {
        case A2
      }
      """,
        origin: "EnumTests.testEnum14",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum15#1",
        source: """
      // Attributes for enum cases.
      """,
        origin: "EnumTests.testEnum15",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum16#1",
        source: """
      enum EnumCaseAttributes {
        @xyz case EmptyAttributes
      }
      """,
        origin: "EnumTests.testEnum16",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum18#1",
        source: """
      enum HasMethodsPropertiesAndCtors {
        case TweedleDee
        case TweedleDum
        func method() {}
        func staticMethod() {}
        init() {}
        subscript(x:Int) -> Int {
          return 0
        }
        var property : Int {
          return 0
        }
      }
      """,
        origin: "EnumTests.testEnum18",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum19#1",
        source: """
      enum ImproperlyHasIVars {
        case Flopsy
        case Mopsy
        var ivar : Int
      }
      """,
        origin: "EnumTests.testEnum19",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum22#1",
        source: """
      enum RawTypeEmpty : Int {}
      """,
        origin: "EnumTests.testEnum22",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum23#1",
        source: """
      enum Raw : Int {
        case Ankeny, Burnside
      }
      """,
        origin: "EnumTests.testEnum23",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum24#1",
        source: """
      enum MultiRawType : Int64, Int32 {
        case Couch, Davis
      }
      """,
        origin: "EnumTests.testEnum24",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum25#1",
        source: """
      protocol RawTypeNotFirstProtocol {}
      enum RawTypeNotFirst : RawTypeNotFirstProtocol, Int {
        case E
      }
      """,
        origin: "EnumTests.testEnum25",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum26#1",
        source: """
      enum ExpressibleByRawTypeNotLiteral : Array<Int> {
        case Ladd, Elliott, Sixteenth, Harrison
      }
      """,
        origin: "EnumTests.testEnum26",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum27#1",
        source: """
      enum RawTypeCircularityA : RawTypeCircularityB, ExpressibleByIntegerLiteral {
        case Morrison, Belmont, Madison, Hawthorne
        init(integerLiteral value: Int) {
          self = .Morrison
        }
      }
      """,
        origin: "EnumTests.testEnum27",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum28#1",
        source: """
      enum RawTypeCircularityB : RawTypeCircularityA, ExpressibleByIntegerLiteral {
        case Willamette, Columbia, Sandy, Multnomah
        init(integerLiteral value: Int) {
          self = .Willamette
        }
      }
      """,
        origin: "EnumTests.testEnum28",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum29#1",
        source: """
      struct ExpressibleByFloatLiteralOnly : ExpressibleByFloatLiteral {
          init(floatLiteral: Double) {}
      }
      enum ExpressibleByRawTypeNotIntegerLiteral : ExpressibleByFloatLiteralOnly {
        case Everett
        case Flanders
      }
      """,
        origin: "EnumTests.testEnum29",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum30#1",
        source: """
      enum RawTypeWithIntValues : Int {
        case Glisan = 17, Hoyt = 219, Irving, Johnson = 97209
      }
      """,
        origin: "EnumTests.testEnum30",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum31#1",
        source: """
      enum RawTypeWithNegativeValues : Int {
        case Glisan = -17, Hoyt = -219, Irving, Johnson = -97209
        case AutoIncAcrossZero = -1, Zero, One
      }
      """,
        origin: "EnumTests.testEnum31",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum32#1",
        source: #"""
      enum RawTypeWithUnicodeScalarValues : UnicodeScalar {
        case Kearney = "K"
        case Lovejoy
        case Marshall = "M"
      }
      """#,
        origin: "EnumTests.testEnum32",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum33#1",
        source: #"""
      enum RawTypeWithCharacterValues : Character {
        case First = "い"
        case Second
        case Third = "は"
      }
      """#,
        origin: "EnumTests.testEnum33",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum34#1",
        source: #"""
      enum RawTypeWithCharacterValues_Correct : Character {
        case First = "😅" // ok
        case Second = "👩‍👩‍👧‍👦" // ok
        case Third = "👋🏽" // ok
        case Fourth = "\u{1F3F4}\u{E0067}\u{E0062}\u{E0065}\u{E006E}\u{E0067}\u{E007F}" // ok
      }
      """#,
        origin: "EnumTests.testEnum34",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum35#1",
        source: #"""
      enum RawTypeWithCharacterValues_Error1 : Character {
        case First = "abc"
      }
      """#,
        origin: "EnumTests.testEnum35",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum36#1",
        source: """
      enum RawTypeWithFloatValues : Float {
        case Northrup = 1.5
        case Overton
        case Pettygrove = 2.25
      }
      """,
        origin: "EnumTests.testEnum36",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum37#1",
        source: #"""
      enum RawTypeWithStringValues : String {
        case Primrose // okay
        case Quimby = "Lucky Lab"
        case Raleigh // okay
        case Savier = "McMenamin's", Thurman = "Kenny and Zuke's"
      }
      """#,
        origin: "EnumTests.testEnum37",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum38#1",
        source: """
      enum RawValuesWithoutRawType {
        case Upshur = 22
      }
      """,
        origin: "EnumTests.testEnum38",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum39#1",
        source: """
      enum RawTypeWithRepeatValues : Int {
        case Vaughn = 22
        case Wilson = 22
      }
      """,
        origin: "EnumTests.testEnum39",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum40#1",
        source: """
      enum RawTypeWithRepeatValues2 : Double {
        case Vaughn = 22
        case Wilson = 22.0
      }
      """,
        origin: "EnumTests.testEnum40",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum41#1",
        source: """
      enum RawTypeWithRepeatValues3 : Double {
        // 2^63-1
        case Vaughn = 9223372036854775807
        case Wilson = 9223372036854775807.0
      }
      """,
        origin: "EnumTests.testEnum41",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum42#1",
        source: """
      enum RawTypeWithRepeatValues4 : Double {
        // 2^64-1
        case Vaughn = 18446744073709551615
        case Wilson = 18446744073709551615.0
      }
      """,
        origin: "EnumTests.testEnum42",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum43#1",
        source: """
      enum RawTypeWithRepeatValues5 : Double {
        // 2^65-1
        case Vaughn = 36893488147419103231
        case Wilson = 36893488147419103231.0
      }
      """,
        origin: "EnumTests.testEnum43",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum44#1",
        source: """
      enum RawTypeWithRepeatValues6 : Double {
        // 2^127-1
        case Vaughn = 170141183460469231731687303715884105727
        case Wilson = 170141183460469231731687303715884105727.0
      }
      """,
        origin: "EnumTests.testEnum44",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum45#1",
        source: """
      enum RawTypeWithRepeatValues7 : Double {
        // 2^128-1
        case Vaughn = 340282366920938463463374607431768211455
        case Wilson = 340282366920938463463374607431768211455.0
      }
      """,
        origin: "EnumTests.testEnum45",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum46#1",
        source: #"""
      enum RawTypeWithRepeatValues8 : String {
        case Vaughn = "XYZ"
        case Wilson = "XYZ"
      }
      """#,
        origin: "EnumTests.testEnum46",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum47#1",
        source: """
      enum RawTypeWithNonRepeatValues : Double {
        case SantaClara = 3.7
        case SanFernando = 7.4
        case SanAntonio = -3.7
        case SanCarlos = -7.4
      }
      """,
        origin: "EnumTests.testEnum47",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum48#1",
        source: """
      enum RawTypeWithRepeatValuesAutoInc : Double {
        case Vaughn = 22
        case Wilson
        case Yeon = 23
      }
      """,
        origin: "EnumTests.testEnum48",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum49#1",
        source: """
      enum RawTypeWithRepeatValuesAutoInc2 : Double {
        case Vaughn = 23
        case Wilson = 22
        case Yeon
      }
      """,
        origin: "EnumTests.testEnum49",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum50#1",
        source: """
      enum RawTypeWithRepeatValuesAutoInc3 : Double {
        case Vaughn
        case Wilson
        case Yeon = 1
      }
      """,
        origin: "EnumTests.testEnum50",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum51#1",
        source: #"""
      enum RawTypeWithRepeatValuesAutoInc4 : String {
        case A = "B"
        case B
      }
      """#,
        origin: "EnumTests.testEnum51",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum52#1",
        source: #"""
      enum RawTypeWithRepeatValuesAutoInc5 : String {
        case A
        case B = "A"
      }
      """#,
        origin: "EnumTests.testEnum52",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum53#1",
        source: #"""
      enum RawTypeWithRepeatValuesAutoInc6 : String {
        case A
        case B
        case C = "B"
      }
      """#,
        origin: "EnumTests.testEnum53",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum54#1",
        source: """
      enum NonliteralRawValue : Int {
        case Yeon = 100 + 20 + 3
      }
      """,
        origin: "EnumTests.testEnum54",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum55#1",
        source: """
      enum RawTypeWithPayload : Int {
        case Powell(Int)
        case Terwilliger(Int) = 17
      }
      """,
        origin: "EnumTests.testEnum55",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum56#1",
        source: #"""
      enum RawTypeMismatch : Int {
        case Barbur = "foo"
      }
      """#,
        origin: "EnumTests.testEnum56",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum57#1",
        source: """
      enum DuplicateMembers1 {
        case Foo
        case Foo
      }
      """,
        origin: "EnumTests.testEnum57",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum58#1",
        source: """
      enum DuplicateMembers2 {
        case Foo, Bar
        case Foo
        case Bar
      }
      """,
        origin: "EnumTests.testEnum58",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum59#1",
        source: """
      enum DuplicateMembers3 {
        case Foo
        case Foo(Int)
      }
      """,
        origin: "EnumTests.testEnum59",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum60#1",
        source: """
      enum DuplicateMembers4 : Int {
        case Foo = 1
        case Foo = 2
      }
      """,
        origin: "EnumTests.testEnum60",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum61#1",
        source: """
      enum DuplicateMembers5 : Int {
        case Foo = 1
        case Foo = 1 + 1
      }
      """,
        origin: "EnumTests.testEnum61",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum62#1",
        source: """
      enum DuplicateMembers6 {
        case Foo // expected-note 2{{'Foo' previously declared here}}
        case Foo
        case Foo
      }
      """,
        origin: "EnumTests.testEnum62",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum63#1",
        source: #"""
      enum DuplicateMembers7 : String {
        case Foo
        case Foo = "Bar"
      }
      """#,
        origin: "EnumTests.testEnum63",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum64#1",
        source: #"""
      // Refs to duplicated enum cases shouldn't crash the compiler.
      // rdar://problem/20922401
      func check20922401() -> String {
        let x: DuplicateMembers1 = .Foo
        switch x {
          case .Foo:
            return "Foo"
        }
      }
      """#,
        origin: "EnumTests.testEnum64",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum65#1",
        source: """
      enum PlaygroundRepresentation : UInt8 {
        case Class = 1
        case Struct = 2
        case Tuple = 3
        case Enum = 4
        case Aggregate = 5
        case Container = 6
        case IDERepr = 7
        case Gap = 8
        case ScopeEntry = 9
        case ScopeExit = 10
        case Error = 11
        case IndexContainer = 12
        case KeyContainer = 13
        case MembershipContainer = 14
        case Unknown = 0xFF
        static func fromByte(byte : UInt8) -> PlaygroundRepresentation {
          let repr = PlaygroundRepresentation(rawValue: byte)
          if repr == .none { return .Unknown } else { return repr! }
        }
      }
      """,
        origin: "EnumTests.testEnum65",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum66#1",
        source: """
      struct ManyLiteralable : ExpressibleByIntegerLiteral, ExpressibleByStringLiteral, Equatable {
        init(stringLiteral: String) {}
        init(integerLiteral: Int) {}
        init(unicodeScalarLiteral: String) {}
        init(extendedGraphemeClusterLiteral: String) {}
      }
      func ==(lhs: ManyLiteralable, rhs: ManyLiteralable) -> Bool { return true }
      """,
        origin: "EnumTests.testEnum66",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum67#1",
        source: """
      enum ManyLiteralA : ManyLiteralable {
        case A
        case B = 0
      }
      """,
        origin: "EnumTests.testEnum67",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum68#1",
        source: #"""
      enum ManyLiteralB : ManyLiteralable {
        case A = "abc"
        case B
      }
      """#,
        origin: "EnumTests.testEnum68",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum69#1",
        source: #"""
      enum ManyLiteralC : ManyLiteralable {
        case A
        case B = "0"
      }
      """#,
        origin: "EnumTests.testEnum69",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum70#1",
        source: """
      // rdar://problem/22476643
      public protocol RawValueA: RawRepresentable
      {
        var rawValue: Double { get }
      }
      """,
        origin: "EnumTests.testEnum70",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum71#1",
        source: """
      enum RawValueATest: Double, RawValueA {
        case A, B
      }
      """,
        origin: "EnumTests.testEnum71",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum72#1",
        source: """
      public protocol RawValueB
      {
        var rawValue: Double { get }
      }
      """,
        origin: "EnumTests.testEnum72",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum73#1",
        source: """
      enum RawValueBTest: Double, RawValueB {
        case A, B
      }
      """,
        origin: "EnumTests.testEnum73",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum74#1",
        source: """
      enum foo : String {
        case bar = nil
      }
      """,
        origin: "EnumTests.testEnum74",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum75#1",
        source: """
      // Static member lookup from instance methods
      """,
        origin: "EnumTests.testEnum75",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum76#1",
        source: """
      struct EmptyStruct {}
      """,
        origin: "EnumTests.testEnum76",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum77#1",
        source: """
      enum EnumWithStaticMember {
        static let staticVar = EmptyStruct()
        func foo() {
          let _ = staticVar
        }
      }
      """,
        origin: "EnumTests.testEnum77",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum78#1",
        source: """
      // SE-0036:
      """,
        origin: "EnumTests.testEnum78",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum79#1",
        source: """
      struct SE0036_Auxiliary {}
      """,
        origin: "EnumTests.testEnum79",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum80#1",
        source: """
      enum SE0036 {
        case A
        case B(SE0036_Auxiliary)
        case C(SE0036_Auxiliary)
        static func staticReference() {
          _ = A
          _ = self.A
          _ = SE0036.A
        }
        func staticReferenceInInstanceMethod() {
          _ = A
          _ = self.A
          _ = SE0036.A
        }
        static func staticReferenceInSwitchInStaticMethod() {
          switch SE0036.A {
          case A: break
          case B(_): break
          case C(let x): _ = x; break
          }
        }
        func staticReferenceInSwitchInInstanceMethod() {
          switch self {
          case A: break
          case B(_): break
          case C(let x): _ = x; break
          }
        }
        func explicitReferenceInSwitch() {
          switch SE0036.A {
          case SE0036.A: break
          case SE0036.B(_): break
          case SE0036.C(let x): _ = x; break
          }
        }
        func dotReferenceInSwitchInInstanceMethod() {
          switch self {
          case .A: break
          case .B(_): break
          case .C(let x): _ = x; break
          }
        }
        static func dotReferenceInSwitchInStaticMethod() {
          switch SE0036.A {
          case .A: break
          case .B(_): break
          case .C(let x): _ = x; break
          }
        }
        init() {
          self = .A
          self = A
          self = SE0036.A
          self = .B(SE0036_Auxiliary())
          self = B(SE0036_Auxiliary())
          self = SE0036.B(SE0036_Auxiliary())
        }
      }
      """,
        origin: "EnumTests.testEnum80",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum81#1",
        source: """
      enum SE0036_Generic<T> {
        case A(x: T)
        func foo() {
          switch self {
          case A(_): break
          }
          switch self {
          case .A(let a): print(a)
          }
          switch self {
          case SE0036_Generic.A(let a): print(a)
          }
        }
      }
      """,
        origin: "EnumTests.testEnum81",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum81b#1",
        source: """
      switch self {
        case A(_): break
      }
      """,
        origin: "EnumTests.testEnum81b",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum83#1",
        source: """
      enum SE0155 {
        case emptyArgs()
      }
      """,
        origin: "EnumTests.testEnum83",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnum84#1",
        source: """
      // https://github.com/apple/swift/issues/53662
      """,
        origin: "EnumTests.testEnum84",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnumCaseWithWildcardAsFirstName#1",
        source: #"""
      enum Foo {
        case a(_ x: Int)
      }
      """#,
        origin: "EnumTests.testEnumCaseWithWildcardAsFirstName",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEnumCaseWithWildcardAsFirstName#2",
        source: """
      enum E {
        case a
          (Int)
      }
      """,
        origin: "EnumTests.testEnumCaseWithWildcardAsFirstName",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testErrors1#1",
        source: #"""
      enum MSV : Error {
        case Foo, Bar, Baz
        case CarriesInt(Int)
        var _domain: String { return "" }
        var _code: Int { return 0 }
      }
      """#,
        origin: "ErrorsTests.testErrors1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testErrors2#1",
        source: """
      func opaque_error() -> Error { return MSV.Foo }
      """,
        origin: "ErrorsTests.testErrors2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testErrors3#1",
        source: """
      do {
        throw opaque_error()
      } catch MSV.Foo, MSV.CarriesInt(let num) {
      } catch {
      }
      """,
        origin: "ErrorsTests.testErrors3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testErrors4#1",
        source: """
      func takesAutoclosure(_ fn : @autoclosure () -> Int) {}
      func takesThrowingAutoclosure(_ fn : @autoclosure () throws -> Int) {}
      """,
        origin: "ErrorsTests.testErrors4",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testErrors5#1",
        source: """
      func genError() throws -> Int { throw MSV.Foo }
      func genNoError() -> Int { return 0 }
      """,
        origin: "ErrorsTests.testErrors5",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testErrors6#1",
        source: """
      func testAutoclosures() throws {
        takesAutoclosure(genError())
        takesAutoclosure(genNoError())
        try takesAutoclosure(genError())
        try takesAutoclosure(genNoError())
        takesAutoclosure(try genError())
        takesAutoclosure(try genNoError())
        takesThrowingAutoclosure(try genError())
        takesThrowingAutoclosure(try genNoError())
        try takesThrowingAutoclosure(genError())
        try takesThrowingAutoclosure(genNoError())
        takesThrowingAutoclosure(genError())
        takesThrowingAutoclosure(genNoError())
      }
      """,
        origin: "ErrorsTests.testErrors6",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testErrors19#1",
        source: """
      // https://github.com/apple/swift/issues/53979
      """,
        origin: "ErrorsTests.testErrors19",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testErrors28#1",
        source: """
      do {
      } catch {
        let error2 = error
      }
      """,
        origin: "ErrorsTests.testErrors28",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testErrors29#1",
        source: """
      do {
      } catch where true {
        let error2 = error
      } catch {
      }
      """,
        origin: "ErrorsTests.testErrors29",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testErrors30#1",
        source: """
      do {
        throw opaque_error()
      } catch MSV {
      } catch {
      }
      """,
        origin: "ErrorsTests.testErrors30",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testErrors31#1",
        source: """
      do {
        throw opaque_error()
      } catch is Error {
      }
      """,
        origin: "ErrorsTests.testErrors31",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testErrors32#1",
        source: """
      func foo() throws {}
        do {
      #if false
          try foo()
      #endif
        } catch {    // don't warn, #if code should be scanned.
        }
        do {
      #if false
          throw opaque_error()
      #endif
        } catch {    // don't warn, #if code should be scanned.
        }
      """,
        origin: "ErrorsTests.testErrors32",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEscapedIdentifiers1#1",
        source: """
      func `protocol`() {}
      """,
        origin: "EscapedIdentifiersTests.testEscapedIdentifiers1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEscapedIdentifiers2#1",
        source: """
      `protocol`()
      """,
        origin: "EscapedIdentifiersTests.testEscapedIdentifiers2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEscapedIdentifiers3#1",
        source: """
      class `Type` {}
      """,
        origin: "EscapedIdentifiersTests.testEscapedIdentifiers3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEscapedIdentifiers4#1",
        source: """
      var `class` = `Type`.self
      """,
        origin: "EscapedIdentifiersTests.testEscapedIdentifiers4",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEscapedIdentifiers5#1",
        source: """
      func foo() {}
      """,
        origin: "EscapedIdentifiersTests.testEscapedIdentifiers5",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEscapedIdentifiers6#1",
        source: """
      `foo`()
      """,
        origin: "EscapedIdentifiersTests.testEscapedIdentifiers6",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEscapedIdentifiers7#1",
        source: """
      // Escaping suppresses identifier contextualization.
      var get: (() -> ()) -> () = { $0() }
      """,
        origin: "EscapedIdentifiersTests.testEscapedIdentifiers7",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEscapedIdentifiers8#1",
        source: """
      var applyGet: Int {
        `get` { }
        return 0
      }
      """,
        origin: "EscapedIdentifiersTests.testEscapedIdentifiers8",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEscapedIdentifiers9#1",
        source: """
      enum `switch` {}
      """,
        origin: "EscapedIdentifiersTests.testEscapedIdentifiers9",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEscapedIdentifiers10#1",
        source: """
      typealias `Self` = Int
      """,
        origin: "EscapedIdentifiersTests.testEscapedIdentifiers10",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEscapedIdentifiers11#1",
        source: """
      func `method with space and .:/`() {}
      `method with space and .:/`()

      class `Class with space and .:/` {}
      var `var with space and .:/` = `Class with space and .:/`.self

      enum `Enum with space and .:/` {
        case `space cases`
        case `case with payload`(`some label`: `Class with space and .:/`)
      }
      let `enum value`: `Enum with space and .:/` =
        .`case with payload`(`some label`: `var with space and .:/`)

      struct `Escaped Type` {}
      func `escaped function`(`escaped label` `escaped arg`: `Escaped Type`) {}
      `escaped function`(`escaped label`: `Escaped Type`())
      let `escaped reference` = `escaped function`(`escaped label`:)
      `escaped reference`(`Escaped Type`())
      """,
        origin: "EscapedIdentifiersTests.testEscapedIdentifiers11",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEscapedIdentifiers12#1",
        source: """
      func `+ start with operator`() {}
      func `end with operator +`() {}
      func ` + `() {}
      """,
        origin: "EscapedIdentifiersTests.testEscapedIdentifiers12",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEscapedIdentifiers13#1",
        source: """
      func `// not a comment`() {}
      func `/* also not a comment */`() {}
      func `func dontDoThis() {}`() {}
      """,
        origin: "EscapedIdentifiersTests.testEscapedIdentifiers13",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEscapedIdentifiers14#1",
        source: """
      let `@atSign` = 0
      let `#octothorpe` = 0
      """,
        origin: "EscapedIdentifiersTests.testEscapedIdentifiers14",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEscapedIdentifiers15#1",
        source: """
      @propertyWrapper
      struct `@PoorlyNamedWrapper`<`The Value`> {
        var wrappedValue: `The Value`
      }
      struct WithWrappedProperty {
        @`@PoorlyNamedWrapper` var x: Int
      }
      """,
        origin: "EscapedIdentifiersTests.testEscapedIdentifiers15",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForeachAsync1#1",
        source: """
      import _Concurrency
      """,
        origin: "ForeachAsyncTests.testForeachAsync1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForeachAsync2#1",
        source: """
      struct AsyncRange<Bound: Comparable & Strideable>: AsyncSequence, AsyncIteratorProtocol where Bound.Stride : SignedInteger {
        var range: Range<Bound>.Iterator
        typealias Element = Bound
        mutating func next() async -> Element? { return range.next() }
        func cancel() { }
        func makeAsyncIterator() -> Self { return self }
      }
      """,
        origin: "ForeachAsyncTests.testForeachAsync2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForeachAsync3#1",
        source: """
      struct AsyncIntRange<Int> : AsyncSequence, AsyncIteratorProtocol {
        typealias Element = (Int, Int)
        func next() async -> (Int, Int)? {}
        func cancel() { }
        typealias AsyncIterator = AsyncIntRange<Int>
        func makeAsyncIterator() -> AsyncIntRange<Int> { return self }
      }
      """,
        origin: "ForeachAsyncTests.testForeachAsync3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForeachAsync4#1",
        source: """
      func for_each(r: AsyncRange<Int>, iir: AsyncIntRange<Int>) async {
        var sum = 0
        // Simple foreach loop, using the variable in the body
        for await i in r {
          sum = sum + i
        }
      }
      """,
        origin: "ForeachAsyncTests.testForeachAsync4",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForeachAsync5#1",
        source: """
      func for_each(r: AsyncRange<Int>, iir: AsyncIntRange<Int>) async {
        var sum = 0
        for await (i, j) in iir {
          sum = sum + i + j
        }
      }
      """,
        origin: "ForeachAsyncTests.testForeachAsync5",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForeachAsync5#2",
        source: """
      func for_each(r: AsyncRange<Int>, iir: AsyncIntRange<Int>) async {
        var sum = 0
        for await (i, j) in iir {
          sum = sum + i + j
        }
      }
      """,
        origin: "ForeachAsyncTests.testForeachAsync5",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForeachAsync5#3",
        source: """
      func for_each(r: AsyncRange<Int>, iir: AsyncIntRange<Int>) async {
        var sum = 0
        for await (i, j) : (Int, Int) in iir {
          sum = sum + i + j
        }
      }
      """,
        origin: "ForeachAsyncTests.testForeachAsync5",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForeach1#1",
        source: """
      struct IntRange<Int> : Sequence, IteratorProtocol {
        typealias Element = (Int, Int)
        func next() -> (Int, Int)? {}
        typealias Iterator = IntRange<Int>
        func makeIterator() -> IntRange<Int> { return self }
      }
      """,
        origin: "ForeachTests.testForeach1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForeach2#1",
        source: """
      func for_each(r: Range<Int>, iir: IntRange<Int>) {
        var sum = 0
        for i in r {
          sum = sum + i
        }
      }
      """,
        origin: "ForeachTests.testForeach2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForeach2#2",
        source: """
      func for_each(r: Range<Int>, iir: IntRange<Int>) {
        var sum = 0
        for (i, j) in iir {
          sum = sum + i + j
        }
      }
      """,
        origin: "ForeachTests.testForeach2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForeach2#3",
        source: """
      func for_each(r: Range<Int>, iir: IntRange<Int>) {
        var sum = 0
        for (i, j) : (Int, Int) in iir {
          sum = sum + i + j
        }
      }
      """,
        origin: "ForeachTests.testForeach2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkippingAllowed7#1",
        source: """
      func d() {
        _ = 1 / 2 + 3 * 4
        _ = 1 / 2 / 3 / 4
      }
      """,
        origin: "ForwardSlashRegexSkippingAllowedTests.testForwardSlashRegexSkippingAllowed7",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkippingAllowed8#1",
        source: #"""
      func e() {
        let arr = [1, 2, 3]
        _ = arr.reduce(0, /) / 2
        func foo(_ i: Int, _ fn: () -> Void) {}
        foo(1 / 2 / 3, { print("}}}{{{") })
      }
      """#,
        origin: "ForwardSlashRegexSkippingAllowedTests.testForwardSlashRegexSkippingAllowed8",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkippingAllowed9#1",
        source: """
      prefix operator /
      prefix func / <T> (_ x: T) -> T { x }
      """,
        origin: "ForwardSlashRegexSkippingAllowedTests.testForwardSlashRegexSkippingAllowed9",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkippingAllowed11#1",
        source: """
      func f() {
        _ = /E.e
        (/E.e).foo(/0)
        func foo<T, U>(_ x: T, _ y: U) {}
        foo(/E.e, /E.e)
        foo((/E.e), /E.e)
        foo((/)(E.e), /E.e)
        func bar<T>(_ x: T) -> Int { 0 }
        _ = bar(/E.e) / 2
      }
      """,
        origin: "ForwardSlashRegexSkippingAllowedTests.testForwardSlashRegexSkippingAllowed11",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkippingAllowed12#1",
        source: """
      postfix operator /
      prefix func / <T> (_ x: T) -> T { x }
      """,
        origin: "ForwardSlashRegexSkippingAllowedTests.testForwardSlashRegexSkippingAllowed12",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkippingAllowed13#1",
        source: """
      func g() {
          _ = 0/
          _ = 0/ / 1/
          _ = 1/ + 1/
          _ = 1 + 2/
      }
      """,
        origin: "ForwardSlashRegexSkippingAllowedTests.testForwardSlashRegexSkippingAllowed13",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkippingInvalid7#1",
        source: """
      func h() {
        _ = /x         {
        }
      }
      """,
        origin: "ForwardSlashRegexSkippingInvalidTests.testForwardSlashRegexSkippingInvalid7",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping3#1",
        source: #"""
      struct A {
        static let r = /test":"(.*?)"/
      }
      """#,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping4#1",
        source: """
      struct B {
        static let r = /x*/
      }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping4",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping5#1",
        source: """
      struct C {
        func foo() {
          let r = /x*/
        }
      }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping5",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping6#1",
        source: """
      struct D {
        func foo() {
          func bar() {
            let r = /x}}*/
          }
        }
      }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping6",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping7#1",
        source: """
      func a() { _ = /abc}}*/ }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping7",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping8#1",
        source: #"""
      func b() { _ = /\// }
      """#,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping8",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping9#1",
        source: #"""
      func c() { _ = /\\/ }
      """#,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping9",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping10#1",
        source: """
      func d() { _ = ^^/x}}*/ }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping10",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping11#1",
        source: """
      func e() { _ = (^^/x}}*/) }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping11",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping12#1",
        source: """
      func f() { _ = ^^/^x}}*/ }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping12",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping13#1",
        source: #"""
      func g() { _ = "\(/x}}*/)" }
      """#,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping13",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping14#1",
        source: #"""
      func h() { _ = "\(^^/x}}*/)" }
      """#,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping14",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping15#1",
        source: #"""
      func i() {
        func foo<T>(_ x: T, y: T) {}
        foo(/}}*/, y: /"/)
      }
      """#,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping15",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping16#1",
        source: """
      func j() {
        _ = {
          0
          /x}}}/ 
          2
        }
      }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping16",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping17#1",
        source: """
      func k() {
        _ = 2
        / 1 / .bitWidth
      }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping17",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping18#1",
        source: """
      func l() {
        _ = 2
        /x}*/ .self
      }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping18",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping20#1",
        source: """
      func m() {
        _ = 2
        / 1 /
          .bitWidth
      }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping20",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping21#1",
        source: """
      func n() {
        _ = 2
        /x}/
          .bitWidth
      }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping21",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping23#1",
        source: """
      func o() {
        _ = /x// comment
      }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping23",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping24#1",
        source: """
      func p() {
        _ = /x // comment
      }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping24",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping25#1",
        source: """
      func q() {
        _ = /x/*comment*/
      }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping25",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping26#1",
        source: """
      func r() { _ = /[(0)]/ }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping26",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping27#1",
        source: """
      func s() { _ = /(x)/ }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping27",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping28#1",
        source: """
      func t() { _ = /[)]/ }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping28",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping29#1",
        source: #"""
      func u() { _ = /[a\])]/ }
      """#,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping29",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping30#1",
        source: """
      func v() { _ = /([)])/ }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping30",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping31#1",
        source: """
      func w() { _ = /]]][)]/ }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping31",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping32#1",
        source: """
      func x() { _ = /,/ }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping32",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping33#1",
        source: """
      func y() { _ = /}/ }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping33",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping34#1",
        source: """
      func z() { _ = /]/ }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping34",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping35#1",
        source: """
      func a1() { _ = /:/ }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping35",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping36#1",
        source: """
      func a2() { _ = /;/ }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping36",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping37#1",
        source: """
      func a3() { _ = /)/ }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping37",
        syntaxVersion: "604.0.0-prerelease-2026-06-05",
        compilerRejects: "expected expression after unary operator"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping39#1",
        source: #"""
      func a5() { _ = /\ / }
      """#,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping39",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping42#1",
        source: #"""
      func a7() { _ = /\/}/ }
      """#,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping42",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping43#1",
        source: """
      func err1() { _ = /0xG/ }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping43",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping44#1",
        source: """
      func err2() { _ = /0oG/ }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping44",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping45#1",
        source: #"""
      func err3() { _ = /"/ }
      """#,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping45",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping46#1",
        source: """
      func err4() { _ = /'/ }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping46",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping47#1",
        source: """
      func err5() { _ = /<#placeholder#>/ }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping47",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping48#1",
        source: """
      func err6() { _ = ^^/0xG/ }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping48",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping49#1",
        source: """
      func err7() { _ = ^^/0oG/ }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping49",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping50#1",
        source: #"""
      func err8() { _ = ^^/"/ }
      """#,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping50",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping51#1",
        source: """
      func err9() { _ = ^^/'/ }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping51",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping52#1",
        source: """
      func err10() { _ = ^^/<#placeholder#>/ }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping52",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping53#1",
        source: """
      func err11() { _ = (^^/0xG/) }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping53",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping54#1",
        source: """
      func err12() { _ = (^^/0oG/) }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping54",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping55#1",
        source: #"""
      func err13() { _ = (^^/"/) }
      """#,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping55",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping56#1",
        source: """
      func err14() { _ = (^^/'/) }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping56",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegexSkipping57#1",
        source: """
      func err15() { _ = (^^/<#placeholder#>/) }
      """,
        origin: "ForwardSlashRegexSkippingTests.testForwardSlashRegexSkipping57",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex1#1",
        source: """
      prefix operator /
      prefix operator ^/
      prefix operator /^/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex2#1",
        source: """
      prefix func ^/ <T> (_ x: T) -> T { x }
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex8#1",
        source: """
      infix operator /^/ : P
      func /^/ (lhs: Int, rhs: Int) -> Int { 1 / 2 }
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex8",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex9#1",
        source: """
      infix operator /^ : P
      func /^ (lhs: Int, rhs: Int) -> Int { 1 / 2 }
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex9",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex10#1",
        source: """
      infix operator ^^/ : P
      func ^^/ (lhs: Int, rhs: Int) -> Int { 1 / 2 }
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex10",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex11#1",
        source: """
      let i = 0 /^/ 1/^/3
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex11",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex12#1",
        source: """
      let x = /abc/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex12",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex13#1",
        source: """
      _ = /abc/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex13",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex14#1",
        source: """
      _ = /x/.self
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex14",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex15#1",
        source: #"""
      _ = /\//
      """#,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex15",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex16#1",
        source: #"""
      _ = /\\/
      """#,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex16",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex19#1",
        source: """
      do {
        _=/0/
      }
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex19",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex21#1",
        source: """
      _ = /x
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex21",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex22#1",
        source: """
      _ = !/x/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex22",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex23#1",
        source: """
      _ = (!/x/)
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex23",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex26#1",
        source: """
      _ = !!/x/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex26",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex27#1",
        source: """
      _ = (!!/x/)
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex27",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex29#1",
        source: """
      _ = /x/!
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex29",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex30#1",
        source: """
      _ = /x/ + /y/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex30",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex31#1",
        source: """
      _ = /x/+/y/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex31",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex32#1",
        source: """
      _ = /x/?.blah
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex32",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex33#1",
        source: """
      _ = /x/!.blah
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex33",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex34#1",
        source: """
      do {
        _ = /x /?
          .blah
      }
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex34",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex35#1",
        source: """
      _ = /x/? 
        .blah
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex35",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex36#1",
        source: """
      _ = 0; /x/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex36",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex39#1",
        source: """
      _ = .random() ? /x/ : .blah
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex39",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex41#1",
        source: """
      _ = /x/??/x/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex41",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex42#1",
        source: """
      _ = /x/ ... /y/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex42",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex43#1",
        source: """
      _ = /x/.../y/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex43",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex44#1",
        source: """
      _ = /x/...
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex44",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex47#1",
        source: #"""
      _ = "\(/x/)"
      """#,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex47",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex48#1",
        source: """
      func defaulted(x: Regex<Substring> = /x/) {}
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex48",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex50#1",
        source: """
      foo(/abc/, y: /abc/)
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex50",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex53#1",
        source: """
      bar(&/x/)
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex53",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex57#1",
        source: """
      func testThrow() throws {
        throw /x/ 
      }
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex57",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex60#1",
        source: """
      _ = [/abc/:/abc/]
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex60",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex61#1",
        source: """
      _ = [/abc/ : /abc/]
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex61",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex62#1",
        source: """
      _ = [/abc/ :/abc/]
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex62",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex63#1",
        source: """
      _ = [/abc/: /abc/]
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex63",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex64#1",
        source: """
      _ = (/abc/, /abc/)
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex64",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex65#1",
        source: """
      _ = ((/abc/))
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex65",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex67#1",
        source: """
      _ = { /abc/ }
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex67",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex68#1",
        source: """
      _ = {
        /abc/
      }
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex68",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex69#1",
        source: """
      let _: () -> Int = {
        0
        / 1 /
        2
      }
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex69",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex70#1",
        source: """
      let _: () -> Int = {
        0
        /1 / 
        2
      }
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex70",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex71#1",
        source: """
      _ = {
        0 
        /1/ 
        2 
      }
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex71",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex73#1",
        source: """
      _ = 2
      / 1 / .bitWidth
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex73",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex74#1",
        source: """
      _ = 2
      /1/ .bitWidth
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex74",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex75#1",
        source: """
      _ = 2
      / 1 /
        .bitWidth
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex75",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex76#1",
        source: """
      _ = 2
      /1 /
        .bitWidth
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex76",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex77#1",
        source: """
      _ = !!/1/ .bitWidth
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex77",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex78#1",
        source: """
      _ = !!/1 / .bitWidth
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex78",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex79#1",
        source: """
      let z =
      /y/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex79",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex83#1",
        source: #"""
      switch "" {
      case _ where /x/:
        break
      default:
        break
      }
      """#,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex83",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex84#1",
        source: """
      do {} catch /x/ {}
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex84",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex86#1",
        source: """
      switch /x/ {
      default:
        break
      }
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex86",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex87#1",
        source: """
      if /x/ {}
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex87",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex88#1",
        source: """
      if /x/.smth {}
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex88",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex89#1",
        source: """
      func testGuard() {
        guard /x/ else { return } 
      }
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex89",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex90#1",
        source: """
      for x in [0] where /x/ {}
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex90",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex92#1",
        source: """
      _ = /x/ as Magic
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex92",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex93#1",
        source: """
      _ = /x/ as! String
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex93",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex94#1",
        source: """
      _ = type(of: /x/)
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex94",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex99#1",
        source: """
      _ = await /x/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex99",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex100#1",
        source: """
      /x/ = 0 
      /x/()
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex100",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex102#1",
        source: """
      _ = /x// comment
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex102",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex103#1",
        source: """
      _ = /x // comment
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex103",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex104#1",
        source: """
      _ = /x/*comment*/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex104",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex108#1",
        source: """
      baz(/, /)
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex108",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex108#2",
        source: """
      baz(/,/)
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex108",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex109#1",
        source: """
      baz((/), /)
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex109",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex110#1",
        source: """
      baz(/^, /)
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex110",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex110#2",
        source: """
      baz(/^,/)
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex110",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex111#1",
        source: """
      baz((/^), /)
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex111",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex112#1",
        source: """
      baz(^^/, /)
      baz(^^/,/) 
      baz((^^/), /)
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex112",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex114#1",
        source: """
      bazbaz(/, 0)
      bazbaz(^^/, 0)
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex114",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex117#1",
        source: #"""
      _ = qux((/), "(") / 2
      """#,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex117",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex118#1",
        source: """
      _ = qux(/, 1) // this comment tests to make sure we don't try and end the regex on the starting '/' of '//'.
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex118",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex119#1",
        source: """
      _ = qux(/, 1) /* same thing with a block comment */
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex119",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex122#1",
        source: """
      quxqux(/^/) 
      quxqux((/^/)) 
      quxqux({ $0 /^/ $1 })
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex122",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex123#1",
        source: """
      quxqux(!/^/)
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex123",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex124#1",
        source: """
      quxqux(/^)
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex124",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex125#1",
        source: """
      _ = quxqux(/^) / 1
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex125",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex127#1",
        source: """
      _ = arr.reduce(1, /) / 3
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex127",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex128#1",
        source: """
      _ = arr.reduce(1, /) + arr.reduce(1, /)
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex128",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex130#1",
        source: """
      _ = (/x)
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex130",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex131#1",
        source: """
      _ = (/x)/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex131",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex132#1",
        source: """
      _ = (/[(0)])/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex132",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex133#1",
        source: """
      _ = /[(0)]/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex133",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex134#1",
        source: """
      _ = /(x)/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex134",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex135#1",
        source: """
      _ = /[)]/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex135",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex136#1",
        source: #"""
      _ = /[a\])]/
      """#,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex136",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex137#1",
        source: """
      _ = /([)])/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex137",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex138#1",
        source: """
      _ = /]]][)]/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex138",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex141#1",
        source: """
      let fn: (Int, Int) -> Int = (/)
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex141",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex147#1",
        source: """
      _ = ^/x/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex147",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex148#1",
        source: """
      _ = (^/x)/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex148",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex149#1",
        source: """
      _ = (!!/x/)
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex149",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex152#1",
        source: #"""
      _ = (^/)("/")
      """#,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex152",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex155#1",
        source: """
      _ = /./
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex155",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex157#1",
        source: #"""
      _ = /\ /
      """#,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex157",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex160#1",
        source: """
      _ = #/  /#
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex160",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex161#1",
        source: #"""
      _ = /x\ /
      """#,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex161",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex162#1",
        source: #"""
      _ = /\ \ /
      """#,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex162",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex163#1",
        source: """

      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex163",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex167#1",
        source: #"""
      _ = /\)/
      """#,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex167",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex168#1",
        source: """
      _ = /)/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex168",
        syntaxVersion: "604.0.0-prerelease-2026-06-05",
        compilerRejects: "expected expression after unary operator"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex169#1",
        source: """
      _ = /,/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex169",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex170#1",
        source: """
      _ = /}/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex170",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex171#1",
        source: """
      _ = /]/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex171",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex172#1",
        source: """
      _ = /:/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex172",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex173#1",
        source: """
      _ = /;/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex173",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex175#1",
        source: """
      _ = /0xG/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex175",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex176#1",
        source: """
      _ = /0oG/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex176",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex177#1",
        source: #"""
      _ = /"/
      """#,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex177",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex178#1",
        source: """
      _ = /'/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex178",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex179#1",
        source: """
      _ = /<#placeholder#>/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex179",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex180#1",
        source: """
      _ = ^^/0xG/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex180",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex181#1",
        source: """
      _ = ^^/0oG/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex181",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex182#1",
        source: #"""
      _ = ^^/"/
      """#,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex182",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex183#1",
        source: """
      _ = ^^/'/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex183",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex184#1",
        source: """
      _ = ^^/<#placeholder#>/
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex184",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex185#1",
        source: """
      _ = (^^/0xG/)
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex185",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex186#1",
        source: """
      _ = (^^/0oG/)
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex186",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex187#1",
        source: #"""
      _ = (^^/"/)
      """#,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex187",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex188#1",
        source: """
      _ = (^^/'/)
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex188",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testForwardSlashRegex189#1",
        source: """
      _ = (^^/<#placeholder#>/)
      """,
        origin: "ForwardSlashRegexTests.testForwardSlashRegex189",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testGenericDisambiguation1#1",
        source: """
      struct A<B> {
        init(x:Int) {}
        static func c() {}
        struct C<D> {
          static func e() {}
        }
        struct F {}
      }
      struct B {}
      struct D {}
      """,
        origin: "GenericDisambiguationTests.testGenericDisambiguation1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testGenericDisambiguation2#1",
        source: """
      protocol Runcible {}
      protocol Fungible {}
      """,
        origin: "GenericDisambiguationTests.testGenericDisambiguation2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testGenericDisambiguation3#1",
        source: """
      func meta<T>(_ m: T.Type) {}
      func meta2<T>(_ m: T.Type, _ x: Int) {}
      """,
        origin: "GenericDisambiguationTests.testGenericDisambiguation3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testGenericDisambiguation4#1",
        source: """
      func generic<T>(_ x: T) {}
      """,
        origin: "GenericDisambiguationTests.testGenericDisambiguation4",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testGenericDisambiguation5#1",
        source: """
      var a, b, c, d : Int
      """,
        origin: "GenericDisambiguationTests.testGenericDisambiguation5",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testGenericDisambiguation6a#1",
        source: """
      _ = a < b
      """,
        origin: "GenericDisambiguationTests.testGenericDisambiguation6a",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testGenericDisambiguation6b#1",
        source: """
      _ = (a < b, c > d)
      """,
        origin: "GenericDisambiguationTests.testGenericDisambiguation6b",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testGenericDisambiguation6c#1",
        source: """
      (a < b, c > (d))
      """,
        origin: "GenericDisambiguationTests.testGenericDisambiguation6c",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testGenericDisambiguation6d#1",
        source: """
      (a<b, c>(d))
      """,
        origin: "GenericDisambiguationTests.testGenericDisambiguation6d",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testGenericDisambiguation6e#1",
        source: """
      _ = a>(b)
      """,
        origin: "GenericDisambiguationTests.testGenericDisambiguation6e",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testGenericDisambiguation6f#1",
        source: """
      _ = a > (b)
      """,
        origin: "GenericDisambiguationTests.testGenericDisambiguation6f",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testGenericDisambiguation7#1",
        source: """
      generic<Int>(0)
      """,
        origin: "GenericDisambiguationTests.testGenericDisambiguation7",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testGenericDisambiguation8#1",
        source: """
      A<B>.c()
      A<A<B>>.c()
      A<A<B>.F>.c()
      A<(A<B>) -> B>.c()
      A<[[Int]]>.c()
      A<[[A<B>]]>.c()
      A<(Int, UnicodeScalar)>.c()
      A<(a:Int, b:UnicodeScalar)>.c()
      A<Runcible & Fungible>.c()
      A<@convention(c) () -> Int32>.c()
      A<(@autoclosure @escaping () -> Int, Int) -> Void>.c()
      _ = [@convention(block) ()  -> Int]().count
      _ = [String: (@escaping (A<B>) -> Int) -> Void]().keys
      """,
        origin: "GenericDisambiguationTests.testGenericDisambiguation8",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testGenericDisambiguation9#1",
        source: """
      A<B>(x: 0)
      """,
        origin: "GenericDisambiguationTests.testGenericDisambiguation9",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testGenericDisambiguation10#1",
        source: """
      meta(A<B>.self)
      """,
        origin: "GenericDisambiguationTests.testGenericDisambiguation10",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testGenericDisambiguation11#1",
        source: """
      meta2(A<B>.self, 0)
      """,
        origin: "GenericDisambiguationTests.testGenericDisambiguation11",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testGenericDisambiguation12#1",
        source: """
      A<B>.C<D>.e()
      """,
        origin: "GenericDisambiguationTests.testGenericDisambiguation12",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testGenericDisambiguation13#1",
        source: """
      A<B>.C<D>(0)
      """,
        origin: "GenericDisambiguationTests.testGenericDisambiguation13",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testGenericDisambiguation14#1",
        source: """
      meta(A<B>.C<D>.self)
      meta2(A<B>.C<D>.self, 0)
      """,
        origin: "GenericDisambiguationTests.testGenericDisambiguation14",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testGenericDisambiguation15#1",
        source: """
      A<>.c()
      """,
        origin: "GenericDisambiguationTests.testGenericDisambiguation15",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testGenericDisambiguation16#1",
        source: """
      A<B, D>.c()
      """,
        origin: "GenericDisambiguationTests.testGenericDisambiguation16",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testGenericDisambiguation17#1",
        source: """
      A<B?>(x: 0) // parses as type
      _ = a < b ? c : d
      """,
        origin: "GenericDisambiguationTests.testGenericDisambiguation17",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testGenericDisambiguation18#1",
        source: """
      A<(B) throws -> D>(x: 0)
      """,
        origin: "GenericDisambiguationTests.testGenericDisambiguation18",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testGuardTopLevel1#1",
        source: """
      let a: Int? = 1
      guard let b = a else {
      }
      """,
        origin: "GuardTopLevelTests.testGuardTopLevel1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testGuardTopLevel2#1",
        source: """
      func foo() {} // to interrupt the TopLevelCodeDecl
      """,
        origin: "GuardTopLevelTests.testGuardTopLevel2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testGuardTopLevel3#1",
        source: """
      let c = b
      """,
        origin: "GuardTopLevelTests.testGuardTopLevel3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testHashbangLibrary1#1",
        source: """
      #!/usr/bin/swift
      class Foo {}
      """,
        origin: "HashbangLibraryTests.testHashbangLibrary1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testHashbangMain1#1",
        source: """
      #!/usr/bin/swift
      let x = 42
      x + x
      // Check that we skip the hashbang at the beginning of the file.
      """,
        origin: "HashbangMainTests.testHashbangMain1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIdentifiers1#1",
        source: """
      func my_print<T>(_ t: T) {}
      """,
        origin: "IdentifiersTests.testIdentifiers1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIdentifiers2#1",
        source: #"""
      class 你好 {
        class שלום {
          class வணக்கம் {
            class Γειά {
              class func привет() {
                my_print("hello")
              }
            }
          }
        }
      }
      """#,
        origin: "IdentifiersTests.testIdentifiers2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIdentifiers3#1",
        source: """
      你好.שלום.வணக்கம்.Γειά.привет()
      """,
        origin: "IdentifiersTests.testIdentifiers3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIdentifiers4#1",
        source: """
      // Identifiers cannot start with combining chars.
      _ = .́duh()
      """,
        origin: "IdentifiersTests.testIdentifiers4",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIdentifiers5#1",
        source: """
      // Combining characters can be used within identifiers.
      func s̈pin̈al_tap̈() {}
      """,
        origin: "IdentifiersTests.testIdentifiers5",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testStructNamedLowercaseAny#1",
        source: """
      struct any {}
      """,
        origin: "IdentifiersTests.testStructNamedLowercaseAny",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIdentifiers9#1",
        source: """
      // SIL keywords are tokenized as normal identifiers in non-SIL mode.
      _ = undef
      _ = sil
      _ = sil_stage
      _ = sil_vtable
      _ = sil_global
      _ = sil_witness_table
      _ = sil_default_witness_table
      _ = sil_coverage_map
      _ = sil_scope
      """,
        origin: "IdentifiersTests.testIdentifiers9",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIdentifiers10#1",
        source: """
      // https://github.com/apple/swift/issues/57542
      // Make sure we do not parse the '_' on the newline as being part of the 'variable' identifier on the line before.
      """,
        origin: "IdentifiersTests.testIdentifiers10",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIdentifiers11#1",
        source: """
      @propertyWrapper
      struct Wrapper {
        var wrappedValue = 0
      }
      """,
        origin: "IdentifiersTests.testIdentifiers11",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIdentifiers12#1",
        source: """
      func localScope() {
        @Wrapper var variable
        _ = 0
      }
      """,
        origin: "IdentifiersTests.testIdentifiers12",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr1#1",
        source: """
      postfix operator ++
      postfix func ++ (_: Int) -> Int { 0 }
      """,
        origin: "IfconfigExprTests.testIfconfigExpr1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr2#1",
        source: """
      struct OneResult {}
      struct TwoResult {}
      """,
        origin: "IfconfigExprTests.testIfconfigExpr2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr3#1",
        source: """
      protocol MyProto {
          func optionalMethod() -> [Int]?
      }
      struct MyStruct {
          var optionalMember: MyProto? { nil }
          func methodOne() -> OneResult { OneResult() }
          func methodTwo() -> TwoResult { TwoResult() }
      }
      """,
        origin: "IfconfigExprTests.testIfconfigExpr3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr4#1",
        source: """
      func globalFunc<T>(_ arg: T) -> T { arg }
      """,
        origin: "IfconfigExprTests.testIfconfigExpr4",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr5#1",
        source: """
      func testBasic(baseExpr: MyStruct) {
          baseExpr
      #if CONDITION_1
            .methodOne()
      #else
            .methodTwo()
      #endif
      }
      """,
        origin: "IfconfigExprTests.testIfconfigExpr5",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr6#1",
        source: """
      MyStruct()
      #if CONDITION_1
        .methodOne()
      #else
        .methodTwo()
      #endif
      """,
        origin: "IfconfigExprTests.testIfconfigExpr6",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr10#1",
        source: """
      func consecutiveIfConfig(baseExpr: MyStruct) {
          baseExpr
      #if CONDITION_1
        .methodOne()
      #endif
      #if CONDITION_2
        .methodTwo()
      #endif
        .unknownMethod()
      }
      """,
        origin: "IfconfigExprTests.testIfconfigExpr10",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr11#1",
        source: """
      func nestedIfConfig(baseExpr: MyStruct) {
        baseExpr
      #if CONDITION_1
        #if CONDITION_2
          .methodOne()
        #endif
        #if CONDITION_1
          .methodTwo()
        #endif
      #else
        .unknownMethod1()
        #if CONDITION_2
          .unknownMethod2()
        #endif
      #endif
      }
      """,
        origin: "IfconfigExprTests.testIfconfigExpr11",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr12#1",
        source: """
      func ifconfigExprInExpr(baseExpr: MyStruct) {
        globalFunc(
          baseExpr
      #if CONDITION_1
            .methodOne()
      #else
            .methodTwo()
      #endif
        )
      }
      """,
        origin: "IfconfigExprTests.testIfconfigExpr12",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr13#1",
        source: """
      #if canImport(A, _version: 2)
        let a = 1
      #endif
      """,
        origin: "IfconfigExprTests.testIfconfigExpr13",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr14#1",
        source: """
      #if canImport(A, _version: 2.2)
        let a = 1
      #endif
      """,
        origin: "IfconfigExprTests.testIfconfigExpr14",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr15#1",
        source: """
      #if canImport(A, _version: 2.2.2)
        let a = 1
      #endif
      """,
        origin: "IfconfigExprTests.testIfconfigExpr15",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr16#1",
        source: """
      #if canImport(A, _version: 2.2.2.2)
        let a = 1
      #endif
      """,
        origin: "IfconfigExprTests.testIfconfigExpr16",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr17#1",
        source: """
      #if canImport(A, _version: 2.2.2.2.2)
        let a = 1
      #endif
      """,
        origin: "IfconfigExprTests.testIfconfigExpr17",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr18#1",
        source: """
      #if canImport(A, _underlyingVersion: 4)
        let a = 1
      #endif
      """,
        origin: "IfconfigExprTests.testIfconfigExpr18",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr19#1",
        source: """
      #if canImport(A, _underlyingVersion: 2.200)
        let a = 1
      #endif
      """,
        origin: "IfconfigExprTests.testIfconfigExpr19",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr20#1",
        source: """
      #if canImport(A, _underlyingVersion: 2.200.1)
        let a = 1
      #endif
      """,
        origin: "IfconfigExprTests.testIfconfigExpr20",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr21#1",
        source: """
      #if canImport(A, _underlyingVersion: 2.200.1.3)
        let a = 1
      #endif
      """,
        origin: "IfconfigExprTests.testIfconfigExpr21",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr22#1",
        source: """
      #if canImport(A, unknown: 2.2)
        let a = 1
      #endif
      """,
        origin: "IfconfigExprTests.testIfconfigExpr22",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr23#1",
        source: """
      #if canImport(A,)
        let a = 1
      #endif
      """,
        origin: "IfconfigExprTests.testIfconfigExpr23",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr24#1",
        source: """
      #if canImport(A, 2.2)
        let a = 1
      #endif
      """,
        origin: "IfconfigExprTests.testIfconfigExpr24",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr25#1",
        source: """
      #if canImport(A, 2.2, 1.1)
        let a = 1
      #endif
      """,
        origin: "IfconfigExprTests.testIfconfigExpr25",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr27#1",
        source: #"""
      #if canImport(A, _version: "")
        let a = 1
      #endif
      """#,
        origin: "IfconfigExprTests.testIfconfigExpr27",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr28#1",
        source: """
      #if canImport(A, _version: >=2.2)
        let a = 1
      #endif
      """,
        origin: "IfconfigExprTests.testIfconfigExpr28",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIfconfigExpr30#1",
        source: #"""
      #if canImport(A, _version: "20A301")
        let a = 1
      #endif
      """#,
        origin: "IfconfigExprTests.testIfconfigExpr30",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIfConfigExpr33#1",
        source: """
      #if arch(x86_64)
      #line
      #endif
      """,
        origin: "IfconfigExprTests.testIfConfigExpr33",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testCanImportFuncCall#1",
        source: """
      canImport(a, b, c)
      """,
        origin: "IfconfigExprTests.testCanImportFuncCall",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testArchFuncCall#1",
        source: """
      arch()
      """,
        origin: "IfconfigExprTests.testArchFuncCall",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOsFuncCall#1",
        source: """
      os(bogus)
      """,
        origin: "IfconfigExprTests.testOsFuncCall",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTargetEnvironmentFuncCall#1",
        source: """
      targetEnvironment(foo, bar)
      """,
        origin: "IfconfigExprTests.testTargetEnvironmentFuncCall",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testCompilerFuncCall#1",
        source: """
      compiler(a)
      """,
        origin: "IfconfigExprTests.testCompilerFuncCall",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwiftFuncCall#1",
        source: """
      swift(foo)
      """,
        origin: "IfconfigExprTests.testSwiftFuncCall",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testUnknownPlatform1#1",
        source: """
      #if hasGreeble(blah)
      #endif
      """,
        origin: "IfconfigExprTests.testUnknownPlatform1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testUnknownPlatform2#1",
        source: """
      // Future compiler, short-circuit right-hand side
      #if compiler(>=10.0) && hasGreeble(blah)
      #endif
      """,
        origin: "IfconfigExprTests.testUnknownPlatform2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testUnknownPlatform3#1",
        source: """
      // Current compiler, short-circuit right-hand side
      #if compiler(<10.0) || hasGreeble(blah)
      #endif
      """,
        origin: "IfconfigExprTests.testUnknownPlatform3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testUnknownPlatform4#1",
        source: """
      // This compiler, don't short-circuit.
      #if compiler(>=5.7) && hasGreeble(blah)
      #endif
      """,
        origin: "IfconfigExprTests.testUnknownPlatform4",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testUnknownPlatform5#1",
        source: """
      // This compiler, don't short-circuit.
      #if compiler(<5.8) || hasGreeble(blah)
      #endif
      """,
        origin: "IfconfigExprTests.testUnknownPlatform5",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testUnknownPlatform6#1",
        source: #"""
      // Not a "version" check, so don't short-circuit.
      #if os(macOS) && hasGreeble(blah)
      #endif
      """#,
        origin: "IfconfigExprTests.testUnknownPlatform6",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testUpcomingFeature1#1",
        source: """
      #if hasFeature(17)
      #endif
      """,
        origin: "IfconfigExprTests.testUpcomingFeature1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testCanImportWithStringVersion#1",
        source: """
      #if canImport(MyModule, _version: "1.2.3")
      #endif
      """,
        origin: "IfconfigExprTests.testCanImportWithStringVersion",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testImplicitGetterIncomplete1#1",
        source: """
      func test1() {
        var a : Int {
      #if arch(x86_64)
          return 0
      #else
          return 1
      #endif
        }
      }
      """,
        origin: "ImplicitGetterIncompleteTests.testImplicitGetterIncomplete1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInitDeinit2#1",
        source: """
      struct FooStructConstructorB {
        init()
      }
      """,
        origin: "InitDeinitTests.testInitDeinit2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInitDeinit4#1",
        source: """
      struct FooStructConstructorD {
        init() -> FooStructConstructorD { }
      }
      """,
        origin: "InitDeinitTests.testInitDeinit4",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInitDeinit5a#1",
        source: """
      struct FooStructDeinitializerA {
        deinit
      }
      """,
        origin: "InitDeinitTests.testInitDeinit5a",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInitDeinit6#1",
        source: """
      struct FooStructDeinitializerB {
        deinit
      }
      """,
        origin: "InitDeinitTests.testInitDeinit6",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInitDeinit7#1",
        source: """
      struct FooStructDeinitializerC {
        deinit {}
      }
      """,
        origin: "InitDeinitTests.testInitDeinit7",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInitDeinit9#1",
        source: """
      class FooClassDeinitializerB {
        deinit { }
      }
      """,
        origin: "InitDeinitTests.testInitDeinit9",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInitDeinit12#1",
        source: """
      deinit {}
      deinit
      deinit {}
      """,
        origin: "InitDeinitTests.testInitDeinit12",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInitDeinit13#1",
        source: """
      struct BarStruct {
        init() {}
        deinit {}
      }
      """,
        origin: "InitDeinitTests.testInitDeinit13",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInitDeinit14#1",
        source: """
      extension BarStruct {
        init(x : Int) {}
        // When/if we allow 'var' in extensions, then we should also allow dtors
        deinit {}
      }
      """,
        origin: "InitDeinitTests.testInitDeinit14",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInitDeinit15#1",
        source: """
      enum BarUnion {
        init() {}
        deinit {}
      }
      """,
        origin: "InitDeinitTests.testInitDeinit15",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInitDeinit16#1",
        source: """
      extension BarUnion {
        init(x : Int) {}
        deinit {}
      }
      """,
        origin: "InitDeinitTests.testInitDeinit16",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInitDeinit17#1",
        source: """
      class BarClass {
        init() {}
        deinit {}
      }
      """,
        origin: "InitDeinitTests.testInitDeinit17",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInitDeinit18#1",
        source: """
      extension BarClass {
        convenience init(x : Int) { self.init() }
        deinit {}
      }
      """,
        origin: "InitDeinitTests.testInitDeinit18",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInitDeinit19#1",
        source: """
      protocol BarProtocol {
        init() {}
        deinit {}
      }
      """,
        origin: "InitDeinitTests.testInitDeinit19",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInitDeinit20#1",
        source: """
      extension BarProtocol {
        init(x : Int) {}
        deinit {}
      }
      """,
        origin: "InitDeinitTests.testInitDeinit20",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInitDeinit21#1",
        source: """
      func fooFunc() {
        init() {}
        deinit {}
      }
      """,
        origin: "InitDeinitTests.testInitDeinit21",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInitDeinit22#1",
        source: """
      func barFunc() {
        var x : () = { () -> () in
          init() {}
          return
        } ()
        var y : () = { () -> () in
          deinit {}
          return
        } ()
      }
      """,
        origin: "InitDeinitTests.testInitDeinit22",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInitDeinit24#1",
        source: """
      class Aaron {
        convenience init() { init(x: 1) }
      }
      """,
        origin: "InitDeinitTests.testInitDeinit24",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInitDeinit25#1",
        source: """
      class Theodosia: Aaron {
        init() {
          init(x: 2)
        }
      }
      """,
        origin: "InitDeinitTests.testInitDeinit25",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInitDeinit26#1",
        source: """
      struct AaronStruct {
        init(x: Int) {}
        init() { init(x: 1) }
      }
      """,
        origin: "InitDeinitTests.testInitDeinit26",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInitDeinit27#1",
        source: """
      enum AaronEnum: Int {
        case A = 1
        init(x: Int) { init(rawValue: x)! }
      }
      """,
        origin: "InitDeinitTests.testInitDeinit27",
        syntaxVersion: "604.0.0-prerelease-2026-06-05",
        disabledReason: "parser produces no root yield for initializer body containing implicit init(rawValue:)!"
    ),
    SwiftSnippet(
        label: "testInitDeinit28#1",
        source: """
      init(_ foo: T) -> Int where T: Comparable {}
      """,
        origin: "InitDeinitTests.testInitDeinit28",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDeinitInSwiftinterfaceIsFollowedByFinalFunc#1",
        source: """
      class Foo {
        deinit
        final func foo()
      }
      """,
        origin: "InitDeinitTests.testDeinitInSwiftinterfaceIsFollowedByFinalFunc",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testDeinitAsync#1",
        source: """
      class FooClassDeinitializerA {
        deinit async {}
      }
      """,
        origin: "InitDeinitTests.testDeinitAsync",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAsyncDeinit#1",
        source: """
      class FooClassDeinitializerA {
        async deinit {}
      }
      """,
        origin: "InitDeinitTests.testAsyncDeinit",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInvalidStringInterpolationProtocol1#1",
        source: """
      // Has a lot of invalid 'appendInterpolation' methods
      public struct BadStringInterpolation: StringInterpolationProtocol {
        //  {{educational-notes=string-interpolation-conformance}}
        public init(literalCapacity: Int, interpolationCount: Int) {}
        public mutating func appendLiteral(_: String) {}
        public static func appendInterpolation(static: ()) {
          //  {{educational-notes=string-interpolation-conformance}}
        }
        private func appendInterpolation(private: ()) {
        }
        func appendInterpolation(default: ()) {
        }
        public func appendInterpolation(intResult: ()) -> Int {
          //  {{educational-notes=string-interpolation-conformance}}
        }
      }
      """,
        origin: "InvalidStringInterpolationProtocolTests.testInvalidStringInterpolationProtocol1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInvalidStringInterpolationProtocol2#1",
        source: """
      // Has no 'appendInterpolation' methods at all
      public struct IncompleteStringInterpolation: StringInterpolationProtocol {
        public init(literalCapacity: Int, interpolationCount: Int) {}
        public mutating func appendLiteral(_: String) {}
      }
      """,
        origin: "InvalidStringInterpolationProtocolTests.testInvalidStringInterpolationProtocol2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInvalidStringInterpolationProtocol3#1",
        source: """
      // Has only good 'appendInterpolation' methods.
      public struct GoodStringInterpolation: StringInterpolationProtocol {
        public init(literalCapacity: Int, interpolationCount: Int) {}
        public mutating func appendLiteral(_: String) {}
        public func appendInterpolation(noResult: ()) {}
        public func appendInterpolation(voidResult: ()) -> Void {}
        @discardableResult
        public func appendInterpolation(discardableResult: ()) -> Int {}
      }
      """,
        origin: "InvalidStringInterpolationProtocolTests.testInvalidStringInterpolationProtocol3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInvalidStringInterpolationProtocol4#1",
        source: """
      // Has only good 'appendInterpolation' methods, but they're in an extension.
      public struct GoodSplitStringInterpolation: StringInterpolationProtocol {
        public init(literalCapacity: Int, interpolationCount: Int) {}
        public mutating func appendLiteral(_: String) {}
      }
      """,
        origin: "InvalidStringInterpolationProtocolTests.testInvalidStringInterpolationProtocol4",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInvalidStringInterpolationProtocol5#1",
        source: """
      extension GoodSplitStringInterpolation {
        public func appendInterpolation(noResult: ()) {}
        public func appendInterpolation(voidResult: ()) -> Void {}
        @discardableResult
        public func appendInterpolation(discardableResult: ()) -> Int {}
      }
      """,
        origin: "InvalidStringInterpolationProtocolTests.testInvalidStringInterpolationProtocol5",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInvalidStringInterpolationProtocol6#1",
        source: """
      // Has only good 'appendInterpolation' methods, and is not public.
      struct GoodNonPublicStringInterpolation: StringInterpolationProtocol {
        init(literalCapacity: Int, interpolationCount: Int) {}
        mutating func appendLiteral(_: String) {}
        func appendInterpolation(noResult: ()) {}
        public func appendInterpolation(voidResult: ()) -> Void {}
        @discardableResult
        func appendInterpolation(discardableResult: ()) -> Int {}
      }
      """,
        origin: "InvalidStringInterpolationProtocolTests.testInvalidStringInterpolationProtocol6",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInvalidStringInterpolationProtocol7#1",
        source: """
      // Has a mixture of good and bad 'appendInterpolation' methods.
      // We don't emit any errors in this case--we assume the others
      // are implementation details or something.
      public struct GoodStringInterpolationWithBadOnesToo: StringInterpolationProtocol {
        public init(literalCapacity: Int, interpolationCount: Int) {}
        public mutating func appendLiteral(_: String) {}
        public func appendInterpolation(noResult: ()) {}
        public static func appendInterpolation(static: ()) {}
        private func appendInterpolation(private: ()) {}
        func appendInterpolation(default: ()) {}
        public func appendInterpolation(intResult: ()) -> Int {}
      }
      """,
        origin: "InvalidStringInterpolationProtocolTests.testInvalidStringInterpolationProtocol7",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInvalid5#1",
        source: """
      func runAction() {}
      """,
        origin: "InvalidTests.testInvalid5",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInvalid7#1",
        source: """
      super.init()
      """,
        origin: "InvalidTests.testInvalid7",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInvalid12#1",
        source: """
      protocol Animal<Food> {
        func feed(_ food: Food)
      }
      """,
        origin: "InvalidTests.testInvalid12",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInvalid16a#1",
        source: """
      func f1_43591(a : inout inout Int) {}
      """,
        origin: "InvalidTests.testInvalid16a",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInvalid28#1",
        source: """
      prefix operator %
      prefix func %<T>(x: T) -> T { return x } // No error expected - the < is considered an identifier but is peeled off by the parser.
      """,
        origin: "InvalidTests.testInvalid28",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInvalid30#1",
        source: """
      let x: () = ()
      !()
      !(())
      !(x)
      !x
      """,
        origin: "InvalidTests.testInvalid30",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInvalid32#1",
        source: """
      func f1_50734(@NSApplicationMain x: Int) {}
      """,
        origin: "InvalidTests.testInvalid32",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInvalid33#1",
        source: """
      func f2_50734(@available(iOS, deprecated: 0) x: Int) {}
      """,
        origin: "InvalidTests.testInvalid33",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInvalid34#1",
        source: """
      func f3_50734(@discardableResult x: Int) {}
      """,
        origin: "InvalidTests.testInvalid34",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInvalid35#1",
        source: """
      func f4_50734(@objcMembers x: String) {}
      """,
        origin: "InvalidTests.testInvalid35",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInvalid36#1",
        source: """
      func f5_50734(@weak x: String) {}
      """,
        origin: "InvalidTests.testInvalid36",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInvalid37#1",
        source: """
      class C_50734<@NSApplicationMain T: AnyObject> {}
      """,
        origin: "InvalidTests.testInvalid37",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInvalid38#1",
        source: """
      func f6_50734<@discardableResult T>(x: T) {}
      """,
        origin: "InvalidTests.testInvalid38",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInvalid39#1",
        source: """
      enum E_50734<@indirect T> {}
      """,
        origin: "InvalidTests.testInvalid39",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInvalid40#1",
        source: """
      protocol P {
        @available(swift, introduced: 4.2) associatedtype Assoc
      }
      """,
        origin: "InvalidTests.testInvalid40",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns1#1",
        source: """
      import imported_enums
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns3#1",
        source: """
      var x:Int
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns4#1",
        source: """
      func square(_ x: Int) -> Int { return x*x }
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns4",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns5#1",
        source: """
      struct A<B> {
        struct C<D> { }
      }
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns5",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns6#1",
        source: #"""
      switch x {
      // Expressions as patterns.
      case 0:
        ()
      case 1 + 2:
        ()
      case square(9):
        ()
      // 'var' and 'let' patterns.
      case var a:
        a = 1
      case let a:
        a = 1
      case inout a:
        a = 1
      case _mutating a:
        a = 1
      case _borrowing a:
        a = 1
      case _consuming a:
        a = 1
      case var var a:
        a += 1
      case var let a:
        print(a, terminator: "")
      case var (var b):
        b += 1
      // 'Any' pattern.
      case _:
        ()
      // patterns are resolved in expression-only positions are errors.
      case 1 + (_):
        ()
      }
      """#,
        origin: "MatchingPatternsTests.testMatchingPatterns6",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns7#1",
        source: """
      switch (x,x) {
      case (var a, var a):
        fallthrough
      case _:
        ()
      }
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns7",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns8#1",
        source: """
      var e : Any = 0
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns8",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns7a#1",
        source: """
      switch (x,x) {
      case _borrowing a:
        ()
      }
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns7a",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns7b#1",
        source: """
      switch (x,x) {
      case _mutating a:
        ()
      }
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns7b",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns7c#1",
        source: """
      switch (x,x) {
      case _consuming a:
        ()
      }
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns7c",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns9#1",
        source: """
      switch e {
      // 'is' pattern.
      case is Int,
           is A<Int>,
           is A<Int>.C<Int>,
           is (Int, Int),
           is (a: Int, b: Int):
        ()
      }
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns9",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns10#1",
        source: """
      // Enum patterns.
      enum Foo { case A, B, C }
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns10",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns11#1",
        source: """
      func == <T>(_: Voluntary<T>, _: Voluntary<T>) -> Bool { return true }
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns11",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns12#1",
        source: """
      enum Voluntary<T> : Equatable {
        case Naught
        case Mere(T)
        case Twain(T, T)
        func enumMethod(_ other: Voluntary<T>, foo: Foo) {
          switch self {
          case other:
            ()
          case .Naught,
               .Naught(),
               .Naught(_),
               .Naught(_, _):
            ()
          case .Mere,
               .Mere(),
               .Mere(_),
               .Mere(_, _):
            ()
          case .Twain(),
               .Twain(_),
               .Twain(_, _),
               .Twain(_, _, _):
            ()
          }
          switch foo {
          case .Naught:
            ()
          case .A, .B, .C:
            ()
          }
        }
      }
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns12",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns13#1",
        source: """
      var n : Voluntary<Int> = .Naught
      if case let .Naught(value) = n {}
      if case let .Naught(value1, value2, value3) = n {}
      if case inout .Naught(value) = n {}
      if case _mutating .Naught(value) = n {}
      if case _borrowing .Naught(value) = n {}
      if case _consuming .Naught(value) = n {}
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns13",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns14#1",
        source: """
      switch n {
      case Foo.A:
        ()
      case Voluntary<Int>.Naught,
           Voluntary<Int>.Naught(),
           Voluntary<Int>.Naught(_, _),
           Voluntary.Naught,
           .Naught:
        ()
      case Voluntary<Int>.Mere,
           Voluntary<Int>.Mere(_),
           Voluntary<Int>.Mere(_, _),
           Voluntary.Mere,
           Voluntary.Mere(_),
           .Mere,
           .Mere(_):
        ()
      case .Twain,
           .Twain(_),
           .Twain(_, _),
           .Twain(_, _, _):
        ()
      }
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns14",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns15#1",
        source: """
      var notAnEnum = 0
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns15",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns16#1",
        source: """
      switch notAnEnum {
      case .Foo:
        ()
      }
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns16",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns17#1",
        source: """
      struct ContainsEnum {
        enum Possible<T> {
          case Naught
          case Mere(T)
          case Twain(T, T)
        }
        func member(_ n: Possible<Int>) {
          switch n {
          case ContainsEnum.Possible<Int>.Naught,
               ContainsEnum.Possible.Naught,
               Possible<Int>.Naught,
               Possible.Naught,
               .Naught:
            ()
          }
        }
      }
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns17",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns18#1",
        source: """
      func nonmemberAccessesMemberType(_ n: ContainsEnum.Possible<Int>) {
        switch n {
        case ContainsEnum.Possible<Int>.Naught,
             .Naught:
          ()
        }
      }
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns18",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns19#1",
        source: """
      var m : ImportedEnum = .Simple
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns19",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns20#1",
        source: """
      switch m {
      case imported_enums.ImportedEnum.Simple,
           ImportedEnum.Simple,
           .Simple:
        ()
      case imported_enums.ImportedEnum.Compound,
           imported_enums.ImportedEnum.Compound(_),
           ImportedEnum.Compound,
           ImportedEnum.Compound(_),
           .Compound,
           .Compound(_):
        ()
      }
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns20",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns21#1",
        source: """
      // Check that single-element tuple payloads work sensibly in patterns.
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns21",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns22#1",
        source: """
      enum LabeledScalarPayload {
        case Payload(name: Int)
      }
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns22",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns23#1",
        source: """
      var lsp: LabeledScalarPayload = .Payload(name: 0)
      func acceptInt(_: Int) {}
      func acceptString(_: String) {}
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns23",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns24#1",
        source: #"""
      switch lsp {
      case .Payload(0):
        ()
      case .Payload(name: 0):
        ()
      case let .Payload(x):
        acceptInt(x)
        acceptString("\(x)")
      case let .Payload(name: x):
        acceptInt(x)
        acceptString("\(x)")
      case let .Payload((name: x)):
        acceptInt(x)
        acceptString("\(x)")
      case .Payload(let (name: x)):
        acceptInt(x)
        acceptString("\(x)")
      case .Payload(let (name: x)):
        acceptInt(x)
        acceptString("\(x)")
      case .Payload(let x):
        acceptInt(x)
        acceptString("\(x)")
      case .Payload((let x)):
        acceptInt(x)
        acceptString("\(x)")
      case .Payload(inout x):
        acceptInt(x)
      case .Payload(_mutating x):
        acceptInt(x)
      case .Payload(_borrowing x):
        acceptInt(x)
      case .Payload(_consuming x):
        acceptInt(x)
      }
      """#,
        origin: "MatchingPatternsTests.testMatchingPatterns24",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns25#1",
        source: """
      // Property patterns.
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns25",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns26#1",
        source: """
      struct S {
        static var stat: Int = 0
        var x, y : Int
        var comp : Int {
          return x + y
        }
        func nonProperty() {}
      }
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns26",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns27#1",
        source: """
      // Tuple patterns.
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns27",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns28#1",
        source: """
      var t = (1, 2, 3)
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns28",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns29#1",
        source: """
      prefix operator +++
      infix operator +++
      prefix func +++(x: (Int,Int,Int)) -> (Int,Int,Int) { return x }
      func +++(x: (Int,Int,Int), y: (Int,Int,Int)) -> (Int,Int,Int) {
        return (x.0+y.0, x.1+y.1, x.2+y.2)
      }
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns29",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns30#1",
        source: """
      switch t {
      case (_, var a, 3):
        a += 1
      case (_, inout a, 3):
        a += 1
      case (_, _mutating a, 3):
        a += 1
      case (_, _borrowing a, 3):
        a += 1
      case (_, _consuming a, 3):
        a += 1
      case var (_, b, 3):
        b += 1
      case var (_, var c, 3):
        c += 1
      case (1, 2, 3):
        ()
      // patterns in expression-only positions are errors.
      case +++(_, var d, 3):
        ()
      case (_, var e, 3) +++ (1, 2, 3):
        ()
      case (let (_, _, _)) + 1:
        ()
      }
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns30",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns31#1",
        source: #"""
      class Base { }
      class Derived : Base { }
      """#,
        origin: "MatchingPatternsTests.testMatchingPatterns31",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns32#1",
        source: """
      switch [Derived(), Derived(), Base()] {
      case let ds as [Derived]:
        ()
      case is [Derived]:
        ()
      default:
        ()
      }
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns32",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns33#1",
        source: """
      // Optional patterns.
      let op1 : Int?
      let op2 : Int??
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns33",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns34#1",
        source: """
      switch op1 {
      case nil: break
      case 1?: break
      case _?: break
      }
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns34",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMatchingPatterns35#1",
        source: """
      switch op2 {
      case nil: break
      case _?: break
      case (1?)?: break
      case (_?)?: break
      }
      """,
        origin: "MatchingPatternsTests.testMatchingPatterns35",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIfCaseMatchMutating#1",
        source: """
      if case _mutating x = y {}
      guard case _mutating z = y else {}
      """,
        origin: "MatchingPatternsTests.testIfCaseMatchMutating",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIfCaseMatchConsuming#1",
        source: """
      if case _consuming x = y {}
      guard case _consuming z = y else {}
      """,
        origin: "MatchingPatternsTests.testIfCaseMatchConsuming",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIfCaseMatchBorrowing#1",
        source: """
      if case _borrowing x = y {}
      guard case _borrowing z = y else {}
      """,
        origin: "MatchingPatternsTests.testIfCaseMatchBorrowing",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testBorrowingContextualParsing#1",
        source: """
      switch 42 {
      case borrowing .foo(): // parses as `borrowing.foo()` as before
        break
      }
      """,
        origin: "MatchingPatternsTests.testBorrowingContextualParsing",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testBorrowingContextualParsing#2",
        source: """
      switch 42 {
      case borrowing (): // parses as `borrowing()` as before
        break
      }
      """,
        origin: "MatchingPatternsTests.testBorrowingContextualParsing",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testBorrowingContextualParsing#3",
        source: """
      switch 42 {
      case borrowing x: // parses as binding
        break
      }
      """,
        origin: "MatchingPatternsTests.testBorrowingContextualParsing",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testBorrowingContextualParsing#4",
        source: """
      switch bar {
      case .payload(borrowing x): // parses as binding
        break
      }
      """,
        origin: "MatchingPatternsTests.testBorrowingContextualParsing",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testBorrowingContextualParsing#5",
        source: """
      switch bar {
      case borrowing x.member: // parses as var introducer surrounding postfix expression (which never is valid)
        break
      }
      """,
        origin: "MatchingPatternsTests.testBorrowingContextualParsing",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testBorrowingContextualParsing#6",
        source: """
      switch 42 {
      case let borrowing: // parses as let binding named 'borrowing'
        break
      }
      """,
        origin: "MatchingPatternsTests.testBorrowingContextualParsing",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testBorrowingContextualParsing#7",
        source: """
      switch 42 {
      case borrowing + borrowing: // parses as expr pattern
        break
      }
      """,
        origin: "MatchingPatternsTests.testBorrowingContextualParsing",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testBorrowingContextualParsing#8",
        source: """
      switch 42 {
      case borrowing(let borrowing): // parses as let binding named 'borrowing' inside a case pattern named 'borrowing'
        break
      }
      """,
        origin: "MatchingPatternsTests.testBorrowingContextualParsing",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testBorrowingContextualParsing#9",
        source: """
      switch 42 {
      case {}(borrowing + borrowing): // parses as expr pattern
        break
      }
      """,
        origin: "MatchingPatternsTests.testBorrowingContextualParsing",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMetatypeObjectConversion1#1",
        source: """
      class C {}
      struct S {}
      """,
        origin: "MetatypeObjectConversionTests.testMetatypeObjectConversion1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMetatypeObjectConversion2#1",
        source: """
      protocol NonClassProto {}
      protocol ClassConstrainedProto : class {}
      """,
        origin: "MetatypeObjectConversionTests.testMetatypeObjectConversion2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMetatypeObjectConversion3#1",
        source: """
      func takesAnyObject(_ x: AnyObject) {}
      """,
        origin: "MetatypeObjectConversionTests.testMetatypeObjectConversion3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMetatypeObjectConversion4#1",
        source: """
      func concreteTypes() {
        takesAnyObject(C.self)
        takesAnyObject(S.self)
        takesAnyObject(ClassConstrainedProto.self)
      }
      """,
        origin: "MetatypeObjectConversionTests.testMetatypeObjectConversion4",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMetatypeObjectConversion5#1",
        source: """
      func existentialMetatypes(nonClass: NonClassProto.Type,
                                classConstrained: ClassConstrainedProto.Type,
                                compo: (NonClassProto & ClassConstrainedProto).Type) {
        takesAnyObject(nonClass)
        takesAnyObject(classConstrained)
        takesAnyObject(compo)
      }
      """,
        origin: "MetatypeObjectConversionTests.testMetatypeObjectConversion5",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testModuleSelectorImports#1",
        source: """
      import struct ModuleSelectorTestingKit::A
      """,
        origin: "ModuleSelectorTests.testModuleSelectorImports",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testModuleSelectorCorrectCode#1",
        source: """
      extension ModuleSelectorTestingKit::A {}
      """,
        origin: "ModuleSelectorTests.testModuleSelectorCorrectCode",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testModuleSelectorCorrectCode#2",
        source: """
      extension A: @retroactive Swift::Equatable {}
      """,
        origin: "ModuleSelectorTests.testModuleSelectorCorrectCode",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testModuleSelectorCorrectCode#3",
        source: """
      @_implements(Swift::Equatable, ==(_:_:))
      public static func equals(_: ModuleSelectorTestingKit::A, _: ModuleSelectorTestingKit::A) -> Swift::Bool {
        Swift::fatalError()
      }
      """,
        origin: "ModuleSelectorTests.testModuleSelectorCorrectCode",
        syntaxVersion: "604.0.0-prerelease-2026-06-05",
        compilerRejects: "static methods may only be declared on a type"
    ),
    SwiftSnippet(
        label: "testModuleSelectorCorrectCode#4",
        source: """
      @_dynamicReplacement(for: ModuleSelectorTestingKit::negate())
      mutating func myNegate() {}
      """,
        origin: "ModuleSelectorTests.testModuleSelectorCorrectCode",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testModuleSelectorCorrectCode#5",
        source: """
      let fn: (Swift::Int, Swift::Int) -> Swift::Int = (Swift::+)
      """,
        origin: "ModuleSelectorTests.testModuleSelectorCorrectCode",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testModuleSelectorCorrectCode#6",
        source: """
      let magnitude: Int.Swift::Magnitude = main::magnitude
      """,
        origin: "ModuleSelectorTests.testModuleSelectorCorrectCode",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testModuleSelectorCorrectCode#7",
        source: """
      if Swift::Bool.Swift::random() {
      }
      """,
        origin: "ModuleSelectorTests.testModuleSelectorCorrectCode",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testModuleSelectorCorrectCode#8",
        source: """
      self.ModuleSelectorTestingKit::negate()
      """,
        origin: "ModuleSelectorTests.testModuleSelectorCorrectCode",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testModuleSelectorCorrectCode#9",
        source: """
      self = ModuleSelectorTestingKit::A(value: .Swift::min)
      """,
        origin: "ModuleSelectorTests.testModuleSelectorCorrectCode",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testModuleSelectorCorrectCode#10",
        source: """
      self = A.ModuleSelectorTestingKit::init(value: .min)
      """,
        origin: "ModuleSelectorTests.testModuleSelectorCorrectCode",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testModuleSelectorCorrectCode#11",
        source: """
      self.main::myNegate()
      """,
        origin: "ModuleSelectorTests.testModuleSelectorCorrectCode",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testModuleSelectorIncorrectAttrNames#1",
        source: """
      @main::available var use2
      """,
        origin: "ModuleSelectorTests.testModuleSelectorIncorrectAttrNames",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testModuleSelectorIncorrectAttrNames#2",
        source: """
      @main::available(foo: bar) var use3
      """,
        origin: "ModuleSelectorTests.testModuleSelectorIncorrectAttrNames",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testModuleSelectorIncorrectAttrNames#3",
        source: """
      func builderUser2(@main::MyBuilder fn: () -> Void) {}
      """,
        origin: "ModuleSelectorTests.testModuleSelectorIncorrectAttrNames",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testModuleSelectorWhitespace#1",
        source: """
      _ = Swift::print
      """,
        origin: "ModuleSelectorTests.testModuleSelectorWhitespace",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testModuleSelectorWhitespace#2",
        source: """
      _ = Swift:: print
      """,
        origin: "ModuleSelectorTests.testModuleSelectorWhitespace",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testModuleSelectorWhitespace#3",
        source: """
      _ = Swift ::print
      """,
        origin: "ModuleSelectorTests.testModuleSelectorWhitespace",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testModuleSelectorWhitespace#4",
        source: """
      _ = Swift :: print
      """,
        origin: "ModuleSelectorTests.testModuleSelectorWhitespace",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testModuleSelectorWhitespace#5",
        source: """
      _ = Swift
      ::print
      """,
        origin: "ModuleSelectorTests.testModuleSelectorWhitespace",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testModuleSelectorWhitespace#6",
        source: """
      _ = Swift
      :: print
      """,
        origin: "ModuleSelectorTests.testModuleSelectorWhitespace",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testModuleSelectorMacroDecls#1",
        source: """
      struct CreatesDeclExpectation {
        #main::myMacro()
      }
      """,
        origin: "ModuleSelectorTests.testModuleSelectorMacroDecls",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testModuleSelectorIncorrectRuntimeBaseAttr#1",
        source: """
      @_swift_native_objc_runtime_base(main::BaseClass)
      class C1 {}
      """,
        origin: "ModuleSelectorTests.testModuleSelectorIncorrectRuntimeBaseAttr",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testModuleSelectorAttrs#1",
        source: """
      @_spi(main::Private)
      public struct BadImplementsAttr: CustomStringConvertible {}
      """,
        origin: "ModuleSelectorTests.testModuleSelectorAttrs",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testModuleSelectorAttrs#2",
        source: """
      @_implements(main::CustomStringConvertible, Swift::description)
      public var stringValue: String { fatalError() }
      """,
        origin: "ModuleSelectorTests.testModuleSelectorAttrs",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testModuleSelectorAttrs#3",
        source: """
      @derivative(of: Swift::Foo.Swift::Bar.Swift::baz(), wrt: quux)
      func fn() {}
      """,
        origin: "ModuleSelectorTests.testModuleSelectorAttrs",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testModuleSelectorExpr#1", source: "let x = Swift::do { 1 }", origin: "ModuleSelectorTests.testModuleSelectorExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testModuleSelectorExpr#2", source: #"_ = \main::Foo.BarKit::bar"#, origin: "ModuleSelectorTests.testModuleSelectorExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testModuleSelectorExpr#3", source: "_ = Swift::nil", origin: "ModuleSelectorTests.testModuleSelectorExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testModuleSelectorExpr#4", source: "_ = Swift::true", origin: "ModuleSelectorTests.testModuleSelectorExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testModuleSelectorExpr#5", source: "_ = Swift::identifier", origin: "ModuleSelectorTests.testModuleSelectorExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testModuleSelectorExpr#6", source: "_ = Swift::self", origin: "ModuleSelectorTests.testModuleSelectorExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testModuleSelectorExpr#7", source: "_ = Swift::init", origin: "ModuleSelectorTests.testModuleSelectorExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testModuleSelectorExpr#8", source: "@attached(extension, names: Swift::deinit) macro m()", origin: "ModuleSelectorTests.testModuleSelectorExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testModuleSelectorExpr#9", source: "@attached(extension, names: Swift::subscript) macro m()", origin: "ModuleSelectorTests.testModuleSelectorExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testModuleSelectorExpr#10", source: "_ = Swift::Self", origin: "ModuleSelectorTests.testModuleSelectorExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testModuleSelectorExpr#11", source: "_ = Swift::Any", origin: "ModuleSelectorTests.testModuleSelectorExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testModuleSelectorExpr#12", source: "_ = Swift::$foo", origin: "ModuleSelectorTests.testModuleSelectorExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testModuleSelectorExpr#13", source: "_ = #Swift::foo", origin: "ModuleSelectorTests.testModuleSelectorExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testModuleSelectorExpr#14", source: "_ = .main::random()", origin: "ModuleSelectorTests.testModuleSelectorExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testModuleSelectorExpr#15", source: "_ = Swift::super.foo()", origin: "ModuleSelectorTests.testModuleSelectorExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testModuleSelectorExpr#16", source: "_ = x.Swift::y", origin: "ModuleSelectorTests.testModuleSelectorExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testModuleSelectorExpr#17", source: "_ = x.Swift::self", origin: "ModuleSelectorTests.testModuleSelectorExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testModuleSelectorExpr#18", source: "_ = x.Swift::Self.self", origin: "ModuleSelectorTests.testModuleSelectorExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testModuleSelectorExpr#19", source: "_ = x.Swift::Type.self", origin: "ModuleSelectorTests.testModuleSelectorExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testModuleSelectorExpr#20", source: "_ = x.Swift::Protocol.self", origin: "ModuleSelectorTests.testModuleSelectorExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testModuleSelectorExpr#21", source: "_ = myArray.reduce(0, Swift::+)", origin: "ModuleSelectorTests.testModuleSelectorExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testModuleSelectorType#1", source: "func fn(_: Swift::Self) {}", origin: "ModuleSelectorTests.testModuleSelectorType", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testModuleSelectorType#2", source: "func fn(_: Swift::Any) {}", origin: "ModuleSelectorTests.testModuleSelectorType", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testModuleSelectorType#3", source: "func fn(_: Swift::Foo) {}", origin: "ModuleSelectorTests.testModuleSelectorType", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testModuleSelectorType#4", source: "func fn(_: Foo.Swift::Type) {}", origin: "ModuleSelectorTests.testModuleSelectorType", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testModuleSelectorType#5", source: "func fn(_: Foo.Swift::Protocol) {}", origin: "ModuleSelectorTests.testModuleSelectorType", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testModuleSelectorType#6", source: "func fn(_: Foo.Swift::Bar) {}", origin: "ModuleSelectorTests.testModuleSelectorType", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testModuleSelectorType#7", source: "func fn(_: Foo.Swift::self) {}", origin: "ModuleSelectorTests.testModuleSelectorType", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testMoveExpr1#1",
        source: """
      var global: Int = 5
      func testGlobal() {
          let _ = _move global
      }
      """,
        origin: "MoveExprTests.testMoveExpr1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMoveExpr2#1",
        source: """
      func testLet() {
          let t = String()
          let _ = _move t
      }
      """,
        origin: "MoveExprTests.testMoveExpr2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMoveExpr3#1",
        source: """
      func testVar() {
          var t = String()
          t = String()
          let _ = _move t
      }
      """,
        origin: "MoveExprTests.testMoveExpr3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMoveExpr4#1",
        source: """
      _move(t)
      """,
        origin: "MoveExprTests.testMoveExpr4",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMoveExpr5#1",
        source: """
      _move(t)
      """,
        origin: "MoveExprTests.testMoveExpr5",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testConsumeExpr1#1",
        source: """
      var global: Int = 5
      func testGlobal() {
          let _ = consume global
      }
      """,
        origin: "MoveExprTests.testConsumeExpr1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testConsumeExpr2#1",
        source: """
      func testLet() {
          let t = String()
          let _ = consume t
      }
      """,
        origin: "MoveExprTests.testConsumeExpr2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testConsumeExpr3#1",
        source: """
      func testVar() {
          var t = String()
          t = String()
          let _ = consume t
      }
      """,
        origin: "MoveExprTests.testConsumeExpr3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testConsumeVariableNameInCast#1",
        source: """
      class ParentKlass {}
      class SubKlass : ParentKlass {}

      func test(_ x: SubKlass) {
        switch x {
        case let consume as ParentKlass:
          fallthrough
        }
      }
      """,
        origin: "MoveExprTests.testConsumeVariableNameInCast",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMultilineString1#1",
        source: """
      import Swift
      """,
        origin: "MultilineStringTests.testMultilineString1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMultilineString2#1",
        source: """
      // ===---------- Multiline --------===
      """,
        origin: "MultilineStringTests.testMultilineString2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMultilineString3#1",
        source: #"""
      _ = """
          One
          ""Alpha""
          """
      """#,
        origin: "MultilineStringTests.testMultilineString3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMultilineString4#1",
        source: #"""
      _ = """
          Two
        Beta
        """
      """#,
        origin: "MultilineStringTests.testMultilineString4",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMultilineString5#1",
        source: #"""
      _ = """
          Three
          Gamma.
        """
      """#,
        origin: "MultilineStringTests.testMultilineString5",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMultilineString6#1",
        source: #"""
      _ = """
          Four
          Delta
      """
      """#,
        origin: "MultilineStringTests.testMultilineString6",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMultilineString7#1",
        source: #"""
      _ = """
          Five\n

          Epsilon
          """
      """#,
        origin: "MultilineStringTests.testMultilineString7",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMultilineString9#1",
        source: #"""
      _ = """
          Six
          Zeta

          """
      """#,
        origin: "MultilineStringTests.testMultilineString9",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMultilineString11#1",
        source: #"""
      _ = """
          Seven
          Eta\n
          """
      """#,
        origin: "MultilineStringTests.testMultilineString11",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMultilineString12#1",
        source: #"""
      _ = """
          \"""
          "\""
          ""\"
          Iota
          """
      """#,
        origin: "MultilineStringTests.testMultilineString12",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMultilineString13#1",
        source: #"""
      _ = """
           \("Nine")
          Kappa
          """
      """#,
        origin: "MultilineStringTests.testMultilineString13",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMultilineString14#1",
        source: #"""
      _ = """
      	first
      	 second
      	third
      	"""
      """#,
        origin: "MultilineStringTests.testMultilineString14",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMultilineString15#1",
        source: #"""
      _ = """
       first
       	second
       third
       """
      """#,
        origin: "MultilineStringTests.testMultilineString15",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMultilineString16#1",
        source: #"""
      _ = """
      \\
      """
      """#,
        origin: "MultilineStringTests.testMultilineString16",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMultilineString17#1",
        source: #"""
      _ = """
        \\
        """
      """#,
        origin: "MultilineStringTests.testMultilineString17",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMultilineString18#1",
        source: #"""
      _ = """

        ABC
        """
      """#,
        origin: "MultilineStringTests.testMultilineString18",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMultilineString20#1",
        source: #"""
      _ = """

      ABC
      """
      """#,
        origin: "MultilineStringTests.testMultilineString20",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMultilineString22#1",
        source: #"""
      _ = """

        ABC
        """
      """#,
        origin: "MultilineStringTests.testMultilineString22",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMultilineString24#1",
        source: #"""
      // contains tabs
      _ = """
      	Twelve
      	Nu
      	"""
      """#,
        origin: "MultilineStringTests.testMultilineString24",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMultilineString25#1",
        source: #"""
      _ = """
        newline \
        elided
        """
      """#,
        origin: "MultilineStringTests.testMultilineString25",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMultilineString26#1",
        source: #"""
      _ = """
        trailing \
        \("""
          substring1 \
          \("""
            substring2 \         \#u{20}
            substring3
            """)
          """) \
        whitespace
        """
      """#,
        origin: "MultilineStringTests.testMultilineString26",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMultilineString27#1",
        source: #"""
      _ = """
          foo

          bar
          """
      """#,
        origin: "MultilineStringTests.testMultilineString27",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMultilineString29#1",
        source: #"""
      _ = """
          foo\\#u{20}
         \#u{20}
          bar
          """
      """#,
        origin: "MultilineStringTests.testMultilineString29",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMultilineString31#1",
        source: #"""
      _ = """
          foo \
            bar
          """
      """#,
        origin: "MultilineStringTests.testMultilineString31",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMultilineString32#1",
        source: #"""
      _ = """

        ABC
        """
      """#,
        origin: "MultilineStringTests.testMultilineString32",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMultilineString34#1",
        source: #"""
      _ = """

          ABC

          """
      """#,
        origin: "MultilineStringTests.testMultilineString34",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMultilineString37#1",
        source: #"""
      _ = """


          """
      """#,
        origin: "MultilineStringTests.testMultilineString37",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMultilineString39#1",
        source: #"""
      _ = """

          """
      """#,
        origin: "MultilineStringTests.testMultilineString39",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMultilineString41#1",
        source: #"""
      _ = """
          """
      """#,
        origin: "MultilineStringTests.testMultilineString41",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMultilineString42#1",
        source: #"""
      _ = "\("""
        \("a" + """
         valid
        """)
        """) literal"
      """#,
        origin: "MultilineStringTests.testMultilineString42",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMultilineString43#1",
        source: #"""
      _ = "hello\("""
        world
        """)"
      """#,
        origin: "MultilineStringTests.testMultilineString43",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMultilineString44#1",
        source: #"""
      _ = """
        hello\("""
           world
           """)
        abc
        """
      """#,
        origin: "MultilineStringTests.testMultilineString44",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMultilineString45#1",
        source: #"""
      _ = "hello\("""
                  "world'
                  """)abc"
      """#,
        origin: "MultilineStringTests.testMultilineString45",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMultilineString46#1",
        source: #"""
      _ = """
          welcome
          \(
            /*
              ')' or '"""' in comment.
              """
            */
            "to\("""
                 Swift
                 """)"
            // ) or """ in comment.
          )
          !
          """
      """#,
        origin: "MultilineStringTests.testMultilineString46",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEscapeNewlineInRawString#1",
        source: ##"""
      #"""
      Three \#
      Gamma
      """#
      """##,
        origin: "MultilineStringTests.testEscapeNewlineInRawString",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEscapeLastNewlineInRawString#1",
        source: ##"""
      #"""
      Three \#
      Gamma \#
      """#
      """##,
        origin: "MultilineStringTests.testEscapeLastNewlineInRawString",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testNoimplicitcopyAttr1#1",
        source: """
      f// RUN: %target-typecheck-verify-swift -parse -parse-stdlib -disable-availability-checking -verify-syntax-tree
      """,
        origin: "NoimplicitcopyAttrTests.testNoimplicitcopyAttr1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testNoimplicitcopyAttr2#1",
        source: """
      import Swift
      """,
        origin: "NoimplicitcopyAttrTests.testNoimplicitcopyAttr2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testNoimplicitcopyAttr3#1",
        source: """
      class Klass {}
      """,
        origin: "NoimplicitcopyAttrTests.testNoimplicitcopyAttr3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testNoimplicitcopyAttr4#1",
        source: """
      func argumentsAndReturns(@_noImplicitCopy _ x: Klass) -> Klass {
          return x
      }
      """,
        origin: "NoimplicitcopyAttrTests.testNoimplicitcopyAttr4",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testNoimplicitcopyAttr5#1",
        source: """
      func letDecls(@_noImplicitCopy  _ x: Klass) -> () {
          @_noImplicitCopy let y: Klass = x
          print(y)
      }
      """,
        origin: "NoimplicitcopyAttrTests.testNoimplicitcopyAttr5",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testNoimplicitcopyAttr6#1",
        source: """
      func varDecls(@_noImplicitCopy _ x: Klass, @_noImplicitCopy _ x2: Klass) -> () {
          @_noImplicitCopy var y: Klass = x
          y = x2
          print(y)
      }
      """,
        origin: "NoimplicitcopyAttrTests.testNoimplicitcopyAttr6",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testNoimplicitcopyAttr7#1",
        source: """
      func getKlass() -> Builtin.NativeObject {
          let k = Klass()
          let b = Builtin.unsafeCastToNativeObject(k)
          return Builtin.move(b)
      }
      """,
        origin: "NoimplicitcopyAttrTests.testNoimplicitcopyAttr7",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testNoimplicitcopyAttr8#1",
        source: """
      @_noImplicitCopy var g: Builtin.NativeObject = getKlass()
      @_noImplicitCopy let g2: Builtin.NativeObject = getKlass()
      """,
        origin: "NoimplicitcopyAttrTests.testNoimplicitcopyAttr8",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testNumberIdentifierErrors1#1",
        source: """
      // Per rdar://problem/32316666 , it is a common mistake for beginners
      // to start a function name with a number, so it's worth
      // special-casing the diagnostic to make it clearer.
      """,
        origin: "NumberIdentifierErrorsTests.testNumberIdentifierErrors1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testObjcEnum1#1",
        source: """
      @objc enum Foo: Int32 {
        case Zim, Zang, Zung
      }
      """,
        origin: "ObjcEnumTests.testObjcEnum1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testObjcEnum2#1",
        source: """
      @objc enum Generic<T>: Int32 {
        case Zim, Zang, Zung
      }
      """,
        origin: "ObjcEnumTests.testObjcEnum2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testObjcEnum3#1",
        source: """
      @objc(EnumRuntimeName) enum RuntimeNamed: Int32 {
        case Zim, Zang, Zung
      }
      """,
        origin: "ObjcEnumTests.testObjcEnum3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testObjcEnum4#1",
        source: """
      @objc enum NoRawType {
        case Zim, Zang, Zung
      }
      """,
        origin: "ObjcEnumTests.testObjcEnum4",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testObjcEnum5#1",
        source: """
      @objc enum NonIntegerRawType: Float {
        case Zim = 1.0, Zang = 1.5, Zung = 2.0
      }
      """,
        origin: "ObjcEnumTests.testObjcEnum5",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testObjcEnum6#1",
        source: """
      enum NonObjCEnum: Int {
        case Zim, Zang, Zung
      }
      """,
        origin: "ObjcEnumTests.testObjcEnum6",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testObjcEnum7#1",
        source: """
      class Bar {
        @objc func foo(x: Foo) {}
        @objc func nonObjC(x: NonObjCEnum) {}
      }
      """,
        origin: "ObjcEnumTests.testObjcEnum7",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testObjcEnum8#1",
        source: """
      // <rdar://problem/23681566> @objc enums with payloads rejected with no source location info
      @objc enum r23681566 : Int32 {
        case Foo(progress: Int)
      }
      """,
        origin: "ObjcEnumTests.testObjcEnum8",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testObjectLiterals2a#1",
        source: """
      let _ = #Color(colorLiteralRed: red, green: green, blue: blue, alpha: alpha)
      """,
        origin: "ObjectLiteralsTests.testObjectLiterals2a",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testObjectLiterals2b#1",
        source: """
      let _ = #Image(imageLiteral: localResourceNameAsString)
      """,
        origin: "ObjectLiteralsTests.testObjectLiterals2b",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testObjectLiterals2c#1",
        source: """
      let _ = #FileReference(fileReferenceLiteral: localResourceNameAsString)
      """,
        origin: "ObjectLiteralsTests.testObjectLiterals2c",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testObjectLiterals3a#1",
        source: """
      let _ = #notAPound
      """,
        origin: "ObjectLiteralsTests.testObjectLiterals3a",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testObjectLiterals3b#1",
        source: """
      let _ = #notAPound(1, 2)
      """,
        origin: "ObjectLiteralsTests.testObjectLiterals3b",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testObjectLiterals3c#1",
        source: """
      let _ = #Color
      """,
        origin: "ObjectLiteralsTests.testObjectLiterals3c",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testObjectLiterals8#1",
        source: """
      let _ = #Color(_: 1, green: 1)
      """,
        origin: "ObjectLiteralsTests.testObjectLiterals8",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperatorDeclDesignatedTypes1#1",
        source: """
      precedencegroup LowPrecedence {
        associativity: right
      }
      """,
        origin: "OperatorDeclDesignatedTypesTests.testOperatorDeclDesignatedTypes1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperatorDeclDesignatedTypes2#1",
        source: """
      precedencegroup MediumPrecedence {
        associativity: left
        higherThan: LowPrecedence
      }
      """,
        origin: "OperatorDeclDesignatedTypesTests.testOperatorDeclDesignatedTypes2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperatorDeclDesignatedTypes3#1",
        source: """
      protocol PrefixMagicOperatorProtocol {
      }
      """,
        origin: "OperatorDeclDesignatedTypesTests.testOperatorDeclDesignatedTypes3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperatorDeclDesignatedTypes4#1",
        source: """
      protocol PostfixMagicOperatorProtocol {
      }
      """,
        origin: "OperatorDeclDesignatedTypesTests.testOperatorDeclDesignatedTypes4",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperatorDeclDesignatedTypes5#1",
        source: """
      protocol InfixMagicOperatorProtocol {
      }
      """,
        origin: "OperatorDeclDesignatedTypesTests.testOperatorDeclDesignatedTypes5",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperatorDeclDesignatedTypes6#1",
        source: """
      prefix operator ^^ : PrefixMagicOperatorProtocol
      infix operator  <*< : MediumPrecedence, InfixMagicOperatorProtocol
      postfix operator ^^ : PostfixMagicOperatorProtocol
      """,
        origin: "OperatorDeclDesignatedTypesTests.testOperatorDeclDesignatedTypes6",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperatorDeclDesignatedTypes7#1",
        source: """
      infix operator ^*^
      prefix operator *^^
      postfix operator ^^*
      """,
        origin: "OperatorDeclDesignatedTypesTests.testOperatorDeclDesignatedTypes7",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperatorDeclDesignatedTypes8#1",
        source: """
      infix operator **>> : UndeclaredPrecedence
      """,
        origin: "OperatorDeclDesignatedTypesTests.testOperatorDeclDesignatedTypes8",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperatorDeclDesignatedTypes9#1",
        source: """
      infix operator **+> : MediumPrecedence, UndeclaredProtocol
      """,
        origin: "OperatorDeclDesignatedTypesTests.testOperatorDeclDesignatedTypes9",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperatorDeclDesignatedTypes10#1",
        source: """
      prefix operator *+*> : MediumPrecedence
      """,
        origin: "OperatorDeclDesignatedTypesTests.testOperatorDeclDesignatedTypes10",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperatorDeclDesignatedTypes11#1",
        source: """
      postfix operator ++*> : MediumPrecedence
      """,
        origin: "OperatorDeclDesignatedTypesTests.testOperatorDeclDesignatedTypes11",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperatorDeclDesignatedTypes12#1",
        source: """
      prefix operator *++> : UndeclaredProtocol
      postfix operator +*+> : UndeclaredProtocol
      """,
        origin: "OperatorDeclDesignatedTypesTests.testOperatorDeclDesignatedTypes12",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperatorDeclDesignatedTypes13#1",
        source: """
      struct Struct {}
      class Class {}
      infix operator *>*> : Struct
      infix operator >**> : Class
      """,
        origin: "OperatorDeclDesignatedTypesTests.testOperatorDeclDesignatedTypes13",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperatorDeclDesignatedTypes14#1",
        source: """
      prefix operator **>> : Struct
      prefix operator *>*> : Class
      """,
        origin: "OperatorDeclDesignatedTypesTests.testOperatorDeclDesignatedTypes14",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperatorDeclDesignatedTypes15#1",
        source: """
      postfix operator >*>* : Struct
      postfix operator >>** : Class
      """,
        origin: "OperatorDeclDesignatedTypesTests.testOperatorDeclDesignatedTypes15",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperatorDeclDesignatedTypes16#1",
        source: """
      infix operator  <*<<< : MediumPrecedence, &
      """,
        origin: "OperatorDeclDesignatedTypesTests.testOperatorDeclDesignatedTypes16",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperatorDeclDesignatedTypes17#1",
        source: """
      infix operator **^^ : MediumPrecedence
      infix operator **^^ : InfixMagicOperatorProtocol
      """,
        origin: "OperatorDeclDesignatedTypesTests.testOperatorDeclDesignatedTypes17",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperatorDeclDesignatedTypes18#1",
        source: """
      infix operator ^%*%^ : MediumPrecedence, Struct, Class
      infix operator ^%*%% : Struct, Class
      prefix operator %^*^^ : Struct, Class
      postfix operator ^^*^% : Struct, Class
      prefix operator %%*^^ : LowPrecedence, Class
      postfix operator ^^*%% : MediumPrecedence, Class
      """,
        origin: "OperatorDeclDesignatedTypesTests.testOperatorDeclDesignatedTypes18",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperatorDeclDesignatedTypes19#1",
        source: """
      infix operator <*<>*> : AdditionPrecedence,
      """,
        origin: "OperatorDeclDesignatedTypesTests.testOperatorDeclDesignatedTypes19",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperatorDecl3#1",
        source: """
      prefix operator ++*++ : A
      """,
        origin: "OperatorDeclTests.testOperatorDecl3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperatorDecl5#1",
        source: """
      postfix operator ++**+ : A
      """,
        origin: "OperatorDeclTests.testOperatorDecl5",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperatorDecl11a#1",
        source: """
      prefix operator ??
      """,
        origin: "OperatorDeclTests.testOperatorDecl11a",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperatorDecl11b#1",
        source: """
      postfix operator ??
      """,
        origin: "OperatorDeclTests.testOperatorDecl11b",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperatorDecl11c#1",
        source: """
      prefix operator !!
      """,
        origin: "OperatorDeclTests.testOperatorDecl11c",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperatorDecl11d#1",
        source: """
      postfix operator !!
      """,
        origin: "OperatorDeclTests.testOperatorDecl11d",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperatorDecl16#1",
        source: """
      precedencegroup F {
        higherThan: A, B, C
      }
      """,
        origin: "OperatorDeclTests.testOperatorDecl16",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperatorDecl17#1",
        source: """
      precedencegroup BangBangBang {
        associativity: none
        associativity: left
      }
      """,
        origin: "OperatorDeclTests.testOperatorDecl17",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperatorDecl18#1",
        source: """
      precedencegroup CaretCaretCaret {
        assignment: true
        assignment: false
      }
      """,
        origin: "OperatorDeclTests.testOperatorDecl18",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperatorDecl19#1",
        source: """
      class Foo {
        infix operator |||
      }
      """,
        origin: "OperatorDeclTests.testOperatorDecl19",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperatorDecl20#1",
        source: """
      infix operator **<< : UndeclaredPrecedenceGroup
      """,
        origin: "OperatorDeclTests.testOperatorDecl20",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperatorDecl21#1",
        source: """
      protocol Proto {}
      infix operator *<*< : F, Proto
      """,
        origin: "OperatorDeclTests.testOperatorDecl21",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperatorDecl22#1",
        source: """
      // https://github.com/apple/swift/issues/60932
      """,
        origin: "OperatorDeclTests.testOperatorDecl22",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testRegexLikeOperator#1", source: "prefix operator /^/", origin: "OperatorDeclTests.testRegexLikeOperator", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testOperators1#1",
        source: """
      // This disables importing the stdlib intentionally.
      """,
        origin: "OperatorsTests.testOperators1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperators2#1",
        source: """
      infix operator == : Equal
      precedencegroup Equal {
        associativity: left
        higherThan: FatArrow
      }
      """,
        origin: "OperatorsTests.testOperators2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperators3#1",
        source: """
      infix operator & : BitAnd
      precedencegroup BitAnd {
        associativity: left
        higherThan: Equal
      }
      """,
        origin: "OperatorsTests.testOperators3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperators4#1",
        source: """
      infix operator => : FatArrow
      precedencegroup FatArrow {
        associativity: right
        higherThan: AssignmentPrecedence
      }
      precedencegroup AssignmentPrecedence {
        assignment: true
      }
      """,
        origin: "OperatorsTests.testOperators4",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperators5#1",
        source: """
      precedencegroup DefaultPrecedence {}
      """,
        origin: "OperatorsTests.testOperators5",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperators6#1",
        source: """
      struct Man {}
      struct TheDevil {}
      struct God {}
      """,
        origin: "OperatorsTests.testOperators6",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperators7#1",
        source: """
      struct Five {}
      struct Six {}
      struct Seven {}
      """,
        origin: "OperatorsTests.testOperators7",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperators8#1",
        source: """
      struct ManIsFive {}
      struct TheDevilIsSix {}
      struct GodIsSeven {}
      """,
        origin: "OperatorsTests.testOperators8",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperators9#1",
        source: """
      struct TheDevilIsSixThenGodIsSeven {}
      """,
        origin: "OperatorsTests.testOperators9",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperators10#1",
        source: """
      func == (x: Man, y: Five) -> ManIsFive {}
      func == (x: TheDevil, y: Six) -> TheDevilIsSix {}
      func == (x: God, y: Seven) -> GodIsSeven {}
      """,
        origin: "OperatorsTests.testOperators10",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperators11#1",
        source: """
      func => (x: TheDevilIsSix, y: GodIsSeven) -> TheDevilIsSixThenGodIsSeven {}
      func => (x: ManIsFive, y: TheDevilIsSixThenGodIsSeven) {}
      """,
        origin: "OperatorsTests.testOperators11",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperators12#1",
        source: """
      func test1() {
        Man() == Five() => TheDevil() == Six() => God() == Seven()
      }
      """,
        origin: "OperatorsTests.testOperators12",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperators13#1",
        source: """
      postfix operator *!*
      prefix operator *!*
      """,
        origin: "OperatorsTests.testOperators13",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperators14#1",
        source: """
      struct LOOK {}
      struct LOOKBang {
        func exclaim() {}
      }
      """,
        origin: "OperatorsTests.testOperators14",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperators15#1",
        source: """
      postfix func *!* (x: LOOK) -> LOOKBang {}
      prefix func *!* (x: LOOKBang) {}
      """,
        origin: "OperatorsTests.testOperators15",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperators16#1",
        source: """
      func test2() {
        *!*LOOK()*!*
      }
      """,
        origin: "OperatorsTests.testOperators16",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperators17#1",
        source: """
      // This should be parsed as (x*!*).exclaim()
      LOOK()*!*.exclaim()
      """,
        origin: "OperatorsTests.testOperators17",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperators18#1",
        source: """
      prefix operator ^
      infix operator ^
      postfix operator ^
      """,
        origin: "OperatorsTests.testOperators18",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperators19#1",
        source: """
      postfix func ^ (x: God) -> TheDevil {}
      prefix func ^ (x: TheDevil) -> God {}
      """,
        origin: "OperatorsTests.testOperators19",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperators20#1",
        source: """
      func ^ (x: TheDevil, y: God) -> Man {}
      """,
        origin: "OperatorsTests.testOperators20",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperators21#1",
        source: """
      var _ : TheDevil = God()^
      var _ : God = ^TheDevil()
      var _ : Man = TheDevil() ^ God()
      var _ : Man = God()^ ^ ^TheDevil()
      let _ = God()^TheDevil()
      """,
        origin: "OperatorsTests.testOperators21",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperators22#1",
        source: """
      postfix func ^ (x: Man) -> () -> God {
        return { return God() }
      }
      """,
        origin: "OperatorsTests.testOperators22",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperators23#1",
        source: """
      var _ : God = Man()^()
      """,
        origin: "OperatorsTests.testOperators23",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperators24#1",
        source: """
      func &(x : Man, y : Man) -> Man { return x } // forgive amp_prefix token
      """,
        origin: "OperatorsTests.testOperators24",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperators25#1",
        source: """
      prefix operator ⚽️
      """,
        origin: "OperatorsTests.testOperators25",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperators26#1",
        source: """
      prefix func ⚽️(x: Man) { }
      """,
        origin: "OperatorsTests.testOperators26",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperators27#1",
        source: """
      infix operator ?? : OptTest
      precedencegroup OptTest {
        associativity: right
      }
      """,
        origin: "OperatorsTests.testOperators27",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperators28#1",
        source: """
      func ??(x: Man, y: TheDevil) -> TheDevil {
        return y
      }
      """,
        origin: "OperatorsTests.testOperators28",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperators29#1",
        source: """
      func test3(a: Man, b: Man, c: TheDevil) -> TheDevil {
        return a ?? b ?? c
      }
      """,
        origin: "OperatorsTests.testOperators29",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperators30#1",
        source: """
      // <rdar://problem/17821399> We don't parse infix operators bound on both
      // sides that begin with ! or ? correctly yet.
      infix operator !!
      """,
        origin: "OperatorsTests.testOperators30",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperators31#1",
        source: """
      func !!(x: Man, y: Man) {}
      """,
        origin: "OperatorsTests.testOperators31",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperators32#1",
        source: """
      let foo = Man()
      """,
        origin: "OperatorsTests.testOperators32",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOperators33#1",
        source: """
      let bar = TheDevil()
      """,
        origin: "OperatorsTests.testOperators33",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOptionalChainLvalues1#1",
        source: """
      struct S {
        var x: Int = 0
        let y: Int = 0  // expected-note 3 {{change 'let' to 'var' to make it mutable}} {{3-6=var}} {{3-6=var}} {{3-6=var}}
        mutating func mutateS() {}
        init() {}
      }
      """,
        origin: "OptionalChainLvaluesTests.testOptionalChainLvalues1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOptionalChainLvalues2#1",
        source: """
      struct T {
        var mutS: S? = nil
        let immS: S? = nil  // expected-note 4 {{change 'let' to 'var' to make it mutable}} {{3-6=var}} {{3-6=var}} {{3-6=var}} {{3-6=var}}
        mutating func mutateT() {}
        init() {}
      }
      """,
        origin: "OptionalChainLvaluesTests.testOptionalChainLvalues2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOptionalChainLvalues3#1",
        source: """
      var mutT: T?
      let immT: T? = nil
      """,
        origin: "OptionalChainLvaluesTests.testOptionalChainLvalues3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOptionalChainLvalues4#1",
        source: """
      postfix operator ++
      prefix operator ++
      """,
        origin: "OptionalChainLvaluesTests.testOptionalChainLvalues4",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOptionalChainLvalues5#1",
        source: """
      public postfix func ++ <T>(rhs: inout T) -> T { fatalError() }
      public prefix func ++ <T>(rhs: inout T) -> T { fatalError() }
      """,
        origin: "OptionalChainLvaluesTests.testOptionalChainLvalues5",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOptionalChainLvalues6#1",
        source: """
      mutT?.mutateT()
      immT?.mutateT()
      mutT?.mutS?.mutateS()
      mutT?.immS?.mutateS()
      mutT?.mutS?.x += 1
      mutT?.mutS?.y++
      """,
        origin: "OptionalChainLvaluesTests.testOptionalChainLvalues6",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOptionalChainLvalues7#1",
        source: """
      // Prefix operators don't chain
      ++mutT?.mutS?.x
      ++mutT?.mutS?.y
      """,
        origin: "OptionalChainLvaluesTests.testOptionalChainLvalues7",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOptionalChainLvalues8#1",
        source: """
      mutT? = T()
      mutT?.mutS = S()
      mutT?.mutS? = S()
      mutT?.mutS?.x += 0
      _ = mutT?.mutS?.x + 0
      mutT?.mutS?.y -= 0
      mutT?.immS = S()
      mutT?.immS? = S()
      mutT?.immS?.x += 0
      mutT?.immS?.y -= 0
      """,
        origin: "OptionalChainLvaluesTests.testOptionalChainLvalues8",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOptionalLvalues1#1",
        source: """
      struct S {
        var x: Int = 0
        let y: Int = 0 // expected-note 4 {{change 'let' to 'var' to make it mutable}} {{3-6=var}} {{3-6=var}} {{3-6=var}} {{3-6=var}}
        init() {}
      }
      """,
        origin: "OptionalLvaluesTests.testOptionalLvalues1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOptionalLvalues2#1",
        source: """
      struct T {
        var mutS: S? = nil
        let immS: S? = nil // expected-note 10 {{change 'let' to 'var' to make it mutable}} {{3-6=var}} {{3-6=var}} {{3-6=var}} {{3-6=var}} {{3-6=var}} {{3-6=var}} {{3-6=var}} {{3-6=var}} {{3-6=var}} {{3-6=var}}
        init() {}
      }
      """,
        origin: "OptionalLvaluesTests.testOptionalLvalues2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOptionalLvalues3#1",
        source: """
      var mutT: T?
      let immT: T? = nil  // expected-note 4 {{change 'let' to 'var' to make it mutable}} {{1-4=var}} {{1-4=var}} {{1-4=var}} {{1-4=var}}
      """,
        origin: "OptionalLvaluesTests.testOptionalLvalues3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOptionalLvalues4#1",
        source: """
      let mutTPayload = mutT!
      """,
        origin: "OptionalLvaluesTests.testOptionalLvalues4",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOptionalLvalues5#1",
        source: """
      mutT! = T()
      mutT!.mutS = S()
      mutT!.mutS! = S()
      mutT!.mutS!.x = 0
      mutT!.mutS!.y = 0
      mutT!.immS = S()
      mutT!.immS! = S()
      mutT!.immS!.x = 0
      mutT!.immS!.y = 0
      """,
        origin: "OptionalLvaluesTests.testOptionalLvalues5",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOptionalLvalues6#1",
        source: """
      immT! = T()
      immT!.mutS = S()
      immT!.mutS! = S()
      immT!.mutS!.x = 0
      immT!.mutS!.y = 0
      immT!.immS = S()
      immT!.immS! = S()
      immT!.immS!.x = 0
      immT!.immS!.y = 0
      """,
        origin: "OptionalLvaluesTests.testOptionalLvalues6",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOptionalLvalues7#1",
        source: """
      var mutIUO: T! = nil
      let immIUO: T! = nil // expected-note 2 {{change 'let' to 'var' to make it mutable}} {{1-4=var}} {{1-4=var}}
      """,
        origin: "OptionalLvaluesTests.testOptionalLvalues7",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOptionalLvalues8#1",
        source: """
      mutIUO!.mutS = S()
      mutIUO!.immS = S()
      immIUO!.mutS = S()
      immIUO!.immS = S()
      """,
        origin: "OptionalLvaluesTests.testOptionalLvalues8",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOptionalLvalues9#1",
        source: """
      mutIUO.mutS = S()
      mutIUO.immS = S()
      immIUO.mutS = S()
      immIUO.immS = S()
      """,
        origin: "OptionalLvaluesTests.testOptionalLvalues9",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOptionalLvalues10#1",
        source: """
      func foo(x: Int) {}
      """,
        origin: "OptionalLvaluesTests.testOptionalLvalues10",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOptionalLvalues11#1",
        source: """
      var nonOptional: S = S()
      _ = nonOptional!
      _ = nonOptional!.x
      """,
        origin: "OptionalLvaluesTests.testOptionalLvalues11",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOptionalLvalues12#1",
        source: """
      class C {}
      class D: C {}
      """,
        origin: "OptionalLvaluesTests.testOptionalLvalues12",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOptionalLvalues13#1",
        source: """
      let c = C()
      let d = (c as! D)!
      """,
        origin: "OptionalLvaluesTests.testOptionalLvalues13",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOptional1#1",
        source: """
      struct A {
        func foo() {}
      }
      """,
        origin: "OptionalTests.testOptional1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOptional3a#1",
        source: """
      var c = a?
      """,
        origin: "OptionalTests.testOptional3a",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOptional3b#1",
        source: """
      var d : ()? = a?.foo()
      """,
        origin: "OptionalTests.testOptional3b",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOptional4#1",
        source: """
      var e : (() -> A)?
      var f = e?()
      """,
        origin: "OptionalTests.testOptional4",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOptional5#1",
        source: """
      struct B<T> {}
      var g = B<A?>()
      """,
        origin: "OptionalTests.testOptional5",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOriginalDefinedInAttr1#1",
        source: #"""
      @_originallyDefinedIn(module: "foo", OSX 13.13)
      public func foo() {}
      """#,
        origin: "OriginalDefinedInAttrTests.testOriginalDefinedInAttr1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOriginalDefinedInAttr3#1",
        source: #"""
      @_originallyDefinedIn(module: "foo", OSX 13.13.3)
      public class ToplevelClass {}
      """#,
        origin: "OriginalDefinedInAttrTests.testOriginalDefinedInAttr3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOriginalDefinedInAttr7#1",
        source: #"""
      @available(OSX 13.10, *)
      @_originallyDefinedIn(module: "foo", * 13.13)
      public class ToplevelClass4 {}
      """#,
        origin: "OriginalDefinedInAttrTests.testOriginalDefinedInAttr7",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOriginalDefinedInAttr7#2",
        source: #"""
      @available(OSX 13.10, *)
      @_originallyDefinedIn(module: "foo", OSX 13.13, iOS 7.0)
      public class ToplevelClass4 {}
      """#,
        origin: "OriginalDefinedInAttrTests.testOriginalDefinedInAttr7",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOriginalDefinedInAttr7#3",
        source: #"""
      @available(OSX 13.10, *)
      @_originallyDefinedIn(module: "foo", OSX 13.14, * 7.0)
      public class ToplevelClass4 {}
      """#,
        origin: "OriginalDefinedInAttrTests.testOriginalDefinedInAttr7",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOriginalDefinedInAttr7#4",
        source: #"""
      public class ToplevelClass4 {
        @_originallyDefinedIn(module: "foo", OSX 13.13)
        subscript(index: Int) -> Int {
              get { return 1 }
              set(newValue) {}
        }
      }
      """#,
        origin: "OriginalDefinedInAttrTests.testOriginalDefinedInAttr7",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOriginalDefinedInAttr8#1",
        source: #"""
      @available(OSX 13.10, *)
      @_originallyDefinedIn(module: "foo", OSX 13.13)
      @_originallyDefinedIn(module: "foo", iOS 7.0)
      internal class ToplevelClass5 {}
      """#,
        origin: "OriginalDefinedInAttrTests.testOriginalDefinedInAttr8",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOriginalDefinedInAttr9#1",
        source: #"""
      @available(OSX 13.10, *)
      @_originallyDefinedIn(module: "foo", OSX 13.13)
      @_originallyDefinedIn(module: "foo", iOS 7.0)
      private class ToplevelClass6 {}
      """#,
        origin: "OriginalDefinedInAttrTests.testOriginalDefinedInAttr9",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOriginalDefinedInAttr10#1",
        source: #"""
      @available(OSX 13.10, *)
      @_originallyDefinedIn(module: "foo", OSX 13.13)
      @_originallyDefinedIn(module: "foo", iOS 7.0)
      fileprivate class ToplevelClass7 {}
      """#,
        origin: "OriginalDefinedInAttrTests.testOriginalDefinedInAttr10",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOriginalDefinedInAttr11#1",
        source: #"""
      @available(OSX 13.10, *)
      @_originallyDefinedIn(module: "foo", OSX 13.13, iOS 7.0)
      internal class ToplevelClass8 {}
      """#,
        origin: "OriginalDefinedInAttrTests.testOriginalDefinedInAttr11",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testOrinalDefinedInAttr12#1",
        source: """
      @_originallyDefinedIn(module: "ToasterKit", _iOS13Aligned)
      struct Vehicle {}
      """,
        origin: "OriginalDefinedInAttrTests.testOrinalDefinedInAttr12",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testPatternWithoutVariablesScript1#1",
        source: """
      _ = 1
      """,
        origin: "PatternWithoutVariablesScriptTests.testPatternWithoutVariablesScript1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testPatternWithoutVariables1#1",
        source: """
      let _ = 1
      inout _ = 1
      _mutating _ = 1
      _borrowing _ = 1
      _consuming _ = 1
      """,
        origin: "PatternWithoutVariablesTests.testPatternWithoutVariables1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testPatternWithoutVariables2#1",
        source: """
      func foo() {
        let _ = 1 // OK
        inout _ = 1
        _mutating _ = 1
        _borrowing _ = 1
        _consuming _ = 1
      }
      """,
        origin: "PatternWithoutVariablesTests.testPatternWithoutVariables2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testPatternWithoutVariables3#1",
        source: """
      struct Foo {
        let _ = 1
        var (_, _) = (1, 2)
        func foo() {
          let _ = 1 // OK
        }
        inout (_, _) = (1, 2)
        _mutating (_, _) = (1, 2)
        _borrowing (_, _) = (1, 2)
        _consuming (_, _) = (1, 2)
      }
      """,
        origin: "PatternWithoutVariablesTests.testPatternWithoutVariables3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testPatternWithoutVariables4#1",
        source: #"""
      // <rdar://problem/19786845> Warn on "let" and "var" when no data is bound in a pattern
      enum SimpleEnum { case Bar }
      """#,
        origin: "PatternWithoutVariablesTests.testPatternWithoutVariables4",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testPatternWithoutVariables5#1",
        source: #"""
      func testVarLetPattern(a : SimpleEnum) {
        switch a {
        case let .Bar: break
        }
        switch a {
        case let x: _ = x; break         // Ok.
        }
        switch a {
        case let _: break
        }
        switch (a, 42) {
        case let (_, x): _ = x; break    // ok
        }
        if case let _ = "str" {}
        switch a {
        case inout .Bar: break
        }
        switch a {
        case _mutating .Bar: break
        }
        switch a {
        case _borrowing .Bar: break
        }
        switch a {
        case _consuming .Bar: break
        }
      }
      """#,
        origin: "PatternWithoutVariablesTests.testPatternWithoutVariables5",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testPatternWithoutVariables6#1",
        source: """
      // https://github.com/apple/swift/issues/53293
      class C_53293 {
        static var _: Int { 0 }
      }
      """,
        origin: "PatternWithoutVariablesTests.testPatternWithoutVariables6",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testMutatingNotADeclarationStartIfNotEnabled#1", source: "_mutating = 2", origin: "PatternWithoutVariablesTests.testMutatingNotADeclarationStartIfNotEnabled", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testPlaygroundLvalues1#1",
        source: """
      var a = 1, b = 2
      let z = 3
      """,
        origin: "PlaygroundLvaluesTests.testPlaygroundLvalues1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testPlaygroundLvalues2#1",
        source: """
      a
      (a, b)
      (a, z)
      """,
        origin: "PlaygroundLvaluesTests.testPlaygroundLvalues2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testPoundAssert1#1",
        source: """
      #assert(true, 123)
      """,
        origin: "PoundAssertTests.testPoundAssert1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testPoundAssert2#1",
        source: #"""
      #assert(true, "error \(1) message")
      """#,
        origin: "PoundAssertTests.testPoundAssert2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testPrefixSlash2#1",
        source: """
      prefix operator /
      prefix func / <T> (_ x: T) -> T { x }
      """,
        origin: "PrefixSlashTests.testPrefixSlash2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testPrefixSlash4#1",
        source: """
      _ = /E.e
      (/E.e).foo(/0)
      """,
        origin: "PrefixSlashTests.testPrefixSlash4",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testPrefixSlash6#1",
        source: """
      foo(/E.e, /E.e)
      foo((/E.e), /E.e)
      foo((/)(E.e), /E.e)
      """,
        origin: "PrefixSlashTests.testPrefixSlash6",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testPrefixSlash8#1",
        source: """
      _ = bar(/E.e) / 2
      """,
        origin: "PrefixSlashTests.testPrefixSlash8",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRawString1#1",
        source: """
      import Swift
      """,
        origin: "RawStringTests.testRawString1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRawString2#1",
        source: ##"""
      _ = #"""
      ###################################################################
      ## This source file is part of the Swift.org open source project ##
      ###################################################################
      """#
      """##,
        origin: "RawStringTests.testRawString2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRawString3#1",
        source: ####"""
      _ = #"""
          # H1 #
          ## H2 ##
          ### H3 ###
          """#
      """####,
        origin: "RawStringTests.testRawString3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRawString5#1",
        source: ###"""
      _ = ##"""
          One
          ""Alpha""
          """##
      """###,
        origin: "RawStringTests.testRawString5",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRawString6#1",
        source: ###"""
      _ = ##"""
          Two
        Beta
        """##
      """###,
        origin: "RawStringTests.testRawString6",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRawString7#1",
        source: ##"""
      _ = #"""
          Three\r
          Gamma\
        """#
      """##,
        origin: "RawStringTests.testRawString7",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRawString8#1",
        source: ####"""
      _ = ###"""
          Four \(foo)
          Delta
      """###
      """####,
        origin: "RawStringTests.testRawString8",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRawString9#1",
        source: ###"""
      _ = ##"""
        print("""
          Five\##n\##n\##nEpsilon
          """)
        """##
      """###,
        origin: "RawStringTests.testRawString9",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRawString10#1",
        source: """
      // ===---------- Single line --------===
      """,
        origin: "RawStringTests.testRawString10",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRawString11#1",
        source: ##"""
      _ = #""Zeta""#
      """##,
        origin: "RawStringTests.testRawString11",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRawString12#1",
        source: ##"""
      _ = #""Eta"\#n\#n\#n\#""#
      """##,
        origin: "RawStringTests.testRawString12",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRawString13#1",
        source: ##"""
      _ = #""Iota"\n\n\n\""#
      """##,
        origin: "RawStringTests.testRawString13",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRawString14#1",
        source: ##"""
      _ = #"a raw string with \" in it"#
      """##,
        origin: "RawStringTests.testRawString14",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRawString15#1",
        source: ###"""
      _ = ##"""
            a raw string with """ in it
            """##
      """###,
        origin: "RawStringTests.testRawString15",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRawString16#1",
        source: """
      // ===---------- False Multiline Delimiters --------===
      """,
        origin: "RawStringTests.testRawString16",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRawString17#1",
        source: ##"""
      /// Source code contains zero-width character in this format: `#"[U+200B]"[U+200B]"#`
      /// The check contains zero-width character in this format: `"[U+200B]\"[U+200B]"`
      /// If this check fails after you implement `diagnoseZeroWidthMatchAndAdvance`,
      /// then you may need to tweak how to test for single-line string literals that
      /// resemble a multiline delimiter in `advanceIfMultilineDelimiter` so that it
      /// passes again.
      /// See https://github.com/apple/swift/issues/51192.
      _ = #"​"​"#
      """##,
        origin: "RawStringTests.testRawString17",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRawString18#1",
        source: ##"""
      _ = #""""#
      """##,
        origin: "RawStringTests.testRawString18",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRawString19#1",
        source: ##"""
      _ = #"""""#
      """##,
        origin: "RawStringTests.testRawString19",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRawString20#1",
        source: ##"""
      _ = #""""""#
      """##,
        origin: "RawStringTests.testRawString20",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRawString21#1",
        source: ##"""
      _ = #"""#
      """##,
        origin: "RawStringTests.testRawString21",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRawString22#1",
        source: ###"""
      _ = ##""" foo # "# "##
      """###,
        origin: "RawStringTests.testRawString22",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRawString23#1",
        source: ####"""
      _ = ###""" "# "## "###
      """####,
        origin: "RawStringTests.testRawString23",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRawString24#1",
        source: ####"""
      _ = ###"""##"###
      """####,
        origin: "RawStringTests.testRawString24",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRawString25#1",
        source: ##"""
      _ = "interpolating \(#"""false delimiter"#)"
      """##,
        origin: "RawStringTests.testRawString25",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRawString26#1",
        source: ##"""
      _ = """
        interpolating \(#"""false delimiters"""#)
        """
      """##,
        origin: "RawStringTests.testRawString26",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRawString27#1",
        source: ##"""
      let foo = "Interpolation"
      _ = #"\b\b \#(foo)\#(foo) Kappa"#
      """##,
        origin: "RawStringTests.testRawString27",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRawString28#1",
        source: ###"""
      _ = """
        interpolating \(##"""
          delimited \##("string")\#n\##n
          """##)
        """
      """###,
        origin: "RawStringTests.testRawString28",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRawString30#1",
        source: ##"""
      #"unused literal"#
      """##,
        origin: "RawStringTests.testRawString30",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRawString32#1",
        source: ##"""
      _ = #"This is a string"#
      """##,
        origin: "RawStringTests.testRawString32",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRawString33#1",
        source: ######"""
      _ = #####"This is a string"#####
      """######,
        origin: "RawStringTests.testRawString33",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRawString34#1",
        source: ###"""
      _ = #"enum\s+.+\{.*case\s+[:upper:]"#
      _ = #"Alice: "How long is forever?" White Rabbit: "Sometimes, just one second.""#
      _ = #"\#\#1"#
      _ = ##"\#1"##
      _ = #"c:\windows\system32"#
      _ = #"\d{3) \d{3} \d{4}"#
      _ = #"""
          a string with
          """
          in it
          """#
      _ = #"a raw string containing \r\n"#
      _ = #"""
          [
              {
                  "id": "12345",
                  "title": "A title that \"contains\" \\\""
              }
          ]
          """#
      _ = #"# #"#
      """###,
        origin: "RawStringTests.testRawString34",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRecovery6#1",
        source: """
      class Container<T> {
        func exists() -> Bool { return true }
      }
      """,
        origin: "RecoveryTests.testRecovery6",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRecovery8#1",
        source: """
      @xyz class BadAttributes {
        func exists() -> Bool { return true }
      }
      """,
        origin: "RecoveryTests.testRecovery8",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRecovery9#1",
        source: """
      func test(a: BadAttributes) -> () {
        _ = a.exists() // no-warning
      }
      """,
        origin: "RecoveryTests.testRecovery9",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRecovery11#1",
        source: """
      func braceStmt2() {
        { () in braceStmt2(); }
      }
      """,
        origin: "RecoveryTests.testRecovery11",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRecovery12#1",
        source: """
      func braceStmt3() {
        {
          undefinedIdentifier {}
        }
      }
      """,
        origin: "RecoveryTests.testRecovery12",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRecovery13#1",
        source: """
      static func toplevelStaticFunc() {}
      static struct StaticStruct {}
      static class StaticClass {}
      static protocol StaticProtocol {}
      static typealias StaticTypealias = Int
      class ClassWithStaticDecls {
        class var a = 42
      }
      """,
        origin: "RecoveryTests.testRecovery13",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRecovery27#1",
        source: """
      {
        missingControllingExprInRepeatWhile();
      }
      """,
        origin: "RecoveryTests.testRecovery27",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRecovery65#1",
        source: """
      _ = foobar // OK.
      """,
        origin: "RecoveryTests.testRecovery65",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRecovery111#1",
        source: """
      //===---
      """,
        origin: "RecoveryTests.testRecovery111",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRecovery112#1",
        source: """
      class Base {}
      """,
        origin: "RecoveryTests.testRecovery112",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRecovery113#1",
        source: """
      class ExprSuper1 {
        init() {
          super
        }
      }
      """,
        origin: "RecoveryTests.testRecovery113",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRecovery115#1",
        source: """
      //===--- Recovery for braces inside a nominal decl.
      """,
        origin: "RecoveryTests.testRecovery115",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRecovery117#1",
        source: """
      func use_BracesInsideNominalDecl1() {
        // Ensure that the typealias decl is not skipped.
        var _ : BracesInsideNominalDecl1.A // no-error
      }
      """,
        origin: "RecoveryTests.testRecovery117",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRecovery123#1",
        source: """
      class Base2<T> {
      }
      """,
        origin: "RecoveryTests.testRecovery123",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRecovery124#1",
        source: """
      class SubModule {
          class Base1 {}
          class Base2<T> {}
      }
      """,
        origin: "RecoveryTests.testRecovery124",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRecovery132#1",
        source: """
      Base=1 as Base=1
      """,
        origin: "RecoveryTests.testRecovery132",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRecovery152#1",
        source: """
      if var y = x, y == 0, var z = x {
        z = y; y = z
      }
      """,
        origin: "RecoveryTests.testRecovery152",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRecovery154#1",
        source: #"""
      // <rdar://problem/20883210> QoI: Following a "let" condition with boolean condition spouts nonsensical errors
      guard let x: Int? = 1, x == 1 else {  }
      """#,
        origin: "RecoveryTests.testRecovery154",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRecovery161#1",
        source: """
      // <rdar://problem/21369926> Malformed Swift Enums crash playground service
      enum Rank: Int {
        case Ace = 1
        case Two = 2.1
      }
      """,
        origin: "RecoveryTests.testRecovery161",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRecovery162#1",
        source: """
      // rdar://22240342 - Crash in diagRecursivePropertyAccess
      class r22240342 {
        lazy var xx: Int = {
          foo {
            let issueView = 42
            issueView.delegate = 12
          }
          return 42
          }()
      }
      """,
        origin: "RecoveryTests.testRecovery162",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRecovery165#1",
        source: """
      // <rdar://problem/23086402> Swift compiler crash in CSDiag
      protocol A23086402 {
        var b: B23086402 { get }
      }
      """,
        origin: "RecoveryTests.testRecovery165",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRecovery166#1",
        source: """
      protocol B23086402 {
        var c: [String] { get }
      }
      """,
        origin: "RecoveryTests.testRecovery166",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRecovery167#1",
        source: #"""
      func test23086402(a: A23086402) {
        print(a.b.c + "") // should not crash but: expected-error {{}}
      }
      """#,
        origin: "RecoveryTests.testRecovery167",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRecovery168#1",
        source: #"""
      // <rdar://problem/23550816> QoI: Poor diagnostic in argument list of "print" (varargs related)
      // The situation has changed. String now conforms to the RangeReplaceableCollection protocol
      // and `ss + s` becomes ambiguous. Disambiguation is provided with the unavailable overload
      // in order to produce a meaningful diagnostics. (Related: <rdar://problem/31763930>)
      func test23550816(ss: [String], s: String) {
        print(ss + s)
      }
      """#,
        origin: "RecoveryTests.testRecovery168",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRecovery169#1",
        source: """
      // <rdar://problem/23719432> [practicalswift] Compiler crashes on &(Int:_)
      func test23719432() {
        var x = 42
          &(Int:x)
      }
      """,
        origin: "RecoveryTests.testRecovery169",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRegexParseError1#1",
        source: """
      _ = /(/
      """,
        origin: "RegexParseErrorTests.testRegexParseError1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRegexParseError2#1",
        source: """
      _ = #/(/#
      """,
        origin: "RegexParseErrorTests.testRegexParseError2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRegexParseError4#1",
        source: """
      _ = /)/
      """,
        origin: "RegexParseErrorTests.testRegexParseError4",
        syntaxVersion: "604.0.0-prerelease-2026-06-05",
        compilerRejects: "expected expression after unary operator"
    ),
    SwiftSnippet(
        label: "testRegexParseError5#1",
        source: """
      _ = #/)/#
      """,
        origin: "RegexParseErrorTests.testRegexParseError5",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRegexParseError10#1",
        source: """
      _ = #/(?/#
      """,
        origin: "RegexParseErrorTests.testRegexParseError10",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRegexParseError11#1",
        source: """
      _ = #/(?'/#
      """,
        origin: "RegexParseErrorTests.testRegexParseError11",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRegexParseError12#1",
        source: """
      _ = #/(?'abc/#
      """,
        origin: "RegexParseErrorTests.testRegexParseError12",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRegexParseError13#1",
        source: """
      _ = #/(?'abc /#
      """,
        origin: "RegexParseErrorTests.testRegexParseError13",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRegexParseError15#1",
        source: #"""
      _ = #/\(?'abc/#
      """#,
        origin: "RegexParseErrorTests.testRegexParseError15",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRegexParseError19#1",
        source: """
      foo(#/(?/#, #/abc/#) 
      foo(#/(?C/#, #/abc/#)
      """,
        origin: "RegexParseErrorTests.testRegexParseError19",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRegexParseError20#1",
        source: """
      foo(#/(?'/#, #/abc/#)
      """,
        origin: "RegexParseErrorTests.testRegexParseError20",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRegex1#1",
        source: """
      _ = /abc/
      _ = #/abc/#
      _ = ##/abc/##
      """,
        origin: "RegexTests.testRegex1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRegex3#1",
        source: """
      foo(/abc/, #/abc/#, ##/abc/##)
      """,
        origin: "RegexTests.testRegex3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRegex4#1",
        source: """
      let arr = [/abc/, #/abc/#, ##/abc/##]
      """,
        origin: "RegexTests.testRegex4",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRegex5#1",
        source: #"""
      _ = /\w+/.self
      _ = #/\w+/#.self
      _ = ##/\w+/##.self
      """#,
        origin: "RegexTests.testRegex5",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRegex6#1",
        source: ##"""
      _ = /#\/\#\\/
      _ = #/#/\/\#\\/#
      _ = ##/#|\|\#\\/##
      """##,
        origin: "RegexTests.testRegex6",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testRegex7#1",
        source: """
      _ = (#/[*/#, #/+]/#, #/.]/#)
      """,
        origin: "RegexTests.testRegex7",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testResultBuilder1#1",
        source: """
      // rdar://70158735
      """,
        origin: "ResultBuilderTests.testResultBuilder1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testResultBuilder2#1",
        source: """
      @resultBuilder
      struct A<T> {
        static func buildBlock(_ values: Int...) -> Int { return 0 }
      }
      """,
        origin: "ResultBuilderTests.testResultBuilder2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testResultBuilder3#1",
        source: """
      struct B<T> {}
      """,
        origin: "ResultBuilderTests.testResultBuilder3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testResultBuilder4#1",
        source: """
      extension B {
        @resultBuilder
        struct Generic<U> {
          static func buildBlock(_ values: Int...) -> Int { return 0 }
        }
        @resultBuilder
        struct NonGeneric {
          static func buildBlock(_ values: Int...) -> Int { return 0 }
        }
      }
      """,
        origin: "ResultBuilderTests.testResultBuilder4",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testResultBuilder5#1",
        source: """
      @A<Float> var test0: Int {
        1
        2
        3
      }
      """,
        origin: "ResultBuilderTests.testResultBuilder5",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testResultBuilder6#1",
        source: """
      @B<Float>.NonGeneric var test1: Int {
        1
        2
        3
      }
      """,
        origin: "ResultBuilderTests.testResultBuilder6",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testResultBuilder7#1",
        source: """
      @B<Float>.Generic<Float> var test2: Int {
        1
        2
        3
      }
      """,
        origin: "ResultBuilderTests.testResultBuilder7",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSelfRebinding1#1",
        source: #"""
      class Writer {
          private var articleWritten = 47
          func stop() {
              let rest: () -> Void = { [weak self] in
                  let articleWritten = self?.articleWritten ?? 0
                  guard let `self` = self else {
                      return
                  }
                  self.articleWritten = articleWritten
              }
              fatalError("I'm running out of time")
              rest()
          }
          func nonStop() {
              let write: () -> Void = { [weak self] in
                  self?.articleWritten += 1
                  if let self = self {
                      self.articleWritten += 1
                  }
                  if let `self` = self {
                      self.articleWritten += 1
                  }
                  guard let self = self else {
                      return
                  }
                  self.articleWritten += 1
              }
              write()
          }
      }
      """#,
        origin: "SelfRebindingTests.testSelfRebinding1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSelfRebinding3#1",
        source: """
      class MyCls {
          func something() {}
          func test() {
              let `self` = Writer() // Even if `self` is shadowed,
              something() // this should still refer `MyCls.something`.
          }
      }
      """,
        origin: "SelfRebindingTests.testSelfRebinding3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSelfRebinding4#1",
        source: """
      // https://github.com/apple/swift/issues/47136
      // Method called 'self' can be confused with regular 'self'
      """,
        origin: "SelfRebindingTests.testSelfRebinding4",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSelfRebinding5#1",
        source: """
      func funcThatReturnsSomething(_ any: Any) -> Any {
          any
      }
      """,
        origin: "SelfRebindingTests.testSelfRebinding5",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSelfRebinding6#1",
        source: """
      struct TypeWithSelfMethod {
          let property = self
          // Existing warning expected, not confusable
          let property2 = self()
          let propertyFromClosure: () = {
              print(self)
          }()
          let propertyFromFunc = funcThatReturnsSomething(self)
          let propertyFromFunc2 = funcThatReturnsSomething(TypeWithSelfMethod.self) // OK
          func `self`() {
          }
      }
      """,
        origin: "SelfRebindingTests.testSelfRebinding6",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSelfRebinding7#1",
        source: """
      /// Test fix_unqualified_access_member_named_self doesn't appear for computed var called `self`
      /// it can't currently be referenced as a static member -- unlike a method with the same name
      struct TypeWithSelfComputedVar {
          let property = self
          let propertyFromClosure: () = {
              print(self)
          }()
          let propertyFromFunc = funcThatReturnsSomething(self)
          var `self`: () {
              ()
          }
      }
      """,
        origin: "SelfRebindingTests.testSelfRebinding7",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSelfRebinding8#1",
        source: """
      /// Test fix_unqualified_access_member_named_self doesn't appear for property called `self`
      /// it can't currently be referenced as a static member -- unlike a method with the same name
      struct TypeWithSelfProperty {
          let property = self
          let propertyFromClosure: () = {
              print(self)
          }()
          let propertyFromFunc = funcThatReturnsSomething(self)
          let `self`: () = ()
      }
      """,
        origin: "SelfRebindingTests.testSelfRebinding8",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSelfRebinding9#1",
        source: """
      enum EnumCaseNamedSelf {
          case `self`
          init() {
              self = .self // OK
              self = .`self` // OK
              self = EnumCaseNamedSelf.`self` // OK
          }
      }
      """,
        origin: "SelfRebindingTests.testSelfRebinding9",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSelfRebinding10#1",
        source: """
      // rdar://90624344 - warning about `self` which cannot be fixed because it's located in implicitly generated code.
      struct TestImplicitSelfUse : Codable {
        let `self`: Int // Ok
      }
      """,
        origin: "SelfRebindingTests.testSelfRebinding10",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSemicolon1#1",
        source: #"""
      let a = 42;
      var b = "b";
      """#,
        origin: "SemicolonTests.testSemicolon1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSemicolon2#1",
        source: """
      struct A {
          var a1: Int;
          let a2: Int ;
          var a3: Int;let a4: Int
          var a5: Int; let a6: Int;
      };
      """,
        origin: "SemicolonTests.testSemicolon2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSemicolon3#1",
        source: """
      enum B {
          case B1;
          case B2(value: Int);
          case B3
          case B4; case B5 ; case B6;
      };
      """,
        origin: "SemicolonTests.testSemicolon3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSemicolon4#1",
        source: """
      class C {
          var x: Int;
          let y = 3.14159;
          init(x: Int) { self.x = x; }
      };
      """,
        origin: "SemicolonTests.testSemicolon4",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSemicolon5#1",
        source: """
      typealias C1 = C;
      """,
        origin: "SemicolonTests.testSemicolon5",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSemicolon6#1",
        source: """
      protocol D {
          var foo: () -> Int { get };
      }
      """,
        origin: "SemicolonTests.testSemicolon6",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSemicolon7#1",
        source: """
      struct D1: D {
          let foo = { return 42; };
      }
      func e() -> Bool {
          return false;
      }
      """,
        origin: "SemicolonTests.testSemicolon7",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSemicolon8#1",
        source: """
      import Swift;
      """,
        origin: "SemicolonTests.testSemicolon8",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSemicolon9#1",
        source: """
      for i in 1..<1000 {
          if i % 2 == 1 {
              break;
          };
      }
      """,
        origin: "SemicolonTests.testSemicolon9",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSemicolon10#1",
        source: """
      let six = (1..<3).reduce(0, +);
      """,
        origin: "SemicolonTests.testSemicolon10",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSemicolon11#1",
        source: """
      func lessThanTwo(input: UInt) -> Bool {
          switch input {
          case 0:     return true;
          case 1, 2:  return true;
          default:
              return false;
          }
      }
      """,
        origin: "SemicolonTests.testSemicolon11",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSemicolon12#1",
        source: """
      enum StarWars {
          enum Quality { case 😀; case 🙂; case 😐; case 😏; case 😞 };
          case Ep4; case Ep5; case Ep6
          case Ep1, Ep2; case Ep3;
      };
      """,
        origin: "SemicolonTests.testSemicolon12",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSubscripting1#1",
        source: """
      struct X { }
      """,
        origin: "SubscriptingTests.testSubscripting1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSubscripting2#1",
        source: """
      // Simple examples
      struct X1 {
        var stored: Int
        subscript(i: Int) -> Int {
          get {
            return stored
          }
          mutating
          set {
            stored = newValue
          }
        }
      }
      """,
        origin: "SubscriptingTests.testSubscripting2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSubscripting3#1",
        source: """
      struct X2 {
        var stored: Int
        subscript(i: Int) -> Int {
          get {
            return stored + i
          }
          set(v) {
            stored = v - i
          }
        }
      }
      """,
        origin: "SubscriptingTests.testSubscripting3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSubscripting4#1",
        source: """
      struct X3 {
        var stored: Int
        subscript(_: Int) -> Int {
          get {
            return stored
          }
          set(v) {
            stored = v
          }
        }
      }
      """,
        origin: "SubscriptingTests.testSubscripting4",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSubscripting5#1",
        source: """
      struct X4 {
        var stored: Int
        subscript(i: Int, j: Int) -> Int {
          get {
            return stored + i + j
          }
          mutating
          set(v) {
            stored = v + i - j
          }
        }
      }
      """,
        origin: "SubscriptingTests.testSubscripting5",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSubscripting6#1",
        source: """
      struct X5 {
        static var stored: Int = 1
        static subscript(i: Int) -> Int {
          get {
            return stored + i
          }
          set {
            stored = newValue - i
          }
        }
      }
      """,
        origin: "SubscriptingTests.testSubscripting6",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSubscripting7#1",
        source: """
      class X6 {
        static var stored: Int = 1
        class subscript(i: Int) -> Int {
          get {
            return stored + i
          }
          set {
            stored = newValue - i
          }
        }
      }
      """,
        origin: "SubscriptingTests.testSubscripting7",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSubscripting8#1",
        source: """
      struct Y1 {
        var stored: Int
        subscript(_: i, j: Int) -> Int {
          get {
            return stored + j
          }
          set {
            stored = j
          }
        }
      }
      """,
        origin: "SubscriptingTests.testSubscripting8",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSubscripting9#1",
        source: """
      // Mutating getters on constants
      // https://github.com/apple/swift/issues/43457
      """,
        origin: "SubscriptingTests.testSubscripting9",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSubscripting10#1",
        source: """
      struct Y2 {
        subscript(_: Int) -> Int {
          mutating get { return 0 }
        }
      }
      """,
        origin: "SubscriptingTests.testSubscripting10",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSubscripting11#1",
        source: """
      let y2 = Y2()
      _ = y2[0]
      """,
        origin: "SubscriptingTests.testSubscripting11",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSubscripting17#1",
        source: """
      struct A5 {
        subscript(i : Int) -> Int
      }
      """,
        origin: "SubscriptingTests.testSubscripting17",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSubscripting19#1",
        source: """
      struct A7 {
        class subscript(a: Float) -> Int {
          get {
            return 42
          }
        }
      }
      """,
        origin: "SubscriptingTests.testSubscripting19",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSubscripting20#1",
        source: """
      class A7b {
        class static subscript(a: Float) -> Int {
          get {
            return 42
          }
        }
      }
      """,
        origin: "SubscriptingTests.testSubscripting20",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSuper1#1",
        source: """
      class B {
        var foo: Int
        func bar() {}
        init() {}
        init(x: Int) {}
        subscript(x: Int) -> Int {
          get {}
          set {}
        }
      }
      """,
        origin: "SuperTests.testSuper1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSuper2a#1",
        source: #"""
      class D : B {
        override init() {
          super.init()
          super.init(42)
        }
      }
      """#,
        origin: "SuperTests.testSuper2a",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSuper2b#1",
        source: #"""
      class D : B {
        override init(x:Int) {
          let _: () -> B = super.init
        }
      }
      """#,
        origin: "SuperTests.testSuper2b",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSuper2c#1",
        source: #"""
      class D : B {
        convenience init(y:Int) {
          let _: () -> D = self.init
        }
      }
      """#,
        origin: "SuperTests.testSuper2c",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSuper2d#1",
        source: #"""
      class D : B {
        init(z: Int) {
          super
            .init(x: z)
        }
      }
      """#,
        origin: "SuperTests.testSuper2d",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSuper2e#1",
        source: #"""
      class D : B {
        func super_calls() {
          super.foo
          super.foo.bar
          super.bar
          super.bar()
          super.init
          super.init()
          super.init(0)
          super[0]
          super
            .bar()
        }
      }
      """#,
        origin: "SuperTests.testSuper2e",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSuper2g#1",
        source: #"""
      class D : B {
        func bad_super_2() {
          super(0)
        }
      }
      """#,
        origin: "SuperTests.testSuper2g",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSuper2h#1",
        source: #"""
      class D : B {
        func bad_super_3() {
          super
            [1]
        }
      }
      """#,
        origin: "SuperTests.testSuper2h",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSuper3#1",
        source: """
      class Closures : B {
        func captureWeak() {
          let g = { [weak self] () -> Void in // expected-note * {{'self' explicitly captured here}}
            super.foo()
          }
          g()
        }
        func captureUnowned() {
          let g = { [unowned self] () -> Void in // expected-note * {{'self' explicitly captured here}}
            super.foo()
          }
          g()
        }
        func nestedInner() {
          let g = { () -> Void in
            let h = { [weak self] () -> Void in // expected-note * {{'self' explicitly captured here}}
              super.foo()
              nil ?? super.foo()
            }
            h()
          }
          g()
        }
        func nestedOuter() {
          let g = { [weak self] () -> Void in // expected-note * {{'self' explicitly captured here}}
            let h = { () -> Void in
              super.foo()
              nil ?? super.foo()
            }
            h()
          }
          g()
        }
      }
      """,
        origin: "SuperTests.testSuper3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch1#1",
        source: """
      func ~= (x: (Int,Int), y: (Int,Int)) -> Bool {
        return true
      }
      """,
        origin: "SwitchTests.testSwitch1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch8#1",
        source: """
      var x: Int
      """,
        origin: "SwitchTests.testSwitch8",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch9#1",
        source: """
      switch x {}
      """,
        origin: "SwitchTests.testSwitch9",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch10#1",
        source: """
      switch x {
      case 0:
        x = 0
      // Multiple patterns per case
      case 1, 2, 3:
        x = 0
      // 'where' guard
      case _ where x % 2 == 0:
        x = 1
        x = 2
        x = 3
      case _ where x % 2 == 0,
           _ where x % 3 == 0:
        x = 1
      case 10,
           _ where x % 3 == 0:
        x = 1
      case _ where x % 2 == 0,
           20:
        x = 1
      case var y where y % 2 == 0:
        x = y + 1
      case _ where 0:
        x = 0
      default:
        x = 1
      }
      """,
        origin: "SwitchTests.testSwitch10",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch11#1",
        source: """
      // Multiple cases per case block
      switch x {
      case 0:
      case 1:
        x = 0
      }
      """,
        origin: "SwitchTests.testSwitch11",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch12#1",
        source: """
      switch x {
      case 0:
      default:
        x = 0
      }
      """,
        origin: "SwitchTests.testSwitch12",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch13#1",
        source: """
      switch x {
      case 0:
        x = 0
      case 1:
      }
      """,
        origin: "SwitchTests.testSwitch13",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch14#1",
        source: """
      switch x {
      case 0:
        x = 0
      default:
      }
      """,
        origin: "SwitchTests.testSwitch14",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch17#1",
        source: """
      switch x {
      default:
        x = 0
      default:
        x = 0
      }
      """,
        origin: "SwitchTests.testSwitch17",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch20#1",
        source: """
      switch x {
      default:
      case 0:
        x = 0
      }
      """,
        origin: "SwitchTests.testSwitch20",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch21#1",
        source: """
      switch x {
      default:
      default:
        x = 0
      }
      """,
        origin: "SwitchTests.testSwitch21",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch23#1",
        source: """
      switch x {
      case 0:
      }
      """,
        origin: "SwitchTests.testSwitch23",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch24#1",
        source: """
      switch x {
      case 0:
      case 1:
        x = 0
      }
      """,
        origin: "SwitchTests.testSwitch24",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch25#1",
        source: """
      switch x {
      case 0:
        x = 0
      case 1:
      }
      """,
        origin: "SwitchTests.testSwitch25",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch27#1",
        source: """
      fallthrough
      """,
        origin: "SwitchTests.testSwitch27",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch28#1",
        source: """
      switch x {
      case 0:
        fallthrough
      case 1:
        fallthrough
      default:
        fallthrough
      }
      """,
        origin: "SwitchTests.testSwitch28",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch29#1",
        source: """
      // Fallthrough can transfer control anywhere within a case and can appear
      // multiple times in the same case.
      switch x {
      case 0:
        if true { fallthrough }
        if false { fallthrough }
        x += 1
      default:
        x += 1
      }
      """,
        origin: "SwitchTests.testSwitch29",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch30#1",
        source: """
      // Cases cannot contain 'var' bindings if there are multiple matching patterns
      // attached to a block. They may however contain other non-binding patterns.
      """,
        origin: "SwitchTests.testSwitch30",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch31#1",
        source: """
      var t = (1, 2)
      """,
        origin: "SwitchTests.testSwitch31",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch32#1",
        source: """
      switch t {
      case (var a, 2), (1, _):
        ()
      case (_, 2), (var a, _):
        ()
      case (var a, 2), (1, var b):
        ()
      case (var a, 2):
      case (1, _):
        ()
      case (_, 2):
      case (1, var a):
        ()
      case (var a, 2):
      case (1, var b):
        ()
      case (1, let b): // let bindings expected-warning {{immutable value 'b' was never used; consider replacing with '_' or removing it}}
        ()
      case (_, 2), (let a, _):
        ()
      // OK
      case (_, 2), (1, _):
        ()
      case (_, var a), (_, var a):
        ()
      case (var a, var b), (var b, var a):
        ()
      case (_, 2):
      case (1, _):
        ()
      }
      """,
        origin: "SwitchTests.testSwitch32",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch33#1",
        source: """
      func patternVarUsedInAnotherPattern(x: Int) {
        switch x {
        case let a,
             value:
          break
        }
      }
      """,
        origin: "SwitchTests.testSwitch33",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch34#1",
        source: """
      // Fallthroughs can only transfer control into a case label with bindings if the previous case binds a superset of those vars.
      switch t {
      case (1, 2):
        fallthrough
      case (var a, var b):
        t = (b, a)
      }
      """,
        origin: "SwitchTests.testSwitch34",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch35#1",
        source: """
      switch t { // specifically notice on next line that we shouldn't complain that a is unused - just never mutated
      case (var a, let b):
        t = (b, b)
        fallthrough // ok - notice that subset of bound variables falling through is fine
      case (2, let a):
        t = (a, a)
      }
      """,
        origin: "SwitchTests.testSwitch35",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch36#1",
        source: """
      func patternVarDiffType(x: Int, y: Double) {
        switch (x, y) {
        case (1, let a):
          fallthrough
        case (let a, _):
          break
        }
      }
      """,
        origin: "SwitchTests.testSwitch36",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch37#1",
        source: """
      func patternVarDiffMutability(x: Int, y: Double) {
        switch x {
        case let a where a < 5, var a where a > 10:
          break
        default:
          break
        }
        switch (x, y) {
        // Would be nice to have a fixit in the following line if we detect that all bindings in the same pattern have the same problem.
        case let (a, b) where a < 5, var (a, b) where a > 10: // expected-error 2{{'var' pattern binding must match previous 'let' pattern binding}}{{none}}
          break
        case (let a, var b) where a < 5, (let a, let b) where a > 10:
          break
        case (let a, let b) where a < 5, (var a, let b) where a > 10, (let a, var b) where a == 8:
          break
        default:
          break
        }
      }
      """,
        origin: "SwitchTests.testSwitch37",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch38#1",
        source: """
      func test_label(x : Int) {
      Gronk:
        switch x {
        case 42: return
        }
      }
      """,
        origin: "SwitchTests.testSwitch38",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch39#1",
        source: """
      func enumElementSyntaxOnTuple() {
        switch (1, 1) {
        case .Bar:
          break
        default:
          break
        }
      }
      """,
        origin: "SwitchTests.testSwitch39",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch40#1",
        source: """
      // https://github.com/apple/swift/issues/42798
      enum Whatever { case Thing }
      func f0(values: [Whatever]) {
          switch value {
          case .Thing: // Ok. Don't emit diagnostics about enum case not found in type <<error type>>.
              break
          }
      }
      """,
        origin: "SwitchTests.testSwitch40",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch41#1",
        source: #"""
      // https://github.com/apple/swift/issues/43334
      // https://github.com/apple/swift/issues/43335
      enum Whichever {
        case Thing
        static let title = "title"
        static let alias: Whichever = .Thing
      }
      func f1(x: String, y: Whichever) {
        switch x {
          case Whichever.title: // Ok. Don't emit diagnostics for static member of enum.
              break
          case Whichever.buzz:
              break
          case Whichever.alias:
          default:
            break
        }
        switch y {
          case Whichever.Thing: // Ok.
              break
          case Whichever.alias: // Ok. Don't emit diagnostics for static member of enum.
              break
          case Whichever.title:
              break
        }
        switch y {
          case .alias:
            break
          default:
            break
        }
      }
      """#,
        origin: "SwitchTests.testSwitch41",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch42#1",
        source: """
      switch Whatever.Thing {
      case .Thing:
      @unknown case _:
        x = 0
      }
      """,
        origin: "SwitchTests.testSwitch42",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch43#1",
        source: """
      switch Whatever.Thing {
      case .Thing:
      @unknown default:
        x = 0
      }
      """,
        origin: "SwitchTests.testSwitch43",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch44#1",
        source: """
      switch Whatever.Thing {
      case .Thing:
        x = 0
      @unknown case _:
      }
      """,
        origin: "SwitchTests.testSwitch44",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch45#1",
        source: """
      switch Whatever.Thing {
      case .Thing:
        x = 0
      @unknown default:
      }
      """,
        origin: "SwitchTests.testSwitch45",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch46#1",
        source: """
      switch Whatever.Thing {
      @unknown default:
        x = 0
      default:
        x = 0
      case .Thing:
        x = 0
      }
      """,
        origin: "SwitchTests.testSwitch46",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch47#1",
        source: """
      switch Whatever.Thing {
      default:
        x = 0
      @unknown case _:
        x = 0
      case .Thing:
        x = 0
      }
      """,
        origin: "SwitchTests.testSwitch47",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch48#1",
        source: """
      switch Whatever.Thing {
      default:
        x = 0
      @unknown default:
        x = 0
      case .Thing:
        x = 0
      }
      """,
        origin: "SwitchTests.testSwitch48",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch50#1",
        source: """
      switch Whatever.Thing {
      @unknown case _:
        fallthrough
      }
      """,
        origin: "SwitchTests.testSwitch50",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch51#1",
        source: """
      switch Whatever.Thing {
      @unknown case _:
        fallthrough
      case .Thing:
        break
      }
      """,
        origin: "SwitchTests.testSwitch51",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch52#1",
        source: """
      switch Whatever.Thing {
      @unknown default:
        fallthrough
      case .Thing:
        break
      }
      """,
        origin: "SwitchTests.testSwitch52",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch53#1",
        source: """
      switch Whatever.Thing {
      @unknown case _, _:
        break
      }
      """,
        origin: "SwitchTests.testSwitch53",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch54#1",
        source: """
      switch Whatever.Thing {
      @unknown case _, _, _:
        break
      }
      """,
        origin: "SwitchTests.testSwitch54",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch55#1",
        source: """
      switch Whatever.Thing {
      @unknown case let value:
        _ = value
      }
      """,
        origin: "SwitchTests.testSwitch55",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch56#1",
        source: """
      switch (Whatever.Thing, Whatever.Thing) {
      @unknown case (_, _):
        break
      }
      """,
        origin: "SwitchTests.testSwitch56",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch57#1",
        source: """
      switch Whatever.Thing {
      @unknown case is Whatever:
        break
      }
      """,
        origin: "SwitchTests.testSwitch57",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch58#1",
        source: """
      switch Whatever.Thing {
      @unknown case .Thing:
        break
      }
      """,
        origin: "SwitchTests.testSwitch58",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch59#1",
        source: """
      switch Whatever.Thing {
      @unknown case (_): // okay
        break
      }
      """,
        origin: "SwitchTests.testSwitch59",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch60#1",
        source: """
      switch Whatever.Thing {
      @unknown case _ where x == 0:
        break
      }
      """,
        origin: "SwitchTests.testSwitch60",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch62#1",
        source: """
      switch Whatever.Thing {
      case .Thing:
        x = 0
      #if true
      @unknown case _:
        x = 0
      #endif
      }
      """,
        origin: "SwitchTests.testSwitch62",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch63#1",
        source: """
      switch x {
      case 0:
        break
      @garbage case _:
        break
      }
      """,
        origin: "SwitchTests.testSwitch63",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch65#1",
        source: """
      @unknown let _ = 1
      """,
        origin: "SwitchTests.testSwitch65",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch66#1",
        source: """
      switch x {
      case _:
        @unknown let _ = 1
      }
      """,
        origin: "SwitchTests.testSwitch66",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch68#1",
        source: """
      switch x {
      case 1:
        break
      @unknown case _:
        break
      }
      """,
        origin: "SwitchTests.testSwitch68",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch69#1",
        source: """
      switch x {
      @unknown case _:
        break
      }
      """,
        origin: "SwitchTests.testSwitch69",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch70#1",
        source: """
      switch x {
      @unknown default:
        break
      }
      """,
        origin: "SwitchTests.testSwitch70",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch71#1",
        source: """
      switch Whatever.Thing {
      case .Thing:
        break
      @unknown case _:
        break
      @unknown case _:
        break
      }
      """,
        origin: "SwitchTests.testSwitch71",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch72#1",
        source: """
      switch Whatever.Thing {
      case .Thing:
        break
      @unknown case _:
        break
      @unknown default:
        break
      }
      """,
        origin: "SwitchTests.testSwitch72",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch73#1",
        source: """
      switch Whatever.Thing {
      case .Thing:
        break
      @unknown default:
        break
      @unknown default:
        break
      }
      """,
        origin: "SwitchTests.testSwitch73",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch74#1",
        source: """
      switch Whatever.Thing {
      @unknown case _:
        break
      @unknown case _:
        break
      }
      """,
        origin: "SwitchTests.testSwitch74",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch75#1",
        source: """
      switch Whatever.Thing {
      @unknown case _:
        break
      @unknown default:
        break
      }
      """,
        origin: "SwitchTests.testSwitch75",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch76#1",
        source: """
      switch Whatever.Thing {
      @unknown default:
        break
      @unknown default:
        break
      }
      """,
        origin: "SwitchTests.testSwitch76",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch77#1",
        source: """
      switch x {
      @unknown case _:
        break
      @unknown case _:
        break
      }
      """,
        origin: "SwitchTests.testSwitch77",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch78#1",
        source: """
      switch x {
      @unknown case _:
        break
      @unknown default:
        break
      }
      """,
        origin: "SwitchTests.testSwitch78",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch79#1",
        source: """
      switch x {
      @unknown default:
        break
      @unknown default:
        break
      }
      """,
        origin: "SwitchTests.testSwitch79",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitch80#1",
        source: """
      func testReturnBeforeUnknownDefault() {
        switch x {
        case 1:
          return
        @unknown default:
          break
        }
      }
      """,
        origin: "SwitchTests.testSwitch80",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testToplevelLibrary1#1",
        source: """
      // make sure trailing semicolons are valid syntax in toplevel library code.
      var x = 4;
      """,
        origin: "ToplevelLibraryTests.testToplevelLibrary1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testToplevelLibraryInvalid1#1",
        source: """
      let x = 42
      x + x;
      x + x;
      // Make sure we don't crash on closures at the top level
      ({ })
      ({ 5 }())
      """,
        origin: "ToplevelLibraryTests.testToplevelLibraryInvalid1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTrailingClosures1#1",
        source: """
      func foo<T, U>(a: () -> T, b: () -> U) {}
      """,
        origin: "TrailingClosuresTests.testTrailingClosures1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTrailingClosures2#1",
        source: #"""
      foo { 42 }
      b: { "" }
      """#,
        origin: "TrailingClosuresTests.testTrailingClosures2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTrailingClosures3#1",
        source: #"""
      foo { 42 } b: { "" }
      """#,
        origin: "TrailingClosuresTests.testTrailingClosures3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTrailingClosures4#1",
        source: """
      func when<T>(_ condition: @autoclosure () -> Bool,
                   `then` trueBranch: () -> T,
                   `else` falseBranch: () -> T) -> T {
        return condition() ? trueBranch() : falseBranch()
      }
      """,
        origin: "TrailingClosuresTests.testTrailingClosures4",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTrailingClosures5#1",
        source: """
      let _ = when (2 < 3) { 3 } else: { 4 }
      """,
        origin: "TrailingClosuresTests.testTrailingClosures5",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTrailingClosures6#1",
        source: """
      struct S {
        static func foo(a: Int = 42, b: (inout Int) -> Void) -> S {
          return S()
        }
        static func foo(a: Int = 42, ab: () -> Void, b: (inout Int) -> Void) -> S {
          return S()
        }
        subscript(v v: () -> Int) -> Int {
          get { return v() }
        }
        subscript(u u: () -> Int, v v: () -> Int) -> Int {
          get { return u() + v() }
        }
        subscript(cond: Bool, v v: () -> Int) -> Int {
          get { return cond ? 0 : v() }
        }
        subscript(cond: Bool, u u: () -> Int, v v: () -> Int) -> Int {
          get { return cond ? u() : v() }
        }
      }
      """,
        origin: "TrailingClosuresTests.testTrailingClosures6",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTrailingClosures7#1",
        source: """
      let _: S = .foo {
        $0 = $0 + 1
      }
      """,
        origin: "TrailingClosuresTests.testTrailingClosures7",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTrailingClosures8#1",
        source: """
      let _: S = .foo {} b: { $0 = $0 + 1 }
      """,
        origin: "TrailingClosuresTests.testTrailingClosures8",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTrailingClosures9#1",
        source: """
      func bar(_ s: S) {
        _ = s[] {
          42
        }
        _ = s[] {
          21
        } v: {
          42
        }
        _ = s[true] {
          42
        }
        _ = s[true] {
          21
        } v: {
          42
        }
      }
      """,
        origin: "TrailingClosuresTests.testTrailingClosures9",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTrailingClosures10#1",
        source: """
      func multiple_trailing_with_defaults(
        duration: Int,
        animations: (() -> Void)? = nil,
        completion: (() -> Void)? = nil) {}
      """,
        origin: "TrailingClosuresTests.testTrailingClosures10",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTrailingClosures11#1",
        source: """
      multiple_trailing_with_defaults(duration: 42) {}
      """,
        origin: "TrailingClosuresTests.testTrailingClosures11",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTrailingClosures12#1",
        source: """
      multiple_trailing_with_defaults(duration: 42) {} completion: {}
      """,
        origin: "TrailingClosuresTests.testTrailingClosures12",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTrailingClosures13a#1",
        source: """
      fn {} g: {}
      fn {} _: {}
      multiple {} _: { }
      mixed_args_1 {} _: {}
      mixed_args_1 {} a: {}  //  {{none}}
      mixed_args_2 {} a: {} _: {}
      mixed_args_2 {} _: {} //  {{none}}
      mixed_args_2 {} _: {} _: {} //  {{none}}
      """,
        origin: "TrailingClosuresTests.testTrailingClosures13a",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTrailingClosures15#1",
        source: """
      func f() -> Int { 42 }
      """,
        origin: "TrailingClosuresTests.testTrailingClosures15",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTrailingClosures16#1",
        source: """
      // This should be interpreted as a trailing closure, instead of being
      // interpreted as a computed property with undesired initial value.
      struct TrickyTest {
          var x : Int = f () {
              3
          }
      }
      """,
        origin: "TrailingClosuresTests.testTrailingClosures16",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTrailingSemi1#1",
        source: """
      struct S {
        var a : Int ;
        func b () {};
        static func c () {};
      }
      """,
        origin: "TrailingSemiTests.testTrailingSemi1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTrailingSemi5#1",
        source: """
      protocol P {
        var a : Int { get };
        func b ();
        static func c ();
      }
      """,
        origin: "TrailingSemiTests.testTrailingSemi5",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTry1#1",
        source: """
      // Intentionally has lower precedence than assignments and ?:
      infix operator %%%% : LowPrecedence
      precedencegroup LowPrecedence {
        associativity: none
        lowerThan: AssignmentPrecedence
      }
      func %%%%<T, U>(x: T, y: U) -> Int { return 0 }
      """,
        origin: "TryTests.testTry1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTry2#1",
        source: """
      // Intentionally has lower precedence between assignments and ?:
      infix operator %%% : MiddlingPrecedence
      precedencegroup MiddlingPrecedence {
        associativity: none
        higherThan: AssignmentPrecedence
        lowerThan: TernaryPrecedence
      }
      func %%%<T, U>(x: T, y: U) -> Int { return 1 }
      """,
        origin: "TryTests.testTry2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTry3#1",
        source: """
      func foo() throws -> Int { return 0 }
      func bar() throws -> Int { return 0 }
      """,
        origin: "TryTests.testTry3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTry4#1",
        source: """
      var x = try foo() + bar()
      x = try foo() + bar()
      x += try foo() + bar()
      x += try foo() %%%% bar()
      x += try foo() %%% bar()
      x = foo() + try bar()
      """,
        origin: "TryTests.testTry4",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTry5#1",
        source: """
      var y = true ? try foo() : try bar() + 0
      var z = true ? try foo() : try bar() %%% 0
      """,
        origin: "TryTests.testTry5",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTry6#1",
        source: """
      var a = try! foo() + bar()
      a = try! foo() + bar()
      a += try! foo() + bar()
      a += try! foo() %%%% bar()
      a += try! foo() %%% bar()
      a = foo() + try! bar()
      """,
        origin: "TryTests.testTry6",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTry7#1",
        source: """
      var b = true ? try! foo() : try! bar() + 0
      var c = true ? try! foo() : try! bar() %%% 0
      """,
        origin: "TryTests.testTry7",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTry8#1",
        source: """
      infix operator ?+= : AssignmentPrecedence
      func ?+=(lhs: inout Int?, rhs: Int?) {
        lhs = lhs! + rhs!
      }
      """,
        origin: "TryTests.testTry8",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTry9#1",
        source: """
      var i = try? foo() + bar()
      let _: Double = i
      i = try? foo() + bar()
      i ?+= try? foo() + bar()
      i ?+= try? foo() %%%% bar()
      i ?+= try? foo() %%% bar()
      _ = foo() == try? bar()
      _ = (try? foo()) == bar()
      _ = foo() == (try? bar())
      _ = (try? foo()) == (try? bar())
      """,
        origin: "TryTests.testTry9",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTry10#1",
        source: """
      let j = true ? try? foo() : try? bar() + 0
      let k = true ? try? foo() : try? bar() %%% 0
      """,
        origin: "TryTests.testTry10",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTry13#1",
        source: #"""
      // Test operators.
      func *(a : String, b : String) throws -> Int { return 42 }
      let _ = "foo"
              *
              "bar"
      let _ = try! "foo"*"bar"
      let _ = try? "foo"*"bar"
      let _ = (try? "foo"*"bar") ?? 0
      """#,
        origin: "TryTests.testTry13",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTry14#1",
        source: """
      // <rdar://problem/21414023> Assertion failure when compiling function that takes throwing functions and rethrows
      func rethrowsDispatchError(handleError: ((Error) throws -> ()), body: () throws -> ()) rethrows {
        do {
          body()
        } catch {
        }
      }
      """,
        origin: "TryTests.testTry14",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTry15#1",
        source: """
      // <rdar://problem/21432429> Calling rethrows from rethrows crashes Swift compiler
      struct r21432429 {
        func x(_ f: () throws -> ()) rethrows {}
        func y(_ f: () throws -> ()) rethrows {
          x(f)
        }
      }
      """,
        origin: "TryTests.testTry15",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTry16#1",
        source: """
      // <rdar://problem/21427855> Swift 2: Omitting try from call to throwing closure in rethrowing function crashes compiler
      func callThrowingClosureWithoutTry(closure: (Int) throws -> Int) rethrows {
        closure(0)
      }
      """,
        origin: "TryTests.testTry16",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTry17#1",
        source: """
      func producesOptional() throws -> Int? { return nil }
      let _: String = try? producesOptional()
      """,
        origin: "TryTests.testTry17",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTry18#1",
        source: """
      let _ = (try? foo())!!
      """,
        origin: "TryTests.testTry18",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTry19#1",
        source: """
      func producesDoubleOptional() throws -> Int?? { return 3 }
      let _: String = try? producesDoubleOptional()
      """,
        origin: "TryTests.testTry19",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTry20#1",
        source: """
      func maybeThrow() throws {}
      try maybeThrow() // okay
      try! maybeThrow() // okay
      try? maybeThrow() // okay since return type of maybeThrow is Void
      _ = try? maybeThrow() // okay
      """,
        origin: "TryTests.testTry20",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTry21#1",
        source: """
      let _: () -> Void = { try! maybeThrow() } // okay
      let _: () -> Void = { try? maybeThrow() } // okay since return type of maybeThrow is Void
      """,
        origin: "TryTests.testTry21",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTry22#1",
        source: """
      if try? maybeThrow() {
      }
      let _: Int = try? foo()
      """,
        origin: "TryTests.testTry22",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTry23#1",
        source: """
      class X {}
      func test(_: X) {}
      func producesObject() throws -> AnyObject { return X() }
      test(try producesObject())
      """,
        origin: "TryTests.testTry23",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTry24#1",
        source: #"""
      _ = "a\(try maybeThrow())b"
      _ = try "a\(maybeThrow())b"
      _ = "a\(maybeThrow())"
      """#,
        origin: "TryTests.testTry24",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTry25#1",
        source: """
      extension DefaultStringInterpolation {
        mutating func appendInterpolation() throws {}
      }
      """,
        origin: "TryTests.testTry25",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTry26#1",
        source: #"""
      _ = try "a\()b"
      _ = "a\()b"
      _ = try "\() \(1)"
      """#,
        origin: "TryTests.testTry26",
        syntaxVersion: "604.0.0-prerelease-2026-06-05",
        compilerRejects: "missing argument for parameter #1 in call"
    ),
    SwiftSnippet(
        label: "testTry27#1",
        source: """
      func testGenericOptionalTry<T>(_ call: () throws -> T ) {
        let _: String = try? call()
      }
      """,
        origin: "TryTests.testTry27",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTry28#1",
        source: """
      func genericOptionalTry<T>(_ call: () throws -> T ) -> T? {
        let x = try? call() // no error expected
        return x
      }
      """,
        origin: "TryTests.testTry28",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTry29#1",
        source: """
      // Test with a non-optional type
      let _: String = genericOptionalTry({ () throws -> Int in return 3 })
      """,
        origin: "TryTests.testTry29",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTry30#1",
        source: """
      // Test with an optional type
      let _: String = genericOptionalTry({ () throws -> Int? in return nil })
      """,
        origin: "TryTests.testTry30",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTry31#1",
        source: """
      func produceAny() throws -> Any {
        return 3
      }
      """,
        origin: "TryTests.testTry31",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTry32#1",
        source: """
      let _: Int? = try? produceAny() as? Int
      let _: Int?? = (try? produceAny()) as? Int // good
      let _: String = try? produceAny() as? Int
      let _: String = (try? produceAny()) as? Int
      """,
        origin: "TryTests.testTry32",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTry33#1",
        source: """
      struct ThingProducer {
        func produceInt() throws -> Int { return 3 }
        func produceIntNoThrowing() -> Int { return 3 }
        func produceAny() throws -> Any { return 3 }
        func produceOptionalAny() throws -> Any? { return 3 }
        func produceDoubleOptionalInt() throws -> Int?? { return 3 }
      }
      """,
        origin: "TryTests.testTry33",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTry34#1",
        source: """
      let optProducer: ThingProducer? = ThingProducer()
      let _: Int? = try? optProducer?.produceInt()
      let _: Int = try? optProducer?.produceInt()
      let _: String = try? optProducer?.produceInt()
      let _: Int?? = try? optProducer?.produceInt() // good
      """,
        origin: "TryTests.testTry34",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTry35#1",
        source: """
      let _: Int? = try? optProducer?.produceIntNoThrowing()
      let _: Int?? = try? optProducer?.produceIntNoThrowing()
      """,
        origin: "TryTests.testTry35",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTry36#1",
        source: """
      let _: Int? = (try? optProducer?.produceAny()) as? Int // good
      let _: Int? = try? optProducer?.produceAny() as? Int
      let _: Int?? = try? optProducer?.produceAny() as? Int // good
      let _: String = try? optProducer?.produceAny() as? Int
      """,
        origin: "TryTests.testTry36",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTry37#1",
        source: """
      let _: String = try? optProducer?.produceDoubleOptionalInt()
      """,
        origin: "TryTests.testTry37",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTry38#1",
        source: """
      let producer = ThingProducer()
      """,
        origin: "TryTests.testTry38",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTry39#1",
        source: """
      let _: Int = try? producer.produceDoubleOptionalInt()
      let _: Int? = try? producer.produceDoubleOptionalInt()
      let _: Int?? = try? producer.produceDoubleOptionalInt()
      let _: Int??? = try? producer.produceDoubleOptionalInt() // good
      let _: String = try? producer.produceDoubleOptionalInt()
      """,
        origin: "TryTests.testTry39",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTry40#1",
        source: """
      // rdar://problem/46742002
      protocol Dummy : class {}
      """,
        origin: "TryTests.testTry40",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTry41#1",
        source: """
      class F<T> {
        func wait() throws -> T { fatalError() }
      }
      """,
        origin: "TryTests.testTry41",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTry42#1",
        source: """
      func bar(_ a: F<Dummy>, _ b: F<Dummy>) {
        _ = (try? a.wait()) === (try? b.wait())
      }
      """,
        origin: "TryTests.testTry42",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypeExpr3#1",
        source: """
      struct Foo {
        struct Bar {
          init() {}
          static var prop: Int = 0
          static func meth() {}
          func instMeth() {}
        }
        init() {}
        static var prop: Int = 0
        static func meth() {}
        func instMeth() {}
      }
      """,
        origin: "TypeExprTests.testTypeExpr3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypeExpr4#1",
        source: """
      protocol Zim {
        associatedtype Zang
        init()
        static func meth() {}
        func instMeth() {}
      }
      """,
        origin: "TypeExprTests.testTypeExpr4",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypeExpr5#1",
        source: """
      protocol Bad {
        init() {}
      }
      """,
        origin: "TypeExprTests.testTypeExpr5",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypeExpr6#1",
        source: """
      struct Gen<T> {
        struct Bar {
          init() {}
          static var prop: Int { return 0 }
          static func meth() {}
          func instMeth() {}
        }
        init() {}
        static var prop: Int { return 0 }
        static func meth() {}
        func instMeth() {}
      }
      """,
        origin: "TypeExprTests.testTypeExpr6",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypeExpr7#1",
        source: """
      func unqualifiedType() {
        _ = Foo.self
        _ = Foo.self
        _ = Foo()
        _ = Foo.prop
        _ = Foo.meth
        let _ : () = Foo.meth()
        _ = Foo.instMeth
        _ = Foo
        _ = Foo.dynamicType
        _ = Bad
      }
      """,
        origin: "TypeExprTests.testTypeExpr7",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypeExpr8#1",
        source: """
      func qualifiedType() {
        _ = Foo.Bar.self
        let _ : Foo.Bar.Type = Foo.Bar.self
        let _ : Foo.Protocol = Foo.self
        _ = Foo.Bar()
        _ = Foo.Bar.prop
        _ = Foo.Bar.meth
        let _ : () = Foo.Bar.meth()
        _ = Foo.Bar.instMeth
        _ = Foo.Bar
        _ = Foo.Bar.dynamicType
      }
      """,
        origin: "TypeExprTests.testTypeExpr8",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testTypeExpr8#2", source: "(X).Y.self", origin: "TypeExprTests.testTypeExpr8", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testTypeExpr8#3", source: "(X.Y).Z.self", origin: "TypeExprTests.testTypeExpr8", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testTypeExpr8#4", source: "((X).Y).Z.self", origin: "TypeExprTests.testTypeExpr8", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testTypeExpr9#1",
        source: """
      // We allow '.Type' in expr context
      func metaType() {
        let _ = Foo.Type.self
        let _ = Foo.Type.self
        let _ = Foo.Type
        let _ = type(of: Foo.Type)
      }
      """,
        origin: "TypeExprTests.testTypeExpr9",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypeExpr10#1",
        source: """
      func genType() {
        _ = Gen<Foo>.self
        _ = Gen<Foo>()
        _ = Gen<Foo>.prop
        _ = Gen<Foo>.meth
        let _ : () = Gen<Foo>.meth()
        _ = Gen<Foo>.instMeth
        _ = Gen<Foo>

        _ = X?.self
        _ = [X].self
        _ = [X : Y].self
      }
      """,
        origin: "TypeExprTests.testTypeExpr10",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testTypeExpr10#2", source: "X?.self", origin: "TypeExprTests.testTypeExpr10", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testTypeExpr10#3", source: "[X].self", origin: "TypeExprTests.testTypeExpr10", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testTypeExpr10#4", source: "[X : Y].self", origin: "TypeExprTests.testTypeExpr10", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testTypeExpr11#1",
        source: """
      func genQualifiedType() {
        _ = Gen<Foo>.Bar.self
        _ = Gen<Foo>.Bar()
        _ = Gen<Foo>.Bar.prop
        _ = Gen<Foo>.Bar.meth
        let _ : () = Gen<Foo>.Bar.meth()
        _ = Gen<Foo>.Bar.instMeth
        _ = Gen<Foo>.Bar
        _ = Gen<Foo>.Bar.dynamicType

        _ = (G<X>).Y.self
        _ = X?.Y.self
        _ = (X)?.Y.self
        _ = (X?).Y.self
        _ = [X].Y.self
        _ = [X : Y].Z.self
      }
      """,
        origin: "TypeExprTests.testTypeExpr11",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testTypeExpr11#2", source: "(G<X>).Y.self", origin: "TypeExprTests.testTypeExpr11", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testTypeExpr11#3", source: "X?.Y.self", origin: "TypeExprTests.testTypeExpr11", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testTypeExpr11#4", source: "(X)?.Y.self", origin: "TypeExprTests.testTypeExpr11", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testTypeExpr11#5", source: "(X?).Y.self", origin: "TypeExprTests.testTypeExpr11", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testTypeExpr11#6", source: "[X].Y.self", origin: "TypeExprTests.testTypeExpr11", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testTypeExpr11#7", source: "[X : Y].Z.self", origin: "TypeExprTests.testTypeExpr11", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testTypeExpr12#1",
        source: """
      func typeOfShadowing() {
        // Try to shadow type(of:)
        func type<T>(of t: T.Type, flag: Bool) -> T.Type {
          return t
        }
        func type<T, U>(of t: T.Type, _ : U) -> T.Type {
          return t
        }
        func type<T>(_ t: T.Type) -> T.Type {
          return t
        }
        func type<T>(fo t: T.Type) -> T.Type {
          return t
        }
        _ = type(of: Gen<Foo>.Bar)
        _ = type(Gen<Foo>.Bar)
        _ = type(of: Gen<Foo>.Bar.self, flag: false) // No error here.
        _ = type(fo: Foo.Bar.self) // No error here.
        _ = type(of: Foo.Bar.self, [1, 2, 3]) // No error here.
      }
      """,
        origin: "TypeExprTests.testTypeExpr12",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypeExpr13#1",
        source: """
      func archetype<T: Zim>(_: T) {
        _ = T.self
        _ = T()
        _ = T.meth
        let _ : () = T.meth()
        _ = T
      }
      """,
        origin: "TypeExprTests.testTypeExpr13",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypeExpr14#1",
        source: """
      func assocType<T: Zim>(_: T) where T.Zang: Zim {
        _ = T.Zang.self
        _ = T.Zang()
        _ = T.Zang.meth
        let _ : () = T.Zang.meth()
        _ = T.Zang
      }
      """,
        origin: "TypeExprTests.testTypeExpr14",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypeExpr15#1",
        source: """
      class B {
        class func baseMethod() {}
      }
      class D: B {
        class func derivedMethod() {}
      }
      """,
        origin: "TypeExprTests.testTypeExpr15",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypeExpr16#1",
        source: """
      func derivedType() {
        let _: B.Type = D.self
        _ = D.baseMethod
        let _ : () = D.baseMethod()
        let _: D.Type = D.self
        _ = D.derivedMethod
        let _ : () = D.derivedMethod()
        let _: B.Type = D
        let _: D.Type = D
      }
      """,
        origin: "TypeExprTests.testTypeExpr16",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypeExpr17#1",
        source: #"""
      // Referencing a nonexistent member or constructor should not trigger errors
      // about the type expression.
      func nonexistentMember() {
        let cons = Foo("this constructor does not exist")
        let prop = Foo.nonexistent
        let meth = Foo.nonexistent()
      }
      """#,
        origin: "TypeExprTests.testTypeExpr17",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypeExpr18#1",
        source: """
      protocol P {}
      """,
        origin: "TypeExprTests.testTypeExpr18",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypeExpr19#1",
        source: """
      func meta_metatypes() {
        let _: P.Protocol = P.self
        _ = P.Type.self
        _ = P.Protocol.self
        _ = P.Protocol.Protocol.self
        _ = P.Protocol.Type.self
        _ = B.Type.self
      }
      """,
        origin: "TypeExprTests.testTypeExpr19",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypeExpr20#1",
        source: """
      class E {
        private init() {}
      }
      """,
        origin: "TypeExprTests.testTypeExpr20",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypeExpr21#1",
        source: """
      func inAccessibleInit() {
        _ = E
      }
      """,
        origin: "TypeExprTests.testTypeExpr21",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypeExpr22#1",
        source: """
      enum F: Int {
        case A, B
      }
      """,
        origin: "TypeExprTests.testTypeExpr22",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypeExpr23#1",
        source: """
      struct G {
        var x: Int
      }
      """,
        origin: "TypeExprTests.testTypeExpr23",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypeExpr24#1",
        source: """
      func implicitInit() {
        _ = F
        _ = G
      }
      """,
        origin: "TypeExprTests.testTypeExpr24",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypeExpr25a#1",
        source: """
      _ = [(Int) -> Int]()
      """,
        origin: "TypeExprTests.testTypeExpr25a",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypeExpr25b#1",
        source: """
      _ = [(Int, Int) -> Int]()
      """,
        origin: "TypeExprTests.testTypeExpr25b",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypeExpr25c#1",
        source: """
      _ = [(x: Int, y: Int) -> Int]()
      """,
        origin: "TypeExprTests.testTypeExpr25c",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypeExpr25d#1",
        source: """
      // Make sure associativity is correct
      let a = [(Int) -> (Int) -> Int]()
      """,
        origin: "TypeExprTests.testTypeExpr25d",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypeExpr25e#1",
        source: """
      let b: Int = a[0](5)(4)
      """,
        origin: "TypeExprTests.testTypeExpr25e",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypeExpr25f#1",
        source: """
      _ = [String: (Int) -> Int]()
      """,
        origin: "TypeExprTests.testTypeExpr25f",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypeExpr25g#1",
        source: """
      _ = [String: (Int, Int) -> Int]()
      """,
        origin: "TypeExprTests.testTypeExpr25g",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypeExpr25h#1",
        source: """
      _ = [1 -> Int]()
      """,
        origin: "TypeExprTests.testTypeExpr25h",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypeExpr25i#1",
        source: """
      _ = [Int -> 1]()
      """,
        origin: "TypeExprTests.testTypeExpr25i",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypeExpr25j#1",
        source: """
      // Should parse () as void type when before or after arrow
      _ = [() -> Int]()
      """,
        origin: "TypeExprTests.testTypeExpr25j",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypeExpr25k#1",
        source: """
      _ = [(Int) -> ()]()
      """,
        origin: "TypeExprTests.testTypeExpr25k",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypeExpr25l#1",
        source: """
      _ = 2 + () -> Int
      """,
        origin: "TypeExprTests.testTypeExpr25l",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypeExpr25m#1",
        source: """
      _ = () -> (Int, Int).2
      """,
        origin: "TypeExprTests.testTypeExpr25m",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypeExpr25n#1",
        source: """
      _ = (Int) -> Int
      """,
        origin: "TypeExprTests.testTypeExpr25n",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypeExpr25o#1",
        source: """
      _ = @convention(c) () -> Int
      """,
        origin: "TypeExprTests.testTypeExpr25o",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypeExpr25p#1",
        source: """
      _ = 1 + (@convention(c) () -> Int).self
      """,
        origin: "TypeExprTests.testTypeExpr25p",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypeExpr25q#1",
        source: """
      _ = (@autoclosure () -> Int) -> (Int, Int).2
      """,
        origin: "TypeExprTests.testTypeExpr25q",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypeExpr25r#1",
        source: """
      _ = ((@autoclosure () -> Int) -> (Int, Int)).1
      """,
        origin: "TypeExprTests.testTypeExpr25r",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypeExpr25s#1",
        source: """
      _ = ((inout Int) -> Void).self
      """,
        origin: "TypeExprTests.testTypeExpr25s",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypeExpr25t#1",
        source: """
      _ = [(Int) throws -> Int]()
      """,
        origin: "TypeExprTests.testTypeExpr25t",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypeExpr25u#1",
        source: """
      _ = [@convention(swift) (Int) throws -> Int]().count
      """,
        origin: "TypeExprTests.testTypeExpr25u",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypeExpr25v#1",
        source: """
      _ = [(inout Int) throws -> (inout () -> Void) -> Void]().count
      """,
        origin: "TypeExprTests.testTypeExpr25v",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypeExpr25w#1",
        source: """
      _ = [String: (@autoclosure (Int) -> Int32) -> Void]().keys
      """,
        origin: "TypeExprTests.testTypeExpr25w",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testCompositionTypeExpr#1", source: "P & Q", origin: "TypeExprTests.testCompositionTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testCompositionTypeExpr#2", source: "P & Q.self", origin: "TypeExprTests.testCompositionTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testCompositionTypeExpr#3", source: "any P & Q", origin: "TypeExprTests.testCompositionTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testCompositionTypeExpr#4", source: "(P & Q).self", origin: "TypeExprTests.testCompositionTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testCompositionTypeExpr#5", source: "((P) & (Q)).self", origin: "TypeExprTests.testCompositionTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testCompositionTypeExpr#6", source: "(A.B & C.D).self", origin: "TypeExprTests.testCompositionTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testCompositionTypeExpr#7", source: "((A).B & (C).D).self", origin: "TypeExprTests.testCompositionTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testCompositionTypeExpr#8", source: "(G<X> & G<Y>).self", origin: "TypeExprTests.testCompositionTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testCompositionTypeExpr#9", source: "(X? & Y?).self", origin: "TypeExprTests.testCompositionTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testCompositionTypeExpr#10", source: "([X] & [Y]).self", origin: "TypeExprTests.testCompositionTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testCompositionTypeExpr#11", source: "([A : B] & [C : D]).self", origin: "TypeExprTests.testCompositionTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testCompositionTypeExpr#12", source: "(G<A>.B & G<C>.D).self", origin: "TypeExprTests.testCompositionTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testCompositionTypeExpr#13", source: "(A?.B & C?.D).self", origin: "TypeExprTests.testCompositionTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testCompositionTypeExpr#14", source: "([A].B & [A].B).self", origin: "TypeExprTests.testCompositionTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testCompositionTypeExpr#15", source: "([A : B].C & [D : E].F).self", origin: "TypeExprTests.testCompositionTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testCompositionTypeExpr#16", source: "(X.Type & Y.Type).self", origin: "TypeExprTests.testCompositionTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testCompositionTypeExpr#17", source: "(X.Protocol & Y.Protocol).self", origin: "TypeExprTests.testCompositionTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testCompositionTypeExpr#18", source: "((A, B) & (C, D)).self", origin: "TypeExprTests.testCompositionTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testTupleTypeExpr#1", source: "(X).self", origin: "TypeExprTests.testTupleTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testTupleTypeExpr#2", source: "(X, Y)", origin: "TypeExprTests.testTupleTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testTupleTypeExpr#3", source: "(X, Y).self", origin: "TypeExprTests.testTupleTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testTupleTypeExpr#4", source: "((X), (Y)).self", origin: "TypeExprTests.testTupleTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testTupleTypeExpr#5", source: "(A.B, C.D).self", origin: "TypeExprTests.testTupleTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testTupleTypeExpr#6", source: "((A).B, (C).D).self", origin: "TypeExprTests.testTupleTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testTupleTypeExpr#7", source: "(G<X>, G<Y>).self", origin: "TypeExprTests.testTupleTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testTupleTypeExpr#8", source: "(X?, Y?).self", origin: "TypeExprTests.testTupleTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testTupleTypeExpr#9", source: "([X], [Y]).self", origin: "TypeExprTests.testTupleTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testTupleTypeExpr#10", source: "([A : B], [C : D]).self", origin: "TypeExprTests.testTupleTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testTupleTypeExpr#11", source: "(G<A>.B, G<C>.D).self", origin: "TypeExprTests.testTupleTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testTupleTypeExpr#12", source: "(A?.B, C?.D).self", origin: "TypeExprTests.testTupleTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testTupleTypeExpr#13", source: "([A].B, [C].D).self", origin: "TypeExprTests.testTupleTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testTupleTypeExpr#14", source: "([A : B].C, [D : E].F).self", origin: "TypeExprTests.testTupleTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testTupleTypeExpr#15", source: "(X.Type, Y.Type).self", origin: "TypeExprTests.testTupleTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testTupleTypeExpr#16", source: "(X.Protocol, Y.Protocol).self", origin: "TypeExprTests.testTupleTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testTupleTypeExpr#17", source: "(P & Q, P & Q).self", origin: "TypeExprTests.testTupleTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testTupleTypeExpr#18",
        source: """
      (
        (G<X>.Y) -> (P) & X?.Y, (X.Y, [X : Y?].Type), [(G<X>).Y], [A.B.C].D
      ).self
      """,
        origin: "TypeExprTests.testTupleTypeExpr",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testFunctionTypeExpr#1", source: "X -> Y", origin: "TypeExprTests.testFunctionTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testFunctionTypeExpr#2", source: "(X) -> Y", origin: "TypeExprTests.testFunctionTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testFunctionTypeExpr#3", source: "(X) -> Y -> Z", origin: "TypeExprTests.testFunctionTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testFunctionTypeExpr#4", source: "P & Q -> X", origin: "TypeExprTests.testFunctionTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testFunctionTypeExpr#5", source: "A & B -> C & D -> X", origin: "TypeExprTests.testFunctionTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testFunctionTypeExpr#6", source: "(X -> Y).self", origin: "TypeExprTests.testFunctionTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testFunctionTypeExpr#7", source: "(A & B -> C & D).self", origin: "TypeExprTests.testFunctionTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testFunctionTypeExpr#8", source: "((X) -> Y).self", origin: "TypeExprTests.testFunctionTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testFunctionTypeExpr#9", source: "(((X)) -> (Y)).self", origin: "TypeExprTests.testFunctionTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testFunctionTypeExpr#10", source: "((A.B) -> C.D).self", origin: "TypeExprTests.testFunctionTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testFunctionTypeExpr#11", source: "(((A).B) -> (C).D).self", origin: "TypeExprTests.testFunctionTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testFunctionTypeExpr#12", source: "((G<X>) -> G<Y>).self", origin: "TypeExprTests.testFunctionTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testFunctionTypeExpr#13", source: "((X?) -> Y?).self", origin: "TypeExprTests.testFunctionTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testFunctionTypeExpr#14", source: "(([X]) -> [Y]).self", origin: "TypeExprTests.testFunctionTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testFunctionTypeExpr#15", source: "(([A : B]) -> [C : D]).self", origin: "TypeExprTests.testFunctionTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testFunctionTypeExpr#16", source: "((Gen<Foo>.Bar) -> Gen<Foo>.Bar).self", origin: "TypeExprTests.testFunctionTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testFunctionTypeExpr#17", source: "((Foo?.Bar) -> Foo?.Bar).self", origin: "TypeExprTests.testFunctionTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testFunctionTypeExpr#18", source: "(([Foo].Element) -> [Foo].Element).self", origin: "TypeExprTests.testFunctionTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testFunctionTypeExpr#19", source: "(([Int : Foo].Element) -> [Int : Foo].Element).self", origin: "TypeExprTests.testFunctionTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testFunctionTypeExpr#20", source: "((X.Type) -> Y.Type).self", origin: "TypeExprTests.testFunctionTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testFunctionTypeExpr#21", source: "((X.Protocol) -> Y.Protocol).self", origin: "TypeExprTests.testFunctionTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testFunctionTypeExpr#22", source: "(() -> X & Y).self", origin: "TypeExprTests.testFunctionTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testFunctionTypeExpr#23", source: "((A & B) -> C & D).self", origin: "TypeExprTests.testFunctionTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testFunctionTypeExpr#24", source: "((A & B) -> (C & D) -> E & Any).self", origin: "TypeExprTests.testFunctionTypeExpr", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testFunctionTypeExpr#25",
        source: """
      (
        ((P) & X?.Y, G<X>.Y, (X, [A : B?].Type)) -> ([(X).Y]) -> [X].Y
      ).self
      """,
        origin: "TypeExprTests.testFunctionTypeExpr",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypeExpr27#1",
        source: """
      func complexSequence() {
        // (assign_expr
        //   (discard_assignment_expr)
        //   (try_expr
        //     (type_expr typerepr='P1 & P2 throws -> P3 & P1')))
        _ = try P1 & P2 throws -> P3 & P1
      }
      """,
        origin: "TypeExprTests.testTypeExpr27",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypeExpr29#1",
        source: """
      func takesOneArg<T>(_: T.Type) {}
      func takesTwoArgs<T>(_: T.Type, _: Int) {}
      """,
        origin: "TypeExprTests.testTypeExpr29",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypeExpr30#1",
        source: """
      func testMissingSelf() {
        // None of these were not caught in Swift 3.
        // See test/Compatibility/type_expr.swift.
        takesOneArg(Int)
        takesOneArg(Swift.Int)
        takesTwoArgs(Int, 0)
        takesTwoArgs(Swift.Int, 0)
        Swift.Int
        _ = Swift.Int
      }
      """,
        origin: "TypeExprTests.testTypeExpr30",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypealias2a#1",
        source: """
      typealias IntPair = (Int, Int)
      """,
        origin: "TypealiasTests.testTypealias2a",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypealias2b#1",
        source: """
      typealias IntTriple = (Int, Int, Int)
      """,
        origin: "TypealiasTests.testTypealias2b",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypealias2c#1",
        source: """
      typealias FiveInts = (IntPair, IntTriple)
      """,
        origin: "TypealiasTests.testTypealias2c",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypealias2d#1",
        source: """
      var fiveInts : FiveInts = ((4,2), (1,2,3))
      """,
        origin: "TypealiasTests.testTypealias2d",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testUnclosedStringInterpolation1#1",
        source: #"""
      let mid = "pete"
      """#,
        origin: "UnclosedStringInterpolationTests.testUnclosedStringInterpolation1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
]

extension SwiftSyntax604Tests {

@Suite("Translated")
struct TranslatedSyntax604Tests {

    @Test("SwiftSyntax accepts", .tags(.swiftSyntaxReference), arguments: translated604Snippets)
    func swiftSyntaxAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        #expect(!swiftSyntaxReferenceHasError(snippet), "SwiftSyntax parse error for: \(snippet.source)")
    }

    @Test("Advent accepts", arguments: translated604Snippets)
    func adventAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let result = try adventParse(snippet)
        #expect(result != nil, "Advent failed to parse: \(snippet.source)")
    }

    @Test("no residual ambiguity", arguments: translated604Snippets)
    func unambiguous(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        guard let result = try adventParse(snippet) else {
            Issue.record("Advent failed to parse: \(snippet.source)")
            return
        }
        #expect(result.isUnambiguous,
                "Residual ambiguity in '\(snippet.diagnosticID)': \(result.builder.diagnostics)")
    }

    @Test("trees match", arguments: translated604Snippets)
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

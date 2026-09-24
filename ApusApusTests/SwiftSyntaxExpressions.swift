//
//  SwiftSyntaxExpressions.swift
//  AdventTests
//
//  Expression snippets extracted from SwiftSyntax ExpressionTests.swift (603.0.1).
//  See SwiftSyntaxTests.swift for shared infrastructure.
//

import Testing
import Foundation
import SwiftSyntax
import SwiftParser

// MARK: - Snippet Catalog

let expressionSnippets: [SwiftSnippet] = [
    SwiftSnippet(label: "testTernary#1", source: "a ? b : c ? d : e", origin: "ExpressionTests.testTernary", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testSequence#1", source: "A as? B + C -> D is E as! F ? G = 42 : H", origin: "ExpressionTests.testSequence", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testClosureLiterals#1",
        source: #"""
      { @MainActor (a: Int) async -> Int in print("hi") }
      """#,
        origin: "ExpressionTests.testClosureLiterals",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testClosureLiterals#2",
        source: """
      { [weak self, weak weakB = b] foo in
        return 0
      }
      """,
        origin: "ExpressionTests.testClosureLiterals",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testClosureLiterals#3",
        source: """
      func f(x:[Void])
      {
        var y:[[Void]] = x.map { [$0] }
        {
          $0.reserveCapacity(1)
        } (&y[0])
      }
      """,
        origin: "ExpressionTests.testClosureLiterals",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTrailingClosures#1",
        source: """
      var button =  View.Button[5, 4, 3
      ] {
        // comment #0
        Text("ABC")
      }
      """,
        origin: "ExpressionTests.testTrailingClosures",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testTrailingClosures#2", source: "compactMap { (parserDiag) in }", origin: "ExpressionTests.testTrailingClosures", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testSequenceExpressions#1", source: "await a()", origin: "ExpressionTests.testSequenceExpressions", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testSequenceExpressions#2",
        source: """
      async let child = testNestedTaskPriority(basePri: basePri, curPri: curPri)
      await child
      """,
        origin: "ExpressionTests.testSequenceExpressions",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testNestedTypeSpecialization#1", source: "Swift.Array<Array<Foo>>()", origin: "ExpressionTests.testNestedTypeSpecialization", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testObjectLiterals#1",
        source: """
      #colorLiteral()
      #colorLiteral(red: 1.0)
      #colorLiteral(red: 1.0, green: 1.0)
      #colorLiteral(red: 1.0, green: 1.0, blue: 1.0, alpha: 1.0)
      """,
        origin: "ExpressionTests.testObjectLiterals",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testObjectLiterals#2",
        source: """
      #imageLiteral()
      #imageLiteral(resourceName: "foo.png")
      #imageLiteral(resourceName: "foo/bar/baz/qux.png")
      #imageLiteral(resourceName: "foo/bar/baz/quux.png")
      """,
        origin: "ExpressionTests.testObjectLiterals",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testKeypathExpression#1",
        source: #"""
      \.?.foo
      """#,
        origin: "ExpressionTests.testKeypathExpression",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testKeypathExpression#2",
        source: #"""
      children.filter(\.type.defaultInitialization.isEmpty)
      """#,
        origin: "ExpressionTests.testKeypathExpression",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testKeypathExpression#3",
        source: #"""
      _ = \Lens<[Int]>.[0]
      """#,
        origin: "ExpressionTests.testKeypathExpression",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testKeypathExpression#4",
        source: #"""
      \(UnsafeRawPointer?, String).1
      """#,
        origin: "ExpressionTests.testKeypathExpression",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testKeypathExpression#5",
        source: #"""
      \a.b.c
      """#,
        origin: "ExpressionTests.testKeypathExpression",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testKeypathExpression#6",
        source: #"""
      \ABCProtocol[100]
      """#,
        origin: "ExpressionTests.testKeypathExpression",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testKeypathExpression#7",
        source: #"""
      \S<T>.x
      """#,
        origin: "ExpressionTests.testKeypathExpression",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testKeypathExpression#8",
        source: #"""
      \TupleProperties.self
      """#,
        origin: "ExpressionTests.testKeypathExpression",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testKeypathExpression#9",
        source: #"""
      \Tuple<Int, Int>.self
      """#,
        origin: "ExpressionTests.testKeypathExpression",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testKeypathExpression#10",
        source: #"""
      \T.extension
      """#,
        origin: "ExpressionTests.testKeypathExpression",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testKeypathExpression#11",
        source: #"""
      \T.12[14]
      """#,
        origin: "ExpressionTests.testKeypathExpression",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testKeypathExpression#12",
        source: #"""
      \Optional.?!?!?!?
      """#,
        origin: "ExpressionTests.testKeypathExpression",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testKeypathExpression#13",
        source: #"""
      _ = distinctUntilChanged(\ .?.status)
      _ = distinctUntilChanged(\.?.status)
      """#,
        origin: "ExpressionTests.testKeypathExpression",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testKeyPathMethodAndInitializers#1", source: #"\Foo.method()"#, origin: "ExpressionTests.testKeyPathMethodAndInitializers", syntaxVersion: "603.0.1", disabledReason: "experimental feature"),
    SwiftSnippet(label: "testKeyPathMethodAndInitializers#2", source: #"\Foo.method(10)"#, origin: "ExpressionTests.testKeyPathMethodAndInitializers", syntaxVersion: "603.0.1", disabledReason: "experimental feature"),
    // PROBE (TODO 39): does swift-syntax PARSE a parenthesized key-path with outer postfix?
    // The `@cannotParse(keyPathExpression)` proposal relies on this staying legal as the escape
    // hatch; nothing in the corpus covered it.
    SwiftSnippet(label: "probeParenKeyPathPostfix#1", source: #"(\Foo).method<Int>()"#,
                 origin: "TODO39 probe", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "probeParenKeyPathMember#1", source: #"(\Foo).bar"#,
                 origin: "TODO39 probe", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testKeyPathMethodAndInitializers#3", source: #"\Foo.method(arg: 10)"#, origin: "ExpressionTests.testKeyPathMethodAndInitializers", syntaxVersion: "603.0.1", disabledReason: "experimental feature"),
    SwiftSnippet(label: "testKeyPathMethodAndInitializers#4", source: #"\Foo.method(_:)"#, origin: "ExpressionTests.testKeyPathMethodAndInitializers", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testKeyPathMethodAndInitializers#5", source: #"\Foo.method(arg:)"#, origin: "ExpressionTests.testKeyPathMethodAndInitializers", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testKeyPathMethodAndInitializers#6", source: #"\Foo.method().anotherMethod(arg: 10)"#, origin: "ExpressionTests.testKeyPathMethodAndInitializers", syntaxVersion: "603.0.1", disabledReason: "experimental feature"),
    SwiftSnippet(label: "testKeyPathMethodAndInitializers#7", source: #"\Foo.Type.init()"#, origin: "ExpressionTests.testKeyPathMethodAndInitializers", syntaxVersion: "603.0.1", disabledReason: "experimental feature"),
    SwiftSnippet(label: "testKeyPathMethodAndInitializers#8", source: #"\Foo.t(a:)(2)"#, origin: "ExpressionTests.testKeyPathMethodAndInitializers", syntaxVersion: "603.0.1", disabledReason: "experimental feature"),
    SwiftSnippet(
        label: "testKeyPathMethodAndInitializers#9",
        source: #"""
      S()[keyPath: \.i] = 1
      """#,
        origin: "ExpressionTests.testKeyPathMethodAndInitializers",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testKeyPathMethodAndInitializers#10",
        source: #"""
      public let keyPath2FromLibB = \AStruct.Type.property
      """#,
        origin: "ExpressionTests.testKeyPathMethodAndInitializers",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testKeyPathMethodAndInitializers#11",
        source: #"""
      public let keyPath9FromLibB = \AStruct.Type.init(val: 2025)
      """#,
        origin: "ExpressionTests.testKeyPathMethodAndInitializers",
        syntaxVersion: "603.0.1",
        disabledReason: "experimental feature"
    ),
    SwiftSnippet(
        label: "testKeyPathMethodAndInitializers#12",
        source: #"""
      _ = ([S]()).map(\.i)
      """#,
        origin: "ExpressionTests.testKeyPathMethodAndInitializers",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testKeyPathMethodAndInitializers#13",
        source: #"""
      let some = Some(keyPath: \Demo.here)
      """#,
        origin: "ExpressionTests.testKeyPathMethodAndInitializers",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testKeyPathMethodAndInitializers#14",
        source: #"""
      _ = ([S.Type]()).map(\.init)
      """#,
        origin: "ExpressionTests.testKeyPathMethodAndInitializers",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testKeyPathMethodAndInitializers#15",
        source: #"""
      \Lens<Lens<Point>>.obj.x
      """#,
        origin: "ExpressionTests.testKeyPathMethodAndInitializers",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testKeyPathMethodAndInitializers#16",
        source: #"""
      _ = \Lens<Point>.y
      """#,
        origin: "ExpressionTests.testKeyPathMethodAndInitializers",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testKeyPathMethodAndInitializers#17",
        source: #"""
      _ = f(\String?.!.count)
      """#,
        origin: "ExpressionTests.testKeyPathMethodAndInitializers",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testKeyPathMethodAndInitializers#18",
        source: #"""
      let _ = \K.Type.init(val: 2025)
      """#,
        origin: "ExpressionTests.testKeyPathMethodAndInitializers",
        syntaxVersion: "603.0.1",
        disabledReason: "experimental feature"
    ),
    SwiftSnippet(
        label: "testKeyPathMethodAndInitializers#19",
        source: #"""
      let _ = \K.Type.init
      let _ = \K.Type.init()
      """#,
        origin: "ExpressionTests.testKeyPathMethodAndInitializers",
        syntaxVersion: "603.0.1",
        disabledReason: "experimental feature"
    ),
    SwiftSnippet(label: "testKeyPathSubscript#1", source: #"\Foo.Type.[2]"#, origin: "ExpressionTests.testKeyPathSubscript", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testKeyPathSubscript#2", source: #"\Foo.Bar.[2]"#, origin: "ExpressionTests.testKeyPathSubscript", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testKeyPathFollowedByOperator#1", source: #"\Foo?.?.bar.?.blah"#, origin: "ExpressionTests.testKeyPathFollowedByOperator", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testKeyPathFollowedByOperator#2", source: #"\Foo?.?.?.blah"#, origin: "ExpressionTests.testKeyPathFollowedByOperator", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testKeypathExpressionWithSugaredRoot#1", source: #"\X.y"#, origin: "ExpressionTests.testKeypathExpressionWithSugaredRoot", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testKeypathExpressionWithSugaredRoot#2", source: #"\X<T>.y"#, origin: "ExpressionTests.testKeypathExpressionWithSugaredRoot", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testKeypathExpressionWithSugaredRoot#3", source: #"\X?.y"#, origin: "ExpressionTests.testKeypathExpressionWithSugaredRoot", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testKeypathExpressionWithSugaredRoot#4", source: #"\X!.y"#, origin: "ExpressionTests.testKeypathExpressionWithSugaredRoot", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testKeypathExpressionWithSugaredRoot#5", source: #"\[X].y"#, origin: "ExpressionTests.testKeypathExpressionWithSugaredRoot", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testKeypathExpressionWithSugaredRoot#6", source: #"\[X : Y].y"#, origin: "ExpressionTests.testKeypathExpressionWithSugaredRoot", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testKeypathExpressionWithSugaredRoot#7", source: #"\().y"#, origin: "ExpressionTests.testKeypathExpressionWithSugaredRoot", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testKeypathExpressionWithSugaredRoot#8", source: #"\(X).y"#, origin: "ExpressionTests.testKeypathExpressionWithSugaredRoot", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testKeypathExpressionWithSugaredRoot#9", source: #"\(X, X).y"#, origin: "ExpressionTests.testKeypathExpressionWithSugaredRoot", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testKeypathExpressionWithSugaredRoot#10", source: #"\Any.y"#, origin: "ExpressionTests.testKeypathExpressionWithSugaredRoot", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testKeypathExpressionWithSugaredRoot#11", source: #"\Self.y"#, origin: "ExpressionTests.testKeypathExpressionWithSugaredRoot", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testBasicLiterals#1",
        source: """
      #file
      #fileID
      (#line)
      #column
      #function
      #dsohandle
      __FILE__
      __LINE__
      __COLUMN__
      __FUNCTION__
      __DSO_HANDLE__

      func f() {
        return #function
      }
      """,
        origin: "ExpressionTests.testBasicLiterals",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testInitializerExpression#1", source: "Lexer.Cursor(input: input, previous: 0)", origin: "ExpressionTests.testInitializerExpression", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testCollectionLiterals#1", source: "[Dictionary<String, Int>: Int]()", origin: "ExpressionTests.testCollectionLiterals", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testCollectionLiterals#2", source: "[(Int, Double) -> Bool]()", origin: "ExpressionTests.testCollectionLiterals", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testCollectionLiterals#3", source: "[(Int, Double) -> Bool]()", origin: "ExpressionTests.testCollectionLiterals", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testCollectionLiterals#4", source: "_ = [@convention(block) ()  -> Int]().count", origin: "ExpressionTests.testCollectionLiterals", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testCollectionLiterals#5", source: "A<@convention(c) () -> Int32>.c()", origin: "ExpressionTests.testCollectionLiterals", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testCollectionLiterals#6", source: "A<(@autoclosure @escaping () -> Int, Int) -> Void>.c()", origin: "ExpressionTests.testCollectionLiterals", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testCollectionLiterals#7", source: "_ = [String: (@escaping (A<B>) -> Int) -> Void]().keys", origin: "ExpressionTests.testCollectionLiterals", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testCollectionLiterals#8",
        source: """
      [
        condition ? firstOption : secondOption,
        bar(),
      ]
      """,
        origin: "ExpressionTests.testCollectionLiterals",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testCollectionLiterals#9",
        source: """
      [
        #line : Calendar(identifier: .gregorian),
        #line : Calendar(identifier: .buddhist),
      ]
      """,
        origin: "ExpressionTests.testCollectionLiterals",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testCollectionLiterals#10",
        source: """
      #fancyMacro<Arg1, Arg2>(hello: "me")
      """,
        origin: "ExpressionTests.testCollectionLiterals",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInterpolatedStringLiterals#1",
        source: #"""
      return "Fixit: \(range.debugDescription) Text: \"\(text)\""
      """#,
        origin: "ExpressionTests.testInterpolatedStringLiterals",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInterpolatedStringLiterals#2",
        source: #"""
      "text \(array.map({ "\($0)" }).joined(separator: ",")) text"
      """#,
        origin: "ExpressionTests.testInterpolatedStringLiterals",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInterpolatedStringLiterals#3",
        source: #"""
      """
      \(gen(xx) { (x) in
          return """
          case
      """
      })
      """
      """#,
        origin: "ExpressionTests.testInterpolatedStringLiterals",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testStringLiterals#1",
        source: #"""
      "–"
      """#,
        origin: "ExpressionTests.testStringLiterals",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testStringLiterals#2",
        source: #"""
      ""
      """#,
        origin: "ExpressionTests.testStringLiterals",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testStringLiterals#3",
        source: #"""
      """
      """
      """#,
        origin: "ExpressionTests.testStringLiterals",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testStringLiterals#4",
        source: ##"""


      #"Hello World"#

      "Hello World"


      """##,
        origin: "ExpressionTests.testStringLiterals",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testStringLiterals#5",
        source: #"""
      "(?i)\\b((?:[a-z][\\w-]+:(?:/{1,3}|[a-z0-9%])|www\\d{0,3}[.]|[a-z0-9.\\-]+[.][a-z]{2,4}/)" +
      "(?:[^\\s()<>]+|\\(([^\\s()<>]+|(\\([^\\s()<>]+\\)))*\\))+(?:\\(([^\\s()<>]+|(\\([^\\s()<>]+\\)))*" +
      "\\)|[^\\s`!()\\[\\]{};:'\".,<>?«»“”‘’]))"
      """#,
        origin: "ExpressionTests.testStringLiterals",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testStringLiterals#6",
        source: #"""
      """
          Custom(custom: \(interval),\
          Expr: \(pause?.debugDescription ?? "–"), \
          PlainWithContinuation: \(countdown), \
          Plain: \(units))"
      """
      """#,
        origin: "ExpressionTests.testStringLiterals",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testStringLiterals#7",
        source: #"""
      "Founded: \(Date.appleFounding, format: 📆)"
      """#,
        origin: "ExpressionTests.testStringLiterals",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testStringLiterals#8",
        source: """

      ""
      """,
        origin: "ExpressionTests.testStringLiterals",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testStringLiterals#9",
        source: ##"""
      #"""#
      """##,
        origin: "ExpressionTests.testStringLiterals",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testStringLiterals#10",
        source: ##"""
      #"""""#
      """##,
        origin: "ExpressionTests.testStringLiterals",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testStringLiterals#11",
        source: ##"""
      #"""
      multiline raw
      """#
      """##,
        origin: "ExpressionTests.testStringLiterals",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testStringLiterals#12",
        source: #"""
      "\(x)"
      """#,
        origin: "ExpressionTests.testStringLiterals",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAdjacentRawStringLiterals#1",
        source: """
      "normal literal"
      #"raw literal"#
      """,
        origin: "ExpressionTests.testAdjacentRawStringLiterals",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAdjacentRawStringLiterals#2",
        source: """
      #"raw literal"#
      #"second raw literal"#
      """,
        origin: "ExpressionTests.testAdjacentRawStringLiterals",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testStringBogusClosingDelimiters#1",
        source: ##"""
      #"\\("#
      """##,
        origin: "ExpressionTests.testStringBogusClosingDelimiters",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSubscript#1",
        source: """
      array[]
      """,
        origin: "ExpressionTests.testSubscript",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSubscript#2",
        source: """
      text[...]
      """,
        origin: "ExpressionTests.testSubscript",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testConsumeExpression#1", source: "consume msg", origin: "ExpressionTests.testConsumeExpression", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testConsumeExpression#2", source: "use(consume msg)", origin: "ExpressionTests.testConsumeExpression", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testConsumeExpression#3", source: "consume msg", origin: "ExpressionTests.testConsumeExpression", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testConsumeExpression#4", source: "let b = (consume self).buffer", origin: "ExpressionTests.testConsumeExpression", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testBorrowExpression#1", source: "borrow msg", origin: "ExpressionTests.testBorrowExpression", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testBorrowExpression#2", source: "use(borrow msg)", origin: "ExpressionTests.testBorrowExpression", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testBorrowExpression#3", source: "borrow msg", origin: "ExpressionTests.testBorrowExpression", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testBorrowExpression#4", source: "let b = (borrow self).buffer", origin: "ExpressionTests.testBorrowExpression", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testBorrowExpression#5", source: "borrow msg", origin: "ExpressionTests.testBorrowExpression", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testBorrowExpression#6", source: "use(borrow msg)", origin: "ExpressionTests.testBorrowExpression", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testBorrowExpression#7", source: "borrow(msg)", origin: "ExpressionTests.testBorrowExpression", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testBorrowExpression#8", source: "borrow (msg)", origin: "ExpressionTests.testBorrowExpression", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testBorrowNameFunctionCallStructure1#1",
        source: """
      borrow(msg)
      """,
        origin: "ExpressionTests.testBorrowNameFunctionCallStructure1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testBorrowNameFunctionCallStructure2#1",
        source: """
      borrow (msg)
      """,
        origin: "ExpressionTests.testBorrowNameFunctionCallStructure2",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testKeywordApplyExpression#1",
        source: """
      optional(x: .some(23))
      optional(x: .none)
      var pair : (Int, Double) = makePair(a: 1, b: 2.5)
      """,
        origin: "ExpressionTests.testKeywordApplyExpression",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testFalseMultilineDelimiters#1",
        source: ###"""
      _ = #"​"​"#

      _ = #""""#

      _ = #"""""#

      _ = #""""""#

      _ = ##""" foo # "# "##
      """###,
        origin: "ExpressionTests.testFalseMultilineDelimiters",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testOperatorReference#1", source: "reduce(0, +)", origin: "ExpressionTests.testOperatorReference", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testBogusCaptureLists#1",
        source: """
      {
          [
              AboutItem(title: TextContent.legalAndMore, accessoryType: .disclosureIndicator, action: { [weak self] context in
                  self?.tracker.buttonPressed(.legal)
                  context.showSubmenu(title: TextContent.legalAndMore, configuration: LegalAndMoreSubmenuConfiguration())
              }),
          ]
      }()
      """,
        origin: "ExpressionTests.testBogusCaptureLists",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testMacroExpansionExpression#1", source: #"#file == $0.path"#, origin: "ExpressionTests.testMacroExpansionExpression", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testMacroExpansionExpression#2", source: #"let a = #embed("filename.txt")"#, origin: "ExpressionTests.testMacroExpansionExpression", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testMacroExpansionExpression#3",
        source: """
      #Test {
        print("This is a test")
      }
      """,
        origin: "ExpressionTests.testMacroExpansionExpression",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testMacroExpansionExpressionWithKeywordName#1", source: "#case", origin: "ExpressionTests.testMacroExpansionExpressionWithKeywordName", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testPostProcessMultilineStringLiteral#1",
        source: #"""
        """
        line 1
        line 2
        """
      """#,
        origin: "ExpressionTests.testPostProcessMultilineStringLiteral",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testPostProcessMultilineStringLiteral#2",
        source: #"""
        """
        line 1 \
        line 2
        """
      """#,
        origin: "ExpressionTests.testPostProcessMultilineStringLiteral",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMultiLineStringInInterpolationOfSingleLineStringLiteral#1",
        source: #"""
      "foo\(test("""
      bar
      """) )"
      """#,
        origin: "ExpressionTests.testMultiLineStringInInterpolationOfSingleLineStringLiteral",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEmptyLineInMultilineStringLiteral#1",
        source: #"""
        """
        line 1

        line 2
        """
      """#,
        origin: "ExpressionTests.testEmptyLineInMultilineStringLiteral",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testEmptyLineInMultilineStringLiteral#2",
        source: #"""
        """
        line 1

        """
      """#,
        origin: "ExpressionTests.testEmptyLineInMultilineStringLiteral",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTabsIndentationInMultilineStringLiteral#1",
        source: #"""
      _ = """
      \#taq
      \#t"""
      """#,
        origin: "ExpressionTests.testTabsIndentationInMultilineStringLiteral",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testMixedIndentationInMultilineStringLiteral#1",
        source: #"""
      _ = """
      \#t aq
      \#t """
      """#,
        origin: "ExpressionTests.testMixedIndentationInMultilineStringLiteral",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTrailingCommasInTypeExpressions#1",
        source: """
      let _ = Foo2<Int, Bool, String,>.self
      """,
        origin: "ExpressionTests.testTrailingCommasInTypeExpressions",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTrailingCommasInTypeExpressions#2",
        source: """
      let _ = Foo2<Int, Bool, String,>()
      """,
        origin: "ExpressionTests.testTrailingCommasInTypeExpressions",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTrailingCommasInTypeExpressions#3",
        source: """
      let _ = ((Int, Bool, String,) -> Void).self
      """,
        origin: "ExpressionTests.testTrailingCommasInTypeExpressions",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTrailingCommasInTypeExpressions#4",
        source: """
      let _ = Array<(
        bar: String,
        baaz: String,
      )>()
      """,
        origin: "ExpressionTests.testTrailingCommasInTypeExpressions",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testIfExprInCoercion#1",
        source: """
      func foo() {
        if .random() { 0 } else { 1 } as Int
      }
      """,
        origin: "ExpressionTests.testIfExprInCoercion",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitchExprInCoercion#1",
        source: """
      switch Bool.random() { case true: 0 case false: 1 } as Int
      """,
        origin: "ExpressionTests.testSwitchExprInCoercion",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testIfExprInReturn#1",
        source: """
      func foo() {
        return if .random() { 0 } else { 1 }
      }
      """,
        origin: "ExpressionTests.testIfExprInReturn",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitchExprInReturn#1",
        source: """
      func foo() {
        return switch Bool.random() { case true: 0 case false: 1 }
      }
      """,
        origin: "ExpressionTests.testSwitchExprInReturn",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTryIf1#1",
        source: """
      func foo() -> Int {
        try if .random() { 0 } else { 1 }
      }
      """,
        origin: "ExpressionTests.testTryIf1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTryIf2#1",
        source: """
      func foo() -> Int {
        return try if .random() { 0 } else { 1 }
      }
      """,
        origin: "ExpressionTests.testTryIf2",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTryIf3#1",
        source: """
      func foo() -> Int {
        let x = try if .random() { 0 } else { 1 }
        return x
      }
      """,
        origin: "ExpressionTests.testTryIf3",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAwaitIf1#1",
        source: """
      func foo() async -> Int {
        await if .random() { 0 } else { 1 }
      }
      """,
        origin: "ExpressionTests.testAwaitIf1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAwaitIf2#1",
        source: """
      func foo() async -> Int {
        return await if .random() { 0 } else { 1 }
      }
      """,
        origin: "ExpressionTests.testAwaitIf2",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAwaitIf3#1",
        source: """
      func foo() async -> Int {
        let x = await if .random() { 0 } else { 1 }
        return x
      }
      """,
        origin: "ExpressionTests.testAwaitIf3",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTrySwitch1#1",
        source: """
      try switch Bool.random() { case true: 0 case false: 1 }
      """,
        origin: "ExpressionTests.testTrySwitch1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTrySwitch2#1",
        source: """
      func foo() -> Int {
        return try switch Bool.random() { case true: 0 case false: 1 }
      }
      """,
        origin: "ExpressionTests.testTrySwitch2",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTrySwitch3#1",
        source: """
      func foo() -> Int {
        let x = try switch Bool.random() { case true: 0 case false: 1 }
        return x
      }
      """,
        origin: "ExpressionTests.testTrySwitch3",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAwaitSwitch1#1",
        source: """
      await switch Bool.random() { case true: 0 case false: 1 }
      """,
        origin: "ExpressionTests.testAwaitSwitch1",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAwaitSwitch2#1",
        source: """
      func foo() async -> Int {
        return await switch Bool.random() { case true: 0 case false: 1 }
      }
      """,
        origin: "ExpressionTests.testAwaitSwitch2",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testAwaitSwitch3#1",
        source: """
      func foo() async -> Int {
        let x = await switch Bool.random() { case true: 0 case false: 1 }
        return x
      }
      """,
        origin: "ExpressionTests.testAwaitSwitch3",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testIfExprCondCast#1",
        source: """
      if .random() { 0 } else { 1 } as? Int
      """,
        origin: "ExpressionTests.testIfExprCondCast",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testIfExprForceCast#1",
        source: """
      if .random() { 0 } else { 1 } as! Int
      """,
        origin: "ExpressionTests.testIfExprForceCast",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitchExprCondCast#1",
        source: """
      switch Bool.random() { case true: 0 case false: 1 } as? Int
      """,
        origin: "ExpressionTests.testSwitchExprCondCast",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSwitchExprForceCast#1",
        source: """
      switch Bool.random() { case true: 0 case false: 1 } as! Int
      """,
        origin: "ExpressionTests.testSwitchExprForceCast",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testUnsafeExpr#1",
        source: """
      func f() {
        let x = unsafe y
      }
      """,
        origin: "ExpressionTests.testUnsafeExpr",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testUnsafeExpr#2",
        source: """
      func f() {
        let x = unsafe
        y
      }
      """,
        origin: "ExpressionTests.testUnsafeExpr",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testUnsafeExpr#3",
        source: """
      func f() {
        unsafe.lock()
      }
      """,
        origin: "ExpressionTests.testUnsafeExpr",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testUnsafeExpr#4",
        source: """
      func f() {
        unsafe .lock
      }
      """,
        origin: "ExpressionTests.testUnsafeExpr",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testUnsafeExpr#5",
        source: """
      func f() {
        _ = [unsafe]
      }
      """,
        origin: "ExpressionTests.testUnsafeExpr",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testUnsafeExpr#6",
        source: """
      func f() {
        _ = [unsafe]
      }
      """,
        origin: "ExpressionTests.testUnsafeExpr",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testUnsafeExpr#7",
        source: """
      func f() {
        unsafe = 17
      }
      """,
        origin: "ExpressionTests.testUnsafeExpr",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testUnsafeExpr#8",
        source: """
      func f() {
        let unsafe = 17
      }
      """,
        origin: "ExpressionTests.testUnsafeExpr",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testUnsafeExpr#9",
        source: """
      func f() {
        f(unsafe, blah: unsafe, unsafe, unsafe: unsafe, unsafe)
      }
      """,
        origin: "ExpressionTests.testUnsafeExpr",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testUnsafeExpr#10",
        source: """
      func f() {
        guard let unsafe = a else { }
      }
      """,
        origin: "ExpressionTests.testUnsafeExpr",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testUnsafeExpr#11",
        source: """
      func f() {
        if unsafe { }
      }
      """,
        origin: "ExpressionTests.testUnsafeExpr",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testUnsafeExpr#12",
        source: """
      func f() {
        unsafe()
      }
      """,
        origin: "ExpressionTests.testUnsafeExpr",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testUnsafeExpr#13",
        source: """
      func f() {
        unsafe ()
      }
      """,
        origin: "ExpressionTests.testUnsafeExpr",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testUnsafeExpr#14",
        source: """
      func f() {
        unsafe[]
      }
      """,
        origin: "ExpressionTests.testUnsafeExpr",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testUnsafeExpr#15",
        source: """
      func f() {
        unsafe []
      }
      """,
        origin: "ExpressionTests.testUnsafeExpr",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testUnsafeExpr#16",
        source: #"""
      func f() {
        "\(unsafe)"
      }
      """#,
        origin: "ExpressionTests.testUnsafeExpr",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testUnsafeExpr#17",
        source: """
      a = unsafe
      """,
        origin: "ExpressionTests.testUnsafeExpr",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTriviaEndingInterpolation#1",
        source: #"""
      "abc\(def )"
      """#,
        origin: "ExpressionTests.testTriviaEndingInterpolation",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testInitCallInPoundIf#1",
        source: """
      class C {
      init() {
      #if true
        init()
      #endif
      }
      }
      """,
        origin: "ExpressionTests.testInitCallInPoundIf",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testClosureParameterWithModifier#1",
        source: """
      _ = { (_const x: Int) in }
      """,
        origin: "ExpressionTests.testClosureParameterWithModifier",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testClosureWithExternalParameterName#1",
        source: """
      _ = { (_ x: MyType) in }
      """,
        origin: "ExpressionTests.testClosureWithExternalParameterName",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testClosureWithExternalParameterName#2",
        source: """
      _ = { (x y: MyType) in }
      """,
        origin: "ExpressionTests.testClosureWithExternalParameterName",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testClosureParameterWithAttribute#1", source: "_ = { (@_noImplicitCopy _ x: Int) -> () in }", origin: "ExpressionTests.testClosureParameterWithAttribute", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testClosureParameterWithAttribute#2", source: "_ = { (@Wrapper x) in }", origin: "ExpressionTests.testClosureParameterWithAttribute", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testClosureParameterWithAttribute#3",
        source: """
      withInvalidOrderings { (comparisonPredicate: @escaping (Int, Int) -> Bool) in
      }
      """,
        origin: "ExpressionTests.testClosureParameterWithAttribute",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testClosureWithDollarIdentifier#1",
        source: """
      let (ids, (actions, tracking)) = state.withCriticalRegion { ($0.valueObservers(for: keyPath), $0.didSet(keyPath: keyPath)) }
      """,
        origin: "ExpressionTests.testClosureWithDollarIdentifier",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testClosureWithDollarIdentifier#2",
        source: """
      let (ids, (actions, tracking)) = state.withCriticalRegion { ($0.valueObservers(for: keyPath), $0.didSet(keyPath: keyPath)) }
      """,
        origin: "ExpressionTests.testClosureWithDollarIdentifier",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testClosureWithDollarIdentifier#3",
        source: """
      state.withCriticalRegion { (1 + 2) }
      for action in tracking {
        action()
      }
      """,
        origin: "ExpressionTests.testClosureWithDollarIdentifier",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testTypedThrowsDisambiguation#1", source: "[() throws(MyError) -> Void]()", origin: "ExpressionTests.testTypedThrowsDisambiguation", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testTypedThrowsDisambiguation#2", source: "[() throws(any Error) -> Void]()", origin: "ExpressionTests.testTypedThrowsDisambiguation", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testTypedThrowsDisambiguation#3", source: "X<() throws(MyError) -> Int>()", origin: "ExpressionTests.testTypedThrowsDisambiguation", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testTypedThrowsDisambiguation#4", source: "X<() async throws(MyError) -> Int>()", origin: "ExpressionTests.testTypedThrowsDisambiguation", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testTypedThrowsClosureParam#1",
        source: """
      try foo { (a, b) throws(S) in 1 }
      """,
        origin: "ExpressionTests.testTypedThrowsClosureParam",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testTypedThrowsShorthandClosureParams#1",
        source: """
      try foo { a, b throws(S) in 1 }
      """,
        origin: "ExpressionTests.testTypedThrowsShorthandClosureParams",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testArrayExprWithNoCommas#1", source: "[() ()]", origin: "ExpressionTests.testArrayExprWithNoCommas", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "testSendableAttributeInClosure#1", source: "f { @Sendable (e: Int) in }", origin: "ExpressionTests.testSendableAttributeInClosure", syntaxVersion: "603.0.1"),
    SwiftSnippet(
        label: "testSubscriptDeinitMembers#1",
        source: """
      .deinit
      """,
        origin: "ExpressionTests.testSubscriptDeinitMembers",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSubscriptDeinitMembers#2",
        source: """
      .subscript
      """,
        origin: "ExpressionTests.testSubscriptDeinitMembers",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSubscriptDeinitMembers#3",
        source: """
      x.deinit
      """,
        origin: "ExpressionTests.testSubscriptDeinitMembers",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(
        label: "testSubscriptDeinitMembers#4",
        source: """
      x.subscript
      """,
        origin: "ExpressionTests.testSubscriptDeinitMembers",
        syntaxVersion: "603.0.1"
    ),
    SwiftSnippet(label: "testNonBreakingSpace#1", source: "a \u{a0}+ 2", origin: "ExpressionTests.testNonBreakingSpace", syntaxVersion: "603.0.1"),
]


// MARK: - Test Suite

extension SwiftSyntax603Tests {

@Suite("Expressions")
struct ExpressionSyntaxTests {

    @Test("SwiftSyntax accepts", .tags(.swiftSyntaxReference), arguments: expressionSnippets)
    func swiftSyntaxAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let parsed = Parser.parse(source: snippet.source)
        #expect(!parsed.hasError, "SwiftSyntax parse error for: \(snippet.source)")
    }

    @Test("Advent accepts", arguments: expressionSnippets)
    func adventAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let result = try adventParse(snippet)
        #expect(result != nil, "Advent failed to parse: \(snippet.source)")
    }

    @Test("no residual ambiguity", arguments: expressionSnippets)
    func unambiguous(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        guard let result = try adventParse(snippet) else {
            Issue.record("Advent failed to parse: \(snippet.source)")
            return
        }
        #expect(result.isUnambiguous,
                "Residual ambiguity in '\(snippet.diagnosticID)': \(result.builder.diagnostics)")
    }

    @Test("trees match", arguments: expressionSnippets)
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

    @Test("ownership keywords prefer postfix call/member/subscript")
    func ownershipKeywordsPreferPostfixCall() throws {
        let snippets = [
            SwiftSnippet(label: "borrow-call-tight", source: "borrow(msg)", origin: "regression", syntaxVersion: "local"),
            SwiftSnippet(label: "borrow-call-spaced", source: "borrow (msg)", origin: "regression", syntaxVersion: "local"),
            SwiftSnippet(label: "borrow-expression", source: "borrow msg", origin: "regression", syntaxVersion: "local"),
            SwiftSnippet(label: "unsafe-spaced-tuple", source: "unsafe ()", origin: "regression", syntaxVersion: "local"),
        ]

        for snippet in snippets {
            let reference = Parser.parse(source: snippet.source)
            let refDump = dumpSwiftSyntaxNode(Syntax(reference), indent: 0)

            guard let adventTree = try adventSwiftSyntaxTree(snippet) else {
                Issue.record("Advent failed to produce SwiftSyntax tree: \(snippet.source)")
                continue
            }
            let adventDump = dumpSwiftSyntaxNode(Syntax(adventTree), indent: 0)
            #expect(refDump == adventDump, "Trees differ for '\(snippet.diagnosticID)'")
        }
    }

    @Test("macro arguments may be spaced but not on the next line")
    func macroArgumentClauseLineBoundary() throws {
        let snippets = [
            SwiftSnippet(label: "macro-arg-spaced", source: "#foo (bar)", origin: "regression", syntaxVersion: "local"),
            SwiftSnippet(label: "macro-arg-next-line", source: "#fileID\n(#line)", origin: "regression", syntaxVersion: "local"),
        ]

        for snippet in snippets {
            let reference = Parser.parse(source: snippet.source)
            let refDump = dumpSwiftSyntaxNode(Syntax(reference), indent: 0)

            guard let adventTree = try adventSwiftSyntaxTree(snippet) else {
                Issue.record("Advent failed to produce SwiftSyntax tree: \(snippet.source)")
                continue
            }
            let adventDump = dumpSwiftSyntaxNode(Syntax(adventTree), indent: 0)
            #expect(refDump == adventDump, "Trees differ for '\(snippet.diagnosticID)'")
        }
    }

    @Test("interpolated strings split into SwiftSyntax segments")
    func rawInterpolatedStringSegments() throws {
        let snippets = [
            SwiftSnippet(label: "raw-single-interpolation", source: ###"let foo = "Interpolation"; _ = #"\b\b \#(foo)\#(foo) Kappa"#"###, origin: "regression", syntaxVersion: "local"),
            SwiftSnippet(label: "raw-multiline-interpolation", source: ####"""
            _ = """
              interpolating \(##"""
                delimited \##("string")\#n\##n
                """##)
              """
            """####, origin: "regression", syntaxVersion: "local"),
        ] + translatedSnippets.filter { snippet in
            [
                "testRawString12#1",
                "testRawString26#1",
                "testRawString27#1",
                "testRawString28#1",
            ].contains(snippet.label)
        } + expressionSnippets.filter { snippet in
            [
                "testStringLiterals#6",
            ].contains(snippet.label)
        } + translatedSnippets.filter { snippet in
            [
                "testMultilineString46#1",
            ].contains(snippet.label)
        }

        for snippet in snippets {
            let reference = Parser.parse(source: snippet.source)
            let refDump = dumpSwiftSyntaxNode(Syntax(reference), indent: 0)

            guard let adventTree = try adventSwiftSyntaxTree(snippet) else {
                Issue.record("Advent failed to produce SwiftSyntax tree: \(snippet.source)")
                continue
            }
            let adventDump = dumpSwiftSyntaxNode(Syntax(adventTree), indent: 0)
            #expect(refDump == adventDump, "Trees differ for '\(snippet.diagnosticID)'")
        }
    }
}
}

// MARK: - SwiftSyntax 604 Corpus

let expression604Snippets: [SwiftSnippet] = [
    SwiftSnippet(label: "testTernary#1", source: "a ? b : c ? d : e", origin: "ExpressionTests.testTernary", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testSequence#1", source: "A as? B + C -> D is E as! F ? G = 42 : H", origin: "ExpressionTests.testSequence", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testClosureLiterals#1",
        source: #"""
      { @MainActor (a: Int) async -> Int in print("hi") }
      """#,
        origin: "ExpressionTests.testClosureLiterals",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testClosureLiterals#2",
        source: """
      { [weak self, weak weakB = b] foo in
        return 0
      }
      """,
        origin: "ExpressionTests.testClosureLiterals",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testClosureLiterals#3",
        source: """
      func f(x:[Void])
      {
        var y:[[Void]] = x.map { [$0] }
        {
          $0.reserveCapacity(1)
        } (&y[0])
      }
      """,
        origin: "ExpressionTests.testClosureLiterals",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTrailingClosures#1",
        source: """
      var button =  View.Button[5, 4, 3
      ] {
        // comment #0
        Text("ABC")
      }
      """,
        origin: "ExpressionTests.testTrailingClosures",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testTrailingClosures#2", source: "compactMap { (parserDiag) in }", origin: "ExpressionTests.testTrailingClosures", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testCollectionTrailingClosureInits#1", source: "let value = [Foo] { bar }", origin: "ExpressionTests.testCollectionTrailingClosureInits", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testCollectionTrailingClosureInits#2", source: "let value = [String: Int] { value }", origin: "ExpressionTests.testCollectionTrailingClosureInits", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testSequenceExpressions#1", source: "await a()", origin: "ExpressionTests.testSequenceExpressions", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testSequenceExpressions#2",
        source: """
      async let child = testNestedTaskPriority(basePri: basePri, curPri: curPri)
      await child
      """,
        origin: "ExpressionTests.testSequenceExpressions",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testNestedTypeSpecialization#1", source: "Swift.Array<Array<Foo>>()", origin: "ExpressionTests.testNestedTypeSpecialization", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testObjectLiterals#1",
        source: """
      #colorLiteral()
      #colorLiteral(red: 1.0)
      #colorLiteral(red: 1.0, green: 1.0)
      #colorLiteral(red: 1.0, green: 1.0, blue: 1.0, alpha: 1.0)
      """,
        origin: "ExpressionTests.testObjectLiterals",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testObjectLiterals#2",
        source: """
      #imageLiteral()
      #imageLiteral(resourceName: "foo.png")
      #imageLiteral(resourceName: "foo/bar/baz/qux.png")
      #imageLiteral(resourceName: "foo/bar/baz/quux.png")
      """,
        origin: "ExpressionTests.testObjectLiterals",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testKeypathExpression#1",
        source: #"""
      \.?.foo
      """#,
        origin: "ExpressionTests.testKeypathExpression",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testKeypathExpression#2",
        source: #"""
      children.filter(\.type.defaultInitialization.isEmpty)
      """#,
        origin: "ExpressionTests.testKeypathExpression",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testKeypathExpression#3",
        source: #"""
      _ = \Lens<[Int]>.[0]
      """#,
        origin: "ExpressionTests.testKeypathExpression",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testKeypathExpression#4",
        source: #"""
      \(UnsafeRawPointer?, String).1
      """#,
        origin: "ExpressionTests.testKeypathExpression",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testKeypathExpression#5",
        source: #"""
      \a.b.c
      """#,
        origin: "ExpressionTests.testKeypathExpression",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testKeypathExpression#6",
        source: #"""
      \ABCProtocol[100]
      """#,
        origin: "ExpressionTests.testKeypathExpression",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testKeypathExpression#7",
        source: #"""
      \S<T>.x
      """#,
        origin: "ExpressionTests.testKeypathExpression",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testKeypathExpression#8",
        source: #"""
      \TupleProperties.self
      """#,
        origin: "ExpressionTests.testKeypathExpression",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testKeypathExpression#9",
        source: #"""
      \Tuple<Int, Int>.self
      """#,
        origin: "ExpressionTests.testKeypathExpression",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testKeypathExpression#10",
        source: #"""
      \T.extension
      """#,
        origin: "ExpressionTests.testKeypathExpression",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testKeypathExpression#11",
        source: #"""
      \T.12[14]
      """#,
        origin: "ExpressionTests.testKeypathExpression",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testKeypathExpression#12",
        source: #"""
      \Optional.?!?!?!?
      """#,
        origin: "ExpressionTests.testKeypathExpression",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testKeypathExpression#13",
        source: #"""
      _ = distinctUntilChanged(\ .?.status)
      _ = distinctUntilChanged(\.?.status)
      """#,
        origin: "ExpressionTests.testKeypathExpression",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testKeyPathMethodAndInitializers#1", source: #"\Foo.method()"#, origin: "ExpressionTests.testKeyPathMethodAndInitializers", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testKeyPathMethodAndInitializers#2", source: #"\Foo.method(10)"#, origin: "ExpressionTests.testKeyPathMethodAndInitializers", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testKeyPathMethodAndInitializers#3", source: #"\Foo.method(arg: 10)"#, origin: "ExpressionTests.testKeyPathMethodAndInitializers", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testKeyPathMethodAndInitializers#4", source: #"\Foo.method(_:)"#, origin: "ExpressionTests.testKeyPathMethodAndInitializers", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testKeyPathMethodAndInitializers#5", source: #"\Foo.method(arg:)"#, origin: "ExpressionTests.testKeyPathMethodAndInitializers", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testKeyPathMethodAndInitializers#6", source: #"\Foo.method().anotherMethod(arg: 10)"#, origin: "ExpressionTests.testKeyPathMethodAndInitializers", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testKeyPathMethodAndInitializers#7", source: #"\Foo.Type.init()"#, origin: "ExpressionTests.testKeyPathMethodAndInitializers", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testKeyPathMethodAndInitializers#8", source: #"\Foo.t(a:)(2)"#, origin: "ExpressionTests.testKeyPathMethodAndInitializers", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testKeyPathMethodAndInitializers#9",
        source: #"""
      S()[keyPath: \.i] = 1
      """#,
        origin: "ExpressionTests.testKeyPathMethodAndInitializers",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testKeyPathMethodAndInitializers#10",
        source: #"""
      public let keyPath2FromLibB = \AStruct.Type.property
      """#,
        origin: "ExpressionTests.testKeyPathMethodAndInitializers",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testKeyPathMethodAndInitializers#11",
        source: #"""
      public let keyPath9FromLibB = \AStruct.Type.init(val: 2025)
      """#,
        origin: "ExpressionTests.testKeyPathMethodAndInitializers",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testKeyPathMethodAndInitializers#12",
        source: #"""
      _ = ([S]()).map(\.i)
      """#,
        origin: "ExpressionTests.testKeyPathMethodAndInitializers",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testKeyPathMethodAndInitializers#13",
        source: #"""
      let some = Some(keyPath: \Demo.here)
      """#,
        origin: "ExpressionTests.testKeyPathMethodAndInitializers",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testKeyPathMethodAndInitializers#14",
        source: #"""
      _ = ([S.Type]()).map(\.init)
      """#,
        origin: "ExpressionTests.testKeyPathMethodAndInitializers",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testKeyPathMethodAndInitializers#15",
        source: #"""
      \Lens<Lens<Point>>.obj.x
      """#,
        origin: "ExpressionTests.testKeyPathMethodAndInitializers",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testKeyPathMethodAndInitializers#16",
        source: #"""
      _ = \Lens<Point>.y
      """#,
        origin: "ExpressionTests.testKeyPathMethodAndInitializers",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testKeyPathMethodAndInitializers#17",
        source: #"""
      _ = f(\String?.!.count)
      """#,
        origin: "ExpressionTests.testKeyPathMethodAndInitializers",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testKeyPathMethodAndInitializers#18",
        source: #"""
      let _ = \K.Type.init(val: 2025)
      """#,
        origin: "ExpressionTests.testKeyPathMethodAndInitializers",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testKeyPathMethodAndInitializers#19",
        source: #"""
      let _ = \K.Type.init
      let _ = \K.Type.init()
      """#,
        origin: "ExpressionTests.testKeyPathMethodAndInitializers",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testKeyPathSubscript#1", source: #"\Foo.Type.[2]"#, origin: "ExpressionTests.testKeyPathSubscript", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testKeyPathSubscript#2", source: #"\Foo.Bar.[2]"#, origin: "ExpressionTests.testKeyPathSubscript", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testKeyPathFollowedByOperator#1", source: #"\Foo?.?.bar.?.blah"#, origin: "ExpressionTests.testKeyPathFollowedByOperator", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testKeyPathFollowedByOperator#2", source: #"\Foo?.?.?.blah"#, origin: "ExpressionTests.testKeyPathFollowedByOperator", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testKeypathExpressionWithSugaredRoot#1", source: #"\X.y"#, origin: "ExpressionTests.testKeypathExpressionWithSugaredRoot", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testKeypathExpressionWithSugaredRoot#2", source: #"\X<T>.y"#, origin: "ExpressionTests.testKeypathExpressionWithSugaredRoot", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testKeypathExpressionWithSugaredRoot#3", source: #"\X?.y"#, origin: "ExpressionTests.testKeypathExpressionWithSugaredRoot", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testKeypathExpressionWithSugaredRoot#4", source: #"\X!.y"#, origin: "ExpressionTests.testKeypathExpressionWithSugaredRoot", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testKeypathExpressionWithSugaredRoot#5", source: #"\[X].y"#, origin: "ExpressionTests.testKeypathExpressionWithSugaredRoot", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testKeypathExpressionWithSugaredRoot#6", source: #"\[X : Y].y"#, origin: "ExpressionTests.testKeypathExpressionWithSugaredRoot", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testKeypathExpressionWithSugaredRoot#7", source: #"\().y"#, origin: "ExpressionTests.testKeypathExpressionWithSugaredRoot", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testKeypathExpressionWithSugaredRoot#8", source: #"\(X).y"#, origin: "ExpressionTests.testKeypathExpressionWithSugaredRoot", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testKeypathExpressionWithSugaredRoot#9", source: #"\(X, X).y"#, origin: "ExpressionTests.testKeypathExpressionWithSugaredRoot", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testKeypathExpressionWithSugaredRoot#10", source: #"\Any.y"#, origin: "ExpressionTests.testKeypathExpressionWithSugaredRoot", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testKeypathExpressionWithSugaredRoot#11", source: #"\Self.y"#, origin: "ExpressionTests.testKeypathExpressionWithSugaredRoot", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testBasicLiterals#1",
        source: """
      #file
      #fileID
      (#line)
      #column
      #function
      #dsohandle
      __FILE__
      __LINE__
      __COLUMN__
      __FUNCTION__
      __DSO_HANDLE__

      func f() {
        return #function
      }
      """,
        origin: "ExpressionTests.testBasicLiterals",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testInitializerExpression#1", source: "Lexer.Cursor(input: input, previous: 0)", origin: "ExpressionTests.testInitializerExpression", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testCollectionLiterals#1", source: "[Dictionary<String, Int>: Int]()", origin: "ExpressionTests.testCollectionLiterals", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testCollectionLiterals#2", source: "[(Int, Double) -> Bool]()", origin: "ExpressionTests.testCollectionLiterals", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testCollectionLiterals#3", source: "[(Int, Double) -> Bool]()", origin: "ExpressionTests.testCollectionLiterals", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testCollectionLiterals#4", source: "_ = [@convention(block) ()  -> Int]().count", origin: "ExpressionTests.testCollectionLiterals", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testCollectionLiterals#5", source: "A<@convention(c) () -> Int32>.c()", origin: "ExpressionTests.testCollectionLiterals", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testCollectionLiterals#6", source: "A<(@autoclosure @escaping () -> Int, Int) -> Void>.c()", origin: "ExpressionTests.testCollectionLiterals", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testCollectionLiterals#7", source: "_ = [String: (@escaping (A<B>) -> Int) -> Void]().keys", origin: "ExpressionTests.testCollectionLiterals", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testCollectionLiterals#8",
        source: """
      [
        condition ? firstOption : secondOption,
        bar(),
      ]
      """,
        origin: "ExpressionTests.testCollectionLiterals",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testCollectionLiterals#9",
        source: """
      [
        #line : Calendar(identifier: .gregorian),
        #line : Calendar(identifier: .buddhist),
      ]
      """,
        origin: "ExpressionTests.testCollectionLiterals",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testCollectionLiterals#10",
        source: """
      #fancyMacro<Arg1, Arg2>(hello: "me")
      """,
        origin: "ExpressionTests.testCollectionLiterals",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInterpolatedStringLiterals#1",
        source: #"""
      return "Fixit: \(range.debugDescription) Text: \"\(text)\""
      """#,
        origin: "ExpressionTests.testInterpolatedStringLiterals",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInterpolatedStringLiterals#2",
        source: #"""
      "text \(array.map({ "\($0)" }).joined(separator: ",")) text"
      """#,
        origin: "ExpressionTests.testInterpolatedStringLiterals",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInterpolatedStringLiterals#3",
        source: #"""
      """
      \(gen(xx) { (x) in
          return """
          case
      """
      })
      """
      """#,
        origin: "ExpressionTests.testInterpolatedStringLiterals",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testStringLiterals#1",
        source: #"""
      "–"
      """#,
        origin: "ExpressionTests.testStringLiterals",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testStringLiterals#2",
        source: #"""
      ""
      """#,
        origin: "ExpressionTests.testStringLiterals",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testStringLiterals#3",
        source: #"""
      """
      """
      """#,
        origin: "ExpressionTests.testStringLiterals",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testStringLiterals#4",
        source: ##"""


      #"Hello World"#

      "Hello World"


      """##,
        origin: "ExpressionTests.testStringLiterals",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testStringLiterals#5",
        source: #"""
      "(?i)\\b((?:[a-z][\\w-]+:(?:/{1,3}|[a-z0-9%])|www\\d{0,3}[.]|[a-z0-9.\\-]+[.][a-z]{2,4}/)" +
      "(?:[^\\s()<>]+|\\(([^\\s()<>]+|(\\([^\\s()<>]+\\)))*\\))+(?:\\(([^\\s()<>]+|(\\([^\\s()<>]+\\)))*" +
      "\\)|[^\\s`!()\\[\\]{};:'\".,<>?«»“”‘’]))"
      """#,
        origin: "ExpressionTests.testStringLiterals",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testStringLiterals#6",
        source: #"""
      """
          Custom(custom: \(interval),\
          Expr: \(pause?.debugDescription ?? "–"), \
          PlainWithContinuation: \(countdown), \
          Plain: \(units))"
      """
      """#,
        origin: "ExpressionTests.testStringLiterals",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testStringLiterals#7",
        source: #"""
      "Founded: \(Date.appleFounding, format: 📆)"
      """#,
        origin: "ExpressionTests.testStringLiterals",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testStringLiterals#8",
        source: """

      ""
      """,
        origin: "ExpressionTests.testStringLiterals",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testStringLiterals#9",
        source: ##"""
      #"""#
      """##,
        origin: "ExpressionTests.testStringLiterals",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testStringLiterals#10",
        source: ##"""
      #"""""#
      """##,
        origin: "ExpressionTests.testStringLiterals",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testStringLiterals#11",
        source: ##"""
      #"""
      multiline raw
      """#
      """##,
        origin: "ExpressionTests.testStringLiterals",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testStringLiterals#12",
        source: #"""
      "\(x)"
      """#,
        origin: "ExpressionTests.testStringLiterals",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAdjacentRawStringLiterals#1",
        source: """
      "normal literal"
      #"raw literal"#
      """,
        origin: "ExpressionTests.testAdjacentRawStringLiterals",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAdjacentRawStringLiterals#2",
        source: """
      #"raw literal"#
      #"second raw literal"#
      """,
        origin: "ExpressionTests.testAdjacentRawStringLiterals",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testStringBogusClosingDelimiters#1",
        source: ##"""
      #"\\("#
      """##,
        origin: "ExpressionTests.testStringBogusClosingDelimiters",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSubscript#1",
        source: """
      array[]
      """,
        origin: "ExpressionTests.testSubscript",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSubscript#2",
        source: """
      text[...]
      """,
        origin: "ExpressionTests.testSubscript",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testConsumeExpression#1", source: "consume msg", origin: "ExpressionTests.testConsumeExpression", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testConsumeExpression#2", source: "use(consume msg)", origin: "ExpressionTests.testConsumeExpression", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testConsumeExpression#3", source: "consume msg", origin: "ExpressionTests.testConsumeExpression", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testConsumeExpression#4", source: "let b = (consume self).buffer", origin: "ExpressionTests.testConsumeExpression", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testBorrowExpression#1", source: "borrow msg", origin: "ExpressionTests.testBorrowExpression", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testBorrowExpression#2", source: "use(borrow msg)", origin: "ExpressionTests.testBorrowExpression", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testBorrowExpression#3", source: "borrow msg", origin: "ExpressionTests.testBorrowExpression", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testBorrowExpression#4", source: "let b = (borrow self).buffer", origin: "ExpressionTests.testBorrowExpression", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testBorrowExpression#5", source: "borrow msg", origin: "ExpressionTests.testBorrowExpression", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testBorrowExpression#6", source: "use(borrow msg)", origin: "ExpressionTests.testBorrowExpression", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testBorrowExpression#7", source: "borrow(msg)", origin: "ExpressionTests.testBorrowExpression", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testBorrowExpression#8", source: "borrow (msg)", origin: "ExpressionTests.testBorrowExpression", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testBorrowNameFunctionCallStructure1#1",
        source: """
      borrow(msg)
      """,
        origin: "ExpressionTests.testBorrowNameFunctionCallStructure1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testBorrowNameFunctionCallStructure2#1",
        source: """
      borrow (msg)
      """,
        origin: "ExpressionTests.testBorrowNameFunctionCallStructure2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testKeywordApplyExpression#1",
        source: """
      optional(x: .some(23))
      optional(x: .none)
      var pair : (Int, Double) = makePair(a: 1, b: 2.5)
      """,
        origin: "ExpressionTests.testKeywordApplyExpression",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testFalseMultilineDelimiters#1",
        source: ###"""
      _ = #"​"​"#

      _ = #""""#

      _ = #"""""#

      _ = #""""""#

      _ = ##""" foo # "# "##
      """###,
        origin: "ExpressionTests.testFalseMultilineDelimiters",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testOperatorReference#1", source: "reduce(0, +)", origin: "ExpressionTests.testOperatorReference", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testBogusCaptureLists#1",
        source: """
      {
          [
              AboutItem(title: TextContent.legalAndMore, accessoryType: .disclosureIndicator, action: { [weak self] context in
                  self?.tracker.buttonPressed(.legal)
                  context.showSubmenu(title: TextContent.legalAndMore, configuration: LegalAndMoreSubmenuConfiguration())
              }),
          ]
      }()
      """,
        origin: "ExpressionTests.testBogusCaptureLists",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testMacroExpansionExpression#1", source: #"#file == $0.path"#, origin: "ExpressionTests.testMacroExpansionExpression", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testMacroExpansionExpression#2", source: #"let a = #embed("filename.txt")"#, origin: "ExpressionTests.testMacroExpansionExpression", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testMacroExpansionExpression#3",
        source: """
      #Test {
        print("This is a test")
      }
      """,
        origin: "ExpressionTests.testMacroExpansionExpression",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testMacroExpansionExpressionWithKeywordName#1", source: "#case", origin: "ExpressionTests.testMacroExpansionExpressionWithKeywordName", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testPostProcessMultilineStringLiteral#1",
        source: #"""
        """
        line 1
        line 2
        """
      """#,
        origin: "ExpressionTests.testPostProcessMultilineStringLiteral",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testPostProcessMultilineStringLiteral#2",
        source: #"""
        """
        line 1 \
        line 2
        """
      """#,
        origin: "ExpressionTests.testPostProcessMultilineStringLiteral",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMultiLineStringInInterpolationOfSingleLineStringLiteral#1",
        source: #"""
      "foo\(test("""
      bar
      """) )"
      """#,
        origin: "ExpressionTests.testMultiLineStringInInterpolationOfSingleLineStringLiteral",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEmptyLineInMultilineStringLiteral#1",
        source: #"""
        """
        line 1

        line 2
        """
      """#,
        origin: "ExpressionTests.testEmptyLineInMultilineStringLiteral",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testEmptyLineInMultilineStringLiteral#2",
        source: #"""
        """
        line 1

        """
      """#,
        origin: "ExpressionTests.testEmptyLineInMultilineStringLiteral",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTabsIndentationInMultilineStringLiteral#1",
        source: #"""
      _ = """
      \#taq
      \#t"""
      """#,
        origin: "ExpressionTests.testTabsIndentationInMultilineStringLiteral",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testMixedIndentationInMultilineStringLiteral#1",
        source: #"""
      _ = """
      \#t aq
      \#t """
      """#,
        origin: "ExpressionTests.testMixedIndentationInMultilineStringLiteral",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testLiteralWithTrailingClosure#1", source: "_ = [1] { return [1] }", origin: "ExpressionTests.testLiteralWithTrailingClosure", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testLiteralWithTrailingClosure#2", source: "_ = [1: 1] { return [1: 1] }", origin: "ExpressionTests.testLiteralWithTrailingClosure", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testTrailingCommasInTypeExpressions#1",
        source: """
      let _ = Foo2<Int, Bool, String,>.self
      """,
        origin: "ExpressionTests.testTrailingCommasInTypeExpressions",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTrailingCommasInTypeExpressions#2",
        source: """
      let _ = Foo2<Int, Bool, String,>()
      """,
        origin: "ExpressionTests.testTrailingCommasInTypeExpressions",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTrailingCommasInTypeExpressions#3",
        source: """
      let _ = ((Int, Bool, String,) -> Void).self
      """,
        origin: "ExpressionTests.testTrailingCommasInTypeExpressions",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTrailingCommasInTypeExpressions#4",
        source: """
      let _ = Array<(
        bar: String,
        baaz: String,
      )>()
      """,
        origin: "ExpressionTests.testTrailingCommasInTypeExpressions",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIfExprInCoercion#1",
        source: """
      func foo() {
        if .random() { 0 } else { 1 } as Int
      }
      """,
        origin: "ExpressionTests.testIfExprInCoercion",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitchExprInCoercion#1",
        source: """
      switch Bool.random() { case true: 0 case false: 1 } as Int
      """,
        origin: "ExpressionTests.testSwitchExprInCoercion",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIfExprInReturn#1",
        source: """
      func foo() {
        return if .random() { 0 } else { 1 }
      }
      """,
        origin: "ExpressionTests.testIfExprInReturn",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitchExprInReturn#1",
        source: """
      func foo() {
        return switch Bool.random() { case true: 0 case false: 1 }
      }
      """,
        origin: "ExpressionTests.testSwitchExprInReturn",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTryIf1#1",
        source: """
      func foo() -> Int {
        try if .random() { 0 } else { 1 }
      }
      """,
        origin: "ExpressionTests.testTryIf1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTryIf2#1",
        source: """
      func foo() -> Int {
        return try if .random() { 0 } else { 1 }
      }
      """,
        origin: "ExpressionTests.testTryIf2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTryIf3#1",
        source: """
      func foo() -> Int {
        let x = try if .random() { 0 } else { 1 }
        return x
      }
      """,
        origin: "ExpressionTests.testTryIf3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAwaitIf1#1",
        source: """
      func foo() async -> Int {
        await if .random() { 0 } else { 1 }
      }
      """,
        origin: "ExpressionTests.testAwaitIf1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAwaitIf2#1",
        source: """
      func foo() async -> Int {
        return await if .random() { 0 } else { 1 }
      }
      """,
        origin: "ExpressionTests.testAwaitIf2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAwaitIf3#1",
        source: """
      func foo() async -> Int {
        let x = await if .random() { 0 } else { 1 }
        return x
      }
      """,
        origin: "ExpressionTests.testAwaitIf3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTrySwitch1#1",
        source: """
      try switch Bool.random() { case true: 0 case false: 1 }
      """,
        origin: "ExpressionTests.testTrySwitch1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTrySwitch2#1",
        source: """
      func foo() -> Int {
        return try switch Bool.random() { case true: 0 case false: 1 }
      }
      """,
        origin: "ExpressionTests.testTrySwitch2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTrySwitch3#1",
        source: """
      func foo() -> Int {
        let x = try switch Bool.random() { case true: 0 case false: 1 }
        return x
      }
      """,
        origin: "ExpressionTests.testTrySwitch3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAwaitSwitch1#1",
        source: """
      await switch Bool.random() { case true: 0 case false: 1 }
      """,
        origin: "ExpressionTests.testAwaitSwitch1",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAwaitSwitch2#1",
        source: """
      func foo() async -> Int {
        return await switch Bool.random() { case true: 0 case false: 1 }
      }
      """,
        origin: "ExpressionTests.testAwaitSwitch2",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testAwaitSwitch3#1",
        source: """
      func foo() async -> Int {
        let x = await switch Bool.random() { case true: 0 case false: 1 }
        return x
      }
      """,
        origin: "ExpressionTests.testAwaitSwitch3",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIfExprCondCast#1",
        source: """
      if .random() { 0 } else { 1 } as? Int
      """,
        origin: "ExpressionTests.testIfExprCondCast",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testIfExprForceCast#1",
        source: """
      if .random() { 0 } else { 1 } as! Int
      """,
        origin: "ExpressionTests.testIfExprForceCast",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitchExprCondCast#1",
        source: """
      switch Bool.random() { case true: 0 case false: 1 } as? Int
      """,
        origin: "ExpressionTests.testSwitchExprCondCast",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSwitchExprForceCast#1",
        source: """
      switch Bool.random() { case true: 0 case false: 1 } as! Int
      """,
        origin: "ExpressionTests.testSwitchExprForceCast",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testUnsafeExpr#1",
        source: """
      func f() {
        let x = unsafe y
      }
      """,
        origin: "ExpressionTests.testUnsafeExpr",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testUnsafeExpr#2",
        source: """
      func f() {
        let x = unsafe
        y
      }
      """,
        origin: "ExpressionTests.testUnsafeExpr",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testUnsafeExpr#3",
        source: """
      func f() {
        unsafe.lock()
      }
      """,
        origin: "ExpressionTests.testUnsafeExpr",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testUnsafeExpr#4",
        source: """
      func f() {
        unsafe .lock
      }
      """,
        origin: "ExpressionTests.testUnsafeExpr",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testUnsafeExpr#5",
        source: """
      func f() {
        _ = [unsafe]
      }
      """,
        origin: "ExpressionTests.testUnsafeExpr",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testUnsafeExpr#6",
        source: """
      func f() {
        _ = [unsafe]
      }
      """,
        origin: "ExpressionTests.testUnsafeExpr",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testUnsafeExpr#7",
        source: """
      func f() {
        unsafe = 17
      }
      """,
        origin: "ExpressionTests.testUnsafeExpr",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testUnsafeExpr#8",
        source: """
      func f() {
        let unsafe = 17
      }
      """,
        origin: "ExpressionTests.testUnsafeExpr",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testUnsafeExpr#9",
        source: """
      func f() {
        f(unsafe, blah: unsafe, unsafe, unsafe: unsafe, unsafe)
      }
      """,
        origin: "ExpressionTests.testUnsafeExpr",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testUnsafeExpr#10",
        source: """
      func f() {
        guard let unsafe = a else { }
      }
      """,
        origin: "ExpressionTests.testUnsafeExpr",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testUnsafeExpr#11",
        source: """
      func f() {
        if unsafe { }
      }
      """,
        origin: "ExpressionTests.testUnsafeExpr",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testUnsafeExpr#12",
        source: """
      func f() {
        unsafe()
      }
      """,
        origin: "ExpressionTests.testUnsafeExpr",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testUnsafeExpr#13",
        source: """
      func f() {
        unsafe ()
      }
      """,
        origin: "ExpressionTests.testUnsafeExpr",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testUnsafeExpr#14",
        source: """
      func f() {
        unsafe[]
      }
      """,
        origin: "ExpressionTests.testUnsafeExpr",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testUnsafeExpr#15",
        source: """
      func f() {
        unsafe []
      }
      """,
        origin: "ExpressionTests.testUnsafeExpr",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testUnsafeExpr#16",
        source: #"""
      func f() {
        "\(unsafe)"
      }
      """#,
        origin: "ExpressionTests.testUnsafeExpr",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testUnsafeExpr#17",
        source: """
      a = unsafe
      """,
        origin: "ExpressionTests.testUnsafeExpr",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTriviaEndingInterpolation#1",
        source: #"""
      "abc\(def )"
      """#,
        origin: "ExpressionTests.testTriviaEndingInterpolation",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testInitCallInPoundIf#1",
        source: """
      class C {
      init() {
      #if true
        init()
      #endif
      }
      }
      """,
        origin: "ExpressionTests.testInitCallInPoundIf",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testClosureParameterWithModifier#1",
        source: """
      _ = { (_const x: Int) in }
      """,
        origin: "ExpressionTests.testClosureParameterWithModifier",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testClosureWithExternalParameterName#1",
        source: """
      _ = { (_ x: MyType) in }
      """,
        origin: "ExpressionTests.testClosureWithExternalParameterName",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testClosureWithExternalParameterName#2",
        source: """
      _ = { (x y: MyType) in }
      """,
        origin: "ExpressionTests.testClosureWithExternalParameterName",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testClosureParameterWithAttribute#1", source: "_ = { (@_noImplicitCopy _ x: Int) -> () in }", origin: "ExpressionTests.testClosureParameterWithAttribute", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testClosureParameterWithAttribute#2", source: "_ = { (@Wrapper x) in }", origin: "ExpressionTests.testClosureParameterWithAttribute", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testClosureParameterWithAttribute#3",
        source: """
      withInvalidOrderings { (comparisonPredicate: @escaping (Int, Int) -> Bool) in
      }
      """,
        origin: "ExpressionTests.testClosureParameterWithAttribute",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testClosureWithDollarIdentifier#1",
        source: """
      let (ids, (actions, tracking)) = state.withCriticalRegion { ($0.valueObservers(for: keyPath), $0.didSet(keyPath: keyPath)) }
      """,
        origin: "ExpressionTests.testClosureWithDollarIdentifier",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testClosureWithDollarIdentifier#2",
        source: """
      let (ids, (actions, tracking)) = state.withCriticalRegion { ($0.valueObservers(for: keyPath), $0.didSet(keyPath: keyPath)) }
      """,
        origin: "ExpressionTests.testClosureWithDollarIdentifier",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testClosureWithDollarIdentifier#3",
        source: """
      state.withCriticalRegion { (1 + 2) }
      for action in tracking {
        action()
      }
      """,
        origin: "ExpressionTests.testClosureWithDollarIdentifier",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testTypedThrowsDisambiguation#1", source: "[() throws(MyError) -> Void]()", origin: "ExpressionTests.testTypedThrowsDisambiguation", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testTypedThrowsDisambiguation#2", source: "[() throws(any Error) -> Void]()", origin: "ExpressionTests.testTypedThrowsDisambiguation", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testTypedThrowsDisambiguation#3", source: "X<() throws(MyError) -> Int>()", origin: "ExpressionTests.testTypedThrowsDisambiguation", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testTypedThrowsDisambiguation#4", source: "X<() async throws(MyError) -> Int>()", origin: "ExpressionTests.testTypedThrowsDisambiguation", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testTypedThrowsClosureParam#1",
        source: """
      try foo { (a, b) throws(S) in 1 }
      """,
        origin: "ExpressionTests.testTypedThrowsClosureParam",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testTypedThrowsShorthandClosureParams#1",
        source: """
      try foo { a, b throws(S) in 1 }
      """,
        origin: "ExpressionTests.testTypedThrowsShorthandClosureParams",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(label: "testArrayExprWithNoCommas#1", source: "[() ()]", origin: "ExpressionTests.testArrayExprWithNoCommas", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(label: "testSendableAttributeInClosure#1", source: "f { @Sendable (e: Int) in }", origin: "ExpressionTests.testSendableAttributeInClosure", syntaxVersion: "604.0.0-prerelease-2026-06-05"),
    SwiftSnippet(
        label: "testSubscriptDeinitMembers#1",
        source: """
      .deinit
      """,
        origin: "ExpressionTests.testSubscriptDeinitMembers",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSubscriptDeinitMembers#2",
        source: """
      .subscript
      """,
        origin: "ExpressionTests.testSubscriptDeinitMembers",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSubscriptDeinitMembers#3",
        source: """
      x.deinit
      """,
        origin: "ExpressionTests.testSubscriptDeinitMembers",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
    SwiftSnippet(
        label: "testSubscriptDeinitMembers#4",
        source: """
      x.subscript
      """,
        origin: "ExpressionTests.testSubscriptDeinitMembers",
        syntaxVersion: "604.0.0-prerelease-2026-06-05"
    ),
]

extension SwiftSyntax604Tests {

@Suite("Expressions")
struct ExpressionSyntax604Tests {

    @Test("SwiftSyntax accepts", .tags(.swiftSyntaxReference), arguments: expression604Snippets)
    func swiftSyntaxAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        #expect(!swiftSyntaxReferenceHasError(snippet), "SwiftSyntax parse error for: \(snippet.source)")
    }

    @Test("Advent accepts", arguments: expression604Snippets)
    func adventAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let result = try adventParse(snippet)
        #expect(result != nil, "Advent failed to parse: \(snippet.source)")
    }

    @Test("no residual ambiguity", arguments: expression604Snippets)
    func unambiguous(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        guard let result = try adventParse(snippet) else {
            Issue.record("Advent failed to parse: \(snippet.source)")
            return
        }
        #expect(result.isUnambiguous,
                "Residual ambiguity in '\(snippet.diagnosticID)': \(result.builder.diagnostics)")
    }

    @Test("trees match", arguments: expression604Snippets)
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

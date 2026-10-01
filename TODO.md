# Active TODO

This file is the canonical active TODO list for the project.
It holds actionable items only.
Put completed work and historical explanations in design notes or commit messages.

1. Fix `_lifetime` labelled dependency arguments. `crawl3` found 22 underaccepts at
   `_lifetime(self: copy self)`, for example
   `/Users/janwillem/Library/Caches/ApusApusCorpus/repos/apple__swift-collections/Sources/BasicContainers/HashTable/_HTable+Deprecated.swift`
   line 21. ApusApus currently stops at `self:` and expects `)`. Add the labelled
   dependency form without weakening the existing `borrow/copy/&name` forms, then add a focused
   SwiftSyntax regression for `@_lifetime(self: copy self)`.

2. Fix `&` type-composition underaccepts in conformance, associatedtype, and inheritance
   positions. `crawl3` found about 19 files where the compiler and swift-syntax accept a type list
   containing `&`, but ApusApus expects `.`, `::`, `where`, `#if`, or `#sourceLocation`. Examples:
   `associatedtype Buffer: RangeReplaceableContainer<ReadElement> & ~Copyable` in
   `apple__swift-async-algorithms/Sources/AsyncStreaming/AsyncReader/AsyncReader.swift`, and
   `struct NonCopyableTests: ~Copyable & ~Escapable` in
   `apple__swift-testing/Sources/Testing/ExitTests/ExitTest.CapturedValue.swift`. Keep the fix in
   the shared type grammar if possible rather than adding position-specific hacks.

3. Fix pack iteration and pack member type/expression forms from real source files. `crawl3`
   underaccepts include `repeat inputTypes.append((each Input).self)`,
   `Array(repeat (each T).self)`, `repeat (each lhs.values, each rhs.values)`, and type-member
   forms such as `(each Input).Output` / `[any Markup].Index`. Example files include
   `apple__swift-foundation/Sources/FoundationEssentials/Predicate/Archiving/PredicateExpressionConstruction.swift`
   and `apple__swift-testing/Sources/Testing/ExitTests/ExitTest.swift`. Extend the existing
   pack/type-member rules, preserving the recent `packType` consolidation.

4. Fix multiple trailing closure labels after an unlabeled trailing closure. `crawl3` has 4
   underaccepts and 26 tree differences around calls shaped like
   `.confirmationDialog(...) { ... } message: { _ in ... }`, for example
   `coteditor__CotEditor/CotEditor/Sources/Settings Window/Other Views/ThemeView.swift` line 261.
   ApusApus currently stops before `message:` / `label:` in some cases, and the converter often
   reports `ClosureExpr != MultipleTrailingClosureElementList`. Acceptance and tree shape should be
   fixed together.

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

4. DONE 2026-10-03 — `@right` replaced the `>n<` gate on `functionCallExpression`'s parenless
   alternate, and both remaining trailing-closure divergences are gone: `x.map ⏎ { $0 }` now
   attaches and `f(1) {} ⏎ {}` now chains. 26/26 trailing-closure corpus files `same`, 400-file
   targeted set 392/5/3 (unchanged), 1,251-file slice 11 × tree-difference → same with zero
   regressions, 2,005 tests green.

   The blocker was a PASS-ORDER bug in the Oracle, not the filter. `APUS_TRACE_ORACLE=1` showed
   `LongestMatchRule` and `AssociativityFilterRule` killing opposite readings inside one pass:

       LongestMatchRule pruned patternInitializer#1867 [25..55]'y:[[Void]] = x.map { [$0] }'
       AssociativityFilterRule pruned nonLiteralPostfix#4229 [38..55]'x.map { [$0] }'
       after phase 2 dead-wood: root full-span yield *** GONE ***

   `@longest` took the maximal initializer (the chained reading), the filter then removed the
   chain, and nothing was left. Root cause: NONE of the preference rules overrode
   `isHardConstraint`, so they inherited the protocol default `true` and ran in the
   hard-constraint pass — the preference pass was effectively empty, contradicting the protocol's
   own documentation ("Preferences (`@longest`/`@shortest`/`@prefer`/`@avoid`, associativity)
   merely choose among readings that are all legal"). `LongestMatchRule` now declares
   `isHardConstraint = false`, so the inter-pass dead-wood sweep runs between the filter's kill and
   `@longest`'s choice, and `@longest` then picks the longest SURVIVING extent.
   RESOLVED 2026-10-03 for four of the five: `ShortestMatchRule`, `LeftAssocRule`,
   `RightAssocRule` and `AvoidOptionalRule` now declare `isHardConstraint = false`. Measured:
   1,251-file slice byte-identical (0 per-file changes), 23,499/23,524 tests — i.e. no effect
   either way, so they are now simply classified correctly. `PreferRule` is the exception; see #6.

5. DONE 2026-10-03 — `@left`/`@right` now take an optional operand list, and the
   `nonLiteralPostfix` / `nonLiteralPrimary` clone pair is gone — 2 rules carrying 21 alternates
   (578 → 576 nonterminals, 3580 → 3562 lines):

       functionCallExpression = @prefer postfixExpression functionCallArgumentClause trailingClosures
                              | @right @right( literalExpression ) postfixExpression trailingClosures .

   Bare `@left`/`@right` is unchanged (associativity: "not my own child"); with operands it is
   SDF's argument-indexed priority ("none of these nonterminals may be that child"). Two stack on
   the one alternate: the bare `@right` is the chain rule from #4, the operand form is B1.

   The match is on EXTENT, which is what made the clone unnecessary. B1's old two-case split —
   "either a non-literal primary, or a literal with at least one postfix operation applied" —
   falls out of span equality: the callee of `1 {}` spans exactly the `literalExpression`, while
   the callee of `1! {}`, `[1][0] {}` or `1.description {}` spans MORE than any literal. No
   enumeration of the allowed alternates is needed.

   The clones had drifted from their originals in four ways, all silently repaired by the
   deletion: missing `inlineArrayType`, missing `parenthesisedSpecifierType`, missing `@prefer`
   on the postfix-operator alternate, and a bare `parenthesizedExpression` that had lost its
   `@prefer @cannotParse(parenthesisedSpecifierType)`.

   Measured, all against the pre-#5 grammar: 1,251-file slice 1239 same / 3 tree-difference /
   6 underaccept / 3 reference-disagreement (identical to post-#4; 11 fixes and 0 regressions
   against the pre-#4 `/tmp/cb0`), 400-file targeted set 392/5/3 unchanged, 26/26 trailing-closure
   files `same`, all 9 REJECTS B1 cases unchanged (#6 regex is still the known open residual —
   regex literals are not in `literalExpression`), 23,499 of 23,524 tests pass — including three
   new fixtures pinning B1's accept side (`1! {}`, `[1][0] {}`, `1.description {}`), which is
   what the extent match buys and was previously untested. The 24 test failures
   (`init()/deinit` in a function body, `nonisolated(nonsending)` inside `[…]`) are pre-existing:
   verified identical at HEAD, pre-#5 and post-#5.

   Scan result for the rest of the grammar (2026-10-02): of 18 left-recursive alternates carrying
   a layout gate, only `nonLiteralPostfix >n< trailingClosures` was a nesting rule in disguise.
   Every other gate is a genuine layout or lexical constraint with reference backing — the call
   `(` and subscript `[` ones cite `allowAtStartOfLine:false`, and the `>s<` ones are token
   tightness (`a !` is not a force-unwrap). So the filter has no further customers here.

6. Decide what to do about `PreferRule`'s pass. It is a preference that must currently run as a
   HARD constraint, and that mis-classification is the direct cause of the 24 standing test
   failures. Measured 2026-10-03, A/B on the one line `PreferRule.isHardConstraint`:

   | `PreferRule` | failures | which |
   |---|---|---|
   | `true` (current) | 24 | `testInitDeinit21/22` (`init()`/`deinit` in a function body), `testNonisolatedSpecifier#4/#13` (`nonisolated(nonsending)` inside `[…]`) — all × 6 assertions |
   | `false` | 1 | `trailing-closure-chained-after-parens`, `let v = f(1) {}`⏎`{}` |

   The 1,251-file corpus slice is byte-identical under both, so this is only visible in the
   focused tests.

   Why it cannot just be moved: `AssociativityFilterRule` is a hard constraint that DEPENDS on
   `@prefer` having already run. `f(1) {}` is derivable twice — as the paren alternate and as the
   parenless one with callee `f(1)` — and `@prefer` removes the second. Run `@prefer` later and
   the filter sees `f(1) {}` as an instance of itself and kills the chain, which is the #4 fix
   undone. So the pass split cannot express "this hard constraint consumes that preference's
   output".

   Net is +23, so moving it is tempting, but it trades 24 long-standing known-bad cases for one
   known-good case that #4 just fixed and that has a corpus fixture behind it. Do not take that
   trade blind. Options, cheapest first:
   a. Give `AssociativityFilterRule` its own third pass AFTER the preferences, so `@prefer` can
      move and the filter still reads settled extents. Needs a check that no other hard
      constraint depends on the filter.
   b. Make the filter not need `@prefer`'s output — e.g. anchor it on the alternate rather than
      on span extents, so the paren reading is never mistaken for the parenless one.
   c. Keep `PreferRule` hard and fix the 24 failures at the grammar level instead.
   Whichever is chosen, re-run the 1,251-file slice and the full suite; both are cheap here.

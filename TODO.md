# Active TODO

This file is the canonical active TODO list for the project.
It holds actionable items only.
Put completed work and historical explanations in design notes or commit messages.

1. Reduce parser-mode performance overhead in the zero-mode hot path. The parser-mode migration
    widened `Descriptor` and CRF `ParsePosition` with a `UInt64 mode`, so every descriptor/CRF hash
    now pays for mode even though almost all descriptors run with mode `0`. A first fast path
    (`GrammarNode.hasModeAnnotation`) recovered some full-suite wall time, but the runnable Xcode
    suite still drifted from the expected ~110s to ~151s. Investigate a principled zero-mode
    specialization for descriptors/CRF keys, or another representation that preserves scoped mode
    semantics without taxing grammars/regions that do not use modes.  Remove previous optimizations that bring more complexity than speedup.

2. DONE (2026-10-06). `compilationCondition = >n< expression` under the new shallow
    `@sameLineOutsideBrackets` (swift-syntax `.poundIfDirective` flavor); `@sameLine` walk fixes
    (zero-width suffix keeps the trailing allowance; cycle-cut `false` no longer memoised); one-element
    tuple `(A,)`; postfix `#if` body head must be `.`; `ifConfigBody` mode cleared after the first
    statement and made disjoint from the lookbehind alternates. Replay: 16/34 artifacts fixed, the
    rest belong elsewhere. Residuals: (a) after a POSTFIX block's `#endif`, a following leading-dot
    `#if` is postfix in swift-syntax, but `<+<( "#endif" )` takes it as statement-level
    (`baseExpr⏎#if C⏎.m()⏎#endif⏎#if C⏎.m()⏎return⏎#endif` overaccepts); (b) tuple TYPE `(Int,)`
    underaccepts; (c) non-`#if` artifacts seen in the replay: `@⏎unknown default`, `get get throws`,
    `while () -> Int { }`, `[any~Copyable]()` tree-difference, `*/()`, `@available(…, consuming:`.
    Original text: Triage the 2026-10-06 fuzzer conditional-compilation context clusters. Strong underaccepts include
    nested `#if` bodies in functions/closures, for example `#if CONDITION_2 .methodOne()` inside a
    function and `fuzz { #if (A, ) #endif }`. Strong overaccepts include leading-dot or malformed
    `#if` bodies that swiftc and SwiftSyntax both reject, such as a closure containing `v = x` then
    `#if FOO .borrowing #else b #endif`, `#if` followed by a newline expression, and malformed
    `#if (macOS)` wrappers around leading-dot expression fragments. Keep this separate from the
    earlier fixed statement/member `#if` cases; the likely boundary is still postfix-vs-statement
    context, but these artifacts mix valid recovery and invalid overaccepts.

3. Triage the 2026-10-06 fuzzer declaration/specifier overaccept clusters. Repeated strong
    overaccepts include invalid `dependsOn` result specifiers (`func foo() -> dependsOn(x, y) X`),
    `using` declarations in invalid positions or spellings (`using nonisolated`, `using test`,
    `using MainActor` in closure/top-level mutation contexts), malformed operator declarations
    (`infix operator <*<>*> : AdditionPrecedence,`, `postfix operator +++ {}`), and initializer
    declarations with return types (`init(ptr: Array< >) -> dependsOn(a) Self`). Reduce by family and
    check whether the fix belongs in specifier grammar, declaration placement, or feature-gated
    `using` handling.

4. DONE (2026-10-07). The raw regex/interpolation timeout cluster was stale fuzzer plumbing, not
    scanner backtracking or parser descriptor explosion. Replay with
    `APUS_COMPILER_TIMEOUT_SECONDS=1` shows malformed interpolation regex samples classify as
    `compiler-timeout` while APUS finishes cheaply (`_ = "a\\(_ = /)b"`: 173 descriptors,
    ~0.004s parse; raw interpolation seed: 112 descriptors, ~0.003s parse). Valid controls such as
    `_ = "a\\( /x/ )b"` still return `same`. `SwiftSyntaxFuzzer/bin/run-night.sh` already exported
    the compiler timeout, but `AdventFuzzRunner` replaced the probe child environment and dropped it;
    the runner now forwards `APUS_COMPILER_TIMEOUT_SECONDS` to both persistent and one-shot probes.

5. DONE (2026-10-07). Replayed the 2026-10-05 crawl residues against the current grammar. The old
    bucket is stale: the named CodexBar close-bracket/subscript underaccept cluster now mostly
    returns `same` (`StatusItemController+MemoryPressure.swift`,
    `OpenRouterProviderDescriptor.swift`, `CodexCompactSubagentAccountingTests.swift`,
    `CodexPATTests.swift`, `CopilotAllowanceCacheTests.swift`), and the Kingfisher/Fluent
    underaccepts from shorthand `self` closure names or trailing closures are fixed or have moved to
    tree-difference territory. Several old string tree-differences also replay as `same`
    (`SnippetResolverTests.swift`, `OutOfProcessReferenceResolverV2Tests.swift`). Current survivors
    should be tracked as fresh, narrower work if they matter: SPM `InitPackage.swift` still
    underaccepts near a nested raw multiline string fragment (`"""#` inside `##"""` context);
    `CommandParser.swift`, `PredicateExpressionConstruction.swift`, and `ChannelOption.swift` still
    produce tree differences; `MultilineErrorsTests.swift` now reports residual ambiguity; the large
    `AISettingsView+AIConfiguration.swift` and original 600s timeout files need a separate
    performance replay with a rebuilt/current probe. Full 60-file replay was stopped at the repo's
    120s command limit, so these are representative targeted results rather than a fresh crawl.

6. Fix condition-list closure-call underaccept. Reduced current fuzzer replay still reports
    `advent-underaccept` for:
    ```
    fuzz {
    if true, {
    }() {}
    }
    ```
    SwiftSyntax and `swiftc -parse` accept it. APUS fails at the closure close brace before the
    immediate call, expecting `>n<`; likely boundary is closure expressions/calls inside
    `conditionList` after the parser-mode condition work.

7. Fix line-broken `@unknown case` underaccept. Reduced current fuzzer replay still reports
    `advent-underaccept` for:
    ```
    switch Thing {
    @
    unknown case ():break
    }
    ```
    SwiftSyntax and `swiftc -parse` accept the trivia split between `@` and `unknown`; APUS fails at
    `unknown`, expecting `>s<`. Check attribute/`@unknown` spelling rules in switch cases without
    broadening ordinary attributes incorrectly.

8. Resolve residual ambiguity for newline metatype continuation after a typealias assignment. Reduced
    current fuzzer replay still reports `residual-ambiguity` (`statement` ambiguous pivot) for:
    ```
    typealias
    Z = Copyable
    .Type
    ```
    Determine whether SwiftSyntax treats `.Type` as a same-statement metatype continuation here and
    adjust statement separation or metatype/member-type disambiguation accordingly.

9. Resolve residual ambiguity for initialized property followed by observer/accessor-looking block.
    Reduced current fuzzer replay still reports `residual-ambiguity` (`statement` ambiguous pivot) for:
    ```
    var x = 0
    { willSet {} }
    ```
    Decide whether this should be one variable declaration with an accessor/observer block or two
    statements under SwiftSyntax, then constrain the competing `statement` derivation.

10. Reduce and fix remaining whole-file tree differences from the October crawl survivors. Current
    replay still produces tree mismatches in:
    - `apple__swift-argument-parser/Sources/ArgumentParser/Parsing/CommandParser.swift`:
      `GenericSpecializationExpr` vs `DeclReferenceExpr`.
    - `apple__swift-foundation/Sources/FoundationEssentials/Predicate/Archiving/PredicateExpressionConstruction.swift`:
      `FunctionCallExpr` vs `SequenceExpr`.
    - `apple__swift-nio/Sources/NIOCore/ChannelOption.swift`: `TupleExpr` vs `PatternExpr`.
    Reduce these before editing grammar/converter code; they are likely real shape bugs but not yet
    small enough to assign to one grammar rule.

11. Reduce and fix multiline string residual ambiguity from `MultilineErrorsTests.swift`. Current
    whole-file replay reports `residual-ambiguity` in `stringLiteral` with competing
    `[interpolatedStringLiteral] | [staticStringLiteral]` readings. Minimize the source before
    changing string literal rules, because several October string tree-differences have already gone
    stale on the current grammar.

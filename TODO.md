# Active TODO

This file is the canonical active TODO list for the project.
It holds actionable items only.
Put completed work and historical explanations in design notes or commit messages.   

1. Fix condition-list closure-call underaccept. Reduced current fuzzer replay still reports
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

2. Fix line-broken `@unknown case` underaccept. Reduced current fuzzer replay still reports
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

3. Resolve residual ambiguity for newline metatype continuation after a typealias assignment. Reduced
    current fuzzer replay still reports `residual-ambiguity` (`statement` ambiguous pivot) for:
    ```
    typealias
    Z = Copyable
    .Type
    ```
    Determine whether SwiftSyntax treats `.Type` as a same-statement metatype continuation here and
    adjust statement separation or metatype/member-type disambiguation accordingly.

4. Resolve residual ambiguity for initialized property followed by observer/accessor-looking block.
    Reduced current fuzzer replay still reports `residual-ambiguity` (`statement` ambiguous pivot) for:
    ```
    var x = 0
    { willSet {} }
    ```
    Decide whether this should be one variable declaration with an accessor/observer block or two
    statements under SwiftSyntax, then constrain the competing `statement` derivation.

5. Reduce and fix remaining whole-file tree differences from the October crawl survivors. Current
    replay still produces tree mismatches in:
    - `apple__swift-argument-parser/Sources/ArgumentParser/Parsing/CommandParser.swift`:
      `GenericSpecializationExpr` vs `DeclReferenceExpr`.
    - `apple__swift-foundation/Sources/FoundationEssentials/Predicate/Archiving/PredicateExpressionConstruction.swift`:
      `FunctionCallExpr` vs `SequenceExpr`.
    - `apple__swift-nio/Sources/NIOCore/ChannelOption.swift`: `TupleExpr` vs `PatternExpr`.
    Reduce these before editing grammar/converter code; they are likely real shape bugs but not yet
    small enough to assign to one grammar rule.

6. Reduce and fix multiline string residual ambiguity from `MultilineErrorsTests.swift`. Current
    whole-file replay reports `residual-ambiguity` in `stringLiteral` with competing
    `[interpolatedStringLiteral] | [staticStringLiteral]` readings. Minimize the source before
    changing string literal rules, because several October string tree-differences have already gone
    stale on the current grammar.

7. Fix comment/trivia being lexed as operators around member access, subscripts, and postfix calls.
    The 2026-10-07 fuzzer run (`SwiftSyntaxFuzzer/runs/worker-*/2026-10-07T08-39-21Z`) produced
    repeated tree differences and over/underaccepts where APUS reads comment delimiters as operator
    tokens instead of trivia. Representative reduced artifacts:
    ```
    ./*c*/init()
    x
    ./*
    */f< >()
    text[.../*c*/]
    ```
    SwiftSyntax treats these as member access/subscript/call through trivia, while APUS produces
    `./*`, `.../*`, or `*/` prefix/binary/postfix operators. This is the strongest new signal from
    the run and likely explains several scattered tree-difference clusters.

8. Fix slash/regex/operator boundary underaccepts around `/)/`. The same fuzzer run wrote many
    reduced underaccepts in this family, including:
    ```
    /)/
    _ = /)/
    something() { _ = ^^/)/ }
    ```
    SwiftSyntax and `swiftc -parse` accept these, but APUS rejects them. Keep this separate from the
    comment-as-operator bug unless reduction shows the same scanner boundary is responsible.

9. Decide and fix top-level closure-expression overaccept policy. The largest normalized
    overaccept bucket from the 2026-10-07 run is `top-level statement cannot begin with a closure
    expression` (about 188 artifacts), with reduced shapes like:
    ```
    { [@Sendable Sendable -> Void]() }
    { func expansion(context: some MacroExpansionContext) throws -> [CodeBlockItemSyntax] }
    ```
    SwiftSyntax/`swiftc -parse` reject these as top-level closure-expression starts, while APUS
    accepts them. Determine whether this belongs in the top-level statement grammar or in a
    recovery/statement-start filter.

10. Treat experimental Swift features consistently in SwiftSyntax tests and fuzzer probes. The
    2026-10-07 run still reports `using` overaccepts such as:
    ```
    using Test
    using nonisolated
    using borrowing
    ```
    because SwiftSyntax/compiler reference parsing runs with the relevant experimental feature
    disabled while APUS grammar accepts the syntax. Decide whether test corpora should exclude
    disabled experimental samples by default, or whether the probe/test harness should enable the
    same experimental features for both references and APUS expectations. Do not solve this with
    ad hoc grammar churn for disabled feature syntax.

11. Reduce and fix small valid-looking underaccepts from the 2026-10-07 run that are not part of the
    `/)/` family. Good first candidates:
    ```
    struct Fuzz { open(set) var openProp = 0 }
    prefix operator =
    nonOptional
    !
    x
    ```
    Recheck each against `Parser.parse(source:).hasError` and `swiftc -parse` before editing; some
    fuzzer reductions in this bucket are malformed real-source fragments, but these three look small
    enough to be actionable.

12. Resolve residual ambiguities found by the 2026-10-07 run. Three artifacts survived reduction:
    ```
    typealias Z = A
    .C

    each
    {
    }

    fuzz() {
    _ = /x(()/
    }
    ```
    The first is a statement/member-type continuation ambiguity, the second is
    `postfixExpression` vs `packElementExpression`, and the third is a regex iteration extent
    ambiguity. Reduce/verify each independently; do not mix these with tree-shape frontier work.

13. Reduce tree-shape differences for generic/macro calls split by newlines or comments. The
    2026-10-07 run repeatedly produced SwiftSyntax `SequenceExpr` shapes where APUS commits to
    generic specialization or macro/function call, for example:
    ```
    A<() -> D>/*
    */()

    let a = #foo<Int>
    ()
    ```
    This may overlap with existing generic-specialization tree differences, but the newline/comment
    boundary makes this a narrower, reproducible family.

# Active TODO

This file is the canonical active TODO list for the project.
It holds actionable items only.
Mark a finished item **Done** (with the date) and leave it in place; put longer historical
explanations in design notes or commit messages.

Source of items 1–24: night run `SwiftSyntaxFuzzer/runs/worker-*/2026-10-09T23-08-37Z` (10 × 100,000
inputs). Its 940 artifacts are 844 unique reduced sources (601 overaccept, 153 underaccept, 85 tree
difference, 5 residual ambiguity). All 844 still reproduce with the probe of 2026-10-10 10:34. Each
example is a minimal form, checked with `swiftc -swift-version 6 -parse`, swift-syntax and the
probe. Counts are unique reduced artifacts, approximate where a bucket mixes causes.

## Overaccepts (swiftc and swift-syntax reject, APUS builds a tree)

1. **Done 2026-10-10.** One `accessorBlock` (accessor list or implicit getter) and one
   `observerBlock`, following swift-syntax `parseAccessorBlock` / `parsePatternBinding`. Fixed 99 of
   the replayed overaccepts plus 2 tree differences and 1 underaccept; no regressions. Left: 13
   artifacts like `{ get get {} }` and `{ get @inlinable set {} }`, which swiftc and swift-syntax
   reject for different, non-grammar reasons (swiftc requires accessor bodies outside protocols;
   swift-syntax uses same-line error recovery). Reject fixture `testInitAccessorsWithDefaultValues#1`
   is disabled: swiftc accepts an `init` accessor after `get`/`set`.
   Accessor blocks accept anything after an accessor (~130). `var i: Int {⏎get {⏎}⏎x⏎}`,
   `var i {⏎_read {⏎}⏎_i⏎}`, `var i: Int { get get {} }`, `var i: Int { get -> Int }`,
   `var x: Int { get get async }`, protocol `var x: Int { get ;}`, and the same in subscripts.
   Once a block starts with an accessor keyword, every item must be an accessor (swift-syntax
   `parseAccessorBlock`); only a block without one is an implicit getter
   (`var x: Int { read {} }` is valid).
2. **Done 2026-10-10.** Operator terminals now match nothing when their run contains a `*/` that
   does not open a comment (swift-syntax Cursor.swift `classifyOperatorToken`). Fixed 55 of the
   replayed overaccepts; no regressions. The regex example `_ = /[/*c*/)]/` has another cause and
   moved to #18.
   A `*/` outside a comment is accepted (~75). `*/x`, `a */ b`, `( (⏎*/) )`, `_ = /[/*c*/)]/`.
   swiftc: "unexpected end of block comment". An operator token must not contain `*/`, and a lone
   `*/` is an error.
3. **Done 2026-10-10.** `operatorDeclaration` now follows swiftc, which is stricter than
   swift-syntax `parseOperatorDeclaration`: only `infix` takes a precedence group, designated types
   (`: P, Q`, also a trailing comma) are an error, a postfix name cannot start with `!`/`?`, a name
   glued to `operator` cannot start with `!`/`?` (Cursor.swift `lexPostfixOptionalChain`), and a
   following `{…}` is an error. 34 swift-syntax fixtures that swiftc rejects are marked
   `compilerRejects`. The several-fixity-modifiers part moved to #25.
   Operator declarations (~95):
   - a trailing comma after the precedence group: `infix operator +++ : P,⏎let x = 1`, also inside
     `f {…}` (53);
   - several fixity modifiers: `prefix⏎infix operator &+&`, `postfix⏎postfix operator ^^*` (13);
   - a body: `infix operator +++⏎{}` inside a closure or `#if` (9);
   - names swiftc forbids: `prefix operator!!` (no space; `!` is not allowed in operator names),
     `postfix operator??` (8);
   - a precedence group on a prefix or postfix operator: `prefix operator +++** : A` (5).
4. **Done 2026-10-11.** A statement-start `init`, `actor A` or `macro m` is a declaration (swift-syntax
   `atStartOfDeclaration`): `initializerHead`, `actorIntroducer` and `macroIntroducer` are `statement`
   predicate targets. A bare `init(…)` call inside an initializer is rejected too: swiftc ParseDecl.cpp
   `isStartOfSwiftDecl` reads it as a call only to diagnose a missing `self.`, and the type checker
   always rejects it. This removed `initializerBodyMode` and merged `bodylessInitializerDeclaration`
   into `initializerDeclaration` (`codeBlock?`, as `parseInitializerDeclaration`). Four swift-syntax
   fixtures are marked `compilerRejects: "typecheck: …"`. Left: `actor⏎let x = 1` (`atStartOfActor`
   skips declaration keywords before the name); declarations in the wrong place are #26.
   `init`, `macro` and `actor` at statement start parse as expressions (~55). `init`, `f {⏎init⏎}`,
   `init? { () }`, `macro⏎m1`, `actor⏎A`. swift-syntax starts a declaration on these keywords (also
   with the name on the next line) and then reports the missing parts.
5. ~~Closure signature without `in` (25). `f {⏎() -> Y⏎}`, `f {⏎_ -> Y⏎}`, `f {⏎() -> Y -> Z⏎}`.
   swift-syntax commits to a closure signature when the body starts with one
   (`canParseClosureSignature`); APUS reads it as an expression statement.~~ ✓ 2026-10-10
6. **Done 2026-10-11.** Conflict marker fixtures are disabled wholesale
   (`ConflictMarkersTests.*`) instead of being modeled in the grammar. `x⏎>>>> ORIGINAL⏎<<<<⏎()`:
   a `<<<<<<<`, `>>>>>>>`, `<<<<` or `>>>>` marker at line start is a lexer error in swiftc and
   swift-syntax; APUS lexes it as an operator.
7. **Done 2026-10-11.** Three narrowings, each to swift-syntax's shape: `opaqueType`/`boxedProtocolType`
   take no second `some`/`any`; `anyTypeExpression` is a `prefixExpression` like `consume`/`copy` (same-line
   operand, not `(`/`[`/`.`/`{`), no longer a `primaryExpression`; `typeExpression` (collection elements)
   only starts with `(`, `@` or a type specifier. The array converter's full-span `any` workaround is
   gone. Left: `let x = any P {}` (swift-syntax accepts; swiftc semantic error); `any~Copyable` tree (#23).
   `any` and type expressions as statements (~35). `any any Q`, `any P {⏎}` (APUS: call with a
   trailing closure), `<any Copyable`, `[any⏎P & Copyable]()`, `_ = [P& ~Copyable]()`,
   `f {⏎[any Copyable~]()⏎}`.
   Analysis 2026-10-11 — three causes:
   - Types: `some`/`any` take a whole `type`, so `any any Q` and `some any P` parse. swift-syntax
     Types.swift `parseSimpleOrCompositionType` takes one `some`/`any`, then a simple type or composition.
   - Expressions: `boxedProtocolType` is a `primaryExpression`, so it takes postfixes (`any P {}`),
     sits under prefix operators (`<any Copyable`) and spans lines. swift-syntax Expressions.swift
     `parseSequenceExpressionElementPrefixIfPresent` makes it a sequence-element prefix with the
     `atContextualKeywordPrefixedSyntax` follower rule — the shape APUS already uses for `consume`/`copy`.
     Also fixes the trees of `any(x)` and `let x = any⏎P`.
   - Collection elements: `arrayLiteralItem = typeExpression = type` admits every type, so `[some P]`,
     `[any⏎P & Q]` and glued `[P& Copyable]` parse. Narrow `typeExpression` to the forms its comment
     names (specifier/attribute-prefixed and function types).
8. **Done 2026-10-11.** `@available` now mirrors swift-syntax
   `parseAvailabilityArgumentSpecList`: `introduced:`/`obsoleted:` take versions, `deprecated`
   optionally takes a version, `message:`/`renamed:` take simple strings, `unavailable` and
   `noasync` are bare tokens, and platform entries are plain identifier tokens rather than
   contextual keywords. Added rejects for `@available(*, introduced, nonmutating)`,
   `@available(iOS⏎: 10.12)`, `@available(*, deprecated, mutating: "x")`,
   `@available( consuming: 0)`, and `@available(message: "x", await: "y")`.
9. **Done 2026-10-11.** TypeExpr primaries are excluded as parenless trailing-closure callees by
   naming the existing `self`/`Any`/attributed/inline-array/function-type primary alternatives as
   `typePrimaryExpression` and adding it beside the existing bare-literal callee filter. This
   rejects `f(Int: @P M {})` and `_ = "a\(Int: @P M {})b"` without cloning the call-argument
   grammar.
10. **Done 2026-10-21.** Generic parameter names no longer reuse `typeName`, whose SE-0491
    module-selector alternative made `T::Equatable` one unconstrained parameter name. They now
    match swift-syntax `expectIdentifier(allowSelfOrCapitalSelfAsIdentifier: true)`: an identifier,
    `self`, or `Self`. This rejects `class C<T:: Equatable> {}` and
    `func f<RX:: Decodable>()` while preserving qualified constraint types such as
    `class C<T: Swift::Equatable> {}`.
11. **Done 2026-10-21.** Effect sequences now own trailing effect keywords after the first
    specifier, so an invalid order cannot split into a shorter declaration plus another statement.
    Declaration and function-type result arrows reject compiler-reserved misplaced effect words,
    while preserving compiler-valid contextual type names such as `reasync` and escaped `async`.
    The collection-only `(Int, await) -> Int` overaccept is rejected by a self-pruning
    `awaitTupleFunctionType` probe on `typeExpression`; genuine type contexts still accept it.
    Covers `func f() throws⏎async`, `func f⏎() -> await`, `func f() ->⏎async {}`, and
    `_ = [String: (Int, await) -> Int]()`.
12. **Done 2026-10-22.** Ordinary expression prefix operators now require their operand on the
    same line, rejecting `[P & ~⏎Copyable]` as well as the corresponding `-` and `!` forms.
    Suppressed types normally retain SwiftSyntax's structural rule that `~` may be separated from
    its type by a newline. After a same-line parameter modifier, however, both the compiler and
    SwiftSyntax require the operand to remain on the tilde's line; a two-way structural split on
    `parameterModifier` models that exception without predicates or flavors.
13. DONE 2026-10-11. `#if` followed by more tokens on its line (13). `#if FOO { init() }⏎#endif`,
    `#if FOO = /[abc/]⏎#endif` ("extra tokens following conditional compilation directive").
    Fixed by keeping directive conditions as expressions, with a small self-pruning probe so
    same-line trailing closures remain extra directive text. The regex example is covered by the
    existing plain-regex extent: `/[abc/` leaves `]` as same-line residue.
14. DONE 2026-10-11. Compound name on the next line (20). `x⏎(_:)`,
    `method⏎(_:⏎)`: the argument-label list must be glued to the name line; on a new line it is a
    tuple, and `(_:)` is not one. Fixed by adding the same no-newline boundary SwiftSyntax uses for
    `parseArgLabelList` to expression, member, and key-path compound names.
15. **Done 2026-10-22.** Extended regex literals use a custom consumer with distinct single-line
    and multiline modes. A newline immediately after the opening delimiter selects multiline mode,
    whose closing delimiter must start its own line (after indentation); mismatched pound counts and
    unterminated literals are rejected. Covers `_ = #/⏎?/#`, `_ = #/⏎abc/#`, and `do { #/\/#⏎}`.
16. DONE 2026-10-11. `=` with unbalanced spacing (6). `do {⏎=/0/ }`: "'=' must have consistent
    whitespace on both sides". The `@preempt` split of `=/` before the regex left `=` as a prefix
    operator; swift-syntax Cursor.swift `classifyOperatorToken` makes that piece `.equal`. Fixed with
    TSPL's reserved operators in the grammar, `operator = … nonArrowOperatorToken ---( "=" "?" )`
    (also catches `?/0/`), plus one engine fix: `---(…)` tests the text, without `@literalMunch`,
    which had hidden the excluded literal behind the longer `=/`. Moving the `@preempt` commit into
    the lexer was tried and dropped: it loses the slot context, so a left-bound `x=/0/` split too.
17. **Done 2026-10-22.** Attribute spelling and position now follows the compiler in three
    contexts: a qualified attribute name may have whitespace before its period but not after it;
    the declaration-only `@rethrows` spelling cannot be reused as a type attribute; and `@Self`
    is not accepted in switch-case attribute position. Covers
    `@_Concurrency. MainActor() struct I {}`, `extension Int: @rethrows Q {}`, and
    `switch x {⏎@Self case _:⏎}`.

## Underaccepts (swiftc and swift-syntax accept, APUS rejects)

18. **Done 2026-10-10.** Regex literals with an unbalanced `)` or `]` (~30). Added separate
    regex extent scanners for normal ambiguous slash positions, must-be-regex positions, and operator
    preemption. This accepts compiler-valid cases like `_ = (/)/`, `_ = /))/`, `_ = /)]/`, `_ = /[]]/`,
    `_ = /])/`, `_ = /),/`, `_ = /[\])/`, and preserves rejects such as `_ = /[/]/`, `_ = /[a/b]/`,
    `_ = /())/`, `_ = /a/*x*/b/`, and `_ = (^/)("/")`. Full Xcode test plan passed: 24,007 passed,
    1 skipped, 0 failed.
19. **Done 2026-10-22.** Bare operator references share one `operatorReference` production across
    tuples and argument lists, including module selection and the lexer-special `&`/`!` spellings.
    A tight prefix operator may also take compiler-remapped `await`. Covers `_ = (&)`, `f(&)`, `P&`,
    `(0, Swift::+)`, `??await`, and `\_`.
20. **Done 2026-10-22.** Conditions now reuse the ordinary expression grammar, including assignment;
    the duplicated condition-expression/infix family was removed. Binding-following restrictions
    remain localized in `conditionListAfterBinding`. Covers `if a = b {}`, `guard a = x else {}`,
    `if 42 = (⏎) {}`, `guard unsafe = a else {}`, and `if count = 1, let first {}`.
21. **Done 2026-10-22.** Binding and matching tuple patterns use the same EBNF list shape with an
    optional trailing comma. Covers `let (x, ) = ()`, `for (i, ) in x {}`, and `case (let a, ):`.
22. **Done 2026-10-22.** Name handling is split by syntactic context instead of widening the global
    identifier rule: argument labels cover closure parameters, `identifierOrSelf` serves declaration
    names, attribute declaration names have their own base category, and compiler-only type-name
    remapping stays in expression/inverse/boxed type productions. Bare closure expressions are valid
    top-level statements. Covers the listed keyword-name cases.

## Tree differences

23. **Done 2026-10-22.** Token kinds and shapes (85):
    - `if⏎_ = 42 {}`: a line break after `if` loses the condition (18);
    - a left-bound operator is `postfixOperator` in swift-syntax: `infix operator%%`,
      `let x: any P& Q`, `where T==Int` (14);
    - keywords used as names keep the `keyword` kind: `@_dynamicReplacement(for: subscript())`,
      `@_effects(escaping else)` (9);
    - type versus expression reading: `X< ~ Copyable>()`, `_ = any()`, `f {⏎any⏎Q⏎}`,
      `foo(nonisolated(nonsending) () -> Void)` (~15);
    - a following block taken as trailing closure or accessor block: `if .random() { } { }`,
      `f {⏎let foo⏎= 1⏎{ }⏎}` (6; the second example is **Done 2026-10-10**, with #1);
    - `switch s { case let copy x: break }`, `case let consume P:` (3);
    - regex versus operator: `_ = x/.../y`, `_ = .?.\foo`, `_ = /\()`, `Self -> /x/!`,
      `_ = "a\(if /x/ {})b"` (~7).

## Residual ambiguities

24. **Done 2026-10-22.** `f { @MainActor() in }`: `closureSignature` `[closureParameterClause "in"] | [attributes "in"]`
    (3; `@MainActor () in` with a space is fine). `yield {⏎}`: `statement`
    `[expression] | [yieldStatement]` (1). `init // c⏎()` twice inside `#if` in a class body:
    ambiguous iteration extent `[statementSeparator statement]` (1).

## Split from earlier items

25. **Done 2026-10-22.** Several fixity modifiers before `operator` (13, from #3). `prefix⏎infix operator &+&`,
    `postfix⏎postfix operator ^^*`: APUS reads the first word as an expression statement and the
    rest as a declaration. swiftc ("'infix' contradicts previous modifier", "duplicate modifier")
    and swift-syntax read all words as modifiers of one declaration (Declarations.swift
    `parseOperatorDeclIntroducer`). `prefix⏎operator +++` is valid. Fixed with one fixity-family
    introducer recognizer: repeated fixities commit to the operator
    declaration and are rejected together, while a single fixity followed by `operator` remains valid.
26. **Done 2026-10-22.** Declarations in the wrong context (~45 in the run). swiftc rejects at parse time what swift-syntax
    leaves to later stages: `init()` outside a type ("initializers may only be declared within a
    type"), `operator`/`precedencegroup` outside file scope, `subscript` and `static func` outside a
    type, `deinit` outside a class. All are swiftc `CurDeclContext` checks (ParseDecl.cpp). Implemented
    as three bounded context flavors (file, member, concrete-type body); ordinary code blocks clear
    them, and the SwiftSyntax recovery-only fixtures are centrally marked compiler-invalid.
27. DONE 2026-10-11. Dot operator before a regex (from #16). `let y = ./0/` is accepted (swiftc:
    "expected identifier after '.' expression") and `let y = ../0/` builds a different tree.
    swift-syntax Cursor.swift `lexOperatorIdentifier` runs the same regex scan for dot operators,
    splitting `../0/` into `..` and `/0/`; APUS's `dotOperator` has no `@preempt`, so it never splits.
    A matrix of 22 operators × 6 positions (132 cases) found this and `->/0/` to be the only gaps,
    both left over from #16's partial copy of one swift-syntax rule. Fixed structurally:
    `nonArrowOperatorToken` (the not-left-bound operator, which carries the `@preempt` split) now
    lexes dot operators too, as `lexOperatorIdentifier` does, so `operator = dotOperator` is gone;
    the reserved pieces are one named set copied from `classifyOperatorToken`,
    `reservedOperatorPiece = "=" | "?" | "." | "->"`, replacing #16's `---( "=" "?" )`. All 132 agree.

# Active TODO

This file is the canonical active TODO list.

## Fuzz campaign 2026-10-23

Source: `SwiftSyntaxFuzzer/runs/worker-*/2026-10-23T10-45-11Z` (10 workers, stopped at 466,406 inputs,
refreshed seeds and the 2026-10-09 interesting corpus). 228 artifacts are 190 distinct sources, all of
which still reproduce: 97 underaccepts, 49 overaccepts, 29 tree differences, 15 residual ambiguities.
Each example below was checked with `swiftc -swift-version 6 -parse`, swift-syntax and the probe.
Against the 2026-10-09 run the overaccept rate fell from 0.076% to 0.014%; the underaccept rate rose
from 0.016% to 0.6%, almost entirely through #5.

### Fuzzer

5. **Done 2026-10-23.** The probe now reports the exception as `compiler-recovery-reject`, decided on
   the swift-syntax tree as swiftc decides it: a code-block item starting with `init` whose nearest
   declaration context is an initializer (closures and other declarations end the search, `#if` does
   not). A type-check run was tried first and rejected: swiftc never type-checks inactive `#if` code or
   a closure passed to an unresolved callee, which hid 64 of the 80. All 80 artifacts reclassify; the
   17 genuine underaccepts stay. The fixed source left `frontier:flavor-scope`. The probe's unused
   type-check helper now passes `-sdk` (direct `swiftc` has no standard library otherwise).
   **Known type-checker exception reported as underaccept (80 of 97, plus 1,931 frontier inputs).**
   A statement-start `init` inside an initializer (`init() { init() }`, `init(rawValue: x)!`, a bare
   `init`, also under `#if`) is rejected on purpose (agreed 2026-10-11, swiftc ParseDecl.cpp
   `isStartOfSwiftDecl`; fixtures carry `compilerRejects: "typecheck: …"`). The runner compares with
   `swiftc -parse` only, so it counts every variant. Teach the runner the exception (or run the type
   checker for this shape), and stop `frontier:flavor-scope` from emitting the fixed source
   `struct Fuzz { init() { init() } }`: it was 0.4% of all inputs.
6. **Done 2026-10-23.** At file scope (also inside a file-scope `#if`, through the `fileScope` flavor)
   the expression statement is gated `>->( "{" )`; elsewhere a leading closure stays fine. The ` {`
   artifacts were not wrapper bugs: the reducer had deleted `let fuzzClosure =` from a valid wrapper,
   which kept the overaccept signal only while APUS accepted bare top-level closures. One test input
   (`keywordsAsNames`) was itself a top-level closure and now uses `_ = { … }`.
   **Top-level closure statements.** `{ }` and `{ x }` at file scope: swiftc rejects ("top-level
   statement cannot begin with a closure expression"); swift-syntax and APUS accept. Compiler wins, so
   this is an overaccept. It also matters for the fuzzer: many wrappers start with ` {`, which hides the
   real cause of an artifact behind this one. Fix the grammar, then check the wrappers.

### Overaccepts

7. **Done 2026-10-23.** Measured, swiftc's rule is broader than "a following accessor needs a body":
   ParseDecl.cpp `parseGetSet` makes a protocol's accessor list a bodyless requirement list (`get`,
   `set`, `borrow`, `mutate`; no implicit getter, no `_read`, no observers) and requires a body on
   every accessor elsewhere, also in protocol extensions. Now one `accessorIntroducer` serves
   `accessorDeclaration` and the implicit-getter predicate (swift-syntax `atStartOfGetSetAccessor`
   looks at the introducer, not the body), and a `protocolBody` flavor, set by `protocolDeclaration`
   like `concreteTypeBody`, picks body or requirement. Observers always need a body. `testAccessors#2`
   (603/604) is `compilerRejects`; swiftc-only rejects are in `FuzzHarvestTests.compilerOnlyRejects`.
   **Accessor lists with a missing body (~10).** `var x: Int { get get {} }`, `{ set set {} }`,
   `{ didSet didSet {} }`, `{ _read _modify {} }`, `{ get@inlinable set {} }`, `{ willSet get {} }`.
   swiftc: "expected '{' to start getter definition". An accessor without a body is valid only as the
   last item (protocol requirements); a following accessor on the same line needs the body. Left over
   from the first #1 (2026-10-10).
8. **Partly done 2026-10-23. Doubled or misplaced type specifiers.** The inverse-type spacing,
   composition `&`, empty `@convention()`, `any ~ ~Copyable` and repeated-attribute cases now agree.
   `(each each B)` and `(repeat repeat A)` are actually accepted by both references and remain legal.
   Still open: `<@convention(c) () ()` is overaccepted as a prefix expression plus calls.
   **Plan:** Diagnose the complete expression derivation before editing. This may be an erroneous
   transition between otherwise valid expression productions rather than a type-grammar problem;
   fix that transition without further restricting valid attributed types.
   **Regression found 2026-10-24 (artifact replay).** A glued `~` after `any` underaccepts:
   `_ = (any~Copyable).self`, `let a: [any~Copyable]`, `fuzz() {⏎[any~Copyable]()⏎}` (was a tree
   difference). `suppressedType` admits `>s< "~"` only after `( [ { , ; : as is ! ?`, and `any` is not
   among them; `any ~Copyable` with a space matches. Real code: `func f(_ x: borrowing any~Copyable)`.
9. **Partly done 2026-10-23. Specifier words before declarations.** `inout f() {}`,
   `inout await(…)` and `inout b/` now agree. Still open: `nonmutating⏎prefix operator *!*`,
   `actor⏎public struct S {}` and `sending enum E {}`.
   swiftc rejects each
   ("consecutive statements on a line", "unexpected attribute 'nonmutating' in operator declaration").
   **Plan:** Study the three cases together as declaration commitment across newlines. Check parser
   modes and their application before adding grammar guards; prefer one structural correction over
   keyword-specific exclusions. Discuss first only if the clean fix changes parser-mode semantics.
10. **Attributed call with trailing closure inside interpolation (2).** `_ = "a\(@objc f() {})b"`,
    `"a\(@available(macOS 10.15, *) borrowing f() {})b"`. swiftc: "expected expression in list of
    expressions".
11. **Done 2026-10-23. Conflict markers (6).** Inputs containing standard or legacy conflict-marker
    lines are classified `skipped-conflict-marker` by the runner and never compared with the grammar.
12. **Partly done 2026-10-23. Smaller overaccepts.** The malformed `#if true@unknown`, spaced
    enum-case member, freestanding-attribute and unterminated extended-regex examples now reject.
    Still open: bodiless-function/`async()` and `#if FOO⏎()⏎!/^/⏎#endif`.
    **Plan:** Treat bodiless-function/`async()` as a focused declaration-boundary problem. Handle the
    `#if` case last and trace its complete derivation plus SwiftSyntax item classification before
    editing; this area is regression-prone and should receive a structural fix, not another local
    annotation.

### Underaccepts (the 17 outside #5)

13. **Partly done 2026-10-23. Expression patterns in bindings.** `if let ([]) = x {}` and
    `if let nil = y {}` now match exactly. Still open: `switch x { case (let y)&: () }`.
    **Plan:** Probe the operator-pattern shape and determine whether the mismatch is confined to the
    converter or needs a grammar route. This should be focused implementation work unless it exposes
    a missing general representation for operator patterns.
    **Closed 2026-10-24, parse-only (see "Parse-only retrospective").** `case (let y)&` never compiles,
    even with a `postfix operator &` declared ("'let' binding pattern cannot appear in an expression").
    `if let ([]) = x` and `if let nil = y` never compile either; their grammar route
    (`optionalBindingMatchPattern`) was removed and APUS now rejects them (`parseOnlyRejects`).
14. **Done 2026-10-23. Attribute arguments (4).** `@available(*, deprecated)⏎precedencegroup P {}`,
    `@transpose(of: -, wrt: (0, ))`, and a space or comment before a declaration name's argument list:
    `@_implements(P, f (x:))`, `f/*c*/(x:y:)` (`declNameArguments` has `>s<`).
15. **Partly done 2026-10-23. Expressions.** Newline `if` operands, `Any { }`, the forced-regex
    extent `_ = /})/`, and lowercase `_ = (self< >).self` now have grammar/converter fixes.
    Still open: `f { _ -> Swift::init }` and the U+FE0F variation-selector case.
    **Plan:** Treat these as three independent focused fixes, testing after each: generic parsing for
    `self< >`, module-qualified `init` in a closure result, then scanner handling of the variation
    selector. Preserve longest-token correctness in the scanner case.
    **Continuation note:** SwiftSyntax parses `f { _ -> Swift::init }` with no closure signature: its
    body is a `SequenceExpr` containing `_`, `->`, and `Swift::init`. APUS's
    `closureSignatureStart` commits the same tokens as a missing-`in` signature. An attempted
    `@cannotParse(moduleSelector "init")` helper was reverted because `@cannotParse` prunes oracle
    choices, not acceptance yields. The eventual fix must structurally narrow declaration
    commitment without excluding valid module-qualified return types. The rebuilt standalone probe
    matches both `self< >` and `Self< >` exactly, with no converter diagnostics or ambiguity.
    **Variation-selector continuation:** Direct compiler checks confirm that an orphan U+FE0F or
    U+E0100 is accepted even through type checking as an identifier (`enum ️ {}`), while U+0300 is
    rejected with “an identifier cannot begin with this character”. An operator head still absorbs
    U+FE0F into the longer operator token (`⚽️`). Both attempted implementations were reverted: adding
    the ranges to RegexBuilder's identifier head, and routing `identifier` through a custom scalar
    scanner, compiled but left the focused probes underaccepted. The likely boundary problem is
    earlier trivia/grapheme consumption: an orphan default-ignorable selector can be attached to the
    preceding space before identifier matching. Verify that boundary before changing identifier
    classification, and preserve operator longest-token behavior.
    **Variation selector done 2026-10-23.** Confirmed: `" \u{FE0F}"` (also `" \u{200D}"`,
    `" \u{E0100}"`) is one `Character` that the grapheme-mode whitespace class does not match, so no
    token could start there; after a newline (a cluster break) it already parsed. The identifier
    classes were already right. `whitespace` is now a scalar-semantics `@builder`; `⚽️`, `\u{0300}` and
    comment controls unchanged. The same grapheme mistake hid a CRLF bug: `GapFacts(classifying:)`
    compared `Character`s with `"\n"`/`"\r"`, so `let x = 1\r\nlet y = 2` lost its line break and
    underaccepted (also before this change); it now classifies per scalar. Suite green; probe
    rechecked.
    **`f { _ -> Swift::init }`: not fixed, by decision 2026-10-23.** swiftc parses it only because its
    closure-signature lookahead (ParseType.cpp `canParseTypeIdentifier`: after `::` only an identifier,
    `Self` or `Any`) fails and the body falls back to an expression; an arrow used as an expression
    statement never type-checks, so this source can never compile (same category as #5). Matching it
    needs a context-dependent type grammar; a `closureResult` flavor over ~35 type productions plus an
    engine FOLLOW change was tried and reverted as disproportionate. Found on the way and fixed: a
    module-qualified type name took the raw `identifier` token, so `Swift::`Int`` and `Swift::$x`
    underaccepted; `typeName` now takes `moduleSelector ( identifierToken | lexerClassifiedKeyword )`.
    **Revised 2026-10-24 (parse-only retrospective).** The `Any { }` and `_ = /})/` fixes were
    reverted: neither can compile ('Any' cannot be constructed; a regex `)` that closes nothing).
    APUS rejects both (`parseOnlyRejects`).
16. **Partly done 2026-10-23. Key paths.** `_ = \Foo..foo` now exits the key path before the
    dot operator. Still open: `_ = \ ./*⏎*/[]`.
    **Plan:** Compare the exact compiler and SwiftSyntax token/trivia boundary, then express where the
    key-path island ends structurally. Avoid a source-specific lookahead or another preference
    annotation if the boundary can be represented by the existing whitespace constructions.
    **Closed 2026-10-24, parse-only.** Only the comment-with-newline spelling fails: `\ .[0]` and
    `\ ./*c*/[0]` compile and APUS accepts them, while `\ ./*⏎*/[0]` crashes swiftc's type checker
    ("failed to produce diagnostic"), so no program compiles it.

### Tree differences

17. **Done 2026-10-23. Operator token kinds by boundness (~6).** swift-syntax picks the kind from boundness
    (Cursor.swift `classifyOperatorToken`): `infix operator+++` and `prefix operator++` name a
    `postfixOperator`, `let v: Copyable& P` has a `postfixOperator("&")`. The converter emits
    `binaryOperator`. Derive the kind from the token's boundness in one place.
18. **Done 2026-10-23. `inout` binding declarations (2).** `inout mid = "pete"`, `inout _ = ()()`: swift-syntax builds a
    `VariableDecl` with an `inout` introducer; APUS builds a type expression. swiftc accepts.
    **Reverted 2026-10-24, parse-only.** `inout` bindings never compile ("'inout' may only be used on
    parameters"). The `"inout" patternInitializerList` declaration and the `inout` value-binding
    pattern were removed; these sources are now plain tree differences.
    **Partly restored 2026-10-24.** Removing the declaration alternative regressed three #9 overaccepts
    (`inout b/`, `inout await(…)`, `inout f() {}`): swiftc commits `inout x` to a binding declaration and
    rejects what follows, so the alternative models swiftc's parse, not only an acceptance. It is back;
    the value-binding pattern stays removed (`case inout y?` is parse-only, no overaccept depends on it).
    Lesson: removing a parse-only rule is safe only if no rejection depends on it; replay overaccepts.
19. **Done 2026-10-23. `@_effects` arguments (3).** `@_effects(escaping throw)`: `throw` is a keyword token in
    swift-syntax, an identifier in APUS.
20. **Remaining tree differences (~18).** `@_dynamicReplacement(for: subscript())`,
    `_ = "a\(if /x/ {})b"`, `_ { (self, ) in }`, `(self<A>.B & G).self`, `case let consume ParentKlass`,
    `..\foo`, `_ -> /[]/`. Triage one by one.
    **Plan:** Split this bucket into individual TODOs after probing every example. Classify each as a
    converter-only mismatch, grammar mismatch, or residual ambiguity before changing code; do not
    treat the examples as one grammar problem.
    **Re-triaged 2026-10-24 (type-checked in a real context).** Closed, parse-only:
    `"a\(if /x/ {})b"` (`if` is never allowed in an interpolation, with or without `else`),
    `case let consume ParentKlass`, `f { _ -> /[]/ }`. `(self<A>.B & G).self` already matches. Still
    open, all compile: `f { (self, ) in }`, `..\foo` (with a custom prefix `..`), and
    `@_dynamicReplacement(for: subscript())` on a subscript.

### Residual ambiguities

21. **Done 2026-10-23. Type annotation, then a member on the next line (8).** `let t: X⏎.Type`, `let t: X⏎.Self`,
    `let _: P⏎. self`, `let m: Int⏎.Swift::magnitude`: the `.member` can continue the type or start a
    new statement. Decide with swift-syntax's rule for a leading `.` after a type.
22. **Done 2026-10-23. `if _ = 42 {}` (4).** Removed the redundant
    `missingIntroducerWildcardCondition`; the ordinary expression already produces the exact tree.
23. **Done 2026-10-23. Smaller ambiguities (3).** Prefer the closure parameter-clause reading of
    `f {⏎@Sendable() in }`; greedy type annotations also resolve the enum `description` iteration
    extent. `@convention(thin)⏎(…)` already matched without residual ambiguity.

## Re-analysis of the leftovers (2026-10-24)

Every case re-probed, measured against swiftc with its neighbours, parse-only cases excluded. #10 already
matches. Each proposal is one local edit.
**Done 2026-10-24: R1–R9, U1, C1–C3** (suite green after each group). Deviations from the proposals:
R4 is a new predicate-only `actorDeclarationStart` (the real `actorIntroducer` keeps `identifierToken`);
R8 sits in `functionHead` (a guard group inside `functionName` broke the converter's name text); R9
replaces the `observerBlock` predicate on `trailingClosures` with `observerBlockStart` (start only, like
swift-syntax). Found on the way, not done: `reasync` as an effect (`func f(…) reasync {}`) is a parse
error in swiftc too, but 11 accept fixtures use it. Still open: R10.

Overaccepts (swiftc rejects at parse):

- **R1 (#8).** An attributed type is never the operand of a prefix operator: `<@convention(c) () ()`,
  `-@convention(c) () -> Void` and `!@Sendable () -> Void` are rejected; `try @Sendable () -> Void` and
  `[@convention(c) () -> Void]()` are fine. Proposal: `prefixOperator >->( "@" )` in `prefixExpression`.
- **R2 (#8).** A doubled pack specifier is rejected in every position (`each each B`, `(each each B)`,
  `(repeat repeat A)`), contrary to the earlier note. Proposal: `"each" >->( "each" ) type` and
  `"repeat" >->( "repeat" ) type`.
- **R3 (#8).** A glued `~` after a parameter modifier is rejected (`borrowing~Copyable`; spaced is fine).
  Proposal: `<s>` before `"~"` in the `parameterModifier "~" >n< simpleType` alternate of `type`.
- **R4 (#9).** `actor` commits to an actor declaration across a newline whatever word follows (`actor⏎S {}`
  is a declaration, `actor⏎foo()` is "expected '{' in actor", `actor⏎struct S {}` and `actor⏎public struct
  S {}` reject). Proposal: `actorName` in the `actorIntroducer` predicate takes the raw `identifier`
  (keywords included).
- **R5 (#9).** A modifier before an operator declaration commits to it (`nonmutating⏎prefix operator *!*`:
  "unexpected attribute 'nonmutating' in operator declaration"; `nonmutating⏎func`/`⏎foo()` already
  match). Proposal: generalise `invalidOperatorDeclarationStart` to `declarationModifier
  { declarationModifier } operatorFixity "operator"` (fixities are modifiers).
- **R6 (#9).** `sending`, `reasync` and `__setter_access` are not declaration modifiers for swiftc
  (`sending enum E {}`, `reasync func f() {}`: "consecutive statements"; `__setter_access` only
  swift-syntax accepts). Proposal: delete them from `declarationModifier`. (`infix func` and `async func`
  are also parse errors, but `prefix func` and `async let` are valid; not worth position rules.)
- **R7 (#12).** After a function signature a following `async` always belongs to it: `-> Int⏎async {}`
  ("'async' may only occur before '->'"), `()⏎async()`, `()⏎async let x = 1`; after a `where` clause it is
  a new statement. Proposal: `>->( "async" )` at the end of `functionSignature`.
- **R8 (#12).** A `?`/`!` glued to `func` is only that character (`func?+=(…)`, `func!=(…)`; spaced and
  `func+(` are fine), the rule `declaredOperator` already models. Proposal: `( <s> | >->( optionalMark
  forceMark ) )` before the operator alternates of `functionName`.
- **R9 (new).** A brace that starts with `didSet`/`willSet` is never a trailing closure (`f { didSet }`,
  `if f { willSet } {}`, `for x in filter { didSet > 4 } { _ = x }`, `let v = f { didSet }`; `get`/`set`
  are fine). swift-syntax `atValidTrailingClosure` / `atStartOfGetSetAccessor`. Proposal:
  `@cannotParse` of `"{" ( "didSet" | "willSet" )` on `trailingClosure`.
- **R10 (#12, deferred).** `()⏎/^/`, `f()⏎!/^/`, `[1]⏎!/^/`: after a regex-blocking token, a line-start
  `/` whose body is only operator characters lexes as an operator (`f()⏎/x/` is a regex). Regex lexer
  territory: read swift-syntax `tryScanOperatorAsRegexLiteral` before touching it.

Underaccept:

- **U1 (#8 regression).** A glued `~` after `any`/`some` underaccepts (`borrowing any~Copyable`,
  `consuming some~Copyable`). Proposal: add `"any" "some"` to the `suppressedType` lookbehind.

Tree differences (#20, all converter-only):

- **C1.** A closure parameter's trailing comma is dropped: `f { (self, ) in }`.
- **C2.** `@_dynamicReplacement(for: subscript())`: `subscript` must be a keyword token.
- **C3.** A dot-led prefix operator before a key path disappears: `_ = ..\Foo.x`, `_ = ...\Foo.x`
  (`!\Foo.x` and `..x` are fine).

## Parse-only retrospective (2026-10-24)

Rule: before changing the grammar for a fuzz sample, type-check it with its names declared. If no
program can compile it, it is parse-only, and the grammar changes only when the change also
simplifies it. Overaccepts are unaffected: if `swiftc -parse` rejects, APUS rejects.

Of the 198 accepted fuzz fixtures, about 24 can never compile. Most of them are accepted as a side
effect of a generalisation that keeps the grammar simpler (`#if` conditions are expressions, generic
constraints are any type), and stay. Removed, because they existed only for parse-only code:

- `( selfType | anyType ) trailingClosures` → `selfType trailingClosures` (`Any { }`).
- `optionalBindingMatchPattern` (`if let nil = y`, `if let ([]) = x`).
- `"inout" patternInitializerList` and the `inout` value-binding pattern (#18).
- The `operatorName` token (`infix operator ->`, "cannot declare a custom '->' operator").
- `forcedRegexLiteralToken` and `allowUnbalancedClosers` in `PlainRegexLiteral`: they only admitted a
  regex with a `)` that closes nothing. `plainRegularExpressionLiteral` is one line.

`parseOnlyRejects` (SwiftSyntaxTests.swift) records these decisions. `extension S where T: _Class {}`
is `compilerRejects:`: swiftc allows layout constraints only inside `@_specialize`; splitting the
where clause for it is not worth it (agreed).

Next: the probe should classify parse-only underaccepts and tree differences itself, after fuzzing
and before the condensing into TODO items.

## Verification artifacts

- `SwiftSyntaxFuzzer/crawls/2026-10-22T2215-top100/summary.txt`
- `SwiftSyntaxFuzzer/crawls/2026-10-22T2215-top100/results.jsonl`
- `SwiftSyntaxFuzzer/runs/worker-*/2026-10-23T10-45-11Z/artifacts/`

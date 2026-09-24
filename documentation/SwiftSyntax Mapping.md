# APUS Swift Grammar → SwiftSyntax Mapping

This document maps nonterminals/terminals in `Swift.apus` to their SwiftSyntax
node types, and describes the incremental plan for building an AST converter.

## Architecture

```
Swift source text
  ├─→ SwiftParser.Parser.parse()       → SwiftSyntax tree (reference)
  └─→ Scanner → MessageParser → Oracle
                                   ↓
                        BSR yields on GrammarNodes
                            ╱               ╲
               DerivationBuilder         SwiftSyntaxGenerator
               (ParseTreeNode trees)     (SwiftSyntax trees)
               for diagram rendering     for comparison with reference
               (Graphviz .gv)            (memberwise inits)
```

Key components:
- `DerivationBuilder` (DerivationBuilder.swift) — walks BSR yields on
  GrammarNodes, produces `ParseTreeNode` trees for diagram rendering. Two modes:
  - `buildAllTrees()` — enumerates all derivations (ambiguous grammars)
  - `buildAST()` — single deterministic tree (after Oracle disambiguation),
    reports residual ambiguity diagnostics
- `SwiftSyntaxGenerator` (GenerateSwiftSyntaxAST.swift) — walks BSR yields
  directly on GrammarNodes, constructs SwiftSyntax trees using memberwise inits.
  Completely decoupled from DerivationBuilder. Assumes all ambiguity resolved.
- `ParseTreeNode` — tree node used by diagram rendering only.

### Operator folding

SwiftParser produces flat `SequenceExprSyntax` nodes — it does NOT fold operators
by precedence at parse time. `OperatorTable.foldAll()` (SwiftOperators) is a
separate post-parse step that restructures into `InfixOperatorExprSyntax`.

Advent's grammar also has no operator precedence — `infixExpressions` is a flat
right-recursive list at the same nonterminal level for all operators.
`SwiftSyntaxGenerator` flattens this right recursion into a flat `ExprListSyntax`,
matching SwiftParser's unfolded output exactly. No precedence logic needed.

## Construction Approach

Use **memberwise initializers** on SwiftSyntax types, not result builders or
string interpolation. Builders are for hand-writing known structure; memberwise
inits are for programmatic tree-to-tree conversion.

```swift
// Example: "let x = 42"
VariableDeclSyntax(
    bindingSpecifier: .keyword(.let),
    bindings: PatternBindingListSyntax([
        PatternBindingSyntax(
            pattern: IdentifierPatternSyntax(identifier: .identifier("x")),
            initializer: InitializerClauseSyntax(
                equal: .equalToken(),
                value: IntegerLiteralExprSyntax(literal: .integerLiteral("42"))
            )
        )
    ])
)
```

## Incremental Phases

### Phase 1 — Literals & Simple Declarations ✅ (2026-09-02)
`let x = 42`, `let s = "hello"`, `var b = true`, `let n: Int? = nil`

Pinned by `Phase1TreeTests` in `AdventTests/SwiftSyntaxTests.swift` — 17 sources
covering every row of the table below, all matching swift-syntax exactly. Unlike
the extracted suites, where `trees match` is aspirational, a red row here is a
regression. Two generator bugs were fixed to get there:

- **Overlapping commits concatenated.** `collectTerminalText` walked every commit
  in the span, but the commit log holds terminals from DEAD derivations too: on
  `1.5` the scanner commits the float `1.5` at the `1` *and* `.5` at the `.`, so
  the literal read `1.5.5`. It now advances a cursor past each commit's content
  end and skips commits that run past the span end.
- **`optionalType` looked for the wrong child.** The rule is
  `optionalType = simpleType >s< optionalMark`, not `type "?"`, so `Int?` yielded
  `MissingType`. `convertType` now also dispatches on `simpleType` (its alternates
  are named identically to `type`'s).

| APUS nonterminal | SwiftSyntax type |
|---|---|
| `constantDeclaration` | `VariableDeclSyntax` (.let) |
| `variableDeclaration` | `VariableDeclSyntax` (.var) |
| `patternInitializerList` | `PatternBindingListSyntax` |
| `patternInitializer` | `PatternBindingSyntax` |
| `initializer` | `InitializerClauseSyntax` |
| `identifierPattern` | `IdentifierPatternSyntax` |
| `typeAnnotation` | `TypeAnnotationSyntax` |
| `typeIdentifier` | `IdentifierTypeSyntax` |
| `integerLiteral` | `IntegerLiteralExprSyntax` |
| `booleanLiteral` | `BooleanLiteralExprSyntax` |
| `nilLiteral` | `NilLiteralExprSyntax` |
| `stringLiteral` | `StringLiteralExprSyntax` |

### Phase 2 — Binary Expressions (flat sequences, no folding)
`1 + 2 * 3`, `x == 0 ? "zero" : "nonzero"`, `value as? Int`

**Hidden structural divergence — Advent NESTS where swift FLATTENS.** The "flatten the right
recursion" note above is only true of `infixExpressions = infixExpression infixExpressions?`.
Two `infixExpression` alternates take a full `expression` on the right, not a `prefixExpression`
(`Swift.apus:959-960`):

```
infixExpression = assignmentOperator expression .
infixExpression = conditionalOperator expression .
```

So for `a = b + c` Advent's tree puts `b + c` inside a NESTED `expression` under the `=`, whereas
swift-syntax's `SequenceExpr` is one flat list — `[a, AssignmentExpr(=), b, BinaryOperator(+), c]`.
A faithful converter must SPLICE the nested expression's elements into the parent sequence rather
than convert it as a sub-expression. `flattenInfixExpression` does neither today: it handles only
`infixOperator` / `conditionalOperator` / `typeCastingOperator` / `prefixExpression`, so the
assignment RHS and the ternary false-branch are dropped entirely.

**RESOLVED 2026-09-03.** `flattenExpression` splices: `convertExpression` now builds a flat element
list and only wraps in `SequenceExpr` when there is more than one element, and the
`assignmentOperator expression` / `conditionalOperator expression` alternates splice the nested
expression's elements into the parent list. `a = b + c` → `[a, AssignmentExpr, b, BinaryOperator, c]`.

My pre-implementation worry about the ternary was WRONG and is recorded here so it isn't repeated:
swift-syntax's `UnresolvedTernaryExpr` carries `? thenExpression :` as ONE element sitting between
the condition and the false-branch, which lines up exactly with
`conditionalOperator = <s> "?" expression ":"` holding the then-branch inside the operator node.
No restructuring was needed. (`as?`/`as!` did need a fix — the mark belongs on `UnresolvedAsExpr`
as `questionOrExclamationMark`, not as a separate element.)

| APUS nonterminal | SwiftSyntax type | Notes |
|---|---|---|
| `expression` + `infixExpressions` | `SequenceExprSyntax` | flatten right recursion to flat ExprList |
| `infixOperator` | `BinaryOperatorExprSyntax` | element in flat sequence |
| `conditionalOperator` | `UnresolvedTernaryExprSyntax` | element in flat sequence |
| `typeCastingOperator` (as) | `UnresolvedAsExprSyntax` + `TypeExprSyntax` | two elements in flat sequence |
| `typeCastingOperator` (is) | `UnresolvedIsExprSyntax` + `TypeExprSyntax` | two elements in flat sequence |
| `prefixExpression` (with op) | `PrefixOperatorExprSyntax` | |
| `postfixExpression` | various | `ForceUnwrapExprSyntax`, `OptionalChainingExprSyntax`, etc. |

### Phase 3 — Functions, Calls, Control Flow
`func f(x: Int) -> Int { ... }`, `f(x: 42)`, `if`/`for`/`while`/`switch`

| APUS nonterminal | SwiftSyntax type |
|---|---|
| `functionDeclaration` | `FunctionDeclSyntax` |
| `parameterClause` | `FunctionParameterClauseSyntax` |
| `parameter` | `FunctionParameterSyntax` |
| `functionResult` | `ReturnClauseSyntax` |
| `functionCallExpression` | `FunctionCallExprSyntax` |
| `functionCallArgument` | `LabeledExprSyntax` |
| `trailingClosures` | `MultipleTrailingClosureElementListSyntax` |
| `closureExpression` | `ClosureExprSyntax` |
| `forInStatement` | `ForStmtSyntax` |
| `whileStatement` | `WhileStmtSyntax` |
| `repeatWhileStatement` | `RepeatStmtSyntax` |
| `ifStatement` / `ifExpression` | `IfExprSyntax` |
| `guardStatement` | `GuardStmtSyntax` |
| `switchStatement` / `switchExpression` | `SwitchExprSyntax` |
| `returnStatement` | `ReturnStmtSyntax` |
| `breakStatement` | `BreakStmtSyntax` |
| `throwStatement` | `ThrowStmtSyntax` |
| `deferStatement` | `DeferStmtSyntax` |
| `doStatement` | `DoStmtSyntax` |

### Phase 4 — Type Declarations, Generics, Patterns
`struct`, `class`, `enum`, `protocol`, generics, pattern matching

| APUS nonterminal | SwiftSyntax type |
|---|---|
| `structDeclaration` | `StructDeclSyntax` |
| `classDeclaration` | `ClassDeclSyntax` |
| `enumDeclaration` | `EnumDeclSyntax` |
| `actorDeclaration` | `ActorDeclSyntax` |
| `protocolDeclaration` | `ProtocolDeclSyntax` |
| `extensionDeclaration` | `ExtensionDeclSyntax` |
| `genericParameterClause` | `GenericParameterClauseSyntax` |
| `genericWhereClause` | `GenericWhereClauseSyntax` |
| `typeInheritanceClause` | `InheritanceClauseSyntax` |

## When to reshape the grammar vs. reshape in the converter

Two cases from Sep 3 2026 that look alike and are not. The question is never "does the grammar
mirror the AST" — a CFG has no obligation to. It is "does the grammar spell the same construct two
different ways for no reason".

**Infix nesting — leave the grammar alone, splice in the converter.** `infixExpression =
assignmentOperator expression` nests the RHS, while swift-syntax emits one flat `SequenceExpr`.
These are genuinely DIFFERENT representations, not the same tree with a different associativity: a
CFG cannot produce swift's flat list without losing the structure it needs. The converter splices
(`flattenExpression`). Rewriting the grammar here would be contorting it to serve a consumer.

**Dotted type names — reshape the GRAMMAR.** `typeIdentifier` was right-recursive
(`typeName genericArgs? "." typeIdentifier`), copied verbatim from TSPL's book grammar, while
`explicitMemberExpression` on the expression side was already LEFT-recursive
(`postfixExpression "." softIdentifier`). Same construct — dotted access — spelled two opposite ways
inside one grammar, and only the type side then needed a collect-the-chain-then-fold-left dance in
the converter. Both spellings describe the same language and the same tree modulo associativity, so
the choice was free; TSPL's shape is not binding because GLL handles left recursion natively.

Changed to left-recursive. Measured: label set IDENTICAL (1081), accepts 0, ambiguity 0, no
wrongly-accepted rejects, wall time unchanged (63.9s vs 63.8s). The converter became direct
recursion — the recursive child simply IS the base, matching `MemberType`.

Rule of thumb: reshape the grammar when it removes an internal inconsistency at zero cost; reshape
in the converter when the two representations genuinely differ.

## Full Nonterminal → SwiftSyntax Mapping

### Declarations

| APUS | SwiftSyntax | Notes |
|---|---|---|
| `topLevelDeclaration` | `SourceFileSyntax` | children: `CodeBlockItemListSyntax` |
| `codeBlock` | `CodeBlockSyntax` | |
| `statements` | `CodeBlockItemListSyntax` | |
| `importDeclaration` | `ImportDeclSyntax` | |
| `constantDeclaration` | `VariableDeclSyntax` | `bindingSpecifier: .keyword(.let)` |
| `variableDeclaration` | `VariableDeclSyntax` | `bindingSpecifier: .keyword(.var)` |
| `functionDeclaration` | `FunctionDeclSyntax` | |
| `enumDeclaration` | `EnumDeclSyntax` | union + raw-value both map here |
| `structDeclaration` | `StructDeclSyntax` | |
| `classDeclaration` | `ClassDeclSyntax` | |
| `actorDeclaration` | `ActorDeclSyntax` | |
| `protocolDeclaration` | `ProtocolDeclSyntax` | |
| `extensionDeclaration` | `ExtensionDeclSyntax` | |
| `initializerDeclaration` | `InitializerDeclSyntax` | |
| `deinitializerDeclaration` | `DeinitializerDeclSyntax` | |
| `subscriptDeclaration` | `SubscriptDeclSyntax` | |
| `typealiasDeclaration` | `TypeAliasDeclSyntax` | |
| `operatorDeclaration` | `OperatorDeclSyntax` | |
| `precedenceGroupDeclaration` | `PrecedenceGroupDeclSyntax` | |
| `macroDeclaration` | `MacroDeclSyntax` | |

### Expressions

| APUS | SwiftSyntax | Notes |
|---|---|---|
| `expression` | `ExprSyntax` (protocol) | |
| `prefixExpression` | `PrefixOperatorExprSyntax` | |
| `infixExpression` | `SequenceExprSyntax` → fold → `InfixOperatorExprSyntax` | |
| `assignmentOperator` | `AssignmentExprSyntax` | |
| `conditionalOperator` | `TernaryExprSyntax` | |
| `typeCastingOperator` (as) | `AsExprSyntax` | |
| `typeCastingOperator` (is) | `IsExprSyntax` | |
| `tryOperator` | `TryExprSyntax` | |
| `awaitOperator` | `AwaitExprSyntax` | |
| `inOutExpression` | `InOutExprSyntax` | |
| `integerLiteral` | `IntegerLiteralExprSyntax` | |
| `decimalFloatingPointLiteral` | `FloatLiteralExprSyntax` | |huh?
| `stringLiteral` | `StringLiteralExprSyntax` | |
| `booleanLiteral` | `BooleanLiteralExprSyntax` | |
| `nilLiteral` | `NilLiteralExprSyntax` | |
| `regularExpressionLiteral` | `RegexLiteralExprSyntax` | |
| `arrayLiteral` | `ArrayExprSyntax` | |
| `dictionaryLiteral` | `DictionaryExprSyntax` | |
| `closureExpression` | `ClosureExprSyntax` | |
| `functionCallExpression` | `FunctionCallExprSyntax` | |
| `subscriptExpression` | `SubscriptCallExprSyntax` | |
| `tupleExpression` / `parenthesizedExpression` | `TupleExprSyntax` | |
| `selfExpression` | `DeclReferenceExprSyntax` | name = "self" |
| `superclassExpression` | `SuperExprSyntax` | |
| `ifExpression` | `IfExprSyntax` | |
| `switchExpression` | `SwitchExprSyntax` | |
| `keyPathExpression` | `KeyPathExprSyntax` | |
| `explicitMemberExpression` | `MemberAccessExprSyntax` | |
| `implicitMemberExpression` | `MemberAccessExprSyntax` | base = nil |
| `forcedValueExpression` | `ForceUnwrapExprSyntax` | |
| `optionalChainingExpression` | `OptionalChainingExprSyntax` | |
| `wildcardExpression` | `DiscardAssignmentExprSyntax` | |
| `macroExpansionExpression` | `MacroExpansionExprSyntax` | or `MacroExpansionDeclSyntax` |

### Statements

| APUS | SwiftSyntax | Notes |
|---|---|---|
| `forInStatement` | `ForStmtSyntax` | |
| `whileStatement` | `WhileStmtSyntax` | |
| `repeatWhileStatement` | `RepeatStmtSyntax` | |
| `ifStatement` | `IfExprSyntax` | SwiftSyntax treats as expr |
| `guardStatement` | `GuardStmtSyntax` | |
| `switchStatement` | `SwitchExprSyntax` | SwiftSyntax treats as expr |
| `breakStatement` | `BreakStmtSyntax` | |
| `continueStatement` | `ContinueStmtSyntax` | |
| `fallthroughStatement` | `FallThroughStmtSyntax` | |
| `returnStatement` | `ReturnStmtSyntax` | |
| `throwStatement` | `ThrowStmtSyntax` | |
| `deferStatement` | `DeferStmtSyntax` | |
| `doStatement` | `DoStmtSyntax` | |
| `labeledStatement` | `LabeledStmtSyntax` | |
| `conditionalCompilationBlock` | `IfConfigDeclSyntax` | treated as decl |
| `lineControlStatement` | `PoundSourceLocationSyntax` | |

### Types

| APUS | SwiftSyntax | Notes |
|---|---|---|
| `typeIdentifier` | `IdentifierTypeSyntax` / `MemberTypeSyntax` | member if dot-qualified |
| `tupleType` | `TupleTypeSyntax` | |
| `functionType` | `FunctionTypeSyntax` | |
| `arrayType` | `ArrayTypeSyntax` | |
| `dictionaryType` | `DictionaryTypeSyntax` | |
| `optionalType` | `OptionalTypeSyntax` | |
| `implicitlyUnwrappedOptionalType` | `ImplicitlyUnwrappedOptionalTypeSyntax` | |
| `protocolCompositionType` | `CompositionTypeSyntax` | |
| `opaqueType` / `boxedProtocolType` | `SomeOrAnyTypeSyntax` | |
| `metatypeType` | `MetatypeTypeSyntax` | |
| `anyType` | `IdentifierTypeSyntax` | name = "Any" |
| `selfType` | `IdentifierTypeSyntax` | name = "Self" |

### Patterns

| APUS | SwiftSyntax |
|---|---|
| `wildcardPattern` | `WildcardPatternSyntax` |
| `identifierPattern` | `IdentifierPatternSyntax` |
| `valueBindingPattern` | `ValueBindingPatternSyntax` |
| `tuplePattern` | `TuplePatternSyntax` |
| `enumCasePattern` | `ExpressionPatternSyntax` |
| `expressionPattern` | `ExpressionPatternSyntax` |
| `isPattern` | `IsTypePatternSyntax` |

## Terminal → TokenKind Mapping

| APUS Terminal | SwiftSyntax TokenKind | Notes |
|---|---|---|
| `plainIdentifier` | `.identifier` | |
| `escapedIdentifier` | `.identifier` | backtick-stripped |
| `implicitParameterName` | `.dollarIdentifier` | |
| `propertyWrapperProjection` | `.dollarIdentifier` | |
| `decimalNumber` | `.integerLiteral` | |
| `binaryLiteral` | `.integerLiteral` | |
| `octalLiteral` | `.integerLiteral` | |
| `hexadecimalLiteral` | `.integerLiteral` | |
| `decimalFloatingPointLiteral` | `.floatLiteral` | |
| `hexadecimalFloatingPointLiteral` | `.floatLiteral` | |
| `singlelineStringLiteral` | `.stringQuote` + segments | complex structure |
| `multilineStringLiteral` | `.multilineStringQuote` + segments | complex structure |
| `plainRegularExpressionLiteral` | `.regexSlash` + pattern | |
| `plainOperator` / `dotOperator` | `.binaryOperator` / `.prefixOperator` / `.postfixOperator` | context-dependent |
| `attributeMarker` | `.atSign` + `.identifier` | SwiftSyntax splits these |
| `macroIdentifier` | `.pound` + `.identifier` | SwiftSyntax splits these |
| keywords (`"if"`, `"let"`, etc.) | `.keyword(.if)`, `.keyword(.let)`, etc. | |

## Key Structural Differences

1. **Operator sequences are flat**: Both SwiftParser and Advent produce flat
   operator sequences (no precedence at parse time). SwiftParser uses flat
   `SequenceExprSyntax`; Advent has right-recursive `infixExpressions`.
   `SwiftSyntaxGenerator` flattens the right recursion to match.
   `OperatorTable.foldAll()` can fold later if needed, but is not used for
   structural comparison.

2. **if/switch are expressions**: SwiftSyntax uses `IfExprSyntax` and
   `SwitchExprSyntax`. Advent has both statement and expression variants.

3. **Intermediate nonterminals collapse**: Advent's `unionStyleEnum` vs
   `rawValueStyleEnum` both map to `EnumDeclSyntax`. Advent's
   `selfMethodExpression` / `selfSubscriptExpression` / `selfInitializerExpression`
   all map to `MemberAccessExprSyntax` on a `self` base.

4. **Tokens**: SwiftSyntax has `TokenSyntax` with a `.tokenKind` enum (~150 cases).
   Advent's 23 APUS terminals map into these, sometimes splitting (e.g.
   `@attribute` → `.atSign` + `.identifier`).

5. **Trivia**: SwiftSyntax attaches leading/trailing trivia (whitespace, comments)
   to every token. Advent's scanner strips whitespace and comments as trivia.
   For structural comparison, trivia can be ignored.

---

## Consolidated learnings (from agent memory, 2026-07-30)

### Disambiguation strategy — encode swift's decisions from its SOURCE, not from failing tests

(Endorsed 2026-07-21.) Swift's grammar is inherently ambiguous; swift-syntax
(hand-written recursive descent) hides it by **committing** at each fork via
unbounded lookahead + a finite documented decision set. A GLL parser surfaces EVERY
derivation, so those procedural decisions become ours to make **declaratively**.
Reactive per-test `@prefer`/`@longest` never converges — there's no shared model of
"which reading wins and why." Three pillars:

1. **Contextual-keyword discipline (~80 words).** Ground truth = swift-syntax
   `Keyword` enum entries with `isLexerClassified == false`. Each is an identifier by
   default; its keyword-productions are gated to EXACTLY swift's positions.
   Hard keywords use `---(…)` exclusion; contextual keywords need the INVERSE —
   allowed as identifiers, keyword-reading suppressed outside its site.
2. **The ≈32 `canParseAsXxx` / `atStartOfXxx` predicates.** Ground truth =
   SwiftParser's `Lookahead` predicates (`canParseType`, `atStartOfDeclaration`,
   `atValidTrailingClosure`, …). Each is a commitment point — encode with directional
   structured lookahead (`>+> >-> <+< <-<`) + structural grammar fixes at its site.
   (The `@unless(X)` predicate that once served this role was retired 2026-07-30.)
3. **Over-generality audit.** Every production must match swift's position-specific
   reachability (keyPath root → member-free simple type, not full `type`; `⚽` via
   faithful code-point classes, not coarse `\p{So}`).

This makes the grammar correct for constructs we have no test for, and converts an
open-ended patch stream into a finite porting task (~80 + ~32 items).

### Tight-`(` rule is NARROW (probe with `hasError`, not `swiftc`)

Requires tight `(` (space → `hasError`): **type specifiers with args**
(`nonisolated(nonsending)`, `dependsOn(...)`) and **`@attribute` arg clauses**
(`@available (*)`, `@convention (c)` reject). Allows a space (do NOT add `>s<`):
`private (set)`, `unowned (safe)`, `nonisolated (unsafe)` **decl modifier**,
`#available (..)`, `f (1)` calls, `yield (x)`. The three `nonisolated(...)` positions
have different valid arg-sets: type specifier = `nonsending` only (tight);
decl modifier = {`unsafe`,`nonsending`} (space OK); conformance = bare only. Bare
`nonisolated` as a type specifier binds a function type only
(`type = "nonisolated" functionType`).

### Reserved operator tokens

TSPL: `=`, `->`, `//`, `/*`, `*/`, `.`, and the unary prefix `&` are reserved — can't
be overloaded or used in custom operators. Grammar consequence: bare `&` must NOT be
in the overloadable `operator` production (not merely excluded from `prefixOperator`).
It has exactly two roles: prefix inout (`inOutExpression = "&" primaryExpression`) and
infix bitwise-and. Treating `&` as a general `prefixOperator` makes `&Y` double-parse
(prefixOperator + inOutExpression) — the root of the `[X] & [Y]` pivot cluster.


## Interpolated strings: tree shape vs our tokenisation (2026-08-29)

swift-syntax structures an interpolated string as SEVEN token kinds:

```
StringLiteralExpr: openingPounds? openingQuote segments closingQuote closingPounds?
ExpressionSegment: backslash pounds? leftParen expressions rightParen
segments:          [ StringSegment | ExpressionSegment ]*
```

Advent fuses these into THREE tokens, because a bare `"` is ambiguous (opening quote / closing quote /
content) and the scanner has no context to decide:

| advent token | example | fuses these swift tokens |
|---|---|---|
| `interpolatedStringLiteralHead` | `"abc\(` | openingQuote + stringSegment + backslash + leftParen |
| `interpolatedStringLiteralPart` | `)def\(` | rightParen + stringSegment + backslash + leftParen |
| `interpolatedStringLiteralTail` | `)ghi"`  | rightParen + stringSegment + closingQuote |

So the shape gap is a TOKENISATION mismatch, not a missing mapping — no post-hoc mapping can recover
swift's tree without splitting these tokens apart. It has the same root cause as REJECTS.md § C2
group C (a newline may not appear in interpolation trivia): swift decides both with lexer STATE, which
we do not have. Matching the shape therefore requires context-dependent lexing.

**Measured before treating this as a priority: only 32 of 1652 `trees differ` labels even CONTAIN a
`\(`** — 1.9%, and not all of those need differ because of interpolation. So decomposing the fused
tokens is NOT a significant lever on the tree-fidelity frontier. If it is ever done, do it for
faithfulness to swift's tokenisation in general, not for these 3 reject tests or for the frontier.

Error shape, for reference — swift does not record an "illegal newline" node. For `_ = "abc\(def⏎ghi)"`
it CLOSES the literal at the newline (`rightParen MISSING`, `closingQuote MISSING`), makes `ghi` a
separate top-level statement, and puts the trailing `)"` in `UnexpectedNodesSyntax`.

### Landed 2026-08-29: interpolated-string tree shape, WITHOUT touching the grammar

The fused tokens do NOT have to be split in the grammar. `GenerateSwiftSyntaxAST.swift` has the token
text and the span positions, so `convertInterpolatedStringLiteral` reassembles swift's shape directly —
one string segment per fused token:

    Head = `"` + segment + `\(`     Part = `)` + segment + `\(`     Tail = `)` + segment + `"`

Probe-confirmed target: segments strictly ALTERNATE and always both begin and end with a string
segment, so N interpolations give N+1 string segments INCLUDING empty ones (`"\(x)"` → `""`, expr, `""`).

This avoids the grammar decomposition entirely, which would have needed a new trivia-suppression
mechanism: `Lexer.lex` calls `skipTrivia` unconditionally, so separate string-internal tokens would
silently eat spaces in string content (`"a\(b) c"` loses its space).

LIMITATION: only the single-interpolation form. A non-empty `{ Part args }` returns nil and falls back
to the old one-segment tree. Extending it needs iteration over the KLN bracket.

### Latent bug found on the way: bare identifiers never converted

`convertPrimaryExpression` had a `find("identifier", …)` branch that could NEVER fire. The path is
`primaryExpression = genericIdentifier` → `genericIdentifier = hardIdentifier …` →
`hardIdentifier = identifier`, and `identifier` is a TERMINAL while `findNonterminal` digs only through
brackets (OPT/DO/KLN/POS), never through non-matching nonterminals. So every bare identifier reference
produced `MissingExpr`. Fixed by descending the two named levels explicitly; a `genericArgumentClause`
(`f<Int>`) still falls through to `MissingExpr` rather than silently dropping type arguments.

**Measured: `trees differ` 1629 → 1617/1619** (two seeds), 13 trees fixed including both interpolation
targets (`testStringLiterals#12`, `testTriviaEndingInterpolation#1`). Reject/accept/ambiguity unchanged
at 30/0/0 — an AST-builder change cannot affect parsing, and did not.

**Caution for future measurements:** 4 labels (`testForwardSlashRegex71#1`, `#78`, `testIdentifiers10#1`,
`testNonisolatedSpecifier#12`) FLAP between runs under non-deterministic hashing — they appeared as
"fixed" in one run and "broken" in the next. Do not read a single-run tree diff as signal; and the
harness reject COUNT can differ by one while the label SET is identical, so compare sets, not counts.

## Key-path components: swift's actual algorithm (read from source, 2026-09-21)

Transcribed from `SwiftParser/Expressions.swift` — `parseKeyPathExpression` and its helper
`getNumOptionalKeyPathPostfixComponents`. Recorded because deriving it from black-box probing cost
four failed attempts, and because the conclusion is the OPPOSITE of the obvious one.

### The loop

After `\` and an optional root type (`parseSimpleType(allowMemberTypes: false)`, absent when the
next token starts with `.`), repeat:

1. **Subscript** — if at `[` (with `allowAtStartOfLine: false`), or `mayBeAfterTypeName` and at
   `.` peeking `[`: consume the optional `.`, then `[args]`. Sets `mayBeAfterTypeName = false`.
2. **Optional/force run** — if at a `prefixOperator`/`binaryOperator`/`postfixOperator` (or
   `postfixQuestionMark`/`exclamationMark`) AND
   `getNumOptionalKeyPathPostfixComponents(text, mayBeAfterTypeName:) > 0`: consume that many
   components.
3. **Property** — if at `.`: `.name`, `.1`, `.name(labels:)`, or (under
   `keypathWithMethodMembers`) `.name(args)`. Does NOT clear `mayBeAfterTypeName`.
4. Otherwise **break** — the key path ends and the enclosing expression parser resumes.

### The splitter

    getNumOptionalKeyPathPostfixComponents(tokenText, mayBeAfterTypeName) -> Int?
      for each byte of tokenText:
        "."          -> if !mayBeAfterTypeName { break }        // stop, keep count so far
                        if lastWasDot { return nil }            // ".." is not a key-path postfix
                        lastWasDot = true
        "!" or "?"   -> mayBeAfterTypeName = false; lastWasDot = false; count += 1
        anything else-> return nil                              // not a key-path postfix at all
      return count

`mayBeAfterTypeName` means "no `!`/`?`/subscript component seen yet". It gates only the DOTTED
forms `.?`, `.!`, `.[` — swift cannot tell a nested type reference from a member, so it permits
those only before the first non-property component.

### THE KEY CONSEQUENCE — `??` is CONSUMED, not rejected

For `\Foo.bar ?? fallback`: properties leave `mayBeAfterTypeName` true, the token `??` is a
`binaryOperator`, and the splitter scans `?`,`?` to **2**. So swift consumes `??` as two
optional-chaining components and `fallback` is left dangling — the statement ends after the key
path and `fallback` becomes a second, erroneous item. That is the `KeyPathExpr` + second
`CodeBlockItem` shape the dumps show.

So the fix is NOT a gate that forbids `??` after a key path. It is to make the key path CONSUME
it, after which the input fails for the right reason. Every other observation follows:

| input | mechanism | verdict |
|---|---|---|
| `\Foo.bar ?? fallback` | `??` splits to 2 components, `fallback` dangles | REJECT |
| `\Foo.bar ? a : b` | a SPACED `?` lexes as *infix* question mark, absent from the branch-2 token set, so the loop breaks | ACCEPT (ternary) |
| `\Foo.bar / value` | splitter hits `/`, returns nil, loop breaks | ACCEPT (infix) |
| `\Foo.bar + 1`, `== x`, `&& y`, `as T` | same as `/` | ACCEPT |
| `\Foo?.?.bar.?.blah` | properties keep `mayBeAfterTypeName` true, so the dotted `.?` is legal | ACCEPT |

Note branch 2 is whitespace-INSENSITIVE: `??` is consumed however it is spaced. The single-`?`
exemption is not a whitespace rule in the parser at all — it falls out of the LEXER classifying a
spaced `?` as infix rather than postfix.

### RESOLVED 2026-09-22 — and the "postfix island" framing was WRONG

The fix is FOUR alternates, no restructuring, no converter change:

    keyPathPivot         = <s> optionalMark >+> ( optionalMark forceMark ) .
    keyPathPivot         = <s> forceMark   >+> ( optionalMark forceMark ) .
    keyPathBareComponent = <s> optionalMark >+> ( optionalMark forceMark ) .
    keyPathBareComponent = <s> forceMark   >+> ( optionalMark forceMark ) .

A mark run is consumed however it is spaced (branch 2 is token-based), so `\Foo.bar ?? fallback`
takes `??` as two components and `fallback` dangles. The `>+>` requires a FOLLOWING mark, so a
lone spaced `?` is untouched and `\Foo.bar ? a : b` stays a ternary. Both phases need it because
`mayBeAfterTypeName` gates only the DOTTED forms, never a bare `?`/`!`.

Two beliefs recorded earlier here were WRONG, and each cost a failed attempt:

1. **"A key path is a postfix island; no postfix operator or member access may follow one."**
   FALSE, and the grammar's own comment says it. Measured: `\Foo?.?.bar.?.blah` has
   `hasError == false` and its tree is a MEMBER ACCESS whose base is the key path — swift ends the
   key path at `.bar` (a dotted form in phase 2 breaks the loop) and the enclosing postfix parser
   resumes. So the escape hatch is CORRECT; closing it with
   `@cannotParse( keyPathExpression )` on `forcedValueExpression`/`optionalChainingExpression`
   broke exactly those two fixtures.
2. **"`keyPathComponents` cannot express the component language, so it must be flattened."**
   FALSE. The three-rule shape already matches swift exactly. Confirmed by enumerating every
   length-2 and length-3 component sequence over `{.p ? ! .? .! [0] .[0]}`: dotted forms are legal
   only while every component so far is a property, a property does NOT restore the allowance
   (`\Foo.?.p.?` is rejected by both), and bare forms are always legal — which is precisely
   `keyPathProperty { keyPathProperty } ( keyPathPivot keyPathBareTail? )?`.

Also worth knowing: `collectKeyPathComponents` already calls `collectListElements` with a SET of
element names and a SET of recursive list names, so it is shape-independent. The 32 failures from
the flattening attempt came from introducing a name OUTSIDE that set, not from converter rigidity.

### RESOLVED 2026-09-22 (second pass): the divergences are TWO different things

`hasError` was the wrong oracle, and that is why the earlier analysis kept contradicting itself.
Measured with the syntax API (`UnexpectedNodesSyntax` present, or a token with
`presence == .missing`) over every component sequence:

| length | cases swift FLAGS | of those, recoveries |
|---|---|---|
| 3 | 396 | **396 — all of them** |
| 4 | 3054 | **3054 — all of them** |

**swift NEVER fails to parse a key path.** `consumeOptionalKeyPathPostfix` consumes a dotted mark
even when `mayBeAfterTypeName` is false — it just moves the period into `unexpectedBeforeComponent`
and sets `period = nil`. So "swift rejects X" always means "swift built a tree for X and annotated
it", never "X is outside the language".

That splits the divergences cleanly:

| class | length 3 | length 4 | is it a grammar bug? |
|---|---|---|---|
| swift RECOVERED (unexpected/missing), Advent accepts | 40 | 242 | **NO** — not a language boundary at all |
| swift CLEAN, Advent REJECTS | **12** | **250** | **YES — real under-acceptance** |

**Class 1 is not expressible as a CFG**, and not because of any limitation in Advent's tooling:
there is no language boundary to express. Matching `hasError` here would require modelling error
RECOVERY — producing a tree plus an annotation — which a recognizer does not do. Advent accepting
these is the defensible behaviour; the fix belongs in the oracle (compare against "swift produced a
CLEAN tree", not `!hasError`), not in the grammar.

**Class 2 is the real bug, and it is an UNDER-acceptance** — the opposite of what the fuzzer report
and all my earlier analysis assumed. Every one of the 12 at length 3 has the same shape: a dotted
mark in phase 2 followed by a BARE subscript.

    \Foo.?.?[0]   \Foo.!.?[0]   \Foo[0].?[0]   \Foo[0].![0]   \Foo.[0].?[0]   \Foo.[0].![0]
    \.?.?[0]      \.?.![0]      \.!.?[0]       \.!.![0]       \.[0].?[0]      \.[0].![0]

swift parses these CLEANLY by STOPPING the key path early and letting the enclosing postfix parser
take the rest: for `\Foo.?.?[0]` the tokens are `period` `?` then a BINARY OPERATOR `.?`, branch 2
returns 0 for it (the leading `.` breaks the scan once the flag is false), branch 3 does not match
an operator token, so the loop breaks and `.?[0]` becomes optional-chaining plus a subscript on the
key-path expression.

So the grammar needs the key path to be ALLOWED TO STOP before a phase-2 dotted mark. Prime
suspect: `keyPathExpression = @prefer "\" keyPathRootType keyPathComponents? .` — the `@prefer`
may be pruning the short reading that leaves the tail to postfix parsing. That is the next thing to
test, and it is a one-annotation experiment, not a rework.

### Superseded: the phase rule is NOT the whole story

The "18 cases" figure and the claim that the three-rule grammar "matches swift exactly" both came
from a NON-EXHAUSTIVE sweep: length 2 was complete, but length 3 varied only the LAST position and
only over dotted items. Exhaustive sweeps over all 7 items in every position give:

| length | cases | disagreements |
|---|---|---|
| 3 | 686 | **52** |
| 4 | 4802 | **492** |

And they expose a class the partial sweep could not see — Advent UNDER-accepting (250 of the 492):

    let v = \Foo.p?.?[0]     swift ACCEPTS, Advent rejects
    let v = \Foo.?.?[0]      swift ACCEPTS, Advent rejects

These falsify the phase rule as stated. `\Foo.?.?[0]` has a dotted `.?` after a non-property
component, which the rule predicts is rejected — and swift accepts it. The reason is almost
certainly TOKEN MERGING: `.?.?` is a single operator token, the splitter consumes part of it and
`consumeOptionalKeyPathPostfix` splits the remainder, so the second `?` arrives as a BARE mark
rather than a dotted one. The component-sequence language therefore depends on how the LEXER
groups runs of `.`/`?`/`!`, not on the component list alone, and cannot be read off a
component-by-component state machine.

So the phase rule is a good approximation that holds for every sequence of length ≤ 2 and for the
real-world shapes in the corpora, but it is NOT the language. Getting this exactly right needs
`consumeOptionalKeyPathPostfix` and swift's operator-splitting lexer read together with the
splitter — the three pieces jointly decide it.

STILL OPEN, both directions:
- Advent OVER-accepts a dotted subscript in phase 2 (`\Foo.p.?.[0]` …) and a bare subscript as the
  first component with no root (`\[0].p` …).
- Advent UNDER-accepts the token-merged forms above (`\Foo.p?.?[0]` …).
None were reported by the fuzzer, and none involve a `??` tail, so the shipped fix stands.

### Porting this to Advent (superseded by the above — kept for the reasoning)

The grammar should become a flat component run with one phase boundary for `mayBeAfterTypeName`
(dotted forms allowed before the first non-property component, bare forms after), replacing the
three-rule `keyPathComponents` / `keyPathPivot` / `keyPathBareTail` / `keyPathBareComponent` shape,
which encodes the same flag far less legibly.

Advent does not need swift's token splitting: `optionalMark` and `forceMark` are munch-exempt
regex terminals, so a run of `?`/`!` already lexes as separate marks. What it DOES need is to
consume a multi-mark run without requiring tightness, while still leaving a single spaced `?` to
the ternary — that is the delicate part, and it is the grammar's stand-in for swift's
postfix-vs-infix `?` lexing.

TWO HARD CONSTRAINTS, both learned by breaking them:
- The converter resolves `keyPathPivot`, `keyPathBareTail`, `keyPathBareComponent`,
  `keyPathPivotFirst` and `keyPathProperty` BY NAME. Renaming without porting the collectors in
  the same change produced 32 failures.
- Adding an alternate alongside the old rules instead of replacing them creates a second
  derivation of `.?` — 15 failures, 4 tree diffs.

The tree shape is asserted by existing fixtures: `testKeypathExpression`, `testKeyPathSubscript`,
`testKeyPathMethodAndInitializers`, `testChainedOptionalUnwrapsWithDot`,
`testChainedOptionalUnwrapsAfterSubscript`, `testKeyPathFollowedByOperator`. Those are the gate.
STILL UNREAD, and the next step before writing code: the key-path half of
`GenerateSwiftSyntaxAST.swift`.

## Key paths: what the EVOLUTION PROPOSALS say (researched 2026-09-22)

First actual research into the proposals rather than reading the parser. Two findings that bear
directly on open divergences, and one general lesson.

### SE-0161 (Smart KeyPaths) resolves the `\[0]` family — it is NOT legal

Accepted with an explicit clarification on exactly our ambiguity: the core team was concerned about
"the ambiguity between contextual keypaths starting with a subscript and keypaths rooted on an
array type, e.g. `\[a]?.foo`", and resolved it by requiring that **ALL contextual key paths start
with `\.`**. So `\.` introduces a contextual key path; a bare `\` introduces one with an explicit
root.

That makes `\[0].p`, `\[0]?`, `\[0]!`, `\[0][0]` INVALID BY DESIGN — they are 4 of our length-2,
16 of our length-3 and 64 of our length-4 over-acceptances. Our grammar admits them explicitly:

    keyPathPivotFirst = "[" functionCallArgumentList? "]" .   // bare [args]  (`\[0].y`, `\Foo[0]`)

The comment even cites `\[0].y` as intended. Per SE-0161 that must be written `\.[0].y`. The rule
conflates two cases — a bare `[args]` AFTER a root (legal, `\Foo[0]`) and as the FIRST component
with no root (illegal). Splitting those two is a real simplification AND a correctness fix, and it
is derived from the spec rather than from a failing case.

### SE-0161 also confirms the "postfix island" intent

"Accessing a property of a key path, e.g. `\Person.friends[0].firstName.someKeyPathProperty`,
requires parenthesizing the key path as `(\Person.friends[0].firstName).someKeyPathProperty`."

So the INTENT is that no member access follows an unparenthesised key path — which is what the
grammar's "postfix islands" comment claims. But swift-syntax's PARSER accepts the unparenthesised
form and recovers. Intent and implementation disagree, and we have been chasing the implementation.
Worth an explicit decision about which one Advent targets.

### SE-0479 explains the one remaining test failure

`\Foo.method<Int>()` — our `testKeyPathMethodAndInitializers#3` reject fixture — is SE-0479
(Method and Initializer Key Paths), reviewed through May 2025. In swift-syntax it is gated behind
the `keypathWithMethodMembers` experimental feature, which is why branch 3 of the parse loop tests
`self.experimentalFeatures.contains(.keypathWithMethodMembers)`. Our fixture expects a REJECT
because the feature is off in the pinned version. So the failure is about feature gating, not about
component structure.

Also noted for later: SE-0438 (Metatype Keypaths) requires `.Type` as the first component
(`\Bee.Type.name`); SE-0249 (Key Path Expressions as Functions) and SE-0416 affect typing, not
syntax.

### THE LESSON

The intended grammar is materially SIMPLER than the parser's recovery-laden implementation, and it
answers questions we spent four failed attempts probing for. Read the proposal before reading the
parser. This was never done for key paths — the whole mapping was reverse-engineered from
swift-syntax source and failing cases.

Sources:
- https://github.com/swiftlang/swift-evolution/blob/main/proposals/0161-key-paths.md
- https://github.com/swiftlang/swift-evolution/blob/main/proposals/0479-method-and-initializer-keypaths.md
- https://github.com/swiftlang/swift-evolution/blob/main/proposals/0438-metatype-keypath.md

---

## 2026-09-23 — Key paths: the model, and what encoding it actually changed

### Method (this is the transferable part)

Rather than patch the grammar per failing case — which had grown key paths to 40 productions and
left residue one sequence-length deeper each time — swift's key-path loop AND the lexer rules it
depends on were ported into an executable model, `AdventTests/KeyPathModel.swift`, and validated
against swift-syntax directly:

| scope | sequences | disagreements |
|---|---|---|
| CORE alphabet x all 9 root forms, lengths 1-6 | 1,235,304 | 0 |
| WIDE alphabet x 9 roots, lengths 1-4 | 11,006,820 | 0 |

Around twenty of the model's rules were guessed WRONG at some point, which is the whole argument
for it existing. Everything in it is ported from swift's source, never inferred, and each rule
cites its originating function.

The model then became the ORACLE FOR THE GRAMMAR (`KeyPathGrammarTests`), which is cheap enough to
run at depth because it needs no swift-syntax parse. That sweep is what found the defects below;
it now stands at **0 over / 0 under over 13,689 sequences**, with no allowance list.

### What it found

Six defects, three of them UNDER-acceptances no fuzzer run had reported:

| defect | fix |
|---|---|
| `\[0]` accepted | `>+> ( keyPathDot )` on the root-absent alternate — swift skips the root parse only when the next token's TEXT starts with `.` |
| `\Foo ??` rejected | spaced mark run was unreachable as a first component → added to `keyPathPivotFirst` |
| `\~x` rejected | `keyPathRootSuppressed` (SE-0390) |
| `\Foo<T>.p<T>` rejected | generic arguments on `keyPathMemberName`, carried onto `KeyPathPropertyComponentSyntax` |
| `\Foo ? ??` accepted | `>+>` is trivia-INSENSITIVE; replaced with tight terminals `keyPathMarkRunOptional`/`keyPathMarkRunForce` |
| `\Foo !` rejected | spaced lone `!` is a component, spaced lone `?` is not — `lexNormalQuestionOrExclamation` gives a not-left-bound `?` its own `infixQuestionMark` kind (the ternary), which branch 2 rejects |

Plus the largest single fix, the STRUCTURAL postfix island (see
`Lexical Disambiguation Tools.md`, 2026-09-23 trap 1), which killed `\Foo.m()` and the whole
`\Foo?.?.[0]` family at once.

### Honest accounting on size

40 productions / 21 nonterminals → 45 / 23. The rules GREW. The plan recorded in TODO
("replace the 13 component nonterminals with ~3") was WITHDRAWN as wrong: reading the DFA off the
model showed the existing two-phase shape — property run, then a state-flipping pivot, then a
bare-only tail — was already the right structure, so there was nothing to collapse. What the
filter machinery had been hiding was six missing or wrong rules, not redundancy.

What did shrink was elsewhere, and only because the model made it safe to test necessity by
deletion: two dead Oracle predicates and the dead terminals `keyPathDotMarkStart`,
`dotOperatorCharacterNoReserved`, `postfixDotOperator`.

### Mark-ending dot operators (closed TODO 1/2/21)

`dotOperator` forbade a trailing `?`/`!` run. MEASURED, that was wrong in BOTH positions:

    x.?  x.!  x.??  x.?.   →  postfixOperator(".?") …
    a .? b                 →  binaryOperator(".?")
    \Foo.?.?[0]            →  …, binaryOperator(".?"), ArrayExpr

so Advent rejected `x.?`, `f(x.?)` and `a .? b` alike. Relaxing the ONE terminal (rather than
adding a second for the postfix position — two terminals matching the same span is an ambiguity)
fixed all of them and let the two hand-written `infixExpression` alternates that had been
spelling `.?`/`.!` explicitly be DELETED: maximal munch, not their `>-> ( "." )` lookahead, is what
keeps `.?.name` as a single `.?.` token.

Also closed in the same area:
- `value as~Copyable` / `value is~Copyable` — `"as"`/`"is"` added to the `suppressedType`
  not-left-bound lookbehind; only `as!~C` had worked, via `forceMark`.
- `Foo.self` / `A<B>?.self` in TYPE position are `MemberType` with a `self` KEYWORD name. The
  alternate existed on `typeIdentifier` but had no converter case (hence `MissingType`) and could
  not take an optional base (hence no tree at all for `as A<B>?.self`). Now `selfMemberType`, based
  on `simpleType` and registered in `type`.
- `var (b, var c) = t` is CLEAN in swift, modelled as a nested `ValueBindingPattern`. TODO item 3
  asserted swift rejects it; that was wrong. The bug was in the CONVERTER —
  `convertBindingSubpattern` had no case for the specifier alternate, so it matched the inner
  identifier and dropped the `var`.

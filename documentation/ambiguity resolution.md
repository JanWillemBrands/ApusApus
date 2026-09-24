# Ambiguity Resolution: swift-syntax predicates ↔ Swift.apus annotations

Where swift-syntax (hand-written recursive descent) resolves Swift's inherent
ambiguity by **committing** at each fork with unbounded lookahead, a GLL parser
surfaces every derivation and must resolve the same forks **declaratively**. This
document cross-correlates swift-syntax's commitment predicates with the annotations
in `Swift.apus`, to convert an open-ended patch stream into a finite porting task and
to guide reduction of the residual reject/ambiguity failures.

## Method & caveat

- **Predicate list = ground truth** from the checked-out `SwiftParser` source
  (`Sources/SwiftParser/*.swift`, `grep` of `func canParse* / atStartOf* / isStartOf* /
  atAttributeOrSpecifier`), 37 methods minus 3 generic helpers (`withLookahead`,
  `atContextualPunctuator`, `atContextualKeywordPrefixedSyntax`) ≈ the "~32".
- **Status column is a structural assessment**, not a per-predicate test. Most
  predicates are NOT named gates in the grammar — they are handled by grammar shape +
  Oracle annotations. Calibrated by three signals: *cited by name* in a grammar
  comment (high confidence), *construct present*, *construct absent*.

## Annotation inventory (Swift.apus)

`@prefer`×59 · `@longest`×34 · `@shortest`×10 · `@avoid`×4 · structured lookahead
`>+>`×16 `<-<`×6 `>->`×5 `<+<`×0 · gates `>s<`×62 `<s>`×29 `>n<`×17 `<n>`×8 ·
`---(…)` exclusion ×11 · `@splitBefore`×5 · `@builder`×9.

## Annotation → predicate family (one line each)

- `atStartOf*` / `canParse*` commitment points → **structured lookahead** `>+> >-> <+< <-<`
  + structural fixes. The "◐ slightly off" rows are where the grammar parses the
  construct but the *commitment* still leaks a second reading — this is the residual
  reject/ambiguity frontier.
- position / tightness predicates (tight `(`, line-leading, no-newline `[`) → **gates**
  `>s< <s> >n< <n>`.
- same-span / extent forks (`preferRegexOverBinaryOperator`, metatype, arrays/dicts,
  accessors) → **`@prefer` / `@longest` / `@shortest`**.
- the ~80 contextual keywords (adjacent pillar) → **`---(…)`** exclusion.

## Correlation

Legend: ✅ complete (cited / faithfully modeled) · ◐ slightly off (construct present,
commitment leaks) · ✗ missing (construct absent).

### Types
| swift-syntax predicate | apus mechanism | status |
|---|---|---|
| `canParseType` | full `type` grammar; forks resolved structurally | ◐ |
| `canParseSimpleType` / `canParseTypeIdentifier` / `canParseTypeScalar` | `simpleType`/`typeIdentifier` | ✅ |
| `canParseSimpleOrCompositionType` | `compositionType` + `@longest` on `any P & Q` | ✅ |
| `canParseAsGenericArgumentList` / `canParseGenericArgument` | cited; `<…>`-as-generics + `@longest genericIdentifier` | ✅ |
| `canParseFunctionTypeArrow` | `functionType` + `@prefer parenthesizedExpression` | ◐ |
| `canParseTupleBodyType` | `tupleType`; tuple-type vs tuple-expr overlap | ◐ |
| `canParseCollectionTypeBody` | `arrayType`/`dictionaryType` + `@prefer expression` | ◐ |
| `canParseInlineArrayTypeBody` / `canParseStartOfInlineArrayTypeBody` | `inlineArray` (`[N of T]`) | ◐ |
| `canParseTypeAttributeList` | `typeAttribute` (thin — 1 site) | ◐ |
| `canParseBaseTypeForQualifiedDeclName` | no dedicated qualified-decl-name base | ✗ |

### Attributes / specifiers
| predicate | apus mechanism | status |
|---|---|---|
| `atAttributeOrSpecifier` | `attributes` + tight-`(` rule | ◐ |
| `canParseCustomAttribute` | `customAttribute`/`attributes` | ◐ |
| `canParseNonisolatedAsSpecifierInExpressionContext` | 3 `nonisolated` arg-sets (SwiftSyntax Mapping.md) | ◐ |

### Patterns / closures / labels
| predicate | apus mechanism | status |
|---|---|---|
| `canParsePattern` / `canParsePatternTuple` | `pattern`/`tuplePattern` + `@prefer expressionPattern` | ✅ |
| `canParseClosureSignature` | `closureSignature`/`closureParameterClause` | ◐ |
| `canParseArgumentLabelList` | cited; label-vs-expr at `(name:` | ◐ |
| `atStartOfLabelledTrailingClosure` | cited; `trailingClosureLabel = … ---("default" …)` | ✅ |
| `canParseIntegerLiteral` | `@longest numericLiteral` (versions, `.0` indices) | ◐ |

### Statement / declaration / expression forks
| predicate | apus mechanism | status |
|---|---|---|
| `atStartOfDeclaration` | cited; `statement = @prefer declaration` | ✅ |
| `atStartOfStatement` | cited; `>->("(" "[" ".")` + `atContextualKeywordPrefixedSyntax` (preferPostfixExpr) | ✅ |
| `atStartOfGetSetAccessor` | cited; `@prefer "{" accessorClauseList "}"` | ✅ |
| `atStartOfConditionalStatementBody` | `@longest functionBody` (greedy `{`-is-body) | ◐ |
| `atStartOfExpression` | structural + the statement fork | ◐ |
| `atStartOfPostfixExprSuffix` | postfix grammar + `>n<` (no-newline `[`/`(`) | ◐ |
| `atStartOfSwitchCase` / `atStartOfConditionalSwitchCases` | `switchCase` | ◐ |
| `atStartOfFreestandingMacroExpansion` | `macroExpansion*` | ◐ |
| `isStartOfReturnExpr` | `returnStatement`; regex-vs-return via operator gates | ◐ |
| `atStartOfActor` | no `actor` declaration | ✗ |
| `atStartOfUsing` | no `using` declaration (Swift 6.2) | ✗ |

### Tally (≈32)
- **✅ complete: 8** — generics list, `any P&Q`, decl-vs-stmt, stmt-start/preferPostfixExpr,
  get/set accessors, labelled-trailing-closure, pattern-expr, simple types.
- **◐ slightly off: 21** — most type predicates, closure signature, argument labels,
  macro/switch/return/conditional-body starts.
- **✗ missing: 3** — `atStartOfActor`, `atStartOfUsing`, `canParseBaseTypeForQualifiedDeclName`.

**Headline:** the expression-level commitment predicates (decl/stmt/accessor/generics/
trailing-closure) are the well-covered core; the type-system `canParse*Type*` family is
uniformly "slightly off" (grammar parses them, commitment leaks); the only outright holes
are two newer declaration forms (`actor`, `using`) and one niche qualified-name base.

## Residual reject/ambiguity frontier (79 rejects, 1 residual ambiguity)

The Oracle is unambiguous by construction; the "79" are `RejectSyntaxTests/adventRejects`
— inputs swift-syntax rejects that Advent still accepts (over-generality = a commitment
leak). Guided by the ◐ rows above, the reduction work is per-predicate: tighten each
"slightly off" construct so its second reading is unreachable at swift's position.

Sources: the maintained cluster inventory in `REJECTS.md` (B/C labels), mapped onto the
predicate families above. Counts are from `REJECTS.md`'s open clusters and should be
reconciled against a fresh sweep (accept 0 / reject 79 / ambiguity 1); they are the shape of
the frontier, not a certified census.

### The open clusters, by predicate family

| REJECTS cluster | ~n | predicate family (this doc) | commitment leak? | reduction lever |
|---|---|---|---|---|
| **B2** trailing closure / brace in cond/subject | ~18 | `atValidTrailingClosure(.stmtCondition)` (kin of `atStartOfLabelledTrailingClosure` ✅, different *flavor*) | ✅ yes | THREE discriminators (measured, REJECTS §B2): (1) newline after closure `{` → layout gate `<n>`; (2) condition opens with `{` → `>->("{")`; (3) follow token after `}` (guard-`else`) → structural lookahead. Only (3) needs a new primitive; scope all to the `conditionExpression` path |
| **C1** key-path postfix chains (`\T.?.!`, `.[n]`, `method<T>()`) | 7 | `atStartOfPostfixExprSuffix` ◐ | ✅ yes | extend key-path postfix grammar to the full postfix-suffix set (same suffixes as ordinary postfix) |
| **C3** forward-slash regex edges (`qux(/,1)/2`, `^/"/"`) | 6 | `preferRegexOverBinaryOperator` / `isStartOfReturnExpr` ◐ | ✅ yes | scanner-side regex-vs-divide gate at operand-ender / after `(` (already partly modeled via `<-<`) |
| **C7** new keywords (`using`, `~Copyable` param, `nonisolated` type) | 4 | `atStartOfUsing` ✗, `canParseNonisolatedAsSpecifierInExpressionContext` ◐ | ✅ yes | the two ✗ holes: add `using` decl + `~T` inverse-type in parameter; tighten `nonisolated` type-position |
| **C8** multiline generic w/ line-leading `of` | 3 | `canParseInlineArrayTypeBody` (`[N of T]`) ◐ | ✅ yes | layout scanner must not treat line-leading `of` as a separator inside a generic-arg `[ … ]` |
| **C4** module selector invalid forms (`Foo::Bar`) | 11 | `canParseBaseTypeForQualifiedDeclName` ✗ | partial | the one genuine ✗ hole + several are malformed-arg checks, not commitment |
| **C13** misc error-recovery (12 tests) | 12 | mixed — mostly `atStartOfDeclaration`/`atStartOfStatement` recovery ◐ | mixed | per-test triage; some are commitment, some are recovery-only `hasError` that need a reject shape |

### Out of family — NOT a commitment leak (won't move by tightening a predicate)

These are the doc's blind spot: rejects that are **lexical or semantic**, so no `canParse*`/
`atStartOf*` tightening touches them. They belong to the two **APUS extension candidates**
(`REJECTS.md` §Extension) or the scanner, not the predicate-porting task.

| cluster | ~n | why out of family | home |
|---|---|---|---|
| **C2** malformed string / multiline literals | 12 | scanner-level (indentation, newline-after-`"""`, termination) | Scanner |
| **C10** spacing-sensitive postfix (`foo!!foo`, `foo??bar`) | 4 | maximal-munch postfix-operator lexing | Scanner (postfix `!`/`?` split) |
| **C5** duplicate access modifiers (`open open(set)`) | 2 | semantic dedup / counting | Post-parse predicate (Oracle filter) |
| **C6** coroutine accessor combos, init-accessor defaults | 3 | invalid *combination*, not shape | Post-parse predicate |
| **C12** `@available` string-literal kind | 4 | property of parsed token kind | Post-parse predicate (parked) |

### Headline for the reduction work

- **~38 of the 79 are genuine commitment leaks** (B2, C1, C3, C7, C8, and the C4/C13 subset) —
  exactly the ◐/✗ rows above. The single highest-leverage item is **B2 (~18)**, gated on one
  reusable primitive (**structural lookahead** past a nonterminal's extent); landing it clears
  the largest cluster and is grammar-agnostic.
- **~25 are out of family** (C2, C5, C6, C10, C12) — scanner or post-parse-predicate work; the
  predicate-porting effort will not touch them, so they should be tracked separately and not
  counted against "commitment leak" progress.
- The two outright predicate **holes** worth closing directly are `atStartOfUsing` (C7) and
  `canParseBaseTypeForQualifiedDeclName` (C4) — small, self-contained declaration/type additions.

_Next: drill B2 first (structural-lookahead primitive), then the C1 postfix-suffix extension;
reconcile the counts with a fresh sweep before committing per-cluster fixes._

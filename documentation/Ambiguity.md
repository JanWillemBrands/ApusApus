# Ambiguity

This document describes how APUS resolves ambiguity. It covers the lexer, the parser gates,
the Oracle and the procedure to fix an ambiguity. It uses Swift as the example language. The
tools are not specific to Swift.

For the full syntax of each annotation, see `apus.md`.

## 1. Terms

| Term | Meaning |
|---|---|
| **derivation** | One way that the grammar can produce the input. |
| **ambiguity** | Two or more derivations for the same input. |
| **yield** | A BSR span `(i, k, j)` on a grammar node. `i` is the start, `j` is the end, `k` is the pivot. |
| **pivot** | The position where the last body symbol of an alternate starts. |
| **extent** | The length of a span. |
| **trivia** | Whitespace, newlines and comments between tokens. |
| **maximal munch** | The lexer rule that selects the longest token at a position. |
| **forest** | All yields that the parser records for one input. |

## 2. The four layers

APUS resolves ambiguity in four layers. Each layer has a different job.

| Layer | When | What it decides | Tools |
|---|---|---|---|
| Lexer | during the parse, per terminal | the extent of a token | `@literalMunch`, munch-exempt terminals, `@preempt` |
| Parser gates | during the parse, per position | if a derivation can continue here | `<s>` `>s<` `<n>` `>n<`, token lookaround, `---()` |
| Oracle | after the parse | which completed derivations to keep | `@canParse`, `@confinedTo`, `@sameLine`, `@prefer`, `@longest`, `@left`, … |
| AST generator | after the Oracle | the operator precedence tree | precedence metadata on the operator alternates |

Obey these rules:

- The parser does all checks on tokens and trivia.
- The Oracle does not read the input. Each Oracle rule is a query on the yields.
- A layer cannot recover a derivation that an earlier layer removed.

## 3. Lexer tools

The lexer is parser-driven. APUS uses the LCNP model from Scott & Johnstone, *Multiple
Lexicalisation — A Java Based Study* (SLE 2019, in `articles/raw/`):

- The parser does not read a token stream. At each slot, it calls `lex(position, terminal)` for
  each terminal that the slot can start with.
- `lex` gives the matches of that one terminal at that position. Each terminal gives its longest
  match in its own language. `@preempt` can add shorter matches.
- For each distinct end position, the parser makes one descriptor.
- All positions are character positions in the source text. BSR spans use these positions.
- The lexer keeps the result of each `(position, terminal)` query in a cache.
- A keyword and an identifier with the same text do not conflict in the lexer. The slot selects
  the terminal that it needs.

Thus two tokenisations of the same text can both reach the parser. The GLL structures share the
common parts. The tools in this section change the answer of `lex`.

### 3.1 `@literalMunch`

```apus
@literalMunch
identifier              - @builder .
@literalMunch @preempt(regexSlash, tryScanOperatorAsRegexLiteral)
nonArrowOperatorToken   - @builder .
@literalMunch
dotOperator             - @builder .
```

A literal terminal does not match when a `@literalMunch` terminal has a longer match at the
same position. Examples:

- `for` does not match inside `foreach`.
- `_` does not match inside `_foo`.
- `&` does not match inside `&&`.

This rule applies to literal terminals only. It applies at all positions, also where the
parser does not expect the longer terminal.

### 3.2 Munch-exempt terminals

A single-character terminal that you write as a regex is not a literal. Thus `@literalMunch`
does not remove it:

```apus
regexSlash      - /\// .
openAngle       - /</ .
closeAngle      - />/ .
optionalMark    - /\?/ .
forceMark       - /!/ .
keyPathDot      - /\./ .
```

Use these terminals where the character must match inside a longer operator. Examples:

- `closeAngle` closes two generic clauses in `Array<Array<Int>>`.
- `optionalMark` gives two marks in `Int??`.
- `keyPathDot` matches the `.` at the start of the operator `.?` in `\Foo.?`.

Use the literal form where the character must not match inside a longer operator.

### 3.3 `@preempt(X[, N])`

`@preempt` prevents a token from taking the start of a construct with a higher priority.

- **`X` (offer).** The terminal also gives each shorter match that ends where terminal `X`
  starts. The first character is not a split point.
- **`N` (commit), optional.** The lexer keeps the first shorter match where nonterminal `N`
  parses. It removes all longer matches. If `N` parses at no split point, the lexer keeps
  only the longest match. A memoised sub-parse does the test for `N`.

Examples:

- `^^/regex/` becomes `^^` followed by `/regex/`. The regex parses, thus the split wins.
- `^/x` stays one operator. No regex parses, thus the longest match wins.
- `@preempt(openAngle)` on `functionNameOperator` gives the `<` in `func %%%<T>` to the
  generic parameter clause.

`X` is a terminal and not every expected terminal. Thus `a +++ b` does not become `a ++ +b`.

## 4. Parser gates

A parser gate is a zero-width test in a production. If the test fails, the derivation stops
at that position.

### 4.1 Boundary predicates

These predicates test the trivia gap skipped between the previous committed token and the current
parse position.

| Predicate | True when |
|---|---|
| `<s>` | there is a non-empty trivia gap |
| `>s<` | there is no trivia gap |
| `<n>` | the trivia gap contains a line break; the previous token and this position are on different source lines |
| `>n<` | the trivia gap contains no line break; the previous token and this position are on the same source line |

A line break inside skipped trivia counts, including inside a block comment.

Use them for these decisions:

- prefix, infix or postfix operator (`a-b`, `a - b`, `a⏎-b`),
- statement separators,
- a call or subscript at the start of a line.

At the end of the input, `<n>` is always true.

### 4.2 Token lookaround

| Form | True when |
|---|---|
| `>+>(…)` | a listed terminal can start at this position |
| `>->(…)` | no listed terminal can start at this position |
| `<+<(…)` | the previous token is a listed terminal |
| `<-<(…)` | the previous token is not a listed terminal |

`EOF` is a valid operand for `>+>` and `>->`. A lookaround is a node in the sequence. The
parser tests it at that position, also after a nonterminal.

```apus
plainRegularExpressionLiteral = … <-< ( … identifier … ")" "]" "}" closeAngle forceMark optionalMark … ) regexSlash … .
genericArgumentClause         = openAngle genericArgumentList ","? closeAngle
                                >+> ( "(" ")" "[" "]" "{" "}" "," ";" ":" "." keyPathDot "?" "!" "&" EOF ) .
```

The first rule is the regex-or-division decision. A regex can start only where the previous
token cannot end an operand.

### 4.3 Exclusion sets

`identifier ---("if" "while")` removes a match when a listed terminal matches the same text at
the same position. Use it to exclude a keyword from an identifier position.

## 5. The Oracle

### 5.1 Purpose

The parser keeps all derivations. The Oracle removes yields until one derivation remains. It
does not build trees.

### 5.2 Sequence

The Oracle (`Oracle.disambiguate`) does these steps:

1. Remove dead yields. A dead yield is not part of a complete derivation. Repeat until no yield
   changes.
2. Apply the hard constraints. Repeat until no yield changes.
3. Remove dead yields again.
4. Apply the preferences. Repeat until no yield changes.
5. Remove dead yields again.

Step 1 makes sure that each remaining yield is part of a complete derivation. Thus a later
rule cannot remove the only complete derivation by accident.

The hard constraints come before the preferences because a removal is permanent. A preference
must not remove a reading that a constraint makes the only legal reading.

### 5.3 Hard constraints

A hard constraint removes a reading that the language does not permit.

| Annotation | Position | Rule |
|---|---|---|
| `@cannotParse(N)` | start of an alternate | Remove the alternate where a yield of `N` starts at the same position. |
| `@canParse(N)` | start of an alternate | Remove the alternate where no yield of `N` starts at the same position. |
| `@confinedTo(N)` | start of an alternate | Keep the alternate only where a yield of `N` contains its span. |
| `@excludedFrom(N)` | start of an alternate | Remove the alternate where a yield of `N` contains its span. |
| `@sameLine` | before a nonterminal | Keep the yield only if a surviving derivation crosses no newline trivia. |

Details:

- `N` is a nonterminal.
- `@canParse` and `@cannotParse` read the yields of `N` before step 1. Thus a yield of `N`
  counts also when its own derivation fails later. This is the same as a speculative
  `canParseX` test in swift-syntax.
- `@cannotParse(A B)` means: neither `A` nor `B` starts here. `@canParse(A B)` means: both start
  here.
- In `@confinedTo(A B)` the containers are alternatives: `A` or `B` must contain the span. Two
  annotations on one alternate must both be true.
- `@sameLine` is derivation-local. It tiles the candidate yield through the current BSR and inspects
  the exact terminal commits used by that tiling. Commits from dead or competing derivations do not
  count.
- For `@sameLine`, only token-to-token trivia gaps count. A newline inside a token (for example, a
  multiline string) does not count. A newline in the annotated construct's trailing trivia does not
  count either, because the construct did not cross it to reach another token.
- The parser must try `N` at the anchor position of `@canParse(N)` or `@cannotParse(N)`. If the
  grammar never tries `N` there, `N` has no yield there, and `@cannotParse(N)` is always true.
  This is a specification error, not a false result. `GrammarDiagnostics` reports a target that
  no reachable production uses. It cannot find all such errors.

Examples:

```apus
statement      = @cannotParse(declaration attributes) expression .
declaration    = @confinedTo(enumMember structMember classMember actorMember protocolMember extensionMember) enumCaseDeclaration .
moduleSelector = @excludedFrom(valueBindingPattern) identifierToken "::" >n< .
```

To use a token or layout fact with a containment rule, put the gate in a nonterminal. The
parser then checks the gate, and the Oracle queries only the yields:

```apus
closureExpression     = samelineOpenedClosure
                      | @excludedFrom(conditionExpression) @excludedFrom(trailingClosures)
                        newlineOpenedClosure .
samelineOpenedClosure = "{" >n< closureSignature? statements? "}" .
newlineOpenedClosure  = "{" <n> closureSignature? statements? "}" .
```

### 5.4 Preferences

A preference selects among readings that are all legal. Each ambiguity differs in one of
three properties. Each preference controls one property.

| Property | What is different | Annotation | Rule |
|---|---|---|---|
| Extent | the length, from the same start | `@longest` / `@shortest` | Keep the longest / shortest span. |
| Pivot | the pivot `k`, for the same span `(i, j)` | `@left` / `@right` | Keep the largest / smallest pivot. |
| Alternate | the alternate, for the same span `(i, j)` | `@prefer` / `@avoid` | Keep the preferred alternate. |

#### Extent: `@longest` and `@shortest`

Put the annotation before a nonterminal definition or before a bracket:

```apus
@longest
prefixExpression = @shortest [ prefixOperator >s< ] postfixExpression .
```

Here `@longest` applies to `prefixExpression`, and `@shortest` applies to the bracket.

- On a nonterminal, the rule compares all yields from the same start.
- On a bracket, the rule compares the length of the bracket in complete derivations of the
  enclosing alternate. Other symbols in the alternate can take the remaining text. The start
  of the bracket can move.
- `@shortest [ X ]` prefers to skip `X`. If the skip does not parse, it prefers the shortest
  match of `X`.

The rule compares the length `j − k`, not the end `j`.

#### Pivot: `@left` and `@right`

Put the annotation before a nonterminal definition or before a group:

```apus
S = @left ( E "+" E | atom ) .
```

`@left` keeps the largest pivot for each span. `@right` keeps the smallest pivot for each span.

#### Alternate: `@prefer` and `@avoid`

Put the annotation at the start of an alternate:

```apus
dictionaryLiteralElement = @prefer expression .
dictionaryLiteralElement = typeExpression .
S = A | B | C | @avoid D .
```

- `@prefer A` removes a sibling where `A` covers the same span `(i, j)`.
- `@avoid D` is the same as `@prefer` on all siblings of `D`.
- The rule compares exact spans. It does not prefer a longer alternate. Use `@longest` for
  that.
- The annotated alternate must not be empty. The rule uses its last body symbol.
- These annotations work at each alternate chain: a nonterminal, a group `( )`, `[ ]`, `{ }` or
  `< >`.

`[ @avoid X ]` as the first item in `[ ]` or `{ }` is a different rule. It prefers to skip `X`
when the enclosing span `(i, j)` is the same. It keeps the smallest pivot on the symbol after
the bracket. `@shortest [ X ]` compares the bracket from its start and ignores the next symbol.
Thus `[ @avoid X ]` removes fewer readings.

### 5.5 The limit of the Oracle

The Oracle selects from derivations that completed. It cannot keep a derivation that died
during the parse.

swift-syntax is a deterministic parser. At each decision it selects one alternative with a
local test. It does not go back. If the selected alternative fails, the input is an error, also
when a different alternative can parse.

APUS keeps all alternatives. Thus APUS can accept input that swift-syntax rejects. You cannot
fix this with a preference, because the correct reading is not in the forest. Use one of these
tools:

- A structural change to the grammar, so the wrong derivation does not exist.
- A parser gate at the decision position.
- A commit with a local test, as `@preempt(X, N)` does for the extent of a token.

Keep the grammar strict. Make the local test match the test in swift-syntax. That test can be
weaker than a full parse.

## 6. Operator precedence

Operator precedence is not an ambiguity in `Swift.apus`. The expression grammar is a flat
chain:

```apus
infixExpressions = infixExpression infixExpressions? .
```

This chain has one derivation. The AST generator builds the precedence tree from precedence
metadata. swift-syntax does the same (`SequenceExprSyntax` and then `SwiftOperators`).

In a left-recursive grammar (`E = E "+" E | …`), precedence is an ambiguity. Use `@left` or
`@right` for it.

## 7. Which tool to use

| Problem | Tool |
|---|---|
| keyword inside an identifier; `&&`, `<<` | `@literalMunch` |
| `>>` in generics; `??` in types; `.?` in key paths | munch-exempt terminal |
| `^^/regex/`; an operator before a generic `<` | `@preempt` |
| prefix, infix or postfix operator; newline continuation; call at line start | boundary predicate |
| regex or division; generic-argument follow set | token lookaround |
| keyword in an identifier position | `---(…)` |
| a construct that is valid only in a context (swift-syntax `ExprFlavor`) | `@confinedTo` / `@excludedFrom` |
| a swift-syntax `atStartOfX` or `canParseX` decision | `@canParse` / `@cannotParse`, or token lookaround |
| the same span, two alternates | `@prefer` / `@avoid` |
| the same start, two lengths | `@longest` / `@shortest` |
| the same span, two pivots | `@left` / `@right` |
| a span that must stay on one line | `@sameLine` |

## 8. Categories of ambiguity

Find the category first. Each category has a different fix. The wrong fix can hide the real
problem.

| Category | Sign | Fix |
|---|---|---|
| redundant alternate | two alternates have the same body | Remove one alternate. |
| terminal overlap | two terminals match the same text | Correct the terminal. |
| one alternate must always win | the same span, a fixed winner | `@prefer` |
| alternate is too wide | for example, `expression` against `type` | Make the alternate smaller or add a context rule. |
| pivot | two pivots for the same span | Examine the boundary. The cause is often a terminal, a `>s<` or a lookaround. |

## 9. Procedure: fix an ambiguity

A **signature** identifies one ambiguity independently of the position:

    (ambiguous node, diagnostic kind, sorted competing-alternate bodies)

All tests with the same signature have the same cause. One fix clears all of them.

1. Set `SWIFT_DETERMINISTIC_HASHING=1` for all test runs.
2. Run the binary with `APUS_SIG_DUMP=1`. It writes one line for each residual ambiguity:
   `SIG <TAB> message-index <TAB> fingerprint`. The message index starts at 0.
3. Group the lines by signature. Start with the signature that has the most tests.
4. Make a minimal input that shows the ambiguity. Print the source text of the span. Do not
   trust only the mapping from an index to a test name.
5. Find the category (section 8).
6. Find the swift-syntax function that parses the same construct. Read how it makes the
   decision.
7. Select the tool (section 7). Prefer a structural change to an annotation.
8. Apply the fix.
9. Make sure that the ambiguity is gone, that acceptance did not change and that `treesMatch`
   did not become worse.
10. Run the full test suites.

To see which rule removed which yield, set `APUS_TRACE_ORACLE=1`.

## 10. Rules

**Oracle annotations run after recognition.** They do not change which descriptors run or which raw
yields the parser initially produces, but hard constraints can remove the last surviving derivation
for invalid input. Use grammar gates when an early parser decision is required. For example,
`keyPathExpression` is an alternate of `prefixExpression` and not of `primaryExpression`. Thus a
postfix operation cannot use a key path as its base.

**`@longest` selects only from complete derivations.** Step 1 removes a long reading that does
not complete. `@longest` cannot then select it. Use a parser gate, for example
`typeName >-> ( openAngle )` in `keyPathRootBase`.

**"Accepts" has two meanings.** `adventAcceptsFile` tests the yields before the Oracle.
`runAdventOnce` tests the tree after the Oracle. The accept and reject suites use
`runAdventOnce`. The difference (`oraclePruned`) shows input that the Oracle rejects but the
grammar accepts.

**Maximal munch can remove a literal from a lookaround set.** If a longer `@literalMunch` token
can start with the literal, the literal never matches there. Add the munch-exempt terminal next
to the literal. Example: `genericArgumentClause` lists `"."` and `keyPathDot`.

**The literal and the munch-exempt terminal have different meanings.** `forceMark` is a postfix
force-unwrap. The literal `"!"` is the mark in `try!`. The regex gate lists `forceMark` and not
`"!"`. Thus `x!/y/` is a division and `try! /re/` is a regex.

**A munch exemption changes only how the mark matches.** Also examine the gates on the next
symbol. `x as!~C` needs `forceMark optionalMark` in the gate before `~`:

```apus
suppressedType = <s> "~" >s< type
               | <+< ( "(" "[" "{" "," ";" ":" "as" "is" forceMark optionalMark ) >s< "~" >s< type .
```

**Gate the incorrect shape. Do not require trivia everywhere.** `"try" <s>` stops `try!-f()`, but
it also rejects `try(f())`, `try[0]` and `try.f()`. Name the incorrect shape:

```apus
tryOperator = "try" <s>
            | "try" >s< >-> ( forceMark optionalMark )
            | "try" >s< "?"
            | "try" >s< "!" .
```

**Use one terminal for each reading.** A terminal regex must describe only its own tokens. Do
not exclude characters from a regex so that a different terminal wins. That change moves
failures to other tests.

**Test for ambiguity, not only for acceptance.** An alternate that has the same extent can keep
all accept and reject results and add an ambiguity. Only the ambiguity test finds it.

**A correct rule can be unreachable.** Put a rule on the nonterminal that the parser reaches at
that position. For example, `<s> forceMark` is on `keyPathPivotFirst`, not on `keyPathPivot`. A
test that enumerates inputs finds this problem. A review of the grammar does not.

## 11. Example: Swift slash regex literals

The character `/` starts a regex literal and is also an operator character. swift-syntax
decides in its lexer (`RegexLiteralLexer.swift`, `Cursor.swift`). It uses four checks in this
sequence. If a check rejects the regex, the lexer does not do the next checks.

| swift-syntax check | Rule | APUS equivalent |
|---|---|---|
| left-bound | No regex if `/` touches the previous character, except after whitespace, `(` `[` `{` `,` `;` `:` or `*/`. | No separate check. The previous-token gate covers it. |
| `func` / `operator` | No regex after `func` or `operator`. | `"func"` and `"operator"` are in the previous-token gate. |
| `try?` / `try!` | Regex after `try?` and `try!`. | The gate lists `forceMark` and `optionalMark`, not the literals `"!"` and `"?"` that `tryOperator` uses. |
| previous token (`isInRegexLiteralPosition`) | No regex after a token that ends an operand. | `<-<( … )` on `plainRegularExpressionLiteral`. |

Tokens that end an operand: identifiers, numeric literals, `true` `false` `nil` `self` `Self`
`super` `Any`, a regex literal, `_`, `)` `]` `}` `>`, a postfix `!` or `?`, `->`, `...`, `.` and
`@`.

The APUS design:

- **`/…/` is a nonterminal, not a terminal.** `plainRegularExpressionLiteral` is a CFG. The CFG
  balances `( )` and `[ ]` in the body. Thus a malformed span such as `/E.e).foo(/` in
  `(/E.e).foo(/0)` is not a regex. A single regex terminal cannot do this balance.
- **One delimiter terminal.** `regexSlash - /\// .` is the opening and the closing `/`. It is
  munch-exempt. Thus an operator token cannot take it.
- **Operator characters in the body are regex terminals.** `regexOperatorChar` matches them. A
  shared operator literal is not used, because operator maximal munch can then take body text.
- **The opening gate.** On the same line, the previous-token gate applies. After a newline, the
  regex is at the start of an expression, and no gate applies.
- **Single line.** Each junction in the body has `>n<`. A plain regex cannot cross a newline.
- **No literal tab.** A lookahead gate (`>-> ( tabbedPlainRegularExpressionLiteral )`) rejects a
  body with a literal tab.
- **`#/…/#` is one token.** The number of `#` characters fixes the closing delimiter. Thus the
  extended form is not ambiguous and does not need a CFG.
- **A regex after a prefix operator.** `@preempt(regexSlash, tryScanOperatorAsRegexLiteral)` on
  `nonArrowOperatorToken` splits `^^/regex/` into `^^` and `/regex/` (section 3.3).

Rule: use a CFG for an ambiguous delimiter (`/`). Use a terminal for a delimiter that is not
ambiguous (`#/…/#`). If the "after a regex" position is in a gate list, name the closing
terminal `regexSlash`, because the regex is a nonterminal.

## 12. Background: predicates in swift-syntax and in other parsers

### 12.1 The swift-syntax `Lookahead` module

swift-syntax is a recursive-descent parser. At many decisions it calls a predicate. The
predicate copies the parser state, parses ahead on the copy, returns a `Bool` and discards the
copy (`SwiftParser/Lookahead.swift`). Some predicates call other predicates.

| File | Predicates |
|---|---|
| `Attributes.swift` | `canParseCustomAttribute` |
| `Declarations.swift` | `atStartOfFreestandingMacroExpansion`, `atStartOfDeclaration`, `atStartOfActor`, `atStartOfUsing` |
| `Expressions.swift` | `atStartOfExpression`, `canParseNonisolatedAsSpecifierInExpressionContext`, `atStartOfLabelledTrailingClosure`, `canParseClosureSignature`, `atStartOfPostfixExprSuffix` |
| `Lookahead.swift` | `atStartOfGetSetAccessor` |
| `Patterns.swift` | `canParsePattern`, `canParsePatternTuple` |
| `Statements.swift` | `isStartOfReturnExpr`, `atStartOfStatement`, `atStartOfSwitchCase`, `atStartOfConditionalSwitchCases`, `atStartOfConditionalStatementBody` |
| `Types.swift` | `canParseType`, `canParseTypeAttributeList`, `canParseTypeScalar`, `canParseSimpleOrCompositionType`, `canParseSimpleType`, `canParseStartOfInlineArrayTypeBody`, `canParseInlineArrayTypeBody`, `canParseCollectionTypeBody`, `canParseTupleBodyType`, `canParseFunctionTypeArrow`, `canParseTypeIdentifier`, `canParseAsGenericArgumentList`, `canParseIntegerLiteral`, `canParseGenericArgument` |

In APUS, the equivalent of such a predicate is a structural grammar rule, a parser gate, or an
Oracle constraint (section 7).

Most `atStartOfX` predicates route to the richer reading when it is possible. In APUS, put the
annotation on the fallback reading, for example `statement = @cannotParse(declaration
attributes) expression .`

### 12.2 Example: `Array<Array<Int>>`

As a CFG, the TSPL grammar gives four derivations for `Array<Array<Int>>`:

1. `Array` with the generic argument clause `<Array<Int>>`.
2. `Array < (Array<Int>) >`: infix `<`, then postfix `>`.
3. `Array < Array < Int >>`: infix `<`, infix `<`, then postfix `>>`.
4. `Array < (Array < Int >) >`: infix `<`, infix `<`, postfix `>`, postfix `>`.

swift-syntax selects derivation 1 with `canParseAsGenericArgumentList`:

```swift
mutating func canParseAsGenericArgumentList() -> Bool {
  guard self.at(prefix: "<"), !self.at(prefix: "<>") else { return false }
  var lookahead = self.lookahead()
  guard lookahead.consumeGenericArguments() else { return false }
  return lookahead.currentToken.isGenericTypeDisambiguatingToken
}
```

The predicate does two checks:

1. It parses `<…>` as a generic argument list on a copy. If this fails, the result is false.
2. The token after the closing `>` must be in a follow set: `)` `]` `{` `}` `.` `,` `;` `:` `!`,
   a postfix `?`, `&`, the end of the input, or `(` or `[` that is not at the start of a line.

In APUS, `closeAngle` is munch-exempt, so `>>` can close two clauses (section 3.2). The follow
set is the `>+>` gate on `genericArgumentClause` (section 4.2).

### 12.3 Predicates in other parsers

- **PEG** (Ford, POPL 2004). `&E` is true if `E` matches here. `!E` is true if `E` does not match
  here. Neither consumes input. Ordered choice makes a PEG parser deterministic.
- **ANTLR** (Parr & Quong 1995; Parr, PLDI 2011). A syntactic predicate `(α)=>β` parses `β` only
  if `α` matches here. A semantic predicate `{p}?` is a Boolean test on the parser state.
- **GLL.** The GLL papers (Scott & Johnstone 2010, 2016, 2019) do not define syntactic predicates.
  Afroozeh (*Practical General Top-Down Parsers*, 2018, §1.4) uses `List<List<T>>` as an example
  and applies declarative filters after the parse. The APUS Oracle uses the same approach.
- **Other general parsers.** Elkhound (McPeak 2002) is a GLR parser with user disambiguation
  functions. DParser (Plum 2005) is a scannerless GLR parser with `&` and `!` lookahead. Marpa
  (Kegler) is an Earley parser with events.

In a parser that keeps all derivations, the answer to "can `N` parse here?" is often already in
the BSR. The Oracle constraints `@canParse` and `@cannotParse` read it there (section 5.3).

## 13. Code

| File | Contents |
|---|---|
| `Lexer.swift` | `OnDemandLiteralLexer.lex`: `@literalMunch`, the `@preempt` split points |
| `MessageParser.swift` | `tokenMatch`: the `@preempt` commit, `---()`; `boundaryMatches`: boundary predicates and token lookaround |
| `Oracle.swift` | `disambiguate`; the rules `LongestMatchRule`, `ShortestMatchRule`, `LeftAssocRule`, `RightAssocRule`, `PreferRule`, `AvoidOptionalRule`, `LookaheadPredicateRule`, `ContainmentRule`, `SameLineSpanRule` |
| `DerivationBuilder.swift` | builds the tree and reports residual ambiguity with a fingerprint |
| `ApusApusTests/OracleDisambiguationTests.swift` | tests for each Oracle rule |

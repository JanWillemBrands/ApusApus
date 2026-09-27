# Lexical Disambiguation Tools

APUS's language-neutral tools for deciding what a character sequence means when the same
text can be tokenised or read in more than one way. Swift is the driving example, but none
of the tools is Swift-specific. Syntax reference: `apus.md`. Oracle internals: `Oracle.md`.

## The problem

A character or token means different things depending on **context** or **adjacency**:

| case | example |
|---|---|
| keyword vs longer identifier | `for` inside `foreach` |
| multi-char operator vs its pieces | `&&`, `<<`, `==` |
| operator that must split | `>>` → `>` `>` (nested generics), `??` → `?` `?` (`Int??`) |
| operator vs following regex | `^^/regex/` → `^^` + `/regex/` |
| regex delimiter vs division | `/abc/` vs `a / b` |
| operator prefix / infix / postfix | `a-b` vs `a - b` vs `a⏎-b` |
| newline: separator vs continuation | `a⏎-b` (two statements) vs `a - b` |
| call `(` / subscript `[` at line start | `g()⏎(x)` (two statements) vs `g()(x)` |

Every case is resolved along one or both of two axes:

1. **Extent**: how far a token reaches. Longest match (maximal munch) by default, or a
   declared shorter reading.
2. **Context**: where the token sits.
   - **adjacency**: the trivia gap and the neighbouring tokens,
   - **grammar position**: which slot the parser is in (grammar structure),
   - **priority**: which of two same-span readings wins.

The lexer is parser-driven (LCNP, Scott & Johnstone, *Multiple Lexicalisation*, SLE 2019):
the parser asks `lex(pos, terminal)` only for the terminals it predicts, and each terminal
answers with its own longest match within its own sublanguage. Most of the tools below
adjust that per-terminal answer or filter it by context.

## Extent tools

### 1. Maximal munch across terminals: `@literalMunch`

```apus
@literalMunch
identifier              - @builder .
@literalMunch @preempt(regexSlash, tryScanOperatorAsRegexLiteral)
nonArrowOperatorToken   - @builder .
@literalMunch
dotOperator             - @builder .
```

A **literal** terminal match is suppressed when any `@literalMunch` regex terminal has a
strictly longer match at the same start: `for` inside `foreach`, `_` inside `_foo`, `&`
inside `&&`. The check is a runtime prefix-match of the declared regex
(`OnDemandLiteralLexer.lex`, `Lexer.swift`). Suppression applies to literals only, and it is
not predict-gated: it fires whether or not the longer terminal is expected at this slot.

### 2. Munch-exempt terminals: single-character regexes

Because suppression only affects literals, a one-character terminal written as a **regex**
survives inside a longer operator:

```apus
regexSlash      - /\// .
openAngle       - /</ .
closeAngle      - />/ .
optionalMark    - /\?/ .
forceMark       - /!/ .
keyPathDot      - /\./ .
```

This is how `>>` closes two generic clauses (`Array<Array<Int>>`), how `Int??` gets two
optional marks, and how `\Foo.?` sees a key-path `.` in front of the `dotOperator` token `.?`.
The grammar position decides which spelling is used: a slot that must see the mark even
inside a longer operator uses the regex form, and a slot that must *not* match inside a
longer operator uses the literal.

### 3. Declared shorter extent: `@preempt(X[, N])`

```apus
@literalMunch @preempt(regexSlash, tryScanOperatorAsRegexLiteral)
nonArrowOperatorToken   - @builder .

@preempt(openAngle)
functionNameOperator    - @builder .
```

A terminal's maximal match must not swallow the start of something with higher priority.

- **`X` (offer):** besides its maximal match, the terminal also offers the prefix ending
  before each *internal* position where terminal `X` begins a non-empty match. A leading
  position is not a split point.
- **`N` (commit, optional):** among the offered shorter matches, keep the earliest one at
  whose end nonterminal `N` actually parses (a memoised speculative sub-parse) and drop all
  longer matches. If no offered split is viable, only the maximal match is kept. Without `N`
  the splits are merely offered and the grammar decides.

This ports swift-syntax's `tryLexOperatorAsRegexLiteral`: `^^/regex/` becomes `^^` +
`/regex/` when a regex scans, while `^/x` stays one operator. `functionNameOperator` uses the
offer-only form so that `func %%%<T>` yields the `<` back to the generic parameter clause.
Split points are keyed on a *terminal* rather than on every predicted terminal, so `a +++ b`
is never fragmented into `a ++ +b`.

Code: `TokenPattern.preemptStart` / `preemptConstruct` (`Scanner.swift`), the split loop in
`OnDemandLiteralLexer.lex`, and the commit in `MessageParser.tokenMatch`.

## Context tools

### 4. Boundary predicates: `<s>` `>s<` `<n>` `>n<`

Zero-width tests on the trivia gap at the current position: trivia present / absent, newline
present / absent. These are the workhorse. They resolve operator boundness (`a+b` / `a + b`
/ `a⏎-b`, where infix means symmetric gaps), statement separators, and call / subscript at
line start (`>n<`).

### 5. Token lookaround: `>+>(…)` `>->(…)` `<+<(…)` `<-<(…)`

Zero-width tests that some / no listed terminal (or `EOF`) occurs next / occurred just
before. They express swift-syntax's next-token and previous-token checks directly:

```apus
plainRegularExpressionLiteral = … <-< ( … identifier … ")" "]" "}" closeAngle forceMark optionalMark … ) regexSlash … .
genericArgumentClause         = openAngle genericArgumentList ","? closeAngle
                                >+> ( "(" ")" "[" "]" "{" "}" "," ";" ":" "." keyPathDot "?" "!" "&" EOF ) .
keyPathRootBase               = … | typeName typeGenericArgumentClause | typeName >-> ( openAngle ) | … .
```

The first is swift's regex-vs-division rule: a regex may start only where the previous token
is not an operand-ender.

### 6. Exclusion sets: `---(…)`

`identifier ---("if" "while")` drops a match when a listed terminal lexes the same extent at
the same position: the local "this keyword is not an identifier here".

### 7. Priority: Oracle annotations

When two readings cover the **same span**, extent and adjacency cannot tell them apart. The
Oracle chooses after parsing: `@prefer`, `@avoid`, `@longest`, `@shortest`, `@left`,
`@right`, plus the constraints `@confinedTo`, `@excludedFrom`, `@canParse` and
`@cannotParse`. For example, prefix operators are right-bound:

```apus
prefixExpression = @shortest [ prefixOperator >s< ] postfixExpression .
```

See `apus.md` (Oracle Preferences / Constraints) and `Oracle.md`.

## Which tool for which case

| case | tool |
|---|---|
| keyword inside identifier, `&&`, `<<` | `@literalMunch` |
| generic `>>`, optional `??`, key-path `.?` | munch-exempt regex terminal |
| `^^/regex/`, operator before a generic `<` | `@preempt` |
| operator prefix / infix / postfix, newline continuation, line-start call / subscript | boundary predicates |
| regex vs division, generic-argument follow set, key-path root | token lookaround |
| keyword excluded from an identifier slot | `---(…)` |
| genuine same-span ties | Oracle annotations |

## Rules for using the tools

These are properties of the tools, not of Swift, so they apply to any grammar.

**Oracle annotations affect trees, not yields.** They run after parsing, so they cannot say
"this must not parse". To exclude a derivation, change the structure. For example,
`keyPathExpression` is an alternate of `prefixExpression`, never of `primaryExpression`, so
no postfix operation can take a bare key path as its base. Likewise, `@longest` chooses only
among *viable* readings: the Oracle prunes dead derivations first, so a greedy reading that
leads to no complete parse is already gone. Use a parse-time gate instead
(`typeName >-> ( openAngle )` in `keyPathRootBase`).

**Two meanings of "accepts".** `adventAcceptsFile` is yield-level (before the Oracle);
`runAdventOnce` is tree-level and is what the accept / reject suites use. The difference,
reported as `oraclePruned`, is over-acceptance carried by the Oracle rather than excluded
structurally.

**A literal in a lookaround operand set is defeated by maximal munch.** If a longer
`@literalMunch` token can start with the literal, the literal never lexes there and the
lookaround never sees it. List the munch-exempt regex form beside it, as `genericArgumentClause`
lists `"."` and `keyPathDot`.

**Literal vs munch-exempt spelling is semantic, not stylistic.** `forceMark` is postfix
force-unwrap; the literal `"!"` is the mark in `try!`. The regex-start lookbehind lists
`forceMark` but not the literal `"!"`, so `x!/y/` stays division while `try! /re/` is a regex.

**A munch exemption only decides how the mark lexes.** Check the next symbol's gates too.
`x as!~C` needs `forceMark optionalMark` in the lookbehind that gates `~T`:

```apus
suppressedType = <s> "~" >s< type
               | <+< ( "(" "[" "{" "," ";" ":" "as" "is" forceMark optionalMark ) >s< "~" >s< type .
```

**Gate the specific shape rather than requiring trivia.** A blanket `"try" <s>` stops
`try!-f()` but also rejects `try(f())`, `try[0]` and `try.f()`. Name the bad shape instead:

```apus
tryOperator = "try" <s>
            | "try" >s< >-> ( forceMark optionalMark )
            | "try" >s< "?"
            | "try" >s< "!" .
```

The lookahead lists the munch-exempt marks (they lex even inside `!-`, so the gate fires);
the `try?` / `try!` alternates use literal marks (munch suppresses them before `?-` / `!-`,
leaving `try!-f()` with no derivation).

**Prefer distinct terminals over cross-terminal reservations.** A terminal's regex should
describe only its own sublanguage (for example, "a lone `!` is not an operator token"). A
regex that excludes characters so that *another* terminal wins moves failures around rather
than removing them. Give each reading its own terminal and let the grammar slot choose.

**Verify ambiguity, not just acceptance.** An alternate reachable at the same extent can
leave accept / reject results unchanged while making the parse ambiguous; only the
`isUnambiguous` check catches it. And a correct rule can be unreachable: put a rule on the
nonterminal that is actually reached at that position (for example, `<s> forceMark` belongs on
`keyPathPivotFirst`, not `keyPathPivot`). An enumerated sweep finds these; reading the grammar
does not.

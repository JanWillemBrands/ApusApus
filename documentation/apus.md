# APUS Language Reference

APUS is grammar language. You write grammar, parser read grammar, parser parse things.

APUS describe itself. Grammar file called `apus.apus`. Self-describing. Very elegant. Like snake eating tail.

Name come from *Apus apus* — the common swift. Bird that never land. Parser that never stop.

## Grammar File

Grammar file have two parts: productions, then messages.

```swift
grammar = < production > { message } .
```

First come productions. One or more. They define terminals and rules. Then come messages — zero or more test inputs, each starting with `^^^`.

Every production end with `.` — the full stop. You forget the dot, parser angry.

## Comments

```swift
// this is a comment
```

Comments start with `//` and run to end of line. APUS does NOT use `#` for comments. The `#` character not an APUS token. You use `#`, scanner scream.

## Productions

Three kinds of production. All start with a name.

### Silent Terminal (`:`)

```swift
whitespace : /\s+/ .
comment    : /\/\/.*/  .
```

Colon mean silent terminal. Scanner match it, scanner throw it away. Good for whitespace, comments. Parser never see these tokens.

Right side is regex or literal. Then dot.

### Visible Terminal (`-`)

```swift
identifier - /\p{XID_Start}\p{XID_Continue}*/ .
literal    - /\"(?:[^\"\\]|\\.)+\"/ .
number     - /[0-9]+/ .
```

Dash mean visible terminal. Scanner match it, scanner keep it. Parser see these tokens. Use for identifiers, numbers, string literals — things with meaning.

Right side is regex or literal. Then dot.

A visible terminal can also be a literal:

```swift
fBrace - "{" .
```

This give the literal `{` a name. Now you can write `fBrace` in production rules instead of `"{"`.

The name is the token *kind*, not an alias. So `fBrace` and a bare `"{"` written elsewhere are two different kinds that both match `{`. Same rule as for a named regex terminal — see "Token kinds" below.

### Production Rule (`=`)

```swift
S = "hello" "world" .
```

Equals sign mean production rule. Left side is nonterminal name. Right side is what it expand to. Then dot.

First production rule in file is the start symbol. Parser start there.

Same nonterminal can have multiple definitions — they merge:

```swift
S = "x" .
S = "x" "x" .
S = "x" "x" "x" .
```

This make S match one, two, or three x's.

## Terminals in Rules

### Literals

```swift
S = "hello" "world" .
```

Double-quoted strings. Match exact text. Literals use Swift string escape conventions — `"\t"` match a tab, `"\\"` match a backslash, `"\/"` match a single slash.

### Regex

```swift
number - /[0-9]+/ .
```

Forward-slash delimited. Swift regex syntax inside. Use in terminal definitions (`:` or `-` productions). Can also appear inline in rules, and then the kind is the pattern itself — see "Token kinds" below.

### Token kinds

One rule, both shapes:

- **Named** — define a token with `-` or `:`, and the LHS *is* the kind. `number - /[0-9]+/ .` gives kind `number`; `fBrace - "{" .` gives kind `fBrace`.
- **Anonymous** — write a literal or regex inline in a rule, and the kind is its own pattern *including the delimiters*: `"while"` gives kind `"while"`, `/[0-9]+/` gives kind `/[0-9]+/`.

Two consequence follow. Anonymous tokens with the same pattern share one kind, so `"{"` written in ten rules is one terminal. And a named token never merge with an anonymous one, so you can give the same text two kinds on purpose — `regexOpenSlash - /\// .` and `regexCloseSlash - /\// .` are distinct kinds, which is how a grammar tell apart two roles of one character.

The delimiters are load-bearing: they keep anonymous kinds in a namespace disjoint from bare names, so a rule referring to `operator` can never collide with the literal `"operator"`.

Named regex terminal can be referenced by name in rules:

```swift
shift - />>/ .
S = shift "other" .
```

Here `shift` in the rule resolve to the regex terminal.

### Identifiers

```swift
S = A B .
A = "a" .
B = "b" .
```

Bare name in a rule is either a nonterminal reference or a terminal reference. If the name was defined as a terminal (`:` or `-`), it resolve as terminal. Otherwise it is a nonterminal. Nonterminal get defined when it appear on the left side of `=`.

### Epsilon

Two ways to say nothing:

```swift
S = "a" | ε .
S = "a" | "" .
```

The Greek letter `ε` and the empty string literal `""` both mean epsilon — match zero tokens. Good for optional things.

## Selection (Alternation)

```swift
selection = sequence { "|" sequence } .
```

Vertical bar separate alternatives:

```swift
S = "a" | "b" | "c" .
```

S match `a` or `b` or `c`. GLL parser explore all alternatives — even ambiguous ones. This not LL(1) parser. This GLL. All paths explored.

## Sequence

```swift
sequence = < factor [ "?" | "*" | "+" ] > .
```

Things next to each other in a rule match in order:

```swift
S = "a" "b" "c" .
```

Match `a` then `b` then `c`.

## EBNF Brackets

APUS support four kinds of bracket:

### Grouping `( )`

```swift
S = "a" ( "b" | "c" ) "d" .
```

Parentheses group alternatives. Match `abd` or `acd`.

### Option `[ ]`

```swift
S = "a" [ "b" ] "c" .
```

Square brackets mean zero or one. Match `ac` or `abc`.

### Kleene Closure `{ }`

```swift
S = "a" { "b" } "c" .
```

Curly braces mean zero or more. Match `ac`, `abc`, `abbc`, `abbbc`, ...

### Positive Closure `< >`

```swift
S = "a" < "b" > "c" .
```

Angle brackets mean one or more. Match `abc`, `abbc`, `abbbc`, ... but NOT `ac`.

## Postfix Repetition Operators

Same three repetition ideas, but postfix style:

```swift
S = "a" "b"? "c" .     // "b" zero or one time
S = "a" "b"* "c" .     // "b" zero or more times
S = "a" "b"+ "c" .     // "b" one or more times
```

`?` is option, `*` is zero-or-more, `+` is one-or-more. Same as brackets but stick after a single factor. Good for compact rules.

## Messages (Test Inputs)

```swift
^^^
hello world
^^^
goodbye world
```

Triple caret `^^^` start a message block. Everything between `^^^` markers (or between `^^^` and end of file) is captured as test input. Parser use these to test the grammar.

Do NOT put comments between `^^^` blocks. Comments become part of message content. Message capture everything.

## Pragmas And Annotations

APUS annotations are position-typed. An `@...` token is not a grammar item by itself;
its meaning comes from where it appears.

```text
Lookaround and layout are zero-width sequence predicates.
They sit between grammar items and consume no input.
```

```text
Oracle annotations choose or prune parse-forest alternatives.
They attach to nonterminals, bracket nodes, or alternates.
```

```text
Terminal pragmas configure lexical recognition.
They belong on terminal definitions, not arbitrary rules.
```

## Actions

``` swift
S = 'init' "x" 'process' { "y" 'accumulate' } 'finalize' .
```

Single-quote delimited blocks are actions — code fragments attached to grammar positions. They are silent terminals (scanner strips them from the visible token stream) and get stored on grammar nodes for code generation.

Actions can appear before the first production (preamble), between the nonterminal name and `=` (signature), between grammar symbols, and after the last production (epilogue).

---

## Oracle Preferences

`@prefer` and `@avoid` are alternate-level only. They may occur only at the start
of an alternate, immediately after `=`, `|`, `(`, `[`, `{`, or `<`.

```swift
S = @prefer A | B .
S = ( @prefer A | B ) .
S = [ @avoid modifier ] name .
```

Meaning:

```text
@prefer = this alternate wins over same-span siblings.
@avoid  = this alternate loses to same-span siblings.
```

Inside `[ ... ]` and `{ ... }`, `@avoid` also competes with the implicit empty
branch. That is why `[ @avoid X ]` means "prefer the skip when the skip still
parses".

`@longest` and `@shortest` are node-level. They may occur before a nonterminal
definition or before a bracketed group.

```swift
@longest expression = prefixExpression { infixOperator prefixExpression } .
S = @shortest [ modifier ] name .
S = @longest { word } .
```

Meaning:

```text
@longest/@shortest = choose maximal/minimal extent for this node.
```

`@left` and `@right` are ALTERNATE-level, in the same position as `@prefer`/`@avoid`.
They say that a production may not be nested directly inside ITSELF:

```swift
E = @left E "+" E | number .        // `1+2+3` is `(1+2)+3`
E = ( @right E "+" E | number ) .   // `1+2+3` is `1+(2+3)`
```

```text
@left  = this production may not be its own RIGHTMOST child.
@right = this production may not be its own LEFTMOST child.
```

Read `@left` as "the left side wins, so the right side may not grow": in `1+2+3`
the reading `1+(2+3)` puts a `+` inside the right slot of a `+`, and `@left`
removes it. `@right` is the mirror image.

This is associativity as SDF states it — a per-production attribute (`{left}`,
`{right}`) that deletes a forbidden parent/child shape — rather than a choice
between competing pivots of one span. The difference matters when the two readings
have DIFFERENT spans, i.e. when one instance is nested inside another rather than
rivalling it:

```swift
x.map {} {}      // the outer closure-call's left child IS a closure-call → removed
x.map {}.filter {}.sorted {}   // children are member accesses → all three kept
```

A pivot choice cannot reach that, because the inner and outer instances start at
the same place but end differently, so there is no single span with two pivots.

Both take an optional list of nonterminals. The bare form forbids the production
in that child position; the list form forbids the NAMED nonterminals there:

```swift
f = @right( literalExpression ) postfixExpression trailingClosures .
//  ↑ the callee may not be a bare literal, so `1 {}` is not a call
```

Several may stack on one alternate, so the same child position can forbid both
the production itself and a listed nonterminal:

```swift
functionCallExpression = @right @right( literalExpression )
                         postfixExpression trailingClosures .
```

The match is on EXTENT: the child is removed when its span is exactly the span of
one of the named nonterminals. That is usually what you want, because it
distinguishes a bare construct from one that has grown. The callee of `1 {}`
spans exactly the literal `1`, so it is removed; the callee of `1! {}` or
`1.description {}` spans more than any literal, so it survives. Writing the
exclusion as its own nonterminal (a copy of `postfixExpression` with the literal
alternates removed) gets the same result but costs a clone that drifts from its
original.

Associativity across DIFFERENT productions — `+` and `-` of one precedence level
being mutually left-associative — is a separate mechanism (in SDF, a priority
relation over a set of productions) and is not expressible with these two.

`@avoid` and `@shortest` are different primitives. They can overlap in simple
optional-skip cases, but they are not synonyms:

```swift
[ @avoid X ]      // alternate X loses to siblings and to the implicit skip
@shortest [ X ]   // the optional node minimizes its consumed extent
```

## Parser Modes

Parser modes are inherited parser context: the flavor or state parameters a handwritten
parser passes down (swift-syntax `ExprFlavor`, `allowInitDecl`, pattern context). An
occurrence annotation changes or tests the mode for that occurrence only; the caller's
continuation keeps the caller's mode.

```swift
@setMode(foo bar) X       // parse X with foo and bar active
@clearMode(foo bar) X     // parse X with foo and bar inactive
@requiresMode(foo bar) X  // keep this path only when all listed modes are active
@rejectsMode(foo bar) X   // reject this path when all listed modes are active
```

`@setMode` and `@clearMode` are set operations. Modes not named by the annotation
are preserved. Tests see the occurrence's mode after its own `@setMode`/`@clearMode`.

### Scopes: `@carries`

Every mode is scoped. `@carries(m …)` at the start of a production declares that the
modes `m …` pass into that nonterminal. An inherited bit enters an occurrence of `Y` only
if `Y` carries it; entering any other nonterminal drops the bit, the way a swift-syntax
parameter disappears when a function does not forward it. Production pragmas may appear in
any order; `@carries` may repeat, and when a nonterminal is defined in several places, the
lists union.

```swift
@carries(stmtCondition) conditionExpression = effectfulConditional coercingOperator? .
@carries(stmtCondition) postfixExpression = … .
@carries(stmtCondition trailingClosure) closureExpression =
    samelineOpenedClosure | @rejectsMode(stmtCondition trailingClosure) newlineOpenedClosure .

condition = @setMode(stmtCondition) conditionExpression | … .
```

Nothing has to clear `stmtCondition` at call arguments or closure bodies:
`functionCallArgument` and the closure productions do not carry it, so the mode stops there.
Keep `@clearMode` for a boundary INSIDE a scope (`statements` clears `ifConfigBody` after
the first statement).

Grammar load checks the declarations and fails on:

- a mode used in an annotation that no production `@carries`;
- `@setMode(m) Y` where `Y` does not carry `m`;
- a `@requiresMode`/`@rejectsMode` test on a mode that can never be present there.

It reports (in `Grammar.parserModeReport` and the grammar log) the copies each mode costs,
`@clearMode`s with no effect, and every SCOPE EXIT: an edge where a carried mode is dropped
although the callee could still reach a test of it. Exits are expected at intended
boundaries; an unexpected one means a scope that is too small.

### How modes run

Modes cost nothing at parse time. `Grammar.specializeParserModes()` compiles them into the
grammar at load: each nonterminal reached under a mode that matters to it gets a copy
`X⟨m⟩`, mode tests are decided statically in each copy, and the parser sees an ordinary
grammar (no mode in descriptors, CRF keys or BSR yields). Copies keep their `name`, so
converter and builder lookups are unaffected; code that looks a nonterminal up BY NAME to
read its yields uses `grammar.instances(of:)`. The cost is proportional to the declared
scopes (Swift: 94 copies of 465 productions). See `Parser Modes Specialization.md`.

Use modes for occurrence-local context that a handwritten parser would carry as a
flavor or state parameter. Do not use them as a replacement for ordinary grammar
structure when a separate nonterminal is clearer.

### Named Positions

A short alias can still be the cleanest way to name a grammar position or attach
a mode to a reused shape:

```swift
ifConfigStatements = @setMode(ifConfigBody) statements .
initializerBody    = @setMode(initializerBodyMode) codeBlock .
```

Do not "simplify" such a rule away by inlining it when anything depends on the
name or the annotated occurrence. The same holds for names the AST converter
resolves by lookup (`structName`, `argumentLabel`, `tupleMatchLabel`, …):
re-pointing one is invisible to the parser and silently drops a child from the tree.

The test for whether an identical-bodied rule is a sentinel or real duplication is
whether anything depends on the NAME. If nothing does, delete it and repoint the uses
(the six `<kind>Members` lists and five `<kind>Body` rules went that way on
2026-09-30); if an annotation or a converter lookup does, keep it and say so in a
comment.

`@canParse(N)` and `@cannotParse(N)` with nonterminal operands are also Oracle constraints:

```swift
statement = @cannotParse(declaration attributes) expression .
```

Meaning:

```text
@canParse(N)    = this alternate is valid only where N can parse here.
@cannotParse(N) = this alternate is invalid where N can parse here.
```

This is a parse-forest predicate, not a token lookaround. A coherent grammar should
keep this separate from token lookaround.

"Can parse HERE" means N has a yield STARTING at this position; it does not require N
to cover the alternate's span. The target set is `Set(parser.yield(of: N).map(\.i))`,
snapshotted from the RAW forest before dead-wood pruning.

The target must therefore be REACHABLE from the start symbol. A nonterminal written
purely as a recogniser for a predicate, referenced by nothing else, is never attempted
by the parser: its yield set is empty, so `@canParse` is always false and
`@cannotParse` always true. These predicates can only interrogate parses the grammar
already attempts for their own sake — they are not a way to run an arbitrary
side-grammar as a lookahead.

`@sameLine` is a nonterminal-level hard constraint. It occurs before a nonterminal
definition, in the same production-start position as `@longest`.

```swift
@sameLine
singleLineInterpolatedStringLiteral =
    interpolatedStringLiteralHead expression? interpolatedStringLiteralTail .
```

Meaning:

```text
@sameLine = keep a yield only when at least one surviving derivation crosses no newline trivia.
```

The check is over the actual token path for the yield, not over every token that
was ever committed in the same source span. This matters in ambiguous parses: a
dead derivation that crossed a newline must not poison a live same-line derivation.

Only token-to-token trivia gaps count. A newline inside token content, such as a
nested multiline string literal, does not count. A newline in the annotated
construct's trailing trivia also does not count, because the construct did not
cross it to reach another token.

Use `@sameLine` for constructs whose internal parse remains ordinary grammar, but
whose skipped trivia must stay on one source line. Swift single-line string
interpolation is the canonical example.

## Sequence Predicates

### Exclusion Sets `---()`

```swift
safeId = identifier ---("if" "while" "for" "return") .
```

Problem: scanner see `if` and produce two tokens of same length — keyword `if` and identifier `if`. These are Schrödinger tokens (same text, same length, different kinds). Parser explore both paths.

Sometimes you know: in this grammar position, `if` is NOT an identifier. The `---()` annotation say: suppress these specific Schrödinger duals here. Kill the bad branch locally.

The annotation goes after an identifier, literal, regex, or grouped factor in a
rule. List the literal values to exclude in parentheses.

### Layout Tokens `>>|` and `|<<`

```swift
block = >>| < statement > |<< .
```

For indent-sensitive languages (Python, Haskell). These are synthetic tokens injected between scanning and parsing:

- `>>|` — indent (column increased on new line)
- `|<<` — dedent (column decreased on new line)

They appear unquoted in grammar rules. When the grammar uses them, the layout injection pass activates automatically. It tracks indentation levels and inserts `>>|` or `|<<` tokens into the token stream. Bracket pairs (configurable) suppress indent tracking inside them.

### Layout Boundaries `<s>` `>s<` `<n>` `>n<`

```swift
prefixOperatorUse = operator >s< operand .
binaryOperatorUse = lhs <s> operator <s> rhs .
sameLine          = lhs >n< rhs .
nextLine          = lhs <n> rhs .
```

These are zero-width predicates over the trivia gap at the current parse position:

| Predicate | Meaning |
|---|---|
| `<s>` | there is a non-empty trivia gap between the previous token and this position |
| `>s<` | there is no trivia gap between the previous token and this position |
| `<n>` | the trivia gap contains a line break, so the previous token and this position are on different source lines |
| `>n<` | the trivia gap contains no line break, so the previous token and this position are on the same source line |

These predicates consume no input. They inspect the trivia gap skipped between the previous
committed token and the current parse position. A line break inside skipped trivia, including
inside a block comment, counts for `<n>` / `>n<`.

### Token Lookaround

Token lookaround is also a zero-width sequence predicate, allowed wherever layout
boundaries are allowed:

```swift
A = X >+>(")") Y .
A = X >->("(") Y .
A = X <+<(identifier) Y .
A = X <-<(operator) Y .
```

Meaning at that exact cursor position:

```text
>+>(...) = some listed terminal can occur after this position.
>->(...) = no listed terminal can occur after this position.
<+<(...) = some listed terminal occurred before this position.
<-<(...) = no listed terminal occurred before this position.
```

`EOF` is the explicit end-of-input operand for token lookahead:

```apus
A = X >+>(")" EOF) .
```

This is the implemented model: token lookaround is a zero-width sequence
boundary. Post-dot terminal-definition `<+<` / `<-<` is not a separate
annotation class; put lookaround where the production cursor should be tested.

## Terminal Pragmas

```swift
@literalMunch operator - /.../ .
@preempt(regexOpenSlash, regularExpressionLiteral) operator - /.../ .
regexLiteral - @builder(plainRegularExpressionLiteral) .
```

Terminal pragmas configure lexical recognition. They should be valid only on
terminal-like productions. Misplaced terminal pragmas should be grammar errors, not
inert annotations.

---

## Full Grammar

APUS is self-described by `apus.apus`. The shape below is the coherent
lookaround-boundary grammar.

```swift
whitespace  : /\s+/ .
comment     : /\/\/.*/  .
action      : /'(?:[^'\\]|\\.)*'/ .

identifier  - /\p{XID_Start}\p{XID_Continue}*/ .
literal     - /\"(?:[^\"\\]|\\.)+\"/ .
regex       - /\/(?!\*)(?:[^\/\\]|\\.)+\// .
pragma      - /@\p{XID_Start}\p{XID_Continue}*/ .

message     - /\^\^\^(?:(?s).*?)(?=\^\^\^|$)/ .

grammar     = < production > { message } .

production  = productionPragma* identifier ( ":" | "-" | "=" ) productionBody "." .

// `:` makes the LHS skipped trivia/token, `-` makes it an emitted token, and
// `=` makes it a grammar node. A direct terminal body uses the scanner fast path;
// a structured `:` body uses a trivia recognizer sub-parse, and a structured `-`
// body uses a lexical recognizer sub-parse that emits one token.
productionBody = terminalBody | selection .

terminalBody = regex | literal | "@builder" builderKey? .
builderKey   = "(" ( identifier | literal ) ")" .

selection   = sequence { "|" sequence } .

sequence    = alternateAnnotation* < sequenceItem > .

sequenceItem = layout
             | lookaround
             | factor [ "?" | "*" | "+" ] [ exclusion ]
             .

factor      = terminal
            | groupPragma* "[" selection "]"
            | groupPragma* "{" selection "}"
            | groupPragma* "<" selection ">"
            | groupPragma* "(" selection ")"
            .

terminal    = identifier
            | literal
            | regex
            | epsilon | empty
            .

epsilon     = "ε" .
empty       = "\"\"" .

layout      = ">>|" | "|<<" | "<n>" | "<s>" | ">n<" | ">s<" .
lookaround  = ( ">+>" | ">->" | "<+<" | "<-<" ) "(" < literal | identifier | "EOF" > ")" .
exclusion   = "---" "(" < literal > ")" .

productionPragma     = terminalPragma | nonterminalPragma .
terminalPragma       = "@literalMunch" | "@preempt" preemptArgs .
nonterminalPragma    = "@longest" | "@shortest" | "@sameLine" | carriesPragma .
carriesPragma        = "@carries" "(" < identifier > ")" .
groupPragma          = "@longest" | "@shortest" .
alternateAnnotation  = "@prefer" | "@avoid" | childPosition | parsePredicate .
modeAnnotation       = ( "@setMode" | "@clearMode" | "@requiresMode" | "@rejectsMode" ) "(" < identifier > ")" .
childPosition        = ( "@left" | "@right" ) [ "(" < identifier > ")" ] .
parsePredicate       = ( "@canParse" | "@cannotParse" ) "(" < identifier > ")" .
preemptArgs          = "(" identifier [ "," identifier ] ")" .
```

## Sample Grammar

A small calculator language:

```swift
whitespace : /\s+/ .
comment    : /\/\/.*/  .

number - /[0-9]+/ .

expr = term { ( "+" | "-" ) term } .
term = atom { ( "*" | "/" ) atom } .
atom = number
     | "(" expr ")"
     .

^^^
1 + 2 * (3 + 4)
^^^
42
^^^
(1 + 2) * (3 + 4)
```

## List spelling: closures, not right recursion

Lists in a grammar should be spelled with the native closures — `item { "," item }` for
zero-or-more repetitions of the tail, `< item >` for one-or-more — rather than as right recursion
(`list = item | item "," list`). As of 2026-09-21 `Swift.apus` has 17 lists in closure form; the
rules got 22% shorter and every one dropped from two alternates to one.

The AST builder is INDIFFERENT to the choice, but only through the shared helpers.
`collectListElements` / `listElements` / `listHops` in `GenerateSwiftSyntaxAST.swift` flatten both
spellings (they handle `.KLN` and `.POS` explicitly). A hand-rolled walker that recurses on
`find("<listName>")` does NOT: rewrite its rule as a closure and the tail lookup matches nothing,
so everything past the FIRST element is dropped silently, with no diagnostic. Before converting a
rule, check its collector routes through the helpers. `collectImportPath` was the one hand-rolled
holdout and had to be rewritten first.

Two things that do NOT belong in a closure:
- Prefix chains and operator precedence (`type = attribute type`,
  `compilationCondition "&&" compilationCondition`). These are right-recursive but not repetitions;
  `{ }` changes their meaning.
- A list whose separator carries per-element meaning. `statements = statement ";"? |
  statement statementSeparator statements` keeps a `;` in the same hop as the statement it
  terminates; `statement { statementSeparator statement } ";"?` moves it to the next statement's
  hop instead. Same language, different tree attribution.

## Inlining single-use nonterminals

A nonterminal used exactly once can often be folded into its use site
(`attribute = … "(" < effectsToken > ")"` instead of a separate `effectsTokens` rule). But the
mechanical criterion is a poor guide. Of 166 single-use, single-production nonterminals in
`Swift.apus` (2026-09-21), only two were worth inlining. Three things disqualify the rest:

1. **The converter resolves nonterminals BY NAME.** 153 of the 166 are named in
   `GenerateSwiftSyntaxAST.swift` (`find("X")`, `recursiveListName: "X"`, …). Inlining one
   silently changes the tree, or breaks a collector, unless those sites are updated in the same
   change. `effectsTokens` had two such references and needed a converter edit.
2. **Mutual recursion makes it impossible.** `regexGroup` is used once by `regexItem` and its own
   body references `regexItem`; same for `tryScanOperatorAsRegexLiteralGroup`. Expansion does not
   terminate.
3. **The name usually IS the documentation.** `mutationModifier`, `actorIsolationModifier`,
   `floatingPointLiteral`, `optionalPattern`, `missingIntroducerWildcardCondition` and the
   `*Declaration`/`*Body` rules each name a concept — most mirror a TSPL production, and
   `missingIntroducerWildcardCondition` records a deliberate error-tolerance case. Folding them
   into a parent alternation makes the parent longer and the intent invisible: not a
   simplification.

So inline only single-use rules that are pure PLUMBING — a list or paren wrapper with no
conceptual content and no converter reference. That was `effectsTokens` and
`lifetimeSpecifierArgumentList`, and nothing else.

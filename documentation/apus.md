# APUS Language Reference

APUS is a grammar language. You write a grammar in APUS. The APUS parser reads the grammar. Then it
parses input with that grammar.

APUS describes itself. The file `apus.apus` contains the grammar of APUS.

The name comes from *Apus apus*, the common swift. This bird does not land. The parser does not
stop.

The parser is a GLL parser. It tries all alternatives, also when the grammar is ambiguous. The
annotations in this manual tell the parser which readings to keep.

## Grammar File

A grammar file has two parts: productions, then messages.

```apus
grammar = < production > { message } .
```

The productions come first. There is one production or more. They define terminals and rules.
Then the messages come: zero or more test inputs. Each message starts with `^^^`.

Each production ends with a full stop `.`. If you leave out the full stop, the grammar does not load.

## Comments

```apus
// this is a comment
```

A comment starts with `//` and continues to the end of the line. APUS does not use `#` for
comments. `#` is not an APUS token.

## Productions

There are three kinds of production. Each one starts with a name.

### Silent Terminal (`:`)

```apus
whitespace : /\s+/ .
comment    : /\/\/.*/ .
```

A colon makes a silent terminal. The scanner matches it and then discards it. The parser does not
see it. Use silent terminals for whitespace and comments (trivia).

### Visible Terminal (`-`)

```apus
identifier - /\p{XID_Start}\p{XID_Continue}*/ .
number     - /[0-9]+/ .
lBrace     - "{" .
```

A dash makes a visible terminal. The scanner matches it and keeps it. The parser sees it. Use
visible terminals for identifiers, numbers, string literals and other tokens with a meaning.

The right side is a regex, a literal or a builder (see "Builder Terminals"). A literal terminal
gives a name to a fixed text: you can write `lBrace` in a rule instead of `"{"`.

### Structured Terminal

The right side of `:` or `-` can also be a rule body. The terminal is then recognized with a small
parse of that body.

```apus
blockComment : "/*" { /[^*\/]+|\*(?!\/)|\/(?!\*)/ | blockComment } "*/" .
```

This silent terminal accepts nested block comments. A regex cannot do that.

### Production Rule (`=`)

```apus
S = "hello" "world" .
```

An equals sign makes a production rule. The left side is the name of a nonterminal. The right side
is what the nonterminal expands to.

The first production rule in the file is the start symbol. The parser starts there.

You can define the same nonterminal more than one time. The definitions merge:

```apus
S = "x" .
S = "x" "x" .
```

`S` matches one or two `x`.

## Terminals in Rules

### Literals

```apus
S = "hello" "world" .
```

A literal is text in double quotes. It matches that text exactly. Literals use Swift string
escapes: `"\t"` matches a tab, `"\\"` matches a backslash.

### Regex

```apus
number - /[0-9]+/ .
```

A regex is text between forward slashes, in Swift regex syntax. Use regexes in terminal
definitions. You can also write a regex directly in a rule.

### Token Kinds

Each terminal has a kind. The kind is how the parser tells tokens apart.

- **Named terminal.** The name on the left side is the kind. `number - /[0-9]+/ .` has the kind
  `number`.
- **Anonymous terminal.** A literal or regex in a rule has its own text as its kind, together with
  the delimiters. `"while"` has the kind `"while"`.

Anonymous terminals with the same text share one kind: `"{"` in ten rules is one terminal. A named
terminal never merges with an anonymous one. So you can give one text two kinds on purpose:

```apus
openSlash  - "/" .
closeSlash - "/" .
```

### Names

```apus
S = A B .
A = "a" .
B = "b" .
```

A name in a rule refers to a terminal or to a nonterminal. If the name is defined with `:` or `-`,
it is a terminal. If not, it is a nonterminal.

### Epsilon

```apus
S = "a" | ε .
S = "a" | "" .
```

`ε` and the empty literal `""` both match nothing (zero tokens).

## Alternatives

```apus
S = "a" | "b" | "c" .
```

A vertical bar separates alternatives. `S` matches `a`, `b` or `c`. The parser tries all
alternatives.

## Sequence

```apus
S = "a" "b" "c" .
```

Items that follow each other match in that order: `a`, then `b`, then `c`.

## Brackets

| Bracket | Meaning | Example | Matches |
| --- | --- | --- | --- |
| `( )` | group | `"a" ( "b" \| "c" ) "d"` | `abd`, `acd` |
| `[ ]` | zero or one | `"a" [ "b" ] "c"` | `ac`, `abc` |
| `{ }` | zero or more | `"a" { "b" } "c"` | `ac`, `abc`, `abbc`, … |
| `< >` | one or more | `"a" < "b" > "c"` | `abc`, `abbc`, … |

The postfix operators do the same for one item:

```apus
S = "a" "b"? "c" .   // "b" zero times or one time
S = "a" "b"* "c" .   // "b" zero or more times
S = "a" "b"+ "c" .   // "b" one or more times
```

## Messages (Test Inputs)

```apus
^^^
hello world
^^^
goodbye world
```

`^^^` starts a message. A message continues to the next `^^^` or to the end of the file. The parser
uses the messages as test inputs.

Do not put comments between messages. A comment there becomes part of the message.

## Actions

```apus
S = 'init' "x" 'process' { "y" 'accumulate' } 'finalize' .
```

An action is code between single quotes. The scanner removes actions from the tokens. The grammar
keeps them on the grammar positions for code generation.

You can put actions before the first production, between a name and `=`, between items, and after
the last production.

---

## Annotations

An annotation starts with `@`. Its meaning depends on its position. There are four positions:

| Position | Annotations |
| --- | --- |
| Start of a production, before the name | `@longest` `@shortest` `@sameLineOutsideBrackets` `@modeScope` `@literalMunch` `@preempt` |
| Start of an alternative, after `=` `\|` `(` `[` `{` `<` | `@prefer` `@avoid` `@left` `@right` `@canParse` `@cannotParse` |
| Before an item | `@setMode` `@clearMode` `@requiresMode` `@rejectsMode` |
| Before a bracket | `@longest` `@shortest` |

An annotation in the wrong position is an error. Exception: a terminal pragma on a production rule
(`=`) has no effect.

Three other predicates also sit between items. They consume no input:

- layout boundaries `<s>` `>s<` `<n>` `>n<`,
- token lookaround `>+>` `>->` `<+<` `<-<`,
- layout tokens `>>|` `|<<`.

## Choosing Between Readings

When the grammar is ambiguous, the parser finds all readings. These annotations remove readings.

### `@prefer` and `@avoid`

```apus
S = @prefer A | B .
S = [ @avoid modifier ] name .
```

- `@prefer`: this alternative wins over the other alternatives that match the same text.
- `@avoid`: this alternative loses to the other alternatives that match the same text.

In `[ … ]` and `{ … }`, `@avoid` also loses to the empty choice. So `[ @avoid X ]` means: skip `X`
if the parse still succeeds without it.

### `@longest` and `@shortest`

```apus
@longest expression = term { "+" term } .
S = @shortest [ modifier ] name .
```

`@longest` keeps the reading in which this node matches the most text. `@shortest` keeps the reading
in which it matches the least text. Put them at the start of a production or before a bracket.

`@avoid` and `@shortest` are not the same. `[ @avoid X ]` compares the alternatives. `@shortest [ X ]`
compares how much text the bracket matches.

### `@left` and `@right`

```apus
E = @left E "+" E | number .     // 1+2+3 is (1+2)+3
E = @right E "^" E | number .    // 2^3^4 is 2^(3^4)
```

- `@left`: this alternative cannot be its own rightmost child.
- `@right`: this alternative cannot be its own leftmost child.

In `1+2+3`, the reading `1+(2+3)` has a `+` as the right child of a `+`. `@left` removes that
reading.

You can give a list of nonterminals. Then those nonterminals cannot be in that child position:

```apus
call = @right( number ) primary "(" ")" .   // 1() is not a call
```

The child is removed when it matches exactly the text of a listed nonterminal. In `1()` the callee
is the number `1`, so this reading is removed. In `x.y()` the callee is longer than a number, so
it stays.

You can put more than one `@left` or `@right` on one alternative.

`@left` and `@right` apply to one production. They cannot make two different productions (for
example `+` and `-`) associative with each other.

### `@canParse` and `@cannotParse`

```apus
statement = @cannotParse( declaration ) expression .
```

- `@canParse(N)`: this alternative is valid only where `N` can start at this position.
- `@cannotParse(N)`: this alternative is not valid where `N` can start at this position.

"Can start" means that `N` has a parse that starts here. `N` does not have to cover the same text as
the alternative.

The parser must try `N` at this position for its own reasons. If no other rule uses `N`, the parser
never tries it. Then `@canParse(N)` is always false and `@cannotParse(N)` is always true. These
predicates cannot run a separate grammar as a lookahead.

### `@sameLineOutsideBrackets`

```apus
@sameLineOutsideBrackets
condition = expression .
```

`@sameLineOutsideBrackets` keeps a reading of this nonterminal only if it has no line break between
two of its tokens, outside `( )`, `[ ]` and `{ }`. These line breaks do not count:

- a line break inside `( )`, `[ ]` or `{ }`,
- a line break in the text of a token (for example in a multiline string),
- a line break after the last token of the nonterminal.

With this rule, `f(a,⏎b)` is a valid condition, and `a⏎|| b` is not.

## Parser Modes

A parser mode is a flag that a part of the grammar gives to its children. The same text can parse
differently when the flag is set. For example, in a condition a `{` can start the body, not a
closure.

### Mode Annotations

```apus
@setMode(foo bar) X       // parse X with foo and bar set
@clearMode(foo bar) X     // parse X with foo and bar not set
@requiresMode(foo bar) X  // keep this path only if foo and bar are both set
@rejectsMode(foo bar) X   // remove this path if foo and bar are both set
```

`@setMode` and `@clearMode` change only the modes that they name. The change applies only to the
annotated item. After that item, the parser continues with the modes it had before.

A test (`@requiresMode`, `@rejectsMode`) uses the modes of its item, after `@setMode` and
`@clearMode` on that same item.

A grammar can have at most 64 modes.

### Mode Scopes: `@modeScope`

Each mode has a scope. `@modeScope(m)` at the start of a production lets the mode `m` go into that
nonterminal. A mode goes only into nonterminals that have it in their scope. At any other
nonterminal, the mode stops.

```apus
ifStatement = "if" @setMode(cond) expression block .

@modeScope(cond) expression = term { "+" term } .
@modeScope(cond) term       = number | name | group | @rejectsMode(cond) closure .
group                       = "(" expression ")" .
```

In the condition of `if`, a term cannot be a closure. `group` does not have `cond` in its scope.
Thus the mode stops at `group`, and a closure is permitted inside parentheses again.

You do not have to clear a mode where its scope ends. Use `@clearMode` only for a boundary inside a
scope.

`@modeScope` can occur more than one time. When a nonterminal has more than one definition, its
scopes are combined.

### Checks

When the grammar loads, these are errors:

- a mode that no production has in its scope,
- `@setMode(m) Y` where `Y` does not have `m` in its scope,
- a test on a mode that can never be set at that position.

The load log also shows:

- the cost of each mode,
- each `@clearMode` that has no effect,
- each scope exit: a place where a mode stops, but a test below could still use it.

A scope exit is correct at a boundary that you want. An unexpected scope exit means that a scope is
too small. A mode with a cost of zero has no effect.

### Cost

Modes have no cost at parse time. When the grammar loads, APUS makes a copy of each nonterminal for
each mode combination that changes its language. Nonterminals outside all scopes are not copied.
The load log shows the number of copies for each mode. Keep scopes small to keep this number low.

### When to Use a Mode

- Use a mode for a flag that must go through one or more nonterminals. If the flag is necessary at
  only one place, write a separate rule there.
- Use a mode to make a reading valid or not valid. To choose between valid readings, use `@prefer`,
  `@longest` and the other annotations in "Choosing Between Readings".
- A mode goes from a parent to its children. It cannot go to a sibling. If the context comes from
  the item to the left, a mode cannot express it.
- Make a scope as small as the context that it models.

## Sequence Predicates

### Exclusion Sets `---( )`

```apus
name = identifier ---( "if" "while" "for" ) .
```

A keyword and an identifier can match the same text, for example `if`. The parser then tries both.
`---( … )` removes the listed texts at this position: here, `if` is not a `name`.

Put `---( … )` after an item. You can also give the name of a rule in which each alternative is one
literal:

```apus
keyword = "if" | "while" | "for" .
name    = identifier ---( keyword ) .
```

### Layout Boundaries `<s>` `>s<` `<n>` `>n<`

```apus
prefixUse = operator >s< operand .
lineStart = <n> statement .
```

A layout boundary tests the trivia between the previous token and the current position:

| Boundary | True when |
| --- | --- |
| `<s>` | there is trivia (whitespace or a comment) |
| `>s<` | there is no trivia |
| `<n>` | the trivia contains a line break |
| `>n<` | the trivia contains no line break |

A line break in a block comment also counts.

### Token Lookaround

```apus
A = X >+>( ")" ) Y .
A = X >->( "(" ) Y .
A = X <+<( identifier ) Y .
A = X <-<( operator ) Y .
```

| Lookaround | True when |
| --- | --- |
| `>+>( … )` | a listed terminal can come after this position |
| `>->( … )` | no listed terminal can come after this position |
| `<+<( … )` | a listed terminal came before this position |
| `<-<( … )` | no listed terminal came before this position |

`EOF` means the end of the input:

```apus
A = X >+>( ")" EOF ) .
```

### Layout Tokens `>>|` and `|<<`

```apus
block = >>| < statement > |<< .
```

Use layout tokens for languages that use indentation, for example Python:

- `>>|` (indent): a new line starts in a column to the right.
- `|<<` (dedent): a new line starts in a column to the left.

When a grammar uses them, APUS adds them to the tokens before it parses. Inside brackets, APUS does
not track the indentation.

## Terminal Pragmas

Terminal pragmas control how the scanner matches a terminal. Use them only on terminals.

### `@literalMunch`

```apus
@literalMunch identifier - /[a-z]+/ .
```

A literal does not match if a `@literalMunch` terminal has a longer match at the same position.
For example, the literal `"for"` does not match at the start of `format`, because `identifier`
matches all of `format`.

### `@preempt`

A terminal usually takes the longest match (maximal munch). `@preempt` lets it also stop before an
inner terminal `X`.

```apus
@preempt(openAngle) functionName - /[-+*\/<>]+/ .
@preempt(slash, regexLiteral) operator - /[-+*\/!^]+/ .
```

- `@preempt(X)`: the terminal also matches up to each inner position where `X` begins. All matches
  stay, and the parse chooses. In `func %%<T>`, the name is `%%` and `<T>` follows. In `func <<<()`,
  the name is `<<<`.
- `@preempt(X, N)`: the same, but the nonterminal `N` decides. At the first inner position where `N`
  can parse, the terminal stops, and the longer matches are removed. If `N` cannot parse at any inner
  position, only the longest match stays. In `!/a/`, the operator is `!` and `/a/` is the regex.

### Builder Terminals

```apus
identifier - @builder .
number     - @builder(decimal) .
```

A builder terminal gets its scanner from the builder library (`SwiftGrammarRegexLibrary.swift`).
`@builder` uses the scanner with the name of the terminal. `@builder(key)` uses the scanner with the
name `key`.

Use a builder when a regex in the grammar is too difficult to read, or when a regex cannot do the
work. A builder can be custom code. It can count brackets, and it can look at the text before its
start position.

## Writing Grammars

### Context-Dependent Tokens

Some tokens depend on their position. For example, `/` can be a division operator or the start of a
regex literal. Let the grammar give the position:

```apus
regex   - @builder .
primary = number | regex | "(" expr ")" .
expr    = primary { "/" primary } .
```

The parser tries a terminal only at positions where the grammar can accept it. Here it tries
`regex` only where a `primary` can start. In `a / b / c`, each `/` is division. In `x = /ab/`, the
`/ab/` is a regex.

Do not try to find the position from the previous token in the scanner. The grammar has that
information already.

### Lists

Write a list with a closure, not with right recursion:

```apus
list = item { "," item } .        // good
list = item | item "," list .     // not good
```

The closure form is shorter and has one alternative.

Do not use a closure for a structure that is not a repetition, for example a prefix chain or an
operator precedence level. A closure changes their meaning.

The position of a separator can be important. `statement { ";" statement }` attaches each `;` to
the statement after it. If each `;` must stay with the statement before it, write the list so
that the `;` follows that statement.

### Rule Names

Keep a rule, also if it is short, when something uses its name:

```apus
condition = @setMode(cond) expression .
```

An annotation, a tool or a converter can use a name. If you put the body of such a rule at the
places that use it, these users lose the name. Remove a rule only if nothing uses its name.

A rule that is used one time can often stay. Its name tells the reader what the part means. Put
the body of a rule at its place of use only if the rule is a simple wrapper with no meaning of its
own.

---

## Full Grammar

`apus.apus` describes APUS. This is its structure:

```apus
whitespace  : /\s+/ .
comment     : /\/\/.*/ .
action      : /'(?:[^'\\]|\\.)*'/ .

identifier  - /\p{XID_Start}\p{XID_Continue}*/ .
literal     - /\"(?:[^\"\\]|\\.)+\"/ .
regex       - /\/(?!\*)(?:[^\/\\]|\\.)+\// .
pragma      - /@\p{XID_Start}\p{XID_Continue}*/ .
message     - /\^\^\^(?:(?s).*?)(?=\^\^\^|$)/ .

grammar        = < production > { message } .
production     = productionPragma* identifier ( ":" | "-" | "=" ) productionBody "." .
productionBody = terminalBody | selection .
terminalBody   = regex | literal | "@builder" [ "(" identifier ")" ] .

selection    = sequence { "|" sequence } .
sequence     = alternateAnnotation* < sequenceItem > .
sequenceItem = layout
             | lookaround
             | modeAnnotation* factor [ "?" | "*" | "+" ] [ exclusion ]
             .

factor   = terminal
         | groupPragma* "[" selection "]"
         | groupPragma* "{" selection "}"
         | groupPragma* "<" selection ">"
         | groupPragma* "(" selection ")"
         .
terminal = identifier | literal | regex | "ε" | "\"\"" .

layout     = ">>|" | "|<<" | "<n>" | "<s>" | ">n<" | ">s<" .
lookaround = ( ">+>" | ">->" | "<+<" | "<-<" ) "(" < literal | identifier | "EOF" > ")" .
exclusion  = "---" "(" < literal | identifier > ")" .

productionPragma    = terminalPragma | nonterminalPragma .
terminalPragma      = "@literalMunch" | "@preempt" "(" identifier [ "," identifier ] ")" .
nonterminalPragma   = "@longest" | "@shortest" | "@sameLineOutsideBrackets"
                    | "@modeScope" "(" < identifier > ")" .
groupPragma         = "@longest" | "@shortest" .
alternateAnnotation = "@prefer" | "@avoid"
                    | ( "@left" | "@right" ) [ "(" < identifier > ")" ]
                    | ( "@canParse" | "@cannotParse" ) "(" < identifier > ")" .
modeAnnotation      = ( "@setMode" | "@clearMode" | "@requiresMode" | "@rejectsMode" )
                      "(" < identifier > ")" .
```

## Sample Grammar

A small calculator:

```apus
whitespace : /\s+/ .
comment    : /\/\/.*/ .

number - /[0-9]+/ .

expr = term { ( "+" | "-" ) term } .
term = atom { ( "*" | "/" ) atom } .
atom = number | "(" expr ")" .

^^^
1 + 2 * (3 + 4)
^^^
42
^^^
(1 + 2) * (3 + 4)
```

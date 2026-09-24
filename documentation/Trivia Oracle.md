# Trivia Rules: Parser vs Oracle (Caveman Notes)

## Big Question

Swift has sneaky space/newline rules.
Where we check?

- parser?
- oracle?

## What We Already Know

- Frankenstein is parser job.
- Schrodinger is parser job.
- Scanner modes (`>>>`, `===`, `<<<`) are scanner job.
- Trivia is kept. Not thrown away.
- BSR built from token positions, with Frankenstein sub-position support.

## Main Decision

New trivia rules go to **oracle first**.

Why:

- safer
- no early false kill of parse path
- easy to tune

Later, maybe move some rules earlier to parser, but only after proof.

## Important Clarification

If we do not check trivia in parser:

- usually we get more candidate parses (superset)
- oracle filters bad ones

So default is: parser permissive, oracle strict.

## When Rule Can Move To Parser

Rule can move only if all true:

1. same predicate code in oracle and parser
2. corpus test says: no valid parse lost
3. ambiguity results still equivalent
4. debug switch can disable parser trivia gating

If not all true, keep in oracle.

## Annotation Policy

Yes, still use annotations.

Why:

- grammar says intent
- oracle code stays generic
- no giant hardcoded `if ruleName == ...`

If you do not want to pollute published Swift grammar text, use sidecar metadata file.
Same semantics.

## 3-Char Trivia Annotations (Edge Only)

Put annotation **between symbols** only.
Never before token, never after token.
This avoids confusion.

Base set:

- `>s<` no space between A and B (touching)
- `>n<` no newline between A and B (same line)
- `<s>` space between A and B (not touching)
- `<n>` one or more newlines between A and B (not on same line)

## Example

```apus
tryOperator = "try" >s< "?" | "try" >s< "!" | "try" .

typeCastingOperator = "as" >s< "?" type
                   | "as" >s< "!" type
                   | "as" type .
```

## Minimal Swift Rule Patch (Proposal Only)

Below is the minimum rewrite block to encode spacing/adjacency behavior with trivia annotations.
This is documentation only. Not applied to `Swift.apus`.

```apus
// keep token definitions unchanged
Operator = plainOperator | dotOperator .

// operator classes become context-constrained by edge annotations
infixOperator = Operator .
prefixOperator = Operator .
postfixOperator = Operator .

expression = tryOperator? awaitOperator? prefixExpression infixExpressions? .

infixExpressions = infixExpression infixExpressions? .

// symmetrical space on both sides of the operator
infixExpression = <s> infixOperator <s> tryOperator? awaitOperator? prefixExpression .
infixExpression = >s< infixOperator >s< tryOperator? awaitOperator? prefixExpression .
infixExpression = <s> assignmentOperator <s> tryOperator? awaitOperator? prefixExpression .
infixExpression = >s< assignmentOperator >s< tryOperator? awaitOperator? prefixExpression .
infixExpression = <s> conditionalOperator <s> tryOperator? awaitOperator? prefixExpression .
infixExpression = >s< conditionalOperator >s< tryOperator? awaitOperator? prefixExpression .

infixExpression = <?> typeCastingOperator .  // TODO: is this required ?

prefixExpression = prefixOperator >s< postfixExpression .
prefixExpression = inOutExpression .

postfixExpression = primaryExpression .
postfixExpression = postfixExpression >s< postfixOperator .
postfixExpression = functionCallExpression .
postfixExpression = initializerExpression .
postfixExpression = explicitMemberExpression .
postfixExpression = postfixSelfExpression .
postfixExpression = subscriptExpression .
postfixExpression = forcedValueExpression .
postfixExpression = optionalChainingExpression .

tryOperator = "try"
            | "try" >s< "?"
            | "try" >s< "!" .

typeCastingOperator = "is" type
                    | "as" type
                    | "as" >s< "?" type
                    | "as" >s< "!" type .

forcedValueExpression = postfixExpression >s< "!" .
optionalChainingExpression = postfixExpression >s< "?" .
```

Why this is minimal:

1. touches only operator-disambiguation hot spots
2. uses `>s<` where Swift requires adjacency (`try?`, `as?`, postfix `!`/`?`)
3. leaves rest of grammar unchanged

## Precedence Question (From Discussion)

Current `Swift.apus` expression core is flat chain.
So precedence/associativity is also oracle/post-pass work in this setup.

Same architecture:

- metadata says intent
- oracle/reducer enforces

## Exhaustive Swift Trivia Inventory (For This Project)

This list is split in two buckets:

1. Swift language reference rules (normative)
2. Project/compiler behavior rules we track in practice

### A) Normative Swift Reference Rules

1. Whitespace includes spaces, tabs, vertical tabs, form feeds, and newlines.
2. Comments are treated as whitespace.
3. Line break is just whitespace at lexical level, but it still affects operator fixity classification.
4. Operator with whitespace on both sides, or on neither side, is infix.
5. Operator with whitespace only on left side is prefix.
6. Operator with whitespace only on right side is postfix.
7. Operator with no left whitespace and followed immediately by `.` is postfix.
8. Delimiters `(` `[` `{` before operator count as left whitespace.
9. Delimiters `)` `]` `}` `,` `:` `;` after operator count as right whitespace.
10. `!` and `?` with no left whitespace are postfix, even if right side has whitespace.
11. Ternary `? :` must have whitespace around both `?` and `:`.
12. Infix operator whose right operand is a regex literal must have whitespace on both sides.
13. In some generic/bracket contexts, tokens that start with `<` or `>` can be split by parser context (max-munch exception handling).

### B) Project + Compiler-Observed Rules We Track

These are in `Swift.apus` comments/TODOs and should be modeled in oracle policy:

1. No space between `try` and `?` / `!` (`try?`, `try!`).
2. No space between `as` and `?` / `!` (`as?`, `as!`).
3. No space before postfix `?` in optional chaining.
4. No space before postfix `!` in forced unwrap.
5. No space between type and `?` in optional type spelling (`T?`).
6. `unowned(safe)` / `unowned(unsafe)` style: no space before `(`.
7. Attribute marker token is glued (`@` + identifier, no space in between) in current scanner model.
8. `#sourceLocation(file:..., line:...)` currently accepted by compiler with flexible whitespace around `file`/`line` and `:`.
9. Newline/context-sensitive keyword behavior (example: `copy` discussion) should be treated as oracle policy until proven-local and safe for parser gating.

### C) Annotation Mapping for Inventory

Use edge annotations only:

1. `>s<` adjacency required
2. `>n<` same line required (no newline)

Rule of use:

1. Add annotation (or sidecar metadata)
2. Evaluate in oracle
3. Promote to parser gating only after equivalence proof

### D) References

1. Swift Book source: Lexical Structure  
https://raw.githubusercontent.com/swiftlang/swift-book/main/TSPL.docc/ReferenceManual/LexicalStructure.md
2. Swift Book source: Expressions  
https://raw.githubusercontent.com/swiftlang/swift-book/main/TSPL.docc/ReferenceManual/Expressions.md
3. Local grammar notes/TODOs: `Advent/Swift.apus`

## Non-Goals

- no hidden semantic hacks only
- no grammar explosion
- no unproven parser hard-prune

## Boundary Operator Semantics (Implementation Note)

For APUS boundary operators used as `.B` grammar nodes:

1. The predicate is evaluated at the current parser boundary: between token `cI-1` and token `cI`.
2. In `a <s> b`, the check happens when parser is at `b`, and measures the gap between `a` and `b`.
3. For robust behavior with synthetic layout tokens (`>>|`, `|<<`), use source indices, not `trivia[right]`:
   - `<s>` means there is an inter-token source gap (`left.end < right.start`).
   - `>s<` means strict adjacency (`left.end == right.start`).
4. `<n>` / `>n<` should continue to use line-break counting over the source span.

This keeps layout injection and boundary predicates composable: synthetic layout tokens can appear in the stream without corrupting spacing predicates.

## Bottom Line

- Keep Frankenstein/Schrodinger/scanner modes where they are.
- Put trivia checks in oracle first.
- Use edge annotations (or sidecar equivalent) as source of truth.
- Promote to parser only after equivalence proof.

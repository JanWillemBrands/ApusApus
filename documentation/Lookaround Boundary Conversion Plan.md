# Lookaround Boundary Conversion Plan

## Goal

Make token lookaround a first-class zero-width sequence predicate, in the same
placement class as layout boundaries:

```apus
A = X >+>(")" EOF) Y .
A = X >->("(") Y .
A = X <+<(identifier) Y .
A = X <-<(operator) Y .
```

Meaning at the current parse position:

```text
>+>(...) = some listed terminal can occur after this position.
>->(...) = no listed terminal can occur after this position.
<+<(...) = some listed terminal occurred before this position.
<-<(...) = no listed terminal occurred before this position.
```

This separates three concepts cleanly:

```text
layout and lookaround = zero-width sequence predicates
Oracle annotations    = parse-forest pruning/selection
terminal pragmas      = lexical-recognition configuration
```

## Implementation Shape

Core token lookaround has been moved into sequence-boundary nodes:

- `<s>`, `>s<`, `<n>`, `>n<` are `.B` boundary nodes parsed in sequence position
  and evaluated by `MessageParser.boundaryMatches`.
- `>+>`, `>->`, `<+<`, and `<-<` in production bodies are `.B` boundary nodes
  with a structured `BoundaryPredicate`, parsed in sequence position and
  evaluated by `MessageParser.boundaryMatches(_ node:at:)`.
- Leading alternate `@canParse` / `@cannotParse` with nonterminal operands is
  stored on the `.ALT` node as `forwardPredicates`, then evaluated by the Oracle
  as a parse-forest predicate.

The Oracle-level alternate predicates stay separate. Post-dot terminal-definition
`<+<` / `<-<` is no longer a grammar feature; token lookaround must appear as a
production-body boundary at the cursor position it constrains.

## Data Model

Structured boundary data lives on `GrammarNode` for `.B` nodes. The full
predicate is not interpreted from `name`; `name` remains display/debug text and
provides a symbol-table ID for the `.B` node.

Current shape:

```swift
enum BoundaryPredicate {
    case tokenLookahead(positive: Bool, kinds: Set<String>)
    case tokenLookbehind(positive: Bool, kinds: Set<String>, distance: Int)
}
```

Then add:

```swift
var boundaryPredicate: BoundaryPredicate?
var boundaryPredicateBS: BitSet = []
```

Layout boundaries leave `boundaryPredicate == nil` and continue to use their
four textual spellings.

## Parsing

`sequence()` has a single boundary parser path:

```swift
sequenceItem =
    layout
  | tokenLookaround
  | factor [ "?" | "*" | "+" ] [ exclusion ]
```

`tokenLookaround` parses:

```apus
( ">+>" | ">->" | "<+<" | "<-<" ) "(" < literal | identifier | "EOF" > ")"
```

Operand resolution rules:

- quoted literal operand resolves to that anonymous literal token kind, including
  quotes;
- bare identifier operand resolves to a named terminal kind;
- bare `EOF` resolves to the end-of-input sentinel;
- unknown operands should be grammar errors.

Keep leading alternate `@canParse(N)` / `@cannotParse(N)` with nonterminal operands
as a distinct Oracle predicate. It is not token lookaround.

## Runtime Evaluation

Change the `.B` path from:

```swift
boundaryMatches(cL.name, at: cI)
```

to:

```swift
boundaryMatches(cL, at: cI)
```

Runtime cases:

- spacing/layout boundaries use the existing trivia-gap logic;
- positive token lookahead succeeds when any listed terminal lexes at `cI`;
- negative token lookahead succeeds when no listed terminal lexes at `cI`;
- positive token lookbehind succeeds when `previousKindIDs(at:cI,distance:1)`
  intersects the listed set;
- negative token lookbehind succeeds when the previous-kind set is disjoint.

Implemented EOF/start behavior:

- positive lookahead at EOF succeeds iff `EOF` is explicitly in the operand set;
- negative lookahead at EOF succeeds iff `EOF` is not in the operand set;
- positive lookbehind at start of input fails;
- negative lookbehind at start of input succeeds.

## Migration Steps

1. DONE: Add `BoundaryPredicate` and bitset resolution for `.B` nodes.
2. DONE: Teach `ApusParser.sequence()` to parse token lookaround wherever layout
   boundaries are accepted.
3. DONE: Extend `MessageParser.boundaryMatches` to evaluate structured
   lookaround boundaries.
4. DONE: Add focused tests:

   ```apus
   S = "a" >+>("b") "b" .
   S = "a" >->("c") "b" .
   S = "a" <+<("a") "b" .
   S = "a" <-<("c") "b" .
   ```

5. DONE: Existing `Swift.apus` token-lookaround sites now parse as sequence
   boundaries because the grammar surface syntax did not need to change.
6. DONE: Remove the factor-attached `followAhead` / `followAheadExclude` storage
   and old runtime checks. Symbolic token lookaround is now single-sourced through
   `.B` boundary nodes.
7. DONE: Remove terminal-definition `<+<` / `<-<` as a separate annotation
   class. The Swift regex constraints now live in production-body boundary
   positions, `lookbehindAnnotations(attachingTo:)` and terminal
   `lookbehindByTerminalID` enforcement are gone, and `@preempt` drops offered
   split points whose viability target cannot parse.

## Validation

Use focused tests first:

- `OracleDisambiguationTests` for no regression in Oracle-level `>+>` / `>->`;
- `SpecialTokenTests` for token lookahead/lookbehind behavior;
- affected `SwiftSyntax*` subsets for converted grammar sites.

Do not run the full suite for every step. After all conversions are complete, run
the full suite once with deterministic hashing enabled.

## Risks

- EOF behavior is explicit through the `EOF` operand. Do not infer EOF acceptance
  from where the boundary appears.
- Lookbehind reads parser commit history. In multi-lex cases, the current
  `previousKindIDs` union means positive lookbehind is existential and negative
  lookbehind rejects if any previous alternative has a forbidden kind.
- Some current `>+>` / `>->` operands are nonterminals in leading alternate
  position. Those must stay Oracle predicates, not become token lookaround.
- Removing factor-attached fields too early risks changing Swift generic
  disambiguation before equivalent boundary sites are in place.

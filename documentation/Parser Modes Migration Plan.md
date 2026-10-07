# Parser Modes Migration Plan

This note sketches a scoped parser-mode mechanism for APUS and a migration path
from `@confinedTo` / `@excludedFrom` to that mechanism.

The goal is not general mutable parser state. The goal is a small, principled
inherited-context mechanism: a finite set of mode flags carried by descriptors
and CRF edges. Mode changes are scoped to grammar occurrences. They are not
global actions and do not require explicit pops.

## Motivation

`@confinedTo` and `@excludedFrom` use BSR span containment as a substitute for
hidden handwritten-parser context. This works for some cases, but it is too
spatial. In particular, SwiftSyntax expression flavors are occurrence-local:
condition parsing changes how an immediate trailing closure decision is made,
but nested expression islands can return to ordinary expression flavor.

The TODO #5 failure shows the mismatch:

```swift
func f() {
  while a(b: {
    d.e {
    }
  }) {}
}
```

APUS currently treats the inner newline-opened trailing closure as being inside
`conditionExpression` by span containment, even though SwiftSyntax has reset to
ordinary expression parsing inside the argument closure.

Parser modes make this context explicit on grammar edges.

## Proposed Annotations

Start with four scoped annotations:

```apus
@setMode(foo bar) X       // parse X with foo and bar added
@clearMode(foo bar) X     // parse X with foo and bar removed
@requiresMode(foo bar) X  // valid only if all listed flags are active
@rejectsMode(foo bar) X   // invalid if all listed flags are active
```

`@setMode` and `@clearMode` are set operations. Unnamed flags remain unchanged:

```text
childMode = parentMode | addedBits
childMode = parentMode & ~removedBits
```

The mode change applies only to the annotated child occurrence. After the child
returns, the caller continuation resumes with the caller's original mode.

This is deliberately not a scanner-mode stack:

- no global mutable mode state
- no terminal side effects
- no explicit pop or reset action
- no order-dependent transitions
- no hidden mode annotations on terminals

## Runtime Representation

Use one `UInt64` bitset for mode flags.

Add mode allocation to `Grammar`:

```swift
var modeNameToBit: [String: UInt64]
```

Assign bits as mode names are parsed. Emit a grammar-load diagnostic if a grammar
declares more than 64 mode names.

Add mode fields to `GrammarNode`:

```swift
var modeAdd: UInt64 = 0
var modeRemove: UInt64 = 0
var requiredModes: UInt64 = 0
var rejectedModes: UInt64 = 0
```

`modeAdd` and `modeRemove` describe the inherited mode for a child occurrence.
`requiredModes` and `rejectedModes` describe validity tests at the annotated
node or alternate.

## Descriptor And CRF Changes

Extend descriptors with mode:

```swift
struct Descriptor: Hashable {
    let L: GrammarNode
    let k: CharPosition
    let i: CharPosition
    let mode: UInt64
}
```

Add current parser mode:

```swift
var cMode: UInt64 = 0
```

Descriptor uniqueness includes `mode`.

Extend CRF identity with mode:

```swift
struct ParsePosition: Hashable {
    let slot: GrammarNode
    let index: CharPosition
    let mode: UInt64
}
```

A nonterminal at the same input position under different modes can accept a
different language, so mode must be part of the CRF cluster key.

Return edges must remember the caller mode, so a child entered under a modified
mode can return to the original continuation mode.

Pops should conservatively include callee mode:

```swift
struct ModePop: Hashable {
    let index: CharPosition
    let mode: UInt64
}
```

There is no `stateOut` dimension for this initial design. Modes are inherited
context, not arbitrary mutable state.

## Parse Loop Semantics

Before executing a node or alternate with mode tests:

```swift
if requiredModes != 0 && (cMode & requiredModes) != requiredModes {
    reject path
}

if rejectedModes != 0 && (cMode & rejectedModes) == rejectedModes {
    reject path
}
```

When entering an annotated child:

```swift
let childMode = (cMode | modeAdd) & ~modeRemove
```

The continuation after the child must retain the original caller mode. This is
the essential discipline that makes modes scoped rather than mutable.

## APUS Meta-Grammar

Teach `grammars/apus.apus` to parse:

```apus
modeAnnotation =
    | "@setMode" "(" < identifier > ")"
    | "@clearMode" "(" < identifier > ")"
    | "@requiresMode" "(" < identifier > ")"
    | "@rejectsMode" "(" < identifier > ")" .
```

Allow mode annotations in sequence position before a factor. Support
`@requiresMode` / `@rejectsMode` at alternate start too if that falls out
naturally, but sequence-position support is enough for the initial migration.

Implementation note: the initial migration replaced all live grammar uses, then
removed `@confinedTo` / `@excludedFrom` from the parser and Oracle.

## Migration Step 1: TODO #5

Replace:

```apus
closureExpression =
    samelineOpenedClosure
  | @excludedFrom(conditionExpression)
    @excludedFrom(trailingClosures)
    newlineOpenedClosure
  .
```

with:

```apus
closureExpression =
    | samelineOpenedClosure
    | @rejectsMode(stmtCondition trailingClosure) newlineOpenedClosure
    .
```

Set condition mode:

```apus
condition =
    | @setMode(stmtCondition) expression
    | availabilityCondition
    | caseCondition
    | missingIntroducerWildcardCondition
    | optionalBindingCondition
    .

whereExpression = @setMode(stmtCondition) expression .

repeatWhileStatement =
    "repeat" codeBlock "while" >-> ( "{" ) @setMode(stmtCondition) expression .
```

Set trailing-closure mode:

```apus
trailingClosures =
    | @setMode(trailingClosure) @cannotParse(willSetDidSetBlock accessorBlockBrace)
      closureExpression labeledTrailingClosures
    | @setMode(trailingClosure) @cannotParse(willSetDidSetBlock accessorBlockBrace)
      closureExpression >-> ( "else" )
    .
```

Clear condition mode at expression islands:

```apus
functionCallArgument =
    | @clearMode(stmtCondition) expression
    | argumentLabel ":" @clearMode(stmtCondition) expression
    .
```

Also check whether closure bodies need `@clearMode(stmtCondition)` around their
`statements?` body to match SwiftSyntax flavor reset behavior.

## Migration Step 2: Remaining Containment Uses

### `@available` raw strings

Current:

```apus
staticStringLiteral =
    | singleLineStringLiteral
    | multilineStringLiteral
    | @excludedFrom(availableAttribute) extendedSinglelineStringLiteral
    | @excludedFrom(availableAttribute) extendedMultilineStringLiteral
    .
```

Mode replacement:

```apus
attribute =
    "@" >s< "available" >s< "("
    @setMode(availableAttributeMode) availabilityAttributeArguments
    ")" .

staticStringLiteral =
    | singleLineStringLiteral
    | multilineStringLiteral
    | @rejectsMode(availableAttributeMode) extendedSinglelineStringLiteral
    | @rejectsMode(availableAttributeMode) extendedMultilineStringLiteral
    .
```

### Module selectors in binding names

Current:

```apus
moduleSelector =
    @excludedFrom(valueBindingPattern) identifierToken "::" >n< .
```

Mode replacement:

```apus
moduleSelector =
    @rejectsMode(bindingIntroducer) identifierToken "::" >n< .
```

Enter `bindingIntroducer` only around introduced binding-name positions. Avoid
putting it around whole patterns unless probes show that is correct.

### Initializer-body `init` expression statement

Current:

```apus
initializerBody = codeBlock .
statement =
    @prefer @confinedTo(initializerBody) >+> ( "init" ) expression .
```

Mode replacement:

```apus
initializerBody = @setMode(initializerBodyMode) codeBlock .

statement =
    @prefer @requiresMode(initializerBodyMode) >+> ( "init" ) expression .
```

If `initializerBody` is only a sentinel, consider inlining the mode at
initializer declaration body sites after the first migration is stable.

### Nested `#if` leading-dot body

Current:

```apus
ifConfigStatements = statements .

ifDirectiveClause =
    @confinedTo(ifConfigStatements)
    ifDirective compilationCondition >+>( "." ) <n> ifConfigStatements? .
```

Mode replacement:

```apus
ifConfigStatements = @setMode(ifConfigBody) statements .

ifDirectiveClause =
    @requiresMode(ifConfigBody)
    ifDirective compilationCondition >+>( "." ) <n> ifConfigStatements? .
```

### Optional-binding `self`

Current:

```apus
identifierPattern =
    | identifierToken
    | @confinedTo(optionalBindingCondition) "self"
    .
```

Mode replacement:

```apus
optionalBindingCondition =
    ( "let" | "var" ) @setMode(optionalBinding) pattern initializer? .

identifierPattern =
    | identifierToken
    | @requiresMode(optionalBinding) "self"
    .
```

Check whether the mode should be even narrower than the whole pattern.

## Removing Containment

Completed as part of the migration:

1. Remove `confinedToContainers` and `excludedFromContainers` from `GrammarNode`.
2. Remove parsing of `@confinedTo` / `@excludedFrom` from `ApusParser`.
3. Remove `ContainmentRule` registration from `Oracle`.
4. Remove `ContainmentRule` itself.
5. Remove containment syntax from `grammars/apus.apus`.
6. Update `documentation/apus.md` and `documentation/Ambiguity.md`.

## Testing Plan

Focused TODO #5 probes:

```swift
func f() {
  while a(b: {
    d.e {
    }
  }) {}
}
```

```swift
func f() {
  if a(b: {
    d.e {
    }
  }) {}
}
```

```swift
func f() {
  a {
    b(content: {
      if !x,
         !models.contains(where: {
           $0.id == x
         })
      {
        y()
      }
    })
  }
}
```

Also keep negative tests where a newline-opened brace after a condition must be
read as the statement body, not a trailing closure.

Regression clusters:

- `@available` string arguments
- module selectors versus binding patterns
- initializer-body `init(...)`
- leading-dot `#if` bodies
- optional-binding `self`

Run focused probes after each migrated containment use. Run the full test suite
after all migrations, then again after deleting containment tooling.

Follow `TESTING.md`; in particular, build before running DerivedData products and
use `SWIFT_DETERMINISTIC_HASHING=1`.

## Migration Order

1. Implement mode machinery while keeping containment.
2. Migrate TODO #5 only.
3. Run focused probes and limited SwiftSyntax tests.
4. Migrate the six remaining containment uses one at a time.
5. Run the full suite.
6. Remove containment machinery.
7. Run the full suite again.
8. Update documentation once syntax and semantics are stable.

This keeps the risky part reversible: modes and containment can coexist until the
grammar no longer depends on containment.

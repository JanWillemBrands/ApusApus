# Parser Flavors Migration Plan

Historical: this plan introduced the RUNTIME design (a bitset in every descriptor). It was
superseded by `Parser Flavors Specialization.md`. "Parser modes" were renamed to flavors on
2026-10-21; the annotations below use the current names.

This note sketches a scoped flavor mechanism for APUS and a migration path
from `@confinedTo` / `@excludedFrom` to that mechanism.

The goal is not general mutable parser state. The goal is a small, principled
inherited-context mechanism: a finite set of flavor flags carried by descriptors
and CRF edges. Flavor changes are scoped to grammar occurrences. They are not
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

Flavors make this context explicit on grammar edges.

## Proposed Annotations

Start with four scoped annotations:

```apus
@setFlavor(foo bar) X       // parse X with foo and bar added
@clearFlavor(foo bar) X     // parse X with foo and bar removed
@requiresFlavor(foo bar) X  // valid only if all listed flags are active
@rejectsFlavor(foo bar) X   // invalid if all listed flags are active
```

`@setFlavor` and `@clearFlavor` are set operations. Unnamed flags remain unchanged:

```text
childFlavor = parentFlavor | addedBits
childFlavor = parentFlavor & ~removedBits
```

The flavor change applies only to the annotated child occurrence. After the child
returns, the caller continuation resumes with the caller's original flavor.

This is deliberately not a scanner-mode stack:

- no global mutable flavor state
- no terminal side effects
- no explicit pop or reset action
- no order-dependent transitions
- no hidden flavor annotations on terminals

## Runtime Representation

Use one `UInt64` bitset for flavor flags.

Add flavor allocation to `Grammar`:

```swift
var flavorNameToBit: [String: UInt64]
```

Assign bits as flavor names are parsed. Emit a grammar-load diagnostic if a grammar
declares more than 64 flavor names.

Add flavor fields to `GrammarNode`:

```swift
var flavorAdd: UInt64 = 0
var flavorRemove: UInt64 = 0
var requiredFlavors: UInt64 = 0
var rejectedFlavors: UInt64 = 0
```

`flavorAdd` and `flavorRemove` describe the inherited flavor for a child occurrence.
`requiredFlavors` and `rejectedFlavors` describe validity tests at the annotated
node or alternate.

## Descriptor And CRF Changes

Extend descriptors with flavor:

```swift
struct Descriptor: Hashable {
    let L: GrammarNode
    let k: CharPosition
    let i: CharPosition
    let flavor: UInt64
}
```

Add current flavor:

```swift
var cFlavor: UInt64 = 0
```

Descriptor uniqueness includes `flavor`.

Extend CRF identity with flavor:

```swift
struct ParsePosition: Hashable {
    let slot: GrammarNode
    let index: CharPosition
    let flavor: UInt64
}
```

A nonterminal at the same input position under different flavors can accept a
different language, so flavor must be part of the CRF cluster key.

Return edges must remember the caller flavor, so a child entered under a modified
flavor can return to the original continuation flavor.

Pops should conservatively include callee flavor:

```swift
struct FlavorPop: Hashable {
    let index: CharPosition
    let flavor: UInt64
}
```

There is no `stateOut` dimension for this initial design. Flavors are inherited
context, not arbitrary mutable state.

## Parse Loop Semantics

Before executing a node or alternate with flavor tests:

```swift
if requiredFlavors != 0 && (cFlavor & requiredFlavors) != requiredFlavors {
    reject path
}

if rejectedFlavors != 0 && (cFlavor & rejectedFlavors) == rejectedFlavors {
    reject path
}
```

When entering an annotated child:

```swift
let childFlavor = (cFlavor | flavorAdd) & ~flavorRemove
```

The continuation after the child must retain the original caller flavor. This is
the essential discipline that makes flavors scoped rather than mutable.

## APUS Meta-Grammar

Teach `grammars/apus.apus` to parse:

```apus
flavorAnnotation =
    | "@setFlavor" "(" < identifier > ")"
    | "@clearFlavor" "(" < identifier > ")"
    | "@requiresFlavor" "(" < identifier > ")"
    | "@rejectsFlavor" "(" < identifier > ")" .
```

Allow flavor annotations in sequence position before a factor. Support
`@requiresFlavor` / `@rejectsFlavor` at alternate start too if that falls out
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
    | @rejectsFlavor(stmtCondition trailingClosure) newlineOpenedClosure
    .
```

Set condition flavor:

```apus
condition =
    | @setFlavor(stmtCondition) expression
    | availabilityCondition
    | caseCondition
    | missingIntroducerWildcardCondition
    | optionalBindingCondition
    .

whereExpression = @setFlavor(stmtCondition) expression .

repeatWhileStatement =
    "repeat" codeBlock "while" >-> ( "{" ) @setFlavor(stmtCondition) expression .
```

Set trailing-closure flavor:

```apus
trailingClosures =
    | @setFlavor(trailingClosure) @cannotParse(willSetDidSetBlock accessorBlockBrace)
      closureExpression labeledTrailingClosures
    | @setFlavor(trailingClosure) @cannotParse(willSetDidSetBlock accessorBlockBrace)
      closureExpression >-> ( "else" )
    .
```

Clear condition flavor at expression islands:

```apus
functionCallArgument =
    | @clearFlavor(stmtCondition) expression
    | argumentLabel ":" @clearFlavor(stmtCondition) expression
    .
```

Also check whether closure bodies need `@clearFlavor(stmtCondition)` around their
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

Flavor replacement:

```apus
attribute =
    "@" >s< "available" >s< "("
    @setFlavor(availableAttributeFlavor) availabilityAttributeArguments
    ")" .

staticStringLiteral =
    | singleLineStringLiteral
    | multilineStringLiteral
    | @rejectsFlavor(availableAttributeFlavor) extendedSinglelineStringLiteral
    | @rejectsFlavor(availableAttributeFlavor) extendedMultilineStringLiteral
    .
```

### Module selectors in binding names

Current:

```apus
moduleSelector =
    @excludedFrom(valueBindingPattern) identifierToken "::" >n< .
```

Flavor replacement:

```apus
moduleSelector =
    @rejectsFlavor(bindingIntroducer) identifierToken "::" >n< .
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

Flavor replacement:

```apus
initializerBody = @setFlavor(initializerBodyFlavor) codeBlock .

statement =
    @prefer @requiresFlavor(initializerBodyFlavor) >+> ( "init" ) expression .
```

If `initializerBody` is only a sentinel, consider inlining the flavor at
initializer declaration body sites after the first migration is stable.

### Nested `#if` leading-dot body

Current:

```apus
ifConfigStatements = statements .

ifDirectiveClause =
    @confinedTo(ifConfigStatements)
    ifDirective compilationCondition >+>( "." ) <n> ifConfigStatements? .
```

Flavor replacement:

```apus
ifConfigStatements = @setFlavor(ifConfigBody) statements .

ifDirectiveClause =
    @requiresFlavor(ifConfigBody)
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

Flavor replacement:

```apus
optionalBindingCondition =
    ( "let" | "var" ) @setFlavor(optionalBinding) pattern initializer? .

identifierPattern =
    | identifierToken
    | @requiresFlavor(optionalBinding) "self"
    .
```

Check whether the flavor should be even narrower than the whole pattern.

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

1. Implement flavor machinery while keeping containment.
2. Migrate TODO #5 only.
3. Run focused probes and limited SwiftSyntax tests.
4. Migrate the six remaining containment uses one at a time.
5. Run the full suite.
6. Remove containment machinery.
7. Run the full suite again.
8. Update documentation once syntax and semantics are stable.

This keeps the risky part reversible: flavors and containment can coexist until the
grammar no longer depends on containment.

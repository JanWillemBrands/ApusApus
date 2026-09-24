# Pattern Split in Swift.apus

Reference: [Swift Language Reference — Patterns](https://raw.githubusercontent.com/swiftlang/swift-book/main/TSPL.docc/ReferenceManual/Patterns.md)

The Swift spec defines two kinds of patterns:

1. **Destructuring patterns** — wildcard, identifier, and tuple patterns (with optional type annotations). Used in variable/constant declarations and optional bindings (`let x`, `guard let x`, `if var (a, b)`).

2. **Full match patterns** — additionally includes value-binding, enum-case, optional, type-casting, and expression patterns. Used in `case` labels, `catch` clauses, and `case` conditions of `if`/`while`/`guard`/`for`-`in`.

## Problem

A single `pattern` nonterminal accepting all 8 alternatives causes massive spurious GLL ambiguity at every declaration site, because `expressionPattern = expression` overlaps with `identifierPattern` — every identifier is both a valid binding pattern and a valid expression.

## Solution

Split into two nonterminals mirroring the spec's two kinds:

- **`bindingPattern`** — wildcard, identifier, tupleBinding (no expressions)
- **`matchPattern`** — full pattern language including expressionPattern

Reference sites updated:

| Context | Nonterminal |
|---------|------------|
| `patternInitializer` (let/var declarations) | `bindingPattern` |
| `optionalBindingCondition` (if/guard let/var) | `bindingPattern` |
| `forInStatement` without `case` | `bindingPattern` |
| `caseCondition` (if/guard case) | `matchPattern` |
| `caseItemList` (switch case labels) | `matchPattern` |
| `catchPattern` (catch clauses) | `matchPattern` |
| `forInStatement` with `case` | `matchPattern` |

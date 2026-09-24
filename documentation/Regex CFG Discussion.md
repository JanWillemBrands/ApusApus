# Regex as CFG Discussion

## Context

Swift slash regex literals are difficult for APUS because `/` can also be an operator character. The original scanner terminal:

```apus
plainRegularExpressionLiteral - /\/(?![\s*])(?:[^\/\\\n]|\\.)*(?:[^\/\\\n\s]|\\.)\// .
```

handles simple slash regexes, but it can over-claim source such as:

```swift
(/E.e).foo(/0)
```

by treating `/E.e).foo(/` as a regex span, even though the body is malformed. The goal was to explore whether the regex literal could be expressed as a character-level CFG so malformed delimiter structure is rejected.

## Basic CFG Shape

A first CFG form was:

```apus
plainRegularExpressionLiteral = "/" >s< regexBody >s< "/" .

regexBody = regexItem { regexItem } .

regexItem = regexEscape
          | regexCharacterClass
          | regexGroup
          | regexAtom
          .

regexGroup = "(" regexBody ")" .

regexCharacterClass = "[" regexClassBody "]" .
regexClassBody = regexClassItem { regexClassItem } .
regexClassItem = regexEscape | regexClassAtom .

regexEscape = /\\[^\r\n]/ .
regexAtom = /[^\/\\\[\]\(\)\r\n]/ .
regexClassAtom = /[^\\\]\r\n]/ .
```

This makes the body non-empty, enforces no whitespace adjacent to the opening and closing `/` via `>s<`, and rejects unmatched `(`, `)`, `[`, and `]` at the grammar level.

Swift rejects empty character classes such as `[]`, so `regexCharacterClass` should use non-optional `regexClassBody`.

## Escape Handling

`regexEscape` should remain separate from `regexAtom`. If `\(` or `\]` is split into ordinary atoms, escaped delimiters can incorrectly participate in balancing. Treating backslash plus the following scalar as one item prevents escaped brackets, parens, and slash from affecting the CFG structure.

## Operator Overlap Problem

The CFG form introduced a scanner/tokenization problem: anonymous regex terminals such as `regexAtom = /.../` overlap with operator terminals. For example, `^` inside `/^/` is both regex content and an operator character.

For:

```swift
^^/^/
```

we want two `^` operator characters followed by the regex `/^/`. But if `regexAtom` competes with operator terminals, the scanner may not expose the token shape needed by the grammar.

A mitigation is to avoid broad anonymous regex terminals for characters already owned by operator/literal terminals. Instead, define regex atoms using existing terminals where possible:

```apus
regexAtom = regexNonOperatorAtom
          | operatorHead
          | operatorSpecial
          | "."
          | "#"
          | ":"
          | ";"
          | ","
          | "="
          | "?"
          .

regexNonOperatorAtom = /[^\/\\\[\]\(\)\r\n\+\-\*%&\|\^~<>=!\?\.#;:,]/ .
```

That lets `^` be accepted inside a regex body through the same token used by operator parsing, avoiding a competing anonymous token.

## What This Solves

The CFG approach can reject malformed regex spans such as:

```swift
/E.e).foo(/
```

because `)` and `(` are not plain atoms. They can only appear as balanced `regexGroup` structure.

It can also accept:

```swift
/^/
```

because `^` is accepted as a regex atom via the existing operator terminal.

## What This Does Not Solve

This approach moves regex recognition from scanner-level to parser-level. The scanner emits ordinary tokens such as `/`, identifiers, dots, parens, and operator characters. The parser then decides whether a sequence is a `plainRegularExpressionLiteral`.

That means it does not preserve the original goal of resolving regex-or-operator entirely in the scanner.

If scanner-level resolution is required, using only existing APUS regex/literal terminals is not enough. The scanner currently knows how to match terminals, not arbitrary CFG productions. A scanner-level CFG would need a new generic mechanism, such as a grammar-declared lexical subgrammar or candidate validator.

## Alternatives Discussed

### Scanner Modes

Scanner modes can isolate regex-body token vocabulary from operator tokens, but a deterministic mode switch on every `/` would be wrong. In Swift, `/E.e` may need to remain ordinary slash/operator syntax, as in:

```swift
(/E.e).foo(/0)
```

So a regex mode would need to be speculative or parser-driven. Carrying mode state through all GLL descriptors would be expensive and unnecessary for this narrow case.

### Speculative Scanner Candidate

A lighter scanner-level option is to keep `plainRegularExpressionLiteral` as one token, but validate its candidate span with a small structural recognizer before accepting it. If validation fails, the scanner falls back to ordinary `/`.

This keeps parser internals unchanged: consuming the regex token still advances by one token, so CRF/SPPF extents, follow checks, boundary predicates, and `Token.dual` assumptions remain simple.

The drawback is that this requires a new scanner-side mechanism. If it is Swift-specific, it is too high-level. If it is grammar-defined, APUS needs a generic way to use a grammar-declared lexical subgrammar as a scanner candidate.

### Extended Schrödinger Tokens

Another possible direction is to allow token alternatives with the same start position but different end positions. This resembles the indexed-token-string model from multiple lexicalisation work.

That is more general but heavier. It changes parser input from a linear token stream plus same-span duals into a token lattice. It affects terminal matching, follow checks, extents, and SPPF construction. For the regex case alone, this is likely overkill unless both `/` and a valid regex span must survive to the parser.

## Current Conclusion

If the solution must use only existing APUS grammar elements, the CFG approach is feasible but parser-level:

```apus
plainRegularExpressionLiteral = "/" >s< regexBody >s< "/" .
```

with regex body rules that reuse existing operator/literal terminals to avoid scanner overlap.

If the solution must remain scanner-level, APUS needs one additional generic mechanism: a grammar-declared lexical subgrammar or candidate validator. Without that, a scanner terminal can only be a regex or literal, and cannot perform CFG-style delimiter balancing before tokenization commits.

---

## Consolidated design (from agent memory, 2026-07-30) — the completed, gated handling

The whole problem is that `/` is both a regex delimiter and an operator character;
swift-syntax resolves it in its lexer (maximal-munch operators +
`tryLexRegexLiteral` gated by `preferRegexOverBinaryOperator`). Our design mirrors it.

**Plain `/…/` — a parser-level CFG, position-gated.**
`plainRegularExpressionLiteral` is a CFG (`regexBody`/`regexItem`/`regexGroup`/
`regexCharacterClass` + atoms), NOT a flat terminal, because the CFG **balances**
nested `(…)`/`[…]` so malformed spans like `(/E.e).foo(/` are rejected (a flat regex
can't balance → over-claims). The CFG was never the ambiguity source; two missing
gates were. Delimiter `/` are regex terminals (`/\//`), exempt from operator munch.
Opening-slash position gate = `preferRegexOverBinaryOperator`, two productions on the
newline boundary: same-line `>n< regexOpenSlash …` and newline-leading
`<n> regexOpenSlashNL …`. `regexOpenSlash` carries `<-<(operand-enders)` (identifiers,
literals, `)]}>!.` `...` `->` `@`, value keywords, and **`regexCloseSlash`**), so
`0 /^/ 1` is operators but `2 ⏎ /x}/` is a regex. **CRITICAL:** since the regex is now
a CFG nonterminal, the token before a following operator is `regexCloseSlash` (the
closing `/` terminal), NOT `plainRegularExpressionLiteral` — any "after a regex"
operand-ender list must name `regexCloseSlash`.

**Extended `#/…/#` — a scanner terminal, NOT a CFG.** Its delimiters are unambiguous
by construction (opening `#`-count fixes the close via backreference `\1`; inside, `/`
is plain content). Rule of thumb: **CFG for the ambiguous delimiter (`/`), scanner
terminal for the unambiguous one (`#/…/#`).**

**Operator side — maximal-munch + prefix-gated split.** `@literalMunch operatorToken`
(includes `/`) munches `=/`, `.../`, `/^/` as single operators (kills the infix-op +
`/regex/` reading). `@splitBefore("/")` additionally offers "operator ends before an
internal `/`" so a regex can follow a **prefix** operator (`^^/regex/` → `^^` +
`/regex/`), gated to prefix position by `<-<(operand-enders)`. Engine rule: a failing
`<-<` on a `@splitBefore` terminal drops the SPLIT matches only (keep the maximal base
match — operators legitimately follow operands). `@splitBefore("/")` is on
`operatorToken` only; `@splitBefore("<")` on `operatorName` is the generic-`<` peel
(unrelated to regex). Outcome: Translated regex ambiguity 8→4, zero acceptance
regressions.

(Superseded note: the old `<<1/<<2` / `--1/++1` scanner-lookbehind naming — see
`Structured Lookahead Design.md` for the current `>+> >-> <+< <-<` scheme.)

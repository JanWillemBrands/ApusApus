# Active TODO

This file is the canonical active TODO list.

## 
## Grammar-directed fuzzer findings (2026-10-29)

## Million-sample grammar campaign findings (2026-10-30)

The campaign was stopped after 598,724 grammar-directed samples. It retained 409 deduplicated
artifacts from 228 overaccept, 166 underaccept, 438 tree-difference, and one residual-ambiguity
observations. The items below collapse repeated contexts and worker-local signal hashes into
independent grammar roots. Parse-only cases and compiler/SwiftSyntax disagreements are excluded.
Tree differences are also excluded here because tree equality remains an aspirational frontier,
not an acceptance-correctness signal.

14. Finish expression-position function-type tree reconstruction.
    - Acceptance is fixed structurally: the general `arrowExpr` recovery route is gone, genuine
      function types use `functionType`, and an `expressionType` flavor prevents `await` from being
      stolen as a bare type argument in expression context while preserving it in declared types.
    - Compiler-rejected/parse-only recovery fixtures are classified separately and APUS rejects
      the broad recovery forms.
    - The direct function-type converter still produces 31 distinct `trees match` failures (61
      parameterized failures across the two SwiftSyntax versions), concentrated in converting
      type-shaped parameter and result syntax back to its expression-shaped SwiftSyntax form.
      Fix that conversion without weakening the grammar or consulting SwiftParser as an oracle.

16. Tighten `switch` expression subjects and case bodies.
    - Representative examples: `switch initxx{}as _x` and
      `switch any{@rethrows default:@rethrows case ():}`.
    - APUS accepts a missing/malformed subject continuation and attributes where a switch body
      requires `case` or `default`. These appear related to permissive expression recovery but
      should be verified as separate grammar routes before editing.

17. Tighten pattern grammar in conditions and catch clauses.
    - Representative examples: `if var(){}as _`, `do{}catch deinit{}`, and
      `let((x: _),let x):some __shared Any{}`.
    - The independent failures are an empty optional binding, a non-pattern contextual keyword,
      and a nested `let`/`var` binding pattern.

18. Reject malformed key-path component sequences that the general expression/type routes admit.
    - Representative examples: `\~async ! init`, `\Protocol ! ! x`, and `[(init)of _]`.
    - Compiler diagnostics distinguish a missing key-path expression, separated unary operator,
      and missing separator; inspect which alternate bypasses `keyPathExpressionStop` before
      deciding whether these reduce to one fix.

19. Require expressions in collection and expression-list elements.
    - Minimal examples: `[,]` and `(inout ~[~some])`.
    - APUS accepts a missing collection element and a type-only construct in an expression list.

20. Tighten specialized attribute argument grammars.
    - Representative examples:
      `@attached(extension,extension,x(==(x:)),value)import x` and
      `@transpose(of:async,wrt:(Self,0,1)) typealias async = _`.
    - The first is missing required labels for attached-macro arguments; the second admits
      `Self` where `wrt:` requires a parameter name, parameter index, or `self`.

21. Reject extra expression tokens in conditional-compilation directives.
    - Minimal strong example: `#if each Self()\n#endif\n;`.
    - This is distinct from item 2: the compiler rejects the directive condition itself for extra
      tokens, whereas item 2 concerns a standalone semicolon after an otherwise complete block.

22. Enforce version syntax inside availability conditions even when nested in an `if` expression.
    - Minimal strong example: `guard if #unavailable(x 0.0,x ){}else{}`.
    - APUS accepts a platform name followed by a missing version where both references reject.
      Keep this separate from item 5, which has a valid availability condition in an invalid
      initializer boundary.

23. Enforce prefix-operator adjacency to its operand.
    - Minimal strong example: `\Protocol ! ! x`.
    - Swift rejects a unary operator separated from its operand; APUS currently finds a different
      expression decomposition. Check overlap with item 18 before implementing either fix.

24. Require at least one `catch` after a `do` statement with a `throws` clause.
    - Minimal strong example: `do throws(_.Type){}`.
    - `doStatement = "do" throwsClause? codeBlock catchClauses?` makes the catch list optional even
      when the throws clause is present; both references reject that combination.

25. Require a guard expression after `where` in a catch clause.
    - Minimal strong example: `do throws(~some){}catch where??await{}`.
    - The operator-looking text must not let the optional catch pattern/guard route reach the code
      block without a valid expression.

26. Reject an `if` expression with a missing condition when it appears as a guard condition.
    - Minimal strong example: `guard if (x){}else{}`.
    - This is not item 5's valid availability-expression boundary: the nested `if` itself lacks a
      condition, and APUS accepts it through a permissive parenthesized-expression route.

27. Enforce specialized type-attribute arguments, not just their balanced-token shape.
    - Minimal strong examples: `do throws(@differentiable(x) __shared){}` and
      `do throws(@isolated(x)__owned _x){}`.
    - The compiler requires `reverse` as the differentiability kind and a supported isolation kind;
      APUS currently accepts arbitrary identifiers. This may overlap items 12 and 20 at the use
      sites, but the root is the attribute argument grammar itself.

1. Investigate whether @preempt should be reworked in a Multiple Input Parsing lexer.
## Oracle: bring Swift in line with Bend/SPEC.bend (2026-10-31)

- Run `@left`/`@right` before `@prefer`/`@avoid`, as `Bend/SPEC.bend` orders them: hard rules
  first (lookahead, `@left`, `@right`), then preferences among the admissible trees, then
  `@longest`/`@shortest`. Today `OraclePass` runs filter → sameSpan → structure → extent, so a
  preferred rival with no admissible tree still beats the plain reading and every reading is
  lost. Test: `OracleDisambiguationTests` / "Annotation order (spec)" (a known issue until
  fixed; remove the `withKnownIssue` when it passes).
  `Bend/UNBEATEN.bend` now implements the joined order and is proven
  (`prefer_avoid_exact`, 2026-11-01); `BendCheck.joinAgainstBend` compares Swift with it on
  the same grammar (also a known issue until Swift is fixed).
  - Before reordering, check `f(1) {}⏎{}` (the measured bug in `Oracle.swift`'s `OraclePass`
    comment, why `@prefer` runs before `@right`) against `Bend/SPEC.bend`'s `@right`: Swift's
    `@left`/`@right` ask which production occupies a span, the spec asks what the alternative
    can derive. Swapping the passes may bring the bug back, or the spec may rule out the
    intended reading.
- Make `@left`/`@right` mean what `Bend/SPEC.bend` says: the edge child is out when the
  alternative itself (bare) or a listed nonterminal derives its tokens. Today
  `AssociativityFilterRule` compares spans with the forbidden extents of the last body symbol
  or the named nonterminals. The spec is stricter in one place: under
  `E = @left E "+" E | E "+" F | number` it also removes a last child that went through
  `E "+" F`. Add a Bend-vs-Swift case for it (`BendCheck.guardCases`).
- Make nonterminal `@longest X`/`@shortest X` local, as agreed for `Bend/SPEC.bend`: a marked
  node is out when the enclosing sequence, over the same tokens, can be read with it longer
  (shorter). Today `LongestMatchRule`/`ShortestMatchRule` keep the longest/shortest yield per
  start across all readings (global, order-dependent, can remove every reading). Bracket
  extent (`constrainedTilings`) is already local.
- Remove the dead wood the extent pass leaves (found by `BendCheck.extentsAgainstBend`,
  2026-11-01). Under `S = "if" "e" "then" S @longest [ "else" S ] | "a"` on
  `if e then if e then a else a`, Swift keeps exactly the best tree, plus two steps of the
  losing reading that are on no tree: `Slot{0, [5]}` at (0, 7, 7) and (3, 7, 9). The outer
  step was removed, but the inner node it held was not. This is the "incremental dead-wood
  removal after rule passes" item. The other 15 extent cases agree with `Bend/EXTENT.bend`,
  apart from loop iteration ends (next item).
  The preference pass does the same: under
  `S = "if" "e" "then" S "else" S | @prefer "if" "e" "then" S | "a"` Swift keeps the losing
  reading's outer node and its children (9 steps on no tree; `BendCheck.preferCases`,
  "dangling else, without else").
  - A note on the semantics, which Swift and Bend share here: with local `@longest`,
    `@longest [ "else" S ]` gives the `else` to the OUTER `if`, because the outer sequence's
    optional is longer that way. The usual dangling-else reading, with the `else` on the
    inner `if`, is what `@shortest [ "else" S ]` selects. Check Swift.apus's uses of
    `@longest` on optionals with this in mind.
- Make the dependency of `@longest` on loop iteration ends explicit: the Oracle's phase 1 keeps
  them on purpose (`Bend/README.md`, the phase 1 exception), and the Bend comparison discounts
  them as dead wood.
- Decide whether token lookaround `>+>`/`>->`/`<+<`/`<-<` takes nonterminals and replaces
  `@canParse`/`@cannotParse` (`Bend/SPEC.bend`, `Ahead`/`NotAhead`; a grammar-language change).
- Oracle speed (paused 2026-10-29): skipping confirming walks and a cheaper `TileKey` measured
  4.7 s → 3.3 s on `Oracle.swift`; `committingStatementDeclaration` fallback sub-parses cost
  0.95 s. Rolled back as unproven; redo once the Bend twin of the Oracle is complete.


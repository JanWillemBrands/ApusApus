# PEG-GLL Deviations for Python: Oracle Pruning Plan

## Objective

Keep the APUS grammar close to CPython's reference PEG grammar, allow controlled over-generation in GLL, and recover CPython-equivalent behavior by pruning the BSR/SPPF with a post-parse oracle.

This note focuses on **where PEG and GLL differ**, and how each difference can be enforced after parsing.

## Working Assumptions

- Scanner can intentionally over-generate (Schrodinger tokens, broad NAME-like tokens, scanner-mode approximations).
- Parser is GLL, so alternatives are explored without PEG ordered-choice commitment.
- Final acceptance is decided by an oracle pass that prunes invalid BSR branches.
- We prefer parser grammar readability and Python-reference parity over embedding too many ad hoc scanner/parser hacks.

## Deviation Catalog (PEG -> GLL)

## 1) Ordered choice and PEG commit (`~`)

Reference examples in `Python3.14.4.txt`:
- `single_target augassign ~ annotated_rhs`
- `for ... in ~ disjunction`

PEG meaning:
- Once the parser reaches `~`, it commits to this alternative.

GLL effect:
- Competing alternatives may survive in the forest.

Oracle rule:
- At each rule with PEG-commit semantics, keep only branches consistent with the committed alternative once commit point is crossed.
- Prune sibling branches at the same nonterminal+span that violate commit.

## 2) Negative and positive syntactic predicates (`!e`, `&e`)

Reference examples:
- `simple_stmt !';' NEWLINE`
- `del_targets &(';' | NEWLINE)`
- `expression !':='`
- `NAME !('.' | '(' | '=')`

PEG meaning:
- Predicate checks are zero-width constraints on viability.

GLL effect:
- Without equivalent constraints, invalid branches can remain.

Oracle rule:
- Re-evaluate predicate at branch boundary using token stream and local subtree context.
- Drop branch if predicate truth value is false.

## 3) Eager parse (`&&e`)

PEG meaning:
- Immediate failure without backtracking if `e` fails.

GLL effect:
- Backtracking-like alternatives may persist.

Oracle rule:
- Treat `&&e` as a hard viability gate for the containing branch.
- If eagerly-required subpattern is absent, prune that branch regardless of alternatives.

## 4) `invalid_*` second-pass error productions

Reference comments in grammar header:
- `invalid_*` rules are excluded first pass, enabled in second pass only.

PEG meaning:
- Two-phase parse strategy for better diagnostics.

GLL effect:
- If invalid rules are always present, forest can include error-intent derivations as normal parses.

Oracle rule:
- Phase A: prune/ignore all `invalid_*` nodes and test if any valid full parse remains.
- Phase B (only if A fails): enable `invalid_*` branches for diagnostic extraction.
- Report first-pass failure location for final error position policy parity.

## 5) Assignment-expression (`:=`) exclusions

Reference examples:
- `assignment_expression: NAME ':=' ~ expression`
- `named_expression: assignment_expression | expression !':='`

PEG meaning:
- Context-specific admissibility of walrus.

GLL effect:
- Both assignment-expression and plain-expression branches may survive.

Oracle rule:
- Enforce context restrictions for `:=` by parent nonterminal kind.
- Remove branches where `:=` appears where PEG excludes it.

## 6) Pattern matching exclusions and capture constraints

Reference examples:
- `!'_' NAME !('.' | '(' | '=')`
- `attr !('.' | '(' | '=')`

PEG meaning:
- Prevent forbidden capture forms.

GLL effect:
- Over-accepts pattern captures/attrs unless constrained.

Oracle rule:
- For pattern nodes, enforce keyword/exclusion predicates and trailing-token constraints.
- Prune captures using `_` and invalid follow sets.

## 7) Rule-order sensitivity used as disambiguation

Reference note:
- `assignment MUST precede expression`

PEG meaning:
- First matching alternative wins.

GLL effect:
- Both interpretations can survive.

Oracle rule:
- Attach PEG priority ranks to alternatives.
- If multiple branches span same nonterminal+extent, keep highest-priority surviving branch after predicate/commit pruning.

## 8) Soft keyword policy (`match`, `case`, `type`)

Current APUS approach:
- `rawName` broad token.
- `NAME` excludes hard keywords only.
- Soft keywords remain admissible as names where grammar permits.

Potential GLL over-generation:
- Simultaneous keyword and identifier interpretations in ambiguous positions.

Oracle rule:
- Keep both token interpretations through parse.
- At contextual nonterminals (e.g., `match_stmt`, `case_block`, type alias contexts), prune branches that violate soft-keyword role constraints.

## 9) `t_lookahead` partitioning for primaries

Reference examples:
- `t_primary ... !t_lookahead`
- parallel alternatives with `&t_lookahead`

PEG meaning:
- Carefully partitions call/subscript/attribute continuations.

GLL effect:
- May retain both continuation and terminal atom forms.

Oracle rule:
- Evaluate lookahead partition deterministically per span boundary.
- Keep only branches consistent with the selected partition.

## 10) F-string structure and nested replacement fields

Reference PEG summary:
- `FSTRING_START fstring_middle* FSTRING_END`
- `fstring_replacement_field` recursively inside format specs.

Current APUS model:
- Scanner modes (`fstr-*`, `fstr-expr`, `fstr-spec`) with transitions.

Known risk:
- Colon transition in expression mode can conflict with lambda-colon and other expression-local colons.

Oracle rule:
- Validate f-string replacement-field shape after parse:
  - braces balanced by replacement-field nesting,
  - conversion segment (`!r`, `!s`, `!a`) placement valid,
  - colon starts format-spec only at valid replacement-field boundary,
  - nested replacement fields in format spec remain structurally valid.
- Prune branches where colon role is inconsistent.

## 11) Deviation interaction: f-strings (5) and bracket newline suppression (6)

Potential interaction bug:
- Newline suppression by `bracket-mode` can mask f-string-expression boundaries or keep invalid multiline shapes.

Oracle rule:
- For each f-string expression subtree, verify newline legality under Python implicit-join rules and brace nesting.
- Reject branches where newline acceptance depends on illegal mode path.

## 12) Layout-token approximation (INDENT/DEDENT and blank lines)

Current APUS approach:
- Pre-injected layout tokens (`>>|`, `|<<`) and permissive blank-line handling.

Risk:
- Alternative layout derivations may survive where CPython tokenizer behavior would be unique.

Oracle rule:
- Enforce indentation stack consistency across statement blocks at tree level.
- Prune branches with impossible indent/dedent transitions or invalid blank-line participation.

## Oracle Pruning Pipeline (Recommended)

1. Build full forest (BSR/SPPF) from scanner + GLL.
2. Annotate candidate nodes with:
   - nonterminal kind,
   - token span,
   - parent context,
   - selected PEG-sensitive markers (commit points, predicates, lookahead sets).
3. Apply pruning passes in this order:
   - predicate pass (`!`, `&`, `&&`),
   - commit pass (`~`),
   - context pass (walrus, patterns, soft keywords),
   - f-string structural pass,
   - layout consistency pass,
   - PEG priority tie-break pass.
4. Iterate to fixed point (until no more branches removed).
5. Accept parse if at least one root-complete branch remains.
6. If none remains, run diagnostic phase with `invalid_*` branches enabled for error reporting.

## Data Needed Per Branch (Minimum)

- Token span and direct children.
- Alternative index for each rule node.
- Predicate metadata (what must hold at boundary).
- Commit metadata (commit point reached or not).
- Lightweight token lookahead view at boundary positions.

## Why This Keeps Grammar Close to Python

- You can preserve CPython-style grammar shape and naming.
- Scanner can stay simple/fast and permissive.
- PEG-specific control logic moves to one explicit semantic-pruning layer.
- Future parity work is incremental: add oracle predicates without destabilizing core scanner/parser.

## Open Questions

1. Should PEG-priority tie-break happen only after all hard constraints, or interleaved per nonterminal class?
2. Do we want a strict mode (exact CPython acceptance) and a permissive mode (keep more branches for tooling)?
3. How much oracle metadata should be encoded in grammar annotations vs generated from rule patterns?
4. For diagnostics, should we retain pruned branch traces for "why rejected" reporting?

## Practical Next Step

Start with a small oracle subset that typically causes real divergence:
- `!':='` / walrus context,
- pattern capture exclusions,
- f-string colon/conversion placement,
- PEG alternative priority on same-span siblings.

Then add commit (`~`) and layout consistency passes.

# Active TODO

This file is the canonical active TODO list for the project. Keep completed investigations, fix logs, and historical run notes out of this file unless they directly describe an open issue.

## Parser / Grammar Correctness

1. **Fuzzer: audit member-list tree differences before changing member-list grammar.**
   From `AdventFuzzer/runs/2026-09-23T13-51-59Z`: largest unique tree-difference bucket was
   `member-list-boundary` with 58 unique artifacts. These deliberately stress semicolon/newline
   attribution across attributes, conditional compilation, subscripts, initializers, and nested enums;
   they probably overlap the existing semicolon-bearing member-list migration TODO. Compare tree
   shape first, especially semicolon ownership and member boundary attribution.

   Verified 2026-09-23: replaying eight saved member-list artifacts produced two current
   `tree-difference` results and six `same` results. The bucket is still present, but the old 58-artifact
   count is stale; run a fresh member-list-focused harvest before making grammar changes.

2. **Fuzzer: fix key-path optional/force component tree differences.**
   The last two runs show a distinct tree-shape bucket where SwiftSyntax emits a
   `KeyPathOptionalComponent`, while Advent emits a plain period/member component. This is separate from
   the Oracle-carried key-path overacceptance tracking below.

   Current run evidence: `AdventFuzzer/runs/2026-09-23T16-51-59Z` has 29 key-path-shaped
   `tree-difference` artifacts. Representative artifacts:

       let fuzzValue = value[keyPath: \Foo.foo! .bar]
       let fuzzValue = \Foo.Bar.default? .name
       let fuzzValue = (\.type.defaultInitialization? .name)

   Artifact IDs: `00000692-tree-difference-820a178f205e92da.json`,
   `00028583-tree-difference-d0eedd27de3f97c8.json`, and
   `00031201-tree-difference-3c83b095bcca8a59.json`. First diff is consistently
   `KeyPathOptionalComponent` vs `period "."`; start in the key-path converter before changing grammar
   acceptance.

3. **Track Oracle-carried overacceptance in key-path grammar sweeps.**
   `KeyPathGrammarTests` reports `oraclePruned`, the gap between yield-level and tree-level
   acceptance. It was non-zero on 2026-09-23 (4 cases at CORE length 3, 9 at WIDE length 2), meaning
   those overacceptances are carried by the Oracle rather than structurally excluded. Not a defect
   under the project's accept/reject criterion, but this is fragile correctness; keep it visible when
   changing key-path or Oracle behavior.

   Verified 2026-09-23: still open as tracking debt; the probe still reports `oraclePruned`, and no
   follow-up sweep result is recorded here proving this gap went to zero.

   Note from completed macro/pound audit: after fixing member-position `#if` conversion, one remaining
   saved candidate that merely contained `#if` first diverged as `KeyPathOptionalComponent` vs `period "."`;
   handle that with key-path work, not macro/pound conversion.

4. **Fuzzer: classify compiler/typechecker-only SwiftSyntax acceptance telemetry.**
   The latest long run contains many `compiler-typecheck-rejects-swiftsyntax-accepts` and
   `compiler-rejects-swiftsyntax-accepts` artifacts. These are not Advent-vs-SwiftSyntax parser
   mismatches, but they add noise and some are useful generator/filter signals.

   From `AdventFuzzer/runs/2026-09-23T16-51-59Z`: 56 signal-deduped telemetry artifacts. Examples:

       struct Fuzz<T: UInt8!> { var value: T }
       struct Fuzz<T: any P> { var value: T }
       let fuzzValue = f { value }
       .
       member
       let fuzzValue = try.
       f()

   Decide whether to keep these as telemetry only, suppress semantic type-check-only failures from
   TODO triage, or create dedicated generator lanes for parser-vs-compiler disagreement.

5. **Audit identifier nonterminal usage against swift-syntax.**
   Check all uses of `identifier`, `softIdentifier`, and `hardIdentifier` against the corresponding swift-syntax parser positions. Be careful: member names, labels, declaration names, pattern names, and type names intentionally differ.

   Verified 2026-09-23: still present. `Swift.apus` still has many position-specific uses of
   `identifier`, `softIdentifier`, and `hardIdentifier`; no completed audit note or fixture sweep is
   recorded in this TODO.

6. **Finish the list migration: the 7 semicolon-bearing member lists.**
   17 of 24 list rules are now EBNF closures (done 2026-09-21). The remaining seven —
   `statements`, `enumMembers`, `structMembers`, `classMembers`, `actorMembers`,
   `protocolMembers`, `extensionMembers` — were left DELIBERATELY, because the rewrite is not a
   simplification there:

       statements = statement ";"? .
       statements = statement statementSeparator statements .

   with `statementSeparator = <n> | ";"`. The `";"?` base case puts a semicolon in the SAME hop as
   the member it terminates, which is what `collectMembers`/`hasExplicitSemicolon(in: hop)` relies
   on ("it belongs to the member it terminates"). A closure spelling
   `statement { statementSeparator statement } ";"?` moves each separator into the hop of the
   FOLLOWING member, inverting that association — same language, different semicolon attribution.
   Converting these needs the semicolon association reworked first (probably per-hop lookbehind
   rather than per-hop membership), so it is a separate change with its own fixtures, not part of a
   mechanical sweep.

   Also leave alone permanently — these are right-recursive but NOT lists, so `{ }` would change
   their meaning: `type = parameterModifier type` / `attribute type`,
   `prefixExpression = "consume"/"borrow"/"copy"/"unsafe" … prefixExpression`, and
   `compilationCondition` `&&`/`||` (prefix chains and operator precedence, not repetition).

   Verified 2026-09-23: still present. `Swift.apus` still has the seven right-recursive
   semicolon-bearing member-list forms at `statements`, `enumMembers`, `structMembers`, `classMembers`,
   `actorMembers`, `protocolMembers`, and `extensionMembers`.

## Regex / Trivia Architecture

3. **Convert the plain-regex body to a lexical recognizer only after the blockers are solved.**
   Prior attempts regressed reject behavior because `regexSlash >s< regexBody >s< regexSlash` also forbids spaces adjacent to delimiters, and recognizer bodies do not automatically propagate tightness through ordinary `=` nonterminals. A viable retry must express delimiter-adjacent space structurally and either inline the recognizer body or safely propagate trivia suppression through recognizer-only calls.

   Related dead code to remove when this is touched: the LEADING `>n< <-<` gate on
   `tryScanOperatorAsRegexLiteral` never fires. A `@preempt` sub-parse starts with an empty commit
   log, so the lookbehind finds nothing and the negative form returns true. It is currently masked
   by the live gates on `plainRegularExpressionLiteral`.

4. **Keep regex literal text reconstruction faithful.**
   `convertLiteral` treats `regularExpressionLiteral` as opaque, but `collectTerminalText` / `tiledText` reconstructs text from committed child tokens. If regex trivia ownership changes, add coverage for spaces and tabs inside regex literals. The overnight run found Advent building `regexLiteralPattern("ab")` for SwiftSyntax's `regexLiteralPattern("a  b")` in `try? /a  b/`; keep the known `_ = /a<TAB>b/` accept/reject gap covered too.

5. **Make trivia handling principled.**
   Current trivia ownership depends on mode: normal tokens consume trailing trivia, recognizers leave it for the surrounding recognizer, and boundary checks are computed on the hot path. Open design work remains around explicit cursor normalization, cached boundary/trivia facts, and a round-trip test asserting trivia spans reconstruct the source byte-for-byte.

## Tests / Fixtures Needed

6. **Add a preserving-trivia round-trip test.**
   This should assert that token/trivia spans reconstruct the original source exactly.

7. **Add tuple-type label ambiguity fixture.**
   `elementName` was fixed to avoid ambiguity on `(_: Int)`, but no dedicated ambiguity fixture currently protects that shape.

8. **Add extension converter tree fixtures.**
   `convertExtensionDeclaration` now delegates to `convertType`, covering `extension [Int] {}` and `extension UInt8? {}`. Add tree-equality fixtures so this converter path is protected, not only acceptance-tested.

9. **Measure swift-syntax source-file tree equality when affordable.**
   Advent source-file tree equality is clean, but the swift-syntax source corpus tree comparison is still too expensive for routine runs. Profile tree building before turning the 317-file tree comparison into a regular gate.
   FIRST DATA POINT (2026-09-21): they are NOT clean — `CompilerPluginMessageHandler.swift`
   differs. Only the Advent corpus was ever brought to tree parity, so the 317 need their own
   pass. A full tree run is ~40min, so profile the tree path first.

## Performance Work

10. **Investigate remaining context-free prediction cost for interpolation Tail/Part terminals.**
   The earlier `followCheck` and Oracle work removed known cliffs, but interpolation Tail/Part prediction can still drive many distinct regex probes. Profile before changing prediction order or caching; `cachedLex` already memoizes `(position, terminalID)` and many expensive calls are first-time queries.

## Maintenance Rule

- Add new TODOs here only when they are active and actionable.
- Move completed investigations and historical explanations to design notes or commit messages.
- Reference an item by its TITLE, never by its number — e.g.
  `TODO.md / Make trivia handling principled`. Numbers rot on every renumber, and at the
  2026-09-23 cleanup a dozen references across `Swift.apus`, the tests and the design notes pointed
  at items that had moved or no longer existed (`TODO #0`, `TODO.md 23`, `TODO.md 10`). The live
  ones were converted to titles; any remaining `TODO #n` in a design note is historical.
- Prefer an executable MODEL over per-case patching when an area starts accreting filters: port the
  reference algorithm, validate it against swift-syntax by enumeration, then use it as the oracle
  for the grammar. That is what closed key paths, and the same harness (`KeyPathGrammarTests`) is
  the template — a sweep that reports over- and under-acceptance separately, with NO allowance list
  (an exemption written for one class silently swallowed a different one).
- `Advent/codex.md` and `Advent/claude.md` should reference this file instead of maintaining separate TODO lists.

# Active TODO

This file is the canonical active TODO list for the project. Keep completed investigations, fix logs, and historical run notes out of this file unless they directly describe an open issue.

## Parser / Grammar Correctness

1. **Fuzzer: regex after a keyword-spelled member name (last open case of the 2026-09-23/25 harvests).**
   `x.default / y`, `x.for / y`, `x.in / y`, `x.init / y`, `\.default / value` are rejected by
   swift-syntax and accepted by Advent. swift-syntax's lexer classifies `default` as a KEYWORD even in
   member position, and after any keyword except `true false nil self Self super Any` a `/` is in
   regex position. A SPACED `/` there is forced to be a regex (`RegexLiteralLexer.swift`
   ~715, `mustBeRegex`), which then fails. Advent's member name commits the word as `identifier`, so
   the regex lookbehind treats it as a non-regex position and `/` becomes the division operator.
   A fix needs both: member names spelled as lexer keywords committed as keyword terminals (e.g. a
   `lexerClassifiedKeyword` alternate in `memberName`), and a gate forbidding a spaced binary `/`
   in regex position. Tight `x.default/y` already agrees.

   Done 2026-09-27 (fixtures: `SwiftSyntax - fuzz harvest fixes`): every other saved case replays
   as `same` — 66 of 68 across both runs' artifacts (`tools/replay_fuzz_sources.py`). Policy:
   swift-syntax is the ground truth, so `compiler-typecheck-rejects-swiftsyntax-accepts` counts as
   Advent underacceptance; its sources now land in `telemetry.jsonl` (FUZZER.md / Triage).

2. **Finish the list migration: the 7 semicolon-bearing member lists.**
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

3. **Fix or replace `@sameLine` (`SameLineSpanRule` in `Oracle.swift`).**
   Kept as is on 2026-09-25; only the stale "exactly one alternate" assertion was removed (it fired
   on every parse once assertions ran in Debug, because `singleLineInterpolatedStringLiteral` has a
   plain and an extended alternate, both legitimately single-line). Known defects, from reading the
   code, not yet probed:
   - Block comments are trivia, not commits, so `newlineBearingTokens` never contains them:
     `"\(x /*⏎*/)"` is probably pruned although swift-syntax (block comment lexed whole in
     `.noNewlines` mode) likely accepts it. Probe `hasError` first.
   - The token cover comes from `commits`, which includes abandoned derivations. For
     `newlineBearingTokens` that can only miss a prune, but `tokenStarts` works the other way: an
     extra token start makes a trailing newline look crossed, so the "never removes a legitimate
     parse" claim in the doc comment does not hold in principle.
   - It is an Oracle rule, so any acceptance check on raw yields ignores it; `adventAcceptsFile`
     (source-file suites) never applies it.
   - Cost: every yield scans all newlines of the input, and each in-span newline scans all
     commits. Possibly a contributor to the slow large-file parses (see
     `TODO.md / Fix the Oracle stack overflow and very long parses on large source files`);
     unmeasured.
   Preferred replacement: model it lexically, as swift-syntax does. From each `\(` in a single-line
   literal, scan to the matching `)` skipping nested strings (raw, multiline) and comments; a
   newline met outside those refuses the Head at that position. Removes the Oracle rule and the
   commit-log scan, and applies uniformly to every acceptance check. Validate against swift-syntax by
   enumeration, as `KeyPathGrammarTests` does. Open question: whether the lexer has a hook for a
   hand-written check like this.

4. **Enum cases in a function body nested in a member list are wrongly accepted.**
   `struct S { func f() {⏎#if FOO⏎case a⏎#endif⏎} }` (and without the `#if`) is rejected by
   swift-syntax but accepted by Advent. `enumCaseDeclaration` is `@confinedTo` the six member-list
   nonterminals, and containment is by SPAN: the function body lies inside a `structMember`, so the
   case counts as contained. The real rule is "the NEAREST enclosing block is a member list", which
   span containment cannot express. Fixed 2026-09-25 alongside this: cases inside `#if` in a member
   list were REJECTED (fixtures `case-ifconfig*` in `Phase3EnumCaseTests`). Options: a
   nearest-context containment rule, or parse member-position `#if` bodies as members and make
   `enumCaseDeclaration` a `memberDeclaration`-only alternative (structural, but the converter's
   member `#if` path reads `statements` today).

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

   GLOBAL REVISIT (2026-09-25): trivia is being handled case by case and is turning into a
   patchwork. Every consumer re-derives "where does the real content end" on its own, differently.
   Symptoms found in one day:
   - A yield's `j` is `triviaEnd`, so every span carries its trailing trivia. The key-path pivot
     converter read `! ` instead of `!` and silently dropped the component; fixed by trimming
     WHITESPACE only, so `\Foo.foo! /* c */ .bar` presumably still loses the mark (untested).
   - `SameLineSpanRule` needs a separate "a token must START after the newline" test just to tell
     a crossed newline from one in the span's own trailing trivia (see
     `TODO.md / Fix or replace @sameLine`).
   - Trivia (`:` declarations: whitespace, comments, block comments) is skipped rather than
     committed, so anything working from `parser.commits` cannot see a block comment; the sameLine
     rule's "newlines inside a block comment are fine" claim does not hold for that reason.
   - The converter reads raw span text in 11 places (`input[from..<to]`) and trims whitespace in 9,
     each deciding locally what trivia to ignore.
   - Layout gates (`>n<`, `<n>`, `>s<`, `<s>`) and `@sameLine` are two independent mechanisms for
     the same kind of fact (what trivia lies between two tokens).
   - Plain `/…/` regex bodies are token sequences with trivia skipped between them. A tab is now
     rejected by a whole-literal token gate, but a `/*…*/` between body tokens is still skipped as a
     comment: `_ = /a/*x*/b/` is accepted, swift rejects. Tight `>s<` junctions cannot fix it,
     because a token absorbs its trailing trivia, so a following SPACE is gone before
     `regexSpaceAtom` can match and `/a b/` would be rejected (tried 2026-09-25). Needs "only spaces
     in this gap", i.e. the trivia facts above.

   ROOT CAUSE, shared by the regex gap and `@sameLine`: APUS has no LEXER MODES. swift-syntax's lexer
   keeps a state stack and changes its trivia policy by context — no trivia at all inside a regex
   literal (the whole `/…/` is ONE token, scanned lexically, bracket balance included), and no
   newlines in trivia inside a single-line string interpolation (`.noNewlines`). APUS applies one
   global trivia policy (whitespace and comments) at every token gap, and the grammar can only veto
   a gap afterwards with coarse gates (`>s<`, `>n<`) or, for interpolation, the Oracle span rule.
   It is a lexer/parser boundary decision: swift keeps the regex body on the lexer side and only
   the "does this `/` start a regex" decision on the parser side; Advent moved the body to the
   parser side (to get group/class balance and the prefix-slash ambiguity from the CFG), and so
   inherited the global trivia policy inside it.
   - REGEX (the easy instance): move the body back to the lexer side WITHOUT losing its structure,
     via the existing structured `-` lexical recognizer (a sub-parse over the same `regexBody`
     rules that emits one token). Inside it no trivia is skipped, so tabs, `/*…*/`, `//` and
     newlines are decided by what body tokens match, exactly as in swift; keep the regex-vs-operator
     gates on the parser side. Blockers are those in
     `TODO.md / Convert the plain-regex body to a lexical recognizer only after the blockers are solved`:
     trivia suppression must hold for the recognizer's WHOLE extent, including ordinary `=`
     nonterminals inside it (the engine fix), and "no space next to a delimiter" must be written
     into the body rule instead of relying on `>s<` at the delimiters.
   - INTERPOLATION (the hard instance): a `\(…)` segment holds full expressions, so it must stay on
     the parser side. It needs a trivia MODE inherited through the expression grammar (a descriptor
     flag or a cloned sub-grammar), which would replace `SameLineSpanRule`
     (`TODO.md / Fix or replace @sameLine`).
   - Not recommended: a new "horizontal whitespace only" gate. It would close the regex case but is
     one more local patch of exactly the kind this item is meant to retire.
   Direction: one source of truth for token CONTENT span vs trivia span — e.g. store content end
   (and leading/trailing trivia ranges, including comments) on commits and expose it to yields, so
   the Oracle and converter ask for content bounds instead of trimming text. Then retire the local
   trims and re-express the sameLine and layout checks over the same facts. The round-trip test
   (`TODO.md / Add a preserving-trivia round-trip test`) is the guard for this refactor.

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

11. **Fix the Oracle stack overflow and very long parses on large source files.**
   Found 2026-09-25 while running the opt-in source-file suites (`APUS_SOURCE_FILE_SUITES=1`, Release).
   - CRASH: the swift-syntax corpus dies with `EXC_BAD_ACCESS` "Thread stack size exceeded due to
     excessive recursion". The stack is the mutual recursion `visit` → `visitAlternates` →
     `tileBody` → `visitSymbol` → … inside `Oracle.pruneUnproductive(endPosition:)`, bottoming out in
     `endPositions`. Recursion depth tracks derivation depth, which on a whole file (long statement
     lists, deep nesting) exceeds the small stack of a Swift Testing worker thread. First files hit:
     `BasicFormat.swift`, `Indenter.swift`, `InferIndentation.swift`, `Syntax+Extensions.swift`,
     `SyntaxProtocol+Formatted.swift`. One crash kills the test process, so every remaining case in
     the run reports the same crash.
   - SLOW — FIXED 2026-09-26. Profiled with `sample` on the fuzzer probe: ~87% of Oracle time was
     `pruneUnproductive` answering "ends of this symbol's yields starting at p" and "is there a yield
     spanning [p, q]" by SCANNING the symbol's yields, i.e. O(yields × queries) — quadratic. A
     per-call yield index (`YieldIndex` in `pruneUnproductive`) makes them lookups. Result: the
     524 KB file 20+ min → ~140 s (parse ~28 s, Oracle ~62 s, tree ~3 s); `ApusToHTML.swift`
     321 s → 10 s; the whole Advent source-file suite now passes in ~145 s.
     Remaining cost is linear but repeated: `pruneUnsupported` and `pruneUnproductive` each rescan
     all ~2M yields per fixpoint pass, and the Oracle alternates them until nothing is removed.
     Next step if it matters: a worklist (re-check only yields whose supporters changed).
   Fix direction for the CRASH: make the walk iterative (explicit work stack) rather than raising
   the thread stack size, which only moves the limit.

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

# Active TODO

This file is the canonical active TODO list for the project. Keep completed investigations, fix logs, and historical run notes out of this file unless they directly describe an open issue.

1. **Improve fuzzer coverage guidance and parallelism.**
   Add feedback from grammar coverage so the corpus keeps inputs that reach something new: a
   `Swift.apus` alternate never seen in a final derivation, an Oracle rule that removes something for
   the first time, a swift-syntax node kind never seen before, or a new `signalHash`. If
   overacceptance stays dominant, add a generation lane from `Swift.apus` itself using depth limits
   and weights that fall as alternatives are used. Later, add tree mutators over the real-source and
   swift-syntax corpora (swap same-kind nodes, delete or duplicate list/optional elements, hoist). Do
   not spend time on a full LibFuzzer/code-coverage integration unless the cheaper coverage signals
   stop finding bugs. Done 2026-09-27: `bin/run-night.sh` now uses all cores by default and gives each
   worker a distinct derived seed.

2. **Finish the list migration: the semicolon-bearing member lists.**
   Check if these can/should be converted: enumMembers`, `structMembers`, `classMembers`, actorMembers`, `protocolMembers`, and `extensionMembers`.

3. **Remove or diagnose SwiftSyntax reparsing fallback for multiline interpolated strings.**
   `GenerateSwiftSyntaxAST.reparseStringLiteralExpression` calls SwiftSyntax's parser for plain
   multiline strings with active interpolation, so `trees match` compares SwiftSyntax with itself for
   that subtree and hides APUS converter gaps. Replace it with APUS-derived conversion, or at least
   record a fallback diagnostic before returning the reparsed subtree.

4. **Fix or replace `@sameLine` (`SameLineSpanRule` in `Oracle.swift`).**
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

5. **Convert the plain-regex body to a lexical recognizer only after the blockers are solved.**
   Prior attempts regressed reject behavior because `regexSlash >s< regexBody >s< regexSlash` also forbids spaces adjacent to delimiters, and recognizer bodies do not automatically propagate tightness through ordinary `=` nonterminals. A viable retry must express delimiter-adjacent space structurally and either inline the recognizer body or safely propagate trivia suppression through recognizer-only calls.

   Related dead code to remove when this is touched: the LEADING `>n< <-<` gate on
   `tryScanOperatorAsRegexLiteral` never fires. A `@preempt` sub-parse starts with an empty commit
   log, so the lookbehind finds nothing and the negative form returns true. It is currently masked
   by the live gates on `plainRegularExpressionLiteral`.

6. **Keep regex literal text reconstruction faithful.**
   `convertLiteral` treats `regularExpressionLiteral` as opaque, but `collectTerminalText` / `tiledText` reconstructs text from committed child tokens. If regex trivia ownership changes, add coverage for spaces and tabs inside regex literals. The overnight run found Advent building `regexLiteralPattern("ab")` for SwiftSyntax's `regexLiteralPattern("a  b")` in `try? /a  b/`; keep the known `_ = /a<TAB>b/` accept/reject gap covered too.

7. **Make trivia handling principled.**
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

8. **Add a preserving-trivia round-trip test.**
   This should assert that token/trivia spans reconstruct the original source exactly.

9. **Add tuple-type label ambiguity fixture.**
   `elementName` was fixed to avoid ambiguity on `(_: Int)`, but no dedicated ambiguity fixture currently protects that shape.

10. **Add extension converter tree fixtures.**
   `convertExtensionDeclaration` now delegates to `convertType`, covering `extension [Int] {}` and `extension UInt8? {}`. Add tree-equality fixtures so this converter path is protected, not only acceptance-tested.

11. **Measure swift-syntax source-file tree equality when affordable.**
   Advent source-file tree equality is clean, but the swift-syntax source corpus tree comparison is still too expensive for routine runs. Profile tree building before turning the 317-file tree comparison into a regular gate.
   FIRST DATA POINT (2026-09-21): they are NOT clean — `CompilerPluginMessageHandler.swift`
   differs. Only the Advent corpus was ever brought to tree parity, so the 317 need their own
   pass. A full tree run is ~40min, so profile the tree path first.

12. **Investigate remaining context-free prediction cost for interpolation Tail/Part terminals.**
   The earlier `followCheck` and Oracle work removed known cliffs, but interpolation Tail/Part prediction can still drive many distinct regex probes. Profile before changing prediction order or caching; `cachedLex` already memoizes `(position, terminalID)` and many expensive calls are first-time queries.

13. **Make whole-file parsing reliable and fast enough to crawl GitHub repositories.**
   Measured 2026-09-27 with the fuzz probe (Release). Typical files cost ~1 ms/token, split about
   half parse, half post-parse (Oracle + DerivationBuilder + converter): `Expressions.swift` 93 KB
   10 s, `SyntaxNodesD.swift` 147 KB 19 s. But size does not predict time: `SyntaxEnum.swift` (61 KB,
   one ~300-case enum plus a ~500-case switch) takes > 300 s.
   - LONG LISTS ARE SUPERLINEAR — the main bottleneck. One function with N `let vI = g(xI).y` lines:

         N     parse   total    yields
         50    0.2 s    0.9 s    24 k
         100   0.4 s    4.6 s    69 k
         200   0.9 s   30.6 s   218 k
         400           > 120 s

     An enum with N `case aI(TI)` lines behaves the same (0.3 / 1.8 / 13.1 s for 50/100/200). The
     parse is ~linear; YIELDS grow ~quadratically (a list should need ~linear), and post-parse time
     ~cubically. Hypothesis: the Oracle's fixpoint loops (`disambiguate()`: `pruneUnsupported` and
     `pruneUnproductive` alternate, each rescanning ALL yields per pass) need a number of passes that
     grows with N — N passes × N² yields.
   - CRASH: `EXC_BAD_ACCESS` "Thread stack size exceeded" in the recursive walk `visit` →
     `visitAlternates` → `tileBody` → `visitSymbol` → … inside `Oracle.pruneUnproductive`, bottoming
     out in `endPositions`. Depth tracks derivation depth. First hit on swift-syntax's
     `BasicFormat.swift`, `Indenter.swift`, `InferIndentation.swift`, `Syntax+Extensions.swift`,
     `SyntaxProtocol+Formatted.swift` (Swift Testing worker thread, small stack). Fix: iterative
     walks (explicit work stack), not a bigger stack.
   - Fixed cost: grammar load ~0.95 s per process, so a crawler must reuse one persistent process.
   - Acceptance: 2 of the first 5 swift-syntax files tried were rejected (`ArenaAllocatedBuffer.swift`,
     `RawSyntax.swift`); a crawl must record rejects rather than stop on them.
   Plan, in order:
   1. Count Oracle fixpoint passes for N = 50/100/200; if they grow with N, replace the rescans with
      a worklist that re-checks only yields whose supporters changed.
   2. Find why list yields are quadratic (right-recursive `statements`/member lists — item 2 — plus
      separators, or code blocks also deriving as closures) and fix it in the grammar or engine.
   3. Make the Oracle and converter walks iterative (the crash).
   4. Crawl harness: one persistent probe per core, per-file timeout that records and moves on, a
      token cap for pathological files.
   Progress 2026-09-27 (profiled with `sample`):
   - DONE: the Oracle fixpoint hypothesis was WRONG (2 rounds at every N). The cost was
     `pruneUnproductive.visitBracket`: for a NON-closure bracket (`statements?` in `codeBlock`) it
     visited the alternates for every end `<= to`, walking `statements(from, j)` for every statement
     boundary j — O(n²) work — and marked prefixes that are in no derivation. Now only `end == to`.
     400 statements: 187 s → 4.6 s (incl. ~1 s grammar load); growth now ~linear.
   - DONE: `DerivationBuilder` built each candidate head subtree before checking that the tail tiles
     (`tileASTBody`, `buildASTClosure`); tail-first now. It also indexes yields per symbol instead of
     scanning them per query. `tileBody` / `bodyTiles` / `visitBracket` in the Oracle are memoised.
   - RESOLVED: the old over-marking had been LOAD-BEARING. Several rejects were reached only through
     dead readings it kept alive (mostly `@longest` comparing against them). A general "compare
     against all parsed extents" for `@longest` broke 372 tests and was reverted. Instead each case
     got the grammar rule swift-syntax actually applies (all in `SwiftSyntax - fuzz harvest fixes`):
     - type position: a type name may not stop right before `<` (`typeIdentifier >-> ( openAngle )`);
       fixes `value as A<B>??x` and the previously unnoticed `x as Int < 5` / `<=` / `is Int << 2`;
     - `1.0` is one float literal, never `1` + tuple member `.0` (`<-<` integer literal before `.`);
     - a left-bound operator directly before `.` is postfix, not binary (`>-> ( "." )`);
     - an implicit-member chain continues with a name (`.Bar.[2]` rejected);
     - the tight condition infix mirrors the tight expression infix (`if rhs??b {}` rejected).
     Verified: full test plan (only item 14's two fixtures fail), the 4,594-source corpus vs the
     pre-change probe, and differential fuzzing old vs new probe — 40,000 inputs, every status
     difference traced and fixed.
   - Still open: iterative walks (the stack-overflow crash), the crawl harness (steps 3–4), and
     converting the right-recursive member lists (item 2), which would also make yields linear.
     Pre-existing, seen on the way: implicit-member chains (`let x: Foo = .a.b`) build a different
     tree than swift-syntax.
   History: 2026-09-26 `YieldIndex` in `pruneUnproductive` removed a quadratic scan (524 KB file
   20+ min → ~140 s; profiled with `sample`). Use the profiler again only if steps 1–2 do not bring
   N = 200 statements to about a second.

14. **Leading-dot `#if` body after another `#if … #endif` block is rejected.**
   swift-syntax accepts, Advent rejects (measured 2026-09-27). Minimal case:

       #if A
       #endif
       #if FOO
       .member
       #endif

   The same `#if FOO⏎.member⏎#endif` parses when it follows a declaration, a statement, a call, a
   closure, or nothing, so the trigger is specifically a preceding `#endif`. Fixtures
   `ifconfig-leading-dot-after-decl` and `ifconfig-leading-dot-after-extension`
   (`SwiftSyntax - fuzz harvest fixes`) fail on it. Not yet diagnosed; first suspect is the gating on
   the statement-level `ifDirectiveClause` (`>->( "." )` and the `<-<` lookbehind list, `Swift.apus`
   ~1971) when the previous token is `#endif`.

15. **Accept compiler-valid `#if` declarations with unsafe address accessors.**
   Compiler-first fuzzer run `2026-09-27T22-50-05Z`, artifact
   `worker-0/artifacts/00560924-advent-underaccept-5a47e4ef682e23b0.json`: `swiftc -parse`
   accepts but Apus rejects a declaration wrapped in `#if FOO … #endif`:

       public struct ArenaAllocatedPointer<Element: Sendable>: @unchecked Sendable {
         init(_ pointer: UnsafePointer<Element>) {}
         var pointee: Element { @_transparent unsafeAddress { pointer } }
         var unsafeRawPointer: UnsafeRawPointer {}
       }

   Start from the original artifact source, not only the reducer output. Determine whether the
   rejection is caused by `@unchecked Sendable` inheritance, `unsafeAddress`, attribute handling in
   accessor blocks, or their combination inside `ifConfigStatements`.

16. **Accept compiler-valid module-selector function types and operator references.**
   Compiler-first fuzzer run `2026-09-27T22-50-05Z`, artifact
   `worker-0/artifacts/00179090-advent-underaccept-1365cd1db8327d78.json`: `swiftc -parse`
   accepts but Apus rejects:

       func fuzz() {
         let fn: (Swift::Int, Swift::Int) /*
         */-> Swift::Int = (Swift::+)
       }

   Fix the grammar path for `Swift::Int` and `Swift::+` in function types / operator references,
   including block-comment trivia before `->`.

17. **Accept compiler-valid split attribute spelling in parameter types.**
   Compiler-first fuzzer run `2026-09-27T22-50-05Z`, artifact
   `worker-0/artifacts/00472975-advent-underaccept-de0b72093adc87f6.json`: `swiftc -parse`
   accepts but Apus rejects:

       struct Fuzz {
         func foo(closure:
         @ // c
         escaping () -> Void) {}
       }

   Diagnose the attribute/type path that fails when `@` and `escaping` are separated by line-comment
   trivia and a newline.

18. **Accept compiler-valid function signatures with effect specifiers and commented arrows.**
   Compiler-first fuzzer run `2026-09-27T22-50-05Z`, artifact
   `worker-0/artifacts/00698942-advent-underaccept-40e086591b3408ff.json`: `swiftc -parse`
   accepts but Apus rejects:

       let fuzzClosure = {
         func f() async throws /*
         */-> Int {}
       }

   Check `functionSignature`, `functionResult`, and trivia/layout gates around `async throws ->`
   when a block comment containing a newline appears before the result arrow.

19. **Reject compiler-invalid underscored ownership keywords in patterns.**
   Compiler-first fuzzer run `2026-09-27T22-50-05Z`, artifact
   `worker-0/artifacts/00087112-advent-overaccept-2edafa850dc2ab91.json`: the compiler rejects but
   Apus accepts switch cases such as:

       switch x {
       case _consuming a:
       }

   Restrict pattern/value-binding grammar so `_consuming`, `_borrowing`, and `_mutating` are not
   accepted as pattern introducers unless the compiler accepts that exact context.

20. **Reject compiler-invalid multiline `#if` condition continuations after infix operators.**
   Compiler-first fuzzer run `2026-09-27T22-50-05Z`, artifact
   `worker-0/artifacts/00053524-advent-overaccept-1d29475078c42e30.json`: the compiler rejects but
   Apus accepts:

       #if compiler(<10.0) ||
       hasGreeble(blah)
       #endif

   Tighten `compilationCondition` so newline layout after `||` does not form a valid condition when
   the compiler treats the directive as malformed.

21. **Reject compiler-invalid whitespace after dots in key paths and member/type references.**
   Compiler-first fuzzer run `2026-09-27T22-50-05Z`, artifact
   `worker-0/artifacts/00112114-advent-overaccept-0462034f66529290.json`: the compiler rejects but
   Apus accepts forms reduced to:

       #if FOO
       AStruct. Type
       #endif

   The original source is a key path `\AStruct. Type.property`. Enforce tight dot/member spelling in
   key-path roots and member/type references.

22. **Reject compiler-invalid whitespace in qualified extension type names.**
   Compiler-first fuzzer run `2026-09-27T22-50-05Z`, artifact
   `worker-0/artifacts/00225614-advent-overaccept-679fb6858b645800.json`: the compiler rejects but
   Apus accepts an extension header with a spaced qualified type:

       extension Parser. Lookahead {
         func canParseArgumentLabelList() -> Bool {}
       }

   Tighten the `typeIdentifier` / `designatedType` grammar for dotted names so whitespace after `.`
   is rejected in extension and declaration contexts.

23. **Resolve `ifConfigStatements` ambiguity for dotted imports inside `#if`.**
   Compiler-first fuzzer run `2026-09-27T22-50-05Z`, artifact
   `worker-0/artifacts/00018685-residual-ambiguity-7209f57a1652e8c3.json`: compiler and Apus accept,
   but derivation remains ambiguous:

       #if FOO
       import A.B
       .C
       #endif

   Residual signature: `ifConfigStatements ambiguous alternate [ifConfigStatement ] |
   [ifConfigStatement statementSeparator ifConfigStatements]`. Decide whether `.C` belongs to the
   import path or starts a following statement, and make the list derivation unique.

24. **Resolve `copy` / `consume` / `borrow` prefix-expression ambiguity.**
   Compiler-first fuzzer run `2026-09-27T22-50-05Z`, artifact
   `worker-1/artifacts/00327596-residual-ambiguity-069c0e7040058152.json`: compiler and Apus accept,
   but `copy { g() }` leaves `prefixExpression` ambiguous between a normal postfix expression and
   the ownership-keyword prefix form. Fix the contextual-keyword gate for `copy`, `consume`, and
   `borrow` before closure/block-looking syntax.

25. **Resolve statement-list pivot ambiguity for declaration-like statements in blocks.**
   Compiler-first fuzzer run `2026-09-27T22-50-05Z`, artifact
   `worker-0/artifacts/00055365-residual-ambiguity-f855f49a2c0b3c73.json`: compiler and Apus accept,
   but `statement` / `statements` tiling is ambiguous around adjacent declaration-like statements:

       while TokenSyntax {
         var isMissing: Bool /*
         */{
         }
         var isPresent: Bool {
         }
       }

   Residual signature: `statement ambiguous pivot body=[statement statementSeparator statements]`.
   This is related to the right-recursive list cleanup, but start with this concrete block/property
   case and verify that the fix also reduces the broader `statements` residual cluster.

## Maintenance Rule

- Add new TODOs here only when they are active and actionable.
- Move completed investigations and historical explanations to design notes or commit messages.
- `codex.md` and `claude.md` reference this file instead of maintaining separate TODO lists.

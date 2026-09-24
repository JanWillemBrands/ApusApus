# Ambiguity Workflow — tackling the residual `unambiguous` backlog

Status: Phase 0–1 built and run (Jul 4 2026). Baseline: `adventAccepts` = 0 failures
across all 7 SwiftSyntax suites; `unambiguous(_:)` = **1058 failures**, which cluster into
just **90 distinct signatures** (see `ambiguity_signatures.tsv`).

## The core idea: fix by *signature*, not by test
The number that matters is not 1058 tests but **90 signatures**. A *signature* is the
canonical, position-independent fingerprint of a single ambiguity:

    (ambiguous node, diagnostic kind, sorted competing-alternate bodies)

Every test sharing a signature is the *same* underlying ambiguity, so **one fix clears the
whole cluster**. The top few signatures dominate — the distribution is very front-loaded.

## Lessons baked in (from the Jul 2026 sessions)
1. **Test families lie.** One family often has several distinct causes; the *node +
   competing alternates* is the true signal. (Family counts were misleading.)
2. **Ambiguities fall into categories, each with a *different* remedy** — and applying the
   wrong one masks the real bug:
   | category | remedy |
   |---|---|
   | redundant / subsumed alternate | delete the rule |
   | terminal/lexer overlap (e.g. `_`) | fix the terminal, not the grammar |
   | one alternate should always win | `@prefer` (Oracle priority) |
   | over-broad alternate (type-as-expression) | tighten / make context-sensitive |
   | pivot/tiling (where one symbol ends) | investigate boundary; often a terminal or `>s<`/lookahead issue |
3. **NOT operator precedence.** Swift-syntax parses expressions into a **flat**
   `SequenceExprSyntax` (Expressions.swift:226) and defers precedence folding to a separate
   pass; our grammar's right-recursive `infixExpressions` mirrors this, so `a + b * c`,
   nested ternaries, `as ?? `, `a < b > c` are all **unambiguous**. An earlier "operator
   precedence ~30%" estimate was a misattribution — exactly the error a systematic harvest
   prevents.
4. **`treesMatch` is the real oracle** — resolve toward the tree swift-syntax builds, not
   "pick any single tree". Turns "which alternate is right?" into a measurable test.
5. **The competing-alternate shape auto-suggests the category** (prefix-of → priority;
   identical → redundant; `expression` vs `type` → over-broad).

## The pipeline
- **Phase 0 — Instrument (done).** `DerivationBuilder.Diagnostic` now carries a canonical
  `signature`/`fingerprint`. `main.swift`, gated by `APUS_SIG_DUMP=1`, emits one
  `SIG\t<msg>\t<node>\t<kind>\t<signature>` line per residual ambiguity. Off the normal path.
- **Phase 1 — Harvest (done).** `harvest_ambiguity.py [labels|ALL]` feeds the failing
  snippets through the binary and writes the ranked `ambiguity_signatures.tsv`
  (`count, node, kind, signature, example_tests`). Re-run after each fix to measure cascade.
- **Phase 2 — Classify** each signature by shape into the table above (mechanical for
  redundant/identical/prefix; judgement for the rest).
- **Phase 3 — swift-syntax oracle (targeted, per node — NOT a whole-grammar line diff).**
  Map the apus nonterminal → swift-syntax `parseXxx`, read how *it* disambiguates, derive
  the faithful fix + citation. Maintain a small `node → parseXxx` map, reused across fixes.
- **Phase 4 — Apply & re-harvest.** Fix; validate on the signature's example snippets via
  the cheap probe (ambiguity gone, `adventAccepts` holds, `treesMatch` improves); re-run the
  harvester to measure how many tests cleared (cascade). Highest-count signatures first.
- **Phase 5 — Batch regression gate.** After a batch, one full sweep to confirm
  `adventAccepts` = 0 and record the `unambiguous` drop.

## ⚠️ Harvester off-by-one (fixed Jul 5 2026)
`main.swift` emits the message index from `enumerated()` — **0-based**. Early probe scripts
AND `harvest_ambiguity.py:78` mapped it with `int(mi)-1`, shifting every attribution to the
*previous* snippet. Signature **counts** were always correct (each SIG line increments its own
signature), but the `example_tests` column pointed at the wrong snippet — which fed bad probe
cases and a multi-hour false "array literal / subscript feeds the `&` pivot" hunt. **Lesson: dump
the actual source span (`input[from..<to]`), never trust index→label mapping alone.** Fixed in
the harvester; when isolating a feeder, reproduce from a minimal case, not from a family.

## Completed fixes
- **`_` wildcard terminal** (was 281 + 82) and **redundant `parameter`** (was 202) — cleared
  (confirmed gone in the Jul 5 re-harvest).
- **Reserved `&` token** (Jul 5) — TSPL reserves bare `&` (can't be overloaded / used in custom
  operators). It was in `operatorHead`, so `&Y` doubly-parsed as `prefixOperator? postfixExpression`
  *and* `inOutExpression`. Fix: removed `&` from `operatorHead`; added a `&`-led `operator`
  production requiring ≥1 continuation (keeps `&&`/`&+`/`&<<`/`&=`); kept `&` as an
  `operatorCharacter` continuation; re-added `infixOperator = "&"` (reserved bitwise-and);
  broadened `inOutExpression = "&" postfixExpression` (lvalue operand: `&y[0]`, `&obj.prop`).
  Net −32 ambiguity instances; direct signature 16→1; prefix-pivot 101→92; **0 acceptance
  regressions**. 3 now-invalid snippets disabled (`testOperators3`/`testOperators24` = declaring
  `&`; `testRecovery169` = crash-recovery). See [[reference-reserved-operator-tokens]].

## The actual top signatures (Jul 5 2026 harvest, corrected indexing, post-`&`-fix)
| tests | node | signature | category (guess) | note |
|---|---|---|---|---|
| 92 | prefixExpression | `pivot body=[prefixExpression]` | pivot/tiling | operator/operand boundary; partly `&`-multichar maximal-munch |
| 91 | infixOperator | `pivot body=[infixOperator prefixExpression]` | pivot/tiling | *not* precedence; `&&`/`&+` split into `&`+op is one contributor (maximal-munch) |
| 83 | unionStyleEnumMember | `[declaration] \| [enumCaseDeclaration]` | over-broad/redundant | member vs case overlap |
| 81 | postfixExpression | `[explicitMemberExpression] \| [postfixSelfExpression]` | priority/redundant | `.self` — swift-syntax uses one member-access node; prefer/merge |
| 72 | statement | `[branchStatement] \| [expression]` | over-broad | e.g. `if`-expr vs `if`-stmt |
| 67 | postfixExpression | `pivot body=[postfixExpression postfixOperator]` | pivot/tiling | postfix chain association |
| 62 | infixExpression | `pivot body=[infixExpression]` | pivot/tiling | |
| 61 | (expr) | `pivot body=[postfixExpression]` | pivot/tiling | |
| 53 | rawValueStyleEnumMember | `[declaration] \| [enumCaseDeclaration]` | over-broad/redundant | as unionStyleEnumMember |
| 53 | enumDeclaration | `[rawValueStyleEnum] \| [unionStyleEnum]` | over-broad | two enum shapes overlap |
| … | | | | 83 signatures total; ~1346 instances; long tail |

**Next up (likely highest impact): the maximal-munch operator pivots** (92/91/67/62/61 — the
top cluster). Hypothesis: multi-char operators (`&&`, `&+`, `<<`, `>>`…) are lexed *and* split
into head+continuation, so `a && b` competes with `a & (&b)` etc. swift-syntax uses maximal
munch (one operator token). Investigate a longest-operator / no-split scanner rule before
touching the enum (`declaration`/`enumCaseDeclaration`, 83+53) and `.self` (81) signatures.

## Recommended order (front-loaded by impact)
1. ✅ **`_` wildcard terminal fix** — done (was 281 + 82).
2. ✅ **Redundant `parameter` rule** — done (was 202).
3. ✅ **Reserved `&` token** — done (see Completed fixes).
4. **Maximal-munch operator pivots** (92/91/67/62/61 — the current top cluster). Likely a
   longest-operator / no-split scanner rule.
5. **enum member** (`declaration` vs `enumCaseDeclaration`, 83+53) and **enum shape**
   (`rawValueStyleEnum` vs `unionStyleEnum`, 53).
6. **`.self`** (81), **statement vs expression** (72), **arrayLiteralItem** (14, mostly cleared).

Each step: fix → re-harvest → confirm the cluster cleared and nothing regressed.

## Reusable assets
- `harvest_ambiguity.py` — the harvester (re-run any time; `ALL` harvests every snippet).
- `ambiguity_signatures.tsv` — the current signature table (the map + progress tracker).
- `APUS_SIG_DUMP=1` + `DerivationBuilder.Diagnostic.fingerprint` — the Phase-0 primitive.

---

## Current ambiguity status (consolidated from agent memory, 2026-07-30)

Corpus residuals were driven down from ~11 signatures. Key resolutions:
- **yield/discard stmt-vs-call (×3)** — swift-syntax's rule is a local 1-token peek
  (`atContextualKeywordPrefixedSyntax(preferPostfixExpr:)`), reproduced with the
  negative-forward `>->("(" "[" ".")` gate on the `yield`/`discard` terminal-use
  (slot-local, so the identifier reading elsewhere is untouched).
- **infix-pivot** (`as () -> ()`, `as?…??`) via `@longest infixExpression`;
  **regex-vs-operator ×4** via the gated regex CFG (see `Regex CFG Discussion.md`);
  **string-delimiter ×3** by requiring a newline after a multiline `#"""` opener;
  **keyPath root-vs-component ×2** by member-free simple-type root + `@prefer` on the
  root-bearing alternate.
- **`testOperators26#1`** (`func ⚽️`) — was NOT context-sensitivity; the coarse
  `\p{So}` shortcut made `⚽` match both identifier and operator. Fixed by faithful,
  disjoint code-point `CharacterClass` ranges under `.matchingSemantics(.unicodeScalar)`
  (in `SwiftGrammarRegexLibrary.swift`). Three tiny identifier deviations remain,
  forced by a hard Swift-`Regex` limitation: a canonically-decomposable code point
  (e.g. U+F900) is rejected as a character-class range **bound** in every form — so
  the faithful ranges dodge it (F8FF for F900, etc.). The 100%-faithful endgame is a
  code-point-class interval-table scanner primitive (see `TODO.md` #8, ~157× faster
  than regex for identifier lexing).
- **`testClosureLiterals#3`** (RESOLVED 2026-07-28) — the fork was the optional
  **function body** (`func f(…)⏎{…}` reading as a *bodiless* decl + a separate
  `{…}(…)` IIFE statement), NOT a trailing closure. Fixed with
  `@longest functionDeclaration = … functionBody? .`: the body stays optional
  (swift-syntax `parseOptionalCodeBlock` — bodiless `func f()` is valid everywhere,
  incl. top-level; a missing body is a *semantic* error), and `@longest` greedily
  prefers the body-taken reading — safe post-parse maximal-munch on the BSR, same as
  `@longest numericLiteral`. **WRONG first attempt (don't repeat):** making the body
  required + a member-only `bodylessFunctionDeclaration` (mirroring `init`) rejected
  top-level bodiless funcs (`@objc func f(_:Int)`, `@abi(func fn()) func fn()`). The
  `init` analogy is false — `func` is a hard keyword, so top-level `func f()` is an
  unambiguous bodiless decl. And the `>->("{")` gate can't help: `followAheadExclude`
  fires only on TERMINAL lex, never on an OPT/`?`/epsilon; and `factor()` consumes
  `>->` before `sequence()` applies the `?` postfix, so `…genericWhereClause? >->("{")`
  won't even load.

**Load-time flakes are ambiguity-adjacent:** the old `testClosureWithDollarIdentifier`
"flake" was a non-confluent exclude-set fixpoint at grammar load (fixed as a greatest
fixpoint) — see `TESTING.md` §7. A shared cached grammar turns any load-time
hash-order dependence into a per-process flake.

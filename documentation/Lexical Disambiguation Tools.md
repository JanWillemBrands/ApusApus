# Lexical Disambiguation Tools — a unified perspective

Written Jul 7 2026, after the maximal-munch / whitespace / merge work drove Swift.apus
ambiguity from ~1378 → ~782. This synthesises the recurring problem and proposes an
**orthogonal, language-neutral tool set**, so future grammars aren't a pile of ad-hoc hacks.

## The recurring problem
A character or token means different things depending on **context** or **adjacency**.
Cases we hit (all in Swift, but every language has its own set):

| case | example |
|---|---|
| keyword vs longer identifier | `for` inside `foreach` |
| multi-char operator vs its pieces | `&&`, `<<`, `==` |
| operator that must *split* | `>>`→`>` `>` (nested generics), `??`→`?` `?` (`Int??`) |
| `.self`/`.Type` vs member access | `Foo.self` |
| regex delimiter vs division | `/abc/` vs `a / b` |
| operator prefix/infix/postfix | `a-b` vs `a - b` vs `a⏎-b` |
| newline: separator vs continuation | `a⏎-b` (two stmts) vs `a - b` |
| call `(` / subscript `[` at line start | `g()⏎(x)` (two stmts) vs `g()(x)` |

## The two underlying axes
Every one of these is resolved by **extent** and/or **context**:

1. **EXTENT** — how far a token reaches: *longest match* (maximal munch), or a permitted *shorter split*.
2. **CONTEXT** — where it sits:
   - **adjacency** — the characters/whitespace bordering it,
   - **grammar position** — which slot the parser is in (handled by grammar *structure*),
   - **priority** — which of two *same-span* interpretations wins.

## The orthogonal tool set (four tools)

### Tool 1 — Boundary predicates (adjacency): `<s>` `>s<` `<n>` `>n<`  ✅ HAVE, proven
Constrain the trivia gap immediately before a symbol (whitespace present/absent, newline
present/absent). Resolves: operator prefix/infix/postfix **boundness** (`a+b`/`a + b`/`a⏎-b`
— infix ⟺ symmetric gaps), **statement separators**, **call/subscript at line-start** (`>n<`).
This is the workhorse and it is genuinely general.
- **Generalisation worth considering:** `<s>`/`<n>` are two hard-wired boundary *classes*
  (any-whitespace, newline). A `<[class]>` / `>[class]<` form — boundary defined by an
  arbitrary grammar-declared character class — would cover other languages' rules
  (e.g. "no tab here", "must be followed by a digit") with the same primitive.

### Tool 2 — Longest match / literal munch: `@literalMunch`  ✅ HAVE, proven
A regex terminal declared with `@literalMunch` suppresses a literal match when it
matches strictly longer at the same start. Resolves maximal munch (keyword `for`
inside `foreach`; operator `&&`). Grammar-derived, language-neutral.

### Tool 3 — Munch exemption / split  ⚠️ EXISTS IN THREE AD-HOC FORMS — should unify
"At *this* position a token shorter than the maximal munch is allowed." Currently spelled:
- `@splitBefore("/")` on `operatorToken` (offer the prefix ending before an internal `/`),
- the *regex-terminal trick* (`closeAngle - />/` closes a generic even inside `>>`, because
  regex terminals are exempt from the literal munch),
- the retired `~~~` Frankenstein marker.
These are **one concept**. They should collapse into a single primitive — e.g. a per-use
`~split` marker meaning "this terminal-use is exempt from maximal munch / may take a single
class char here." Resolves `>>`, `??`, `^^/regex/`.

### Tool 4 — Priority (same-span choice): Oracle `@prefer` / `@longest` / `@shortest`  ⚠️ UNDERUSED — the outstanding one
When two interpretations cover the **same span**, choose one. Resolves **regex-vs-division**
(prefer regex at expression-start) and same-span keyword-vs-identifier. This is *not* an
extent or adjacency problem — both readings have identical extent — so Tools 1-3 cannot
touch it. It is the Oracle's job. TODO #19 independently concluded "regex ambiguity is
structural — use the Oracle."

## Mapping (which tool each case wants)
| ambiguity | tool |
|---|---|
| keyword/`foreach`, `&&`, `<<` | 2 (`@literalMunch`) |
| generic `>>`, optional `??`, `^^/regex/` | 3 (exemption/split) |
| `.self` | grammar redundancy (it *is* a member access) |
| operator prefix/infix/postfix, newline continuation, call/subscript line-start | 1 (boundary) |
| **regex vs division** | **4 (priority)** ← the residual |

## The insight / where to invest
- **Tools 1 (adjacency) & 2 (extent) are in place and carry most of the load.** They're
  orthogonal and reusable — the boundary annotations especially.
- **Tool 3 is fragmented** (three spellings of "exempt from munch"). Unify into one primitive
  before adding more languages, or the ad-hoc forms multiply.
- **Tool 4 (priority) is the missing piece for the regex residual.** regex-vs-`/` is a
  same-span choice (regex preferred at expression-start; `/` is division only after a value).
  Boundary/munch can't express it; it belongs in the Oracle (`@prefer`) — OR is sidestepped
  by a targeted grammar fact (below).

## Regex: analysis + attack
`/abc/` at expression-start parses two ways: **(1)** a `regularExpressionLiteral`, and
**(2)** prefix-`/` applied to (`abc` with postfix-`/`) — because `/` ∈ `operatorToken`, so it
is a candidate prefix *and* postfix operator. swift-syntax never sees (2): its lexer prefers
regex at expression-start (`preferRegexOverBinaryOperator`). Both `/`s in (2) are even
correctly prefix/postfix-*shaped* by whitespace, so Tool 1 can't kill it — it's a genuine
same-span priority (Tool 4).

**Attempted grammar workaround — and why it's not the answer.** The faithful positional
statement is narrow: *at expression-start (= the prefix position), `/` is regex, not a prefix
operator*. That justifies excluding `/` from **`prefixOperator` only** — and since reading
(2) *starts* with prefix-`/`, breaking that start alone kills it (the postfix exclusion I
first wrote was redundant AND mis-justified — "expression-start" says nothing about postfix).
But the exclusion can't be expressed with the tools we have: `---("/")` is a no-op (`/` is
not a literal terminal — it reaches prefix position via the `operatorToken` regex), and a
`/`-less prefix-operator terminal would duplicate the big `operatorToken` regex (the exact
duplication we've been *removing*). It's also not truly faithful — swift-syntax doesn't forbid
`/` as a prefix operator; it *prefers regex by position*.
**Conclusion: regex-vs-`/` is Tool 4 (priority), full stop.** The clean fix is an Oracle
priority — "at expression-start, prefer `regularExpressionLiteral` over the `/`-operator
tiling" — i.e. `preferRegexOverBinaryOperator` realised as an Oracle rule, not a grammar
hack. This is a separate track (the Oracle), consistent with TODO #19.

**✅ DONE Jul 7 — via a new `@avoid` bracket pragma (Tool 4, the negative dual of `@prefer`).**
First attempt used `@prefer`, but `@prefer` is *start-keyed*: it prunes a non-preferred sibling
`(i…j)` where a preferred sibling yields from the same start, and it keys on the preferred
alternate's *last body symbol*. That forces two shapes the inline OPT can't provide — the readings
must be **sibling alternates** (the Oracle only walks top-level `nt.alt`) and the preferred branch
must be **non-empty**. The regex "skip the operator" reading is the *empty* branch of an OPT, so
`@prefer` needed a manufactured split into a helper nonterminal (`prefixOperatorApplication`) that
duplicated `postfixExpression` into two non-empty siblings.

`@avoid` removes the split. It marks the **explicit, non-empty "take" branch** instead:
```
prefixExpression = [ @avoid prefixOperator ] postfixExpression .
```
Preferring the empty branch is really a **pivot** choice, not a same-start choice: in the enclosing
alternate `[OPT postfixExpression]` over `(i,j)`, `postfixExpression`'s BSR pivot `k` is the OPT
boundary — `k=i` ⟺ operator skipped, `k>i` ⟺ operator taken. So `@avoid` compiles to a **min-pivot**
rule (`AvoidOptionalRule`, = `pruneByPivot keep:min`) on the symbol *following* the bracket. That
needs no empty branch to key on. Where skipping fails (`-x`), phase-1 already drops the `k=i` yield,
so the lone "taken" pivot survives untouched. Harvest **782→720 (−62)**, regex `postfixExpression`
pivot **64→4**, **0 acceptance regressions**, and **one fewer signature** than the `@prefer` split
(no helper nonterminal). `-x`/`!x`/`consume x`/`a/b` unaffected.

`@avoid` generalizes: a fallback sibling alternate or a lazy `{…}`/`<…>` repetition can be
`@avoid`ed the same way (min-pivot on the following symbol = prefer fewest iterations). Syntax:
`@avoid` as the first token inside any bracket — `[ @avoid X ]`, `{ @avoid X }`, `< @avoid X >`.

## Does the `<c>`/`>c<` generalization subsume Tool 3 (munch-exemption)? — No.
They are on **orthogonal axes**: `<c>`/`>c<` is *adjacency* (which character borders the token —
a generalization of `<s>`/`<n>` to arbitrary declared char-classes), whereas munch-exemption is
*extent* (this token may be shorter than maximal munch here). A boundary predicate constrains
neighbours; it cannot "opt out of the length check" (what `closeAngle` does by being a regex
terminal) nor "offer two extents" (what `@splitBefore` does). So `<c>`/`>c<` is a valuable Tool-1
generalization (cross-language: "followed-by-digit", "no-tab-here") but leaves Tool 3 standing.
Tool 3's cleanup remains its own exercise: unify `@splitBefore` / regex-terminal-trick / `~~~`
into ONE "exempt-from-munch-here" primitive.

## 2026-08-07 — Empirical conclusion: the `?`/`!` keypath case and the `@splitBefore` class are the same disease, and it cannot be cured by a global lexer edit

Two connected observations opened this: (1) the LCNP migration left the parser's **multi-match
fork wired but starved** — `tokenMatch()` forks a descriptor per distinct `lex` end, but the
only producer that ever returns >1 match for a single terminal is the `@splitBefore` arm of
`OnDemandLiteralLexer`; (2) `@splitBefore` (and the `?`/`!` operator handling it neighbours)
"feels like a crutch." Both are Tool 3 (munch-exemption / split).

### Anchoring in Scott & Johnstone (*Multiple Lexicalisation*, SLE 2019, §5.2)

The paper's summary is the design constraint. Its key claim: **longest match is "hard to reason
about in the case of context-free grammars"**, and the fix is to *keep lexical disambiguation
separate from the CFG* — each terminal keeps its **own** longest-match within its **own**
sublanguage, and the parser uses **terminal-level lookup** (`lex(pos, t)` per terminal ID) with
GLL/CRF/BSR providing the sharing (cost goes from the *product* of component lexicalisations to
their *sum*). This is exactly APUS's `OnDemandLiteralLexer` + Phase F predict-gating (`lexLKH`).

Two consequences the paper forces on the earlier `lexFull` sketch:
- **Do NOT enumerate one terminal's prefixes.** A shorter extent should come from a *different*
  predicted terminal (e.g. `>>`→`>` `>` comes from `closeAngle - />/`, not from `operatorToken`
  offering extent-1). The fork fires because *distinct predicted terminals return different
  extents at the same position* — the paper's actual shape.
- **The only irreducible same-terminal-non-maximal case** is `^^/regex/` (a shorter `operatorToken`
  than the greedy `^^/`, with no separate terminal for `^^`). swift-syntax handles it by *demand
  re-lex* (`tryLexOperatorAsRegexLiteral`). That is the one narrow, principled place a
  predict-gated same-terminal split (i.e. today's `@splitBefore`) is justified — not as a general
  mechanism.

### The audit test for every `?`/`!` (and munch) knob

Each knob is one of two kinds; Scott's separation is the discriminator:
- **(a) Per-terminal self-disambiguation** — a rule about a terminal's *own* sublanguage.
  `operatorSpecial (cont)+` ("a lone `!`/`?`/`=`/`&` is not a valid `operatorToken`") is this.
  It is *not* a crutch; it is what makes a per-terminal `lex` correct. **KEEP.**
- **(b) Cross-terminal reservation** — one terminal's regex carrying a rule about what *other*
  terminals should win. `postfixOperatorToken`'s `(?![!?])` lookahead and
  `dotOperatorCharacter.subtracting(.anyOf("!?"))` are this — the "merging" Scott calls
  uncomfortable. **These are the knobs to retire**, replacing them with distinct terminals +
  grammar slot + predict-gating.

### The experiment (and why it is a WASH, not a fix)

Live tracker: `testKeyPathFollowedByOperator` — `\Foo?.?.bar.?.blah` needs `.?.` tokenised **two
ways** over the same chars (one infix `binaryOperator ".?."` vs keypath `.` + `?`). Its
`disabledReason` names the blocker precisely: the single-token path "can't offer `.?.` (operator)
and `.`/`?` (keypath split) as competing tokenizations — needs multi-lex." The knob is
`dotOperatorCharacter.subtracting(.anyOf("!?"))` — a class (b) cross-terminal reservation that
makes `.?.`-as-operator impossible in order to protect the keypath `.?` split.

Removing the `!?` exclusion, measured with `tools/run_tests.sh Expressions` (identical snippet set,
`treesMatch` correctly ignored per `TESTING.md` §2):

| | reject fails | accept fails | residual ambiguity |
|---|---|---|---|
| baseline (`!?` excluded) | 0 | **4** (`testInitializerExpression#1`, `testKeyPathFollowedByOperator#1/#2`, `testKeyPathMethodAndInitializers#5`) | 0 |
| change (`!?` allowed)   | 0 | **4** (`testKeypathExpression#1/#5/#13`, `testKeypathExpressionWithSugaredRoot#4`) | 0 |

**Same count, a different four.** The change fixes `KeyPathFollowedByOperator#1/#2` and breaks
`Keypath#1/#5/#13` + `SugaredRoot#4`. **A global lexer-class edit is conservation of failures:**
it *relocates* the trade, never removes it — the whack-a-mole, quantified. (First read was a false
alarm from mis-weighting `treesMatch`, which is red by design; the corrected run via the canonical
runner gives the numbers above. Change reverted.)

### Conclusion for both topics

1. **The `?`/`!` keypath problem cannot be fixed by editing `dotOperatorCharacter` (or any global
   char-class / lookahead).** Those are class-(b) cross-terminal reservations; toggling one only
   moves the failure. The real fix is **demand-driven per-slot terminal-level lookup**: let `.?.`
   (a `dotOperator`, maximal within its own sublanguage) and the keypath marks (`.`,
   `optionalMark`, `forceMark`) be **distinct predicted terminals**, and let the grammar slot +
   predict-gating decide which tokenisation survives — feeding the multi-match fork with genuine
   competing tokenisations (Scott's separation). Removing the `(?![!?])` / `!?`-exclusion knobs is
   correct **only when paired with** that slot mechanism; alone it is a wash (proven above).

2. **`@splitBefore` is the same disease, one narrow case.** It is currently the *only* feeder of
   the multi-match fork. Under Scott: per-terminal longest-match is the default; shorter extents
   come from *other predicted terminals*, not prefix-enumeration; the single irreducible
   same-terminal-non-maximal extent (`^^/regex/`) is the one place a predict-gated demand split is
   warranted. So `@splitBefore` → a predict-gated demand-split primitive, scoped to that residual —
   not a general `lexFull`, and not a per-character annotation.

**Net:** Tools 1 (boundary) and 2 (per-terminal longest-match) stay. Tool 3 collapses to "predict-
gated demand split for the one same-terminal residual." Tool 4 (Oracle) shrinks to genuine
same-span ties only. The general mechanism the whole thread was after is **not a new annotation —
it is finishing the LCNP move**: distinct terminals + grammar slot + predict-gating actually
generating the competing tokenisations the fork was built to receive.

## Munch-exempt marks vs. context gates (measured 2026-09-21)

Two lessons from aligning the `!`/`?` sites, both of which cost a wrong first attempt.

**1. A munch exemption only decides how the MARK lexes.** Making `as!`/`as?` use the munch-exempt
`forceMark`/`optionalMark` was necessary but NOT sufficient for `x as!~C`: the SE-0390 `~T` type
form is *separately* gated on what precedes the `~` (whitespace, or a lookbehind on
`( [ { , ; :`). After a tight `as!` the committed token is `forceMark`, which was in neither
branch, so the cast stayed rejected however the mark lexed. Fixed by adding
`forceMark optionalMark` to that lookbehind list. When exempting a mark, check the NEXT symbol's
preconditions too.

**2. Requiring trivia is a blunt instrument; gate the specific shape instead.** Bare `try` was
given `<s>` to stop `try!-f()`, which also rejected the legal tight forms `try(f())`, `try[0]`,
`try.f()`. But removing `<s>` alone is worse: it re-admits `try!-f()`/`try?-f()` AND makes
`try!f()` ambiguous, because a lone `!` is not an operator token (`operatorBody` needs
`operatorSpecial` plus at least one more operator character), so bare `try` + prefix `!` competes
with the `try!` alternate. Both bad readings are one shape — bare `try` tight against a mark — so
the gate names it:

    tryOperator = "try" <s>
                | "try" >s< >-> ( forceMark optionalMark )
                | "try" >s< "?"
                | "try" >s< "!" .

The lookahead names the munch-EXEMPT marks (they lex even where `!-` exists, so the gate fires);
the `try?`/`try!` alternates keep LITERAL marks (munch suppresses them before `?-`/`!-`, leaving
`try!-f()` with no derivation). Verified on 12 forms for accept, reject, ambiguity and tree.

NOTE: acceptance testing alone would NOT have caught the `try!f()` ambiguity — only
`isUnambiguous` did. Any change that adds an alternate reachable at the same extent needs the
ambiguity check, not just an accept/reject matrix.

**3. `suppressedType` and the branch it replaced.** Extracting the two loose `~` alternates of
`type` into a named nonterminal (after swift-syntax's own `SuppressedType`) moved the `~` one level
down. `convertType` had an in-line branch guarded on
`find("type", in: spans) && spansContainKeyword(spans, "~")`, which could no longer fire once the
`~` was nested, so it was REMOVED rather than left as unreachable code. `convertSuppressedType`
now handles it explicitly. No `type`/`simpleType` alternate carries a bare `~` any more, which is
what makes the old guard provably dead. Verified by deleting it and re-running 13 `~` positions —
all still match, so the new branch is demonstrably the live path.

METHOD NOTE: the old branch was initially missed because the search for it was
`grep -n 'Suppressed\|"~"' … | head -8`, and the truncation hid the match at what was then line
8536. That produced a false claim that `convertType` had no `~` handling at all, and left an
unexplained "it matches via some other path". When a grep is being used to establish the ABSENCE
of something, do not pipe it through `head`.

## 2026-09-23 — Three traps found while closing TODO 1/2/3/6/21

All three cost a wrong turn each, and none was visible from reading the grammar. They are
properties of the TOOLS, not of Swift, so they will recur.

### 1. `@cannotParse` / `@prefer` / `@longest` do not affect YIELDS, only trees

They are Oracle predicates (`GrammarNode.forwardPredicates`), applied after parsing. So:

- They cannot express "this must not PARSE". The key-path postfix island was spelled as
  `@cannotParse( keyPathExpression )` on `postfixExpression` and `explicitMemberExpression`, and it
  never removed a single derivation — `\Foo.m()` still parsed as a CALL on `\Foo.m`. The working
  version is STRUCTURAL: `keyPathExpression` is an alternate of `prefixExpression`, never of
  `primaryExpression`, so `postfixExpression` cannot derive a bare key path. Both predicates were
  then deleted as dead.
- `@longest` cannot be greedy at the cost of the parse. It chooses among VIABLE readings, and the
  Oracle prunes dead wood FIRST — so for `\Foo<T>.?.[0]` the greedy root `Foo<T>` (which leads to no
  complete parse) was already gone before `@longest` ran, leaving the short root `Foo` and a
  spurious `< T >` comparison. The fix was a parse-time terminal gate,
  `keyPathRootBase = typeName typeGenericArgumentClause | typeName >-> ( openAngle )`.
- Consequence for MEASUREMENT: "Advent accepts" has two meanings. `adventAcceptsFile` is
  yield-level (pre-Oracle); `runAdventOnce` is tree-level, and that is what the accept/reject
  suites use. `KeyPathGrammarTests` asserts on the tree measure and also reports `oraclePruned` —
  the gap. It is currently non-zero (4 cases at CORE length 3, 9 at WIDE length 2): those
  over-acceptances are carried by the Oracle rather than structurally excluded.

### 2. A LITERAL in a lookaround operand set is defeated by maximal munch

`genericArgumentClause`'s follow set (swift's `isGenericTypeDisambiguatingToken`) lists the literal
`"."`. The moment `dotOperator` was relaxed to match `.?`, the longer token SUPPRESSED that literal,
and `\Foo.p<T>.?` — clean in swift — was rejected. swift tests the next token's `.` PREFIX, not
whole-token equality, so the antidote is to spell the munch-exempt regex `keyPathDot` beside the
literal. Same device as the root-absent gate `"\\" >+> ( keyPathDot )`.

RULE: any literal in a `>+>` / `>->` / `<+<` / `<-<` operand set is only as good as munch allows.
If a longer token can start with it, add the munch-exempt regex form too.

### 3. Literal vs munch-exempt spelling is a SEMANTIC distinction, not a style choice

The regex-opener gates listed both `"!"` and `forceMark`. They are different positions:
postfix force-unwrap is `forceMark` (`forcedValueExpression`), while `tryOperator` spells
`"try" >s< "!"` with the literal. Listing the literal blocked a regex after `try!`, so
`try! /re/.wholeMatch(in: s)` parsed as `/` prefix + `re` + `/` postfix and built the WRONG TREE
while still being accepted. The list never contained the literal `"?"` — and `try? /re/` was
already right; that asymmetry was the tell. Removing the literal `"!"` keeps `x!/y/` as division,
because that `!` is a `forceMark`, which stays listed.

### Corollary: a rule can be correct and unreachable

`<s> forceMark` was added to `keyPathPivot` to accept `\Foo !`. It changed nothing, because
`keyPathPivot` is only reachable through the alternate with a leading property run. It belongs on
`keyPathPivotFirst`. The mark-run rule had the identical bug. Reading the grammar did not reveal
either; the enumerated sweep did.

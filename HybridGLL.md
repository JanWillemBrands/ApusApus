# Hybrid GLL

A plan, and what is built so far, for a GLL parser that only sporadically uses the full
machinery: deterministic stretches run like plain recursive descent, and descriptors, clusters
and return edges are made only where the grammar really branches. The experiment runs in
`tinyGLL` first; ApusApus follows only if it pays off (it is an engine change there, agreed
first).

Status (2026-11-21):

| Part | State |
|---|---|
| FIRST / FOLLOW and one-character prediction | built in tinyGLL (`Prediction.swift`) |
| EBNF brackets `( ) [ ] { } < >` | built in tinyGLL (`Engine.swift`, `Derivation.swift`) |
| enter / leave / resume, Need on return edges | built in tinyGLL |
| fast mode: frames, splits, watermark (per path, no "only path alive" rule) | built in tinyGLL (`enterFast`, `leaveFast`, `materialize`) |

## 1. Why

Measured on Swift.apus (`/tmp/apus-decision-stats.txt`, Oracle.swift: 4,583 tokens, 125,468
descriptors, about 27 per token):

- 79% of decisions let through at most one alternative: the parse is already deterministic
  there, but GLL still pays for a cluster, a return edge and descriptors at every call.
- The other 21% make all the waste, 98% of it dying within one token. Most of it (≈ 76% of
  the dead alternatives) comes from left recursion in the postfix-expression family, ≈ 15% from
  alternatives with different first symbols but the same first token, ≤ 4% from alternatives
  with an identical first symbol (what FGLL-style factoring would fix).

So: run the deterministic 79% cheaply (this document), and remove the busiest non-LL(1) sites
by grammar transformations (left recursion to loops, inlining plus factoring), which is a
separate track.

## 2. The picture

GLL is a recursive-descent parser that may try every alternative. Two things differ from plain
recursive descent:

- a call can return more than once (`A = a | a a` at 3 may end at 4 and at 5);
- the same call can be asked for from many places, and is done once and shared.

What is shared is the **cluster (A, j)**: a notebook for "A, starting at j", with

- **returns**: who waits for the answer. A *return edge* says "I called A from this place in my
  alternative, and my own work started at u" — and, since the brackets, what the caller needs
  (section 4).
- **pops**: where A, started at j, has ended so far.

A descriptor `(L, k, i)` is one piece of pending work: continue at slot `L`, inside a cluster that
started at `k`, at input position `i`.

## 3. enter, leave, resume

**enter — "I want A at position j".** Write yourself down as a waiter in the notebook (A, j). If
the notebook is new, start A: a descriptor for every alternate the next character can begin. If
it existed, A at j is already running or done: the endings it has found so far are yours too,
handed over through `resume`.

**leave — "A, started at k, has just ended at i".** Write `i` in the pops of (A, k); if it was
already there, stop (everyone was told). Otherwise tell every waiter, through `resume`.

**resume — "one waiter, one ending".** The single place where "a call came back" is handled:

1. Does this waiter accept this ending? (A caller that needs something refuses an empty one.)
2. Record the yield: this occurrence of A, called at `start`, read up to `end`.
3. Continue the waiter's alternative after A, from `end`, if the next character fits.
4. For a loop: perhaps go round again — call the body at `end` with the same waiter.

Results reach a waiter by two routes: through `leave` (the waiter was there first) and through
`enter` (the waiter came after A had already ended). Both call `resume`, so the outcome does not
depend on who came first — which is what makes GLL correct.

Example, `S = A A . A = a | ε .` on `a`: the first `A` enters (A, 0) and seeds it; the ε
alternate ends at 0, so the second `A` enters (A, 0) — an existing notebook with pop 0, so it is
resumed at once; the `a` alternate ends at 1 and resumes both waiters. A at 0 was parsed once.

### In the hybrid

| | general (today) | fast (deterministic stretch) |
|---|---|---|
| **enter** | find or create the notebook, add the waiter, seed descriptors | exactly one alternative fits: push a **frame** on an ordinary call stack and run that alternative in place; no notebook, no descriptor |
| **leave** | write the pop, tell all waiters | the only waiter is the top frame: pop it and resume it |
| **resume** | as above | **the same** |

`resume` is what the two modes share: how a call is made and remembered differs, what happens
when it returns does not. So both modes record the same yields, and the hybrid can be checked
against plain GLL by comparing yields.

**A split.** When two alternatives fit, the parse needs full GLL. The frames on the call stack
are turned into notebooks and waiters — each frame becomes one return edge in a cluster — and
from then on those calls return through `leave` like any other. Descriptors then run in fast
mode again until their next split.

**When a call may go fast.** Exactly one alternate fits, there is no cluster for the call, and
the same call is not already open at this position (left recursion needs GLL). "No cluster" is
a lookup, but only at or below the **watermark**, the highest position at which any cluster was
made: beyond it none can exist.

**Why other paths do not matter.** Frames belong to the current path alone: it runs until it
ends, dies or splits before any other descriptor is processed, so no other path can attach to
an open frame; at a split its open frames become clusters, which other paths then find and join.
So each path uses its own LL(1) stretches, also in the middle of ambiguous regions.

**The cost: repeated fast work.** A call one path completed in fast mode leaves no cluster, so a
different path wanting the same call at the same position parses it again — the same yields,
but the work twice. The repeat is bounded: it is a deterministic parse (one result, cost its
length), and a call that split inside became a cluster and is joined, not repeated. Paths that
merge (two readings returning to one cluster) lose their duplicate there, so what follows the
merge is parsed once. It costs only where two genuinely different readings both parse the same
construct at the same position (section 6: characters read 240 → 450 in that case, while
descriptors drop 392 → 121).

A memo of fast calls would remove the repeat, but a lookup keyed by (call, position) is exactly
the cluster lookup fast mode exists to skip; it is not worth it unless measurements on real
grammars say otherwise.

**Rejected: Elkhound's rule.** Elkhound runs plain LR only while the GLR stack has a single top.
The GLL version — go fast only when the worklist is empty — was built and measured (2026-11-21):
it fails, because our worklist is depth first. After a split, one branch runs while its sibling
waits in the worklist, so everything after the first split ran slow: `S = A T`, `A = a | a`, then
300 × `b`, gave 307 descriptors, the same as plain GLL. GLR escapes this because it processes all
stacks in step, token by token. Processing descriptors in position order would restore that, but
needs a priority queue and still goes slow throughout every ambiguous stretch.

## 4. Need

**The rule.** Brackets must give "reading nothing" exactly one tree. `[ ε ]` over nothing could
otherwise be a skip or a pick of ε, and `{ a | ε }` could take any number of empty rounds. The
rule (FormalGrammar.md §5, decided 2026-11-13): a pick of `[ ]` must read something (the skip is
how it reads nothing), every round of `{ }` and `< >` must read something, and only `< ε >` over
nothing has one empty round.

**Why on the return edge.** The need belongs to the call, not to what is called: the body of
`< A >` is called by its first round (may be empty) and by later rounds (must read something) —
the same body, possibly at the same position.

| Where the need is kept | Effect |
|---|---|
| in the body (one notebook per need) | the same work done twice |
| nowhere (filtered when building trees) | empty rounds parsed for nothing; dead wood in the yields |
| **on the return edge** | one shared notebook; each waiter applies its own need in `resume` |

tinyGLL needs two values, `mayBeEmpty` and `nonEmpty`. Bend's "must read nothing" is not needed:
"a round that read nothing gets no next round" already makes an empty round of `< >` the only one.

**What it does in the code.**

1. `resume`: a `nonEmpty` waiter ignores an ending equal to its start.
2. Seeding: a notebook started only by `nonEmpty` callers seeds only the alternates that can
   begin with the next character — an alternate that cannot could only read nothing here.
3. `seeded`: when a `mayBeEmpty` caller arrives later, the notebook also seeds the alternates
   that read nothing, once. What a notebook starts is the union of what its callers asked for,
   so arrival order does not matter.

**In the hybrid.** A frame carries its need like an edge does, and keeps it when a split turns
it into an edge. Need also makes more choices deterministic: in `{ a | ε } b` a round must read
something, so only `a` is a candidate — fast mode — where without the rule every round would be
a split between `a` and ε. And a loop's own decision (round again, or stop) is a choice point
like any other: one option possible, stay fast; both, split.

## 5. Prediction

At a slot X ::= α·β the parse can go on with next character t only if t ∈ FIRST(β), or β can
read nothing and t ∈ FOLLOW(X). tinyGLL asks this before every step that may fail: choosing an
alternate, entering, skipping a bracket, going on after a return. FOLLOW is global, so the test
may let through a step that dies later, but never stops one that would succeed: leaving a step
out removes only dead wood. A caller that needs something is served by FIRST alone.

In the hybrid the same test decides the mode: a choice where exactly one option passes is
deterministic.

## 6. Measured in tinyGLL (2026-11-20)

All variants gave identical derivations on every input. Descriptors:

| Grammar, input | needs on edges | needs ignored | no prediction | BNF translation |
|---|---|---|---|---|
| `{ a \| ε } b`, "aaab" | **7** | 12 | 12 | 9 |
| `< A >`, `A = a \| ε`, "a" | **8** | 11 | 12 | – |
| `{ A B } c`, nullable A, B, "c" | **1** | 7 | 8 | 3 (hand ε-removal) |
| `E { p E }`, "ipoipicpi" | **20** | 20 | 27 | 23 |
| `{ a \| a a }`, "aaaaaaaa" (34 trees) | **25** | 25 | 27 | 34 |

After trimming tinyGLL to one mode (prediction everywhere, needs on edges): on every input up
to length 6 over 10 grammars it agrees with the original BNF-only tinyGLL, run on exact BNF
translations, in acceptance and number of derivations (12,420 of 12,424; the rest are a cyclic
grammar, whose infinitely many trees the two tree builders cut off differently), with 53,715
descriptors against 181,622.

Lesson from the BNF column: where a bracket body consists of nullable nonterminals
(`{ A B }`), bookkeeping cannot help; the grammar has to change (ε-removal). That belongs to the
transformation track.

### Fast mode (2026-11-21)

tinyGLL takes the fast path when there is no cluster for the call (a lookup only at or below the
watermark) and exactly one alternate fits (section 3). On every input up to length 7 (5 for
larger alphabets) over 20 grammars — the EBNF ones above, ambiguous, left-recursive and
nullable-cyclic BNF grammars, and four mostly-LL(1) grammars with local ambiguity — the hybrid
and general-only GLL agree in acceptance, derivations and **every yield** (20,537 inputs);
descriptors 52,895 against 100,397.

Mostly LL(1) with local ambiguity, the profile of Swift (characters read count repeated work):

| Grammar | Length | Descriptors general → hybrid | Characters read general → hybrid |
|---|---|---|---|
| `S = A T`, `A = a \| a`, `T = { b }`: one early split | 301 | 307 → **4** | 302 → 302 |
| statements, labeled `i k X` vs expression `X`, both starting with `i` | 240 | 398 → **121** | 270 → 270 |
| two readings `E x` and `E y` sharing one expression `E` | 240 | 392 → **121** | 240 → **450** |
| two readings that both survive to the end of each statement | 240 | 482 → **121** | 480 → 480 |

The third row is the repeat of section 3: `E` is parsed by both readings instead of shared.
(An earlier version also required an empty worklist — Elkhound's rule; it gave no gain at all on
the first row, see section 3.)

Long valid inputs:

| Grammar | Length | Descriptors general → hybrid | Clusters general → hybrid |
|---|---|---|---|
| expression grammar, BNF (LL(1)) | 201 | 845 → **1** | 423 → **1** |
| `S = E { p E }` | 201 | 344 → **1** | 202 → **1** |
| `S = { a }` | 300 | 302 → **1** | 301 → **1** |
| `S = { a \| ε } b` | 301 | 302 → **1** | 301 → **1** |
| `S = { [ a ] b }` | 300 | 402 → **1** | 301 → **1** |
| `S = { a \| a a }` (ambiguous) | 40 | 82 → 82 | 41 → 41 |
| `S = b \| S S \| S S S` (ambiguous) | 20 | 972 → 972 | 20 → 20 |

The one descriptor and cluster left are the start symbol's. Where the grammar really branches,
nothing changes, as it should.

**Open: a loop that started in general mode stays general.** Its next round is started by
`resume`, which runs inside `leave`'s loop over all waiters and so cannot take over the
registers. Once the other paths have died, the loop could go fast again; how often this costs
something on real grammars is still to be measured, together with the two measurements in
section 3.

## 7. Where the ideas come from

- **GLL and CNP.** GLL is due to Elizabeth Scott and Adrian Johnstone (*GLL parsing*, 2010). The
  form used here — clusters (X, k) instead of a graph-structured stack, descriptors (L, k, i),
  `call`/`rtn`/`ntAdd`, and the BSR set of yields instead of an SPPF — is Clustered Nonterminal
  Parsing from *Derivation representation using binary subtree sets* (Scott, Johnstone, van
  Binsbergen, 2019) and *A reference GLL implementation* (2023). Our `enter`/`leave` are the
  papers' `call`/`rtn`. The pops set, so that a late waiter still gets earlier endings, is GLL's
  contingent return set P; the same need appears in Earley's algorithm, as *Structuring the GLL
  parsing algorithm for performance* points out.
- **resume** is our own refactoring: the two copies of "deliver an ending to a waiter" in
  `call` and `rtn`, made one function once delivery had more to do.
- **Prediction** is classic LL(1): FIRST, FOLLOW and select sets as in the compiler textbooks
  (Aho, Sethi, Ullman); the GLL papers apply them through `testSelect`. The rules are written
  the way Bend states them (`Bend/core/TABLES.bend`): the least sets closed under a few rules.
- **EBNF loops** as one shared call rather than a recursion per round follow *GLL Syntax
  Analysers for EBNF Grammars* (Scott, Johnstone). That a group at the end of an alternate needs
  no return point is the observation behind FGLL in *Structuring the GLL parsing algorithm for
  performance*; here it appears as the next round being a tail call with the same edge — the
  tail-call idea from programming languages.
- **Need** comes from this project: the rule on empty brackets in FormalGrammar.md §5, and Bend's
  needs on occurrences (`G!`, `G⁰`, `Core.Need`) in the EBNF-to-BNF translation. It is related to
  the classic ε-free variants of nonterminals used in ε-removal, but kept at run time on the
  caller instead of in the grammar. Putting it on the return edge follows one principle: a demand
  that depends on the caller is a filter on the edge, never part of the shared cluster, and what
  a cluster starts is the union of what its edges asked for.
- **The hybrid** is inspired by Elkhound (McPeak and Necula, *Elkhound: A Fast, Practical GLR
  Parser Generator*, 2004), which runs plain LR while there is one stack top and one action, and
  GLR only where the parse splits. Its condition does not carry over to depth-first GLL (section
  3); here each path goes fast on its own, and a split turns its open calls into clusters.
  ANTLR's ALL(*) (Parr, Harwell, Fisher, 2014) is related in spirit:
  cheap deterministic prediction first, the full analysis only on conflict. The Bend laws
  `tables_ll1_at` and `seeds_one_at` (at an LL(1) choice point at most one production is seeded)
  are the formal ground for taking the fast path.

**Prior art, checked 2026-11-21.** In the papers: the original GLL paper and *GLL parse-tree
generation* (§4.6) give LL(1) nonterminals a template that jumps to the one alternate instead of
creating its descriptor — decided statically per nonterminal, and calls still create stack nodes,
edges and pops. *A reference GLL implementation* (2023) adds a FIFO short circuit for the last
descriptor of a call, and says the conditions for suppressing descriptor creation "are yet to be
fully studied". *GLL Syntax Analysers for EBNF Grammars* says deterministic behaviour on LL(1)
parts is "straightforward" but does not describe it. In code (GitHub `AJohnstone2007` and
`iguana-parser`): ART v2 (C++) declares an option `artExploitDeterminism`, "use deterministic
parsing on LL(1) deterministic parts of the grammar", that is never used; ART v3's "pop short
circuit" is the duplicate-pop guard; current ART (`GLLModal`) and the reference implementation
create a stack node per call, with their lookahead tests commented out or absent; Iguana has an
LL(1) sub-grammar detection that is commented out. Not found anywhere: calls without any cluster
or edge, materialised only at a split; the per-position, need-aware decision; fast mode per path.

## 8. Next steps

1. ~~Fast mode in tinyGLL: frames, the split, and a yield comparison against general mode.~~
   Done 2026-11-21 (section 6), without a flag: the comparison used a saved copy of the
   general-only engine.
2. On real grammars, measure repeated fast work (characters read, against plain GLL) and loops
   stuck in general mode; act only on what the numbers show.
3. A Bend twin law: the hybrid's yields equal GLL's.
4. Only then, and agreed first, ApusApus.

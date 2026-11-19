# Formal grammar: a layered specification

Version 3, 2026-11-13. A plan in progress: step 0 (measurements), step 1 (the core and the
translation) and step 2 (the parser, pruning and the exact set) are done, in `Bend/core/`, and
so are step 4 (all three phases), step 5 (rule 2; rule 1 dropped) and step 6 (the LL(1) laws on
the core).
Version 1 (2026-11-11) proposed well-formedness rules on today's specification; version 2 put
them on a smaller core; version 3 keeps the LL(1) laws on that core, with a second
translation of loops. Section 11 lists the changes.

## 1. Why

The Bend twin (`Bend/`) specifies what a grammar with annotations means (`SPEC.bend`) and
proves algorithms against that meaning (`LAWS.bend`). Three things make it larger and weaker
than it needs to be:

- **An escape hatch.** Every law about an algorithm says "whenever it hands out an answer,
  the answer is right" (`Bend/README.md`, "What the laws promise"). An oracle that does not
  implement part of the spec returns nothing there, and its law still holds. Twice now a class
  of grammars turned out to be silently unchecked this way (the witness search on cyclic
  grammars; several extent marks in one sequence).
- **No notion of an illegal annotation.** The spec gives every combination a meaning. Legality
  is decided in four other places instead: `ApusParser`, Swift's grammar loader, the oracles'
  refusals and the Bend export's refusals.
- **Everything is stated on full EBNF.** Trees have seven shapes (node, pick, loop, round,
  skip, leaf, and ε) and slots carry paths through nested brackets. Every definition and every
  proof walks all of them: the same seven-case tree walk exists in eight copies in the phase
  proofs (3.6k lines), and paths and their prefixes run through all 52k proof lines.

**Size.** `Bend/` has 59.5k lines (2026-11-13). It grew from 12.9k (2026-10-28, parser and
exactness) to 34.4k (2026-11-01, the three oracle phases) to 58.6k (2026-11-12, the LL(1) laws,
prediction, plugging, support). The simplifications shrank what they touched; the growth is
new laws, each paid for in seven tree shapes and, for the phases, in copies of one walk.

| Area | Lines |
|---|---|
| oracle proofs (prefer, extent, guard, plug, support, subparse, local) | 24.1k |
| LL(1) proofs (generated) | 14.8k |
| parser proofs (GLL, prune, rounds, spell, exact, trees) | 8.6k |
| spec, laws, lemmas, examples | 4.1k |
| prediction proofs | 2.1k |
| definitions (parser, oracles, LL(1), prediction, cost) | 4.9k |

The plan aims at 25–30k, keeping every law the tests and the LL(1) transforms rely on
(section 10): the bracket shapes and the copies go, not the claims.

## 2. Principles

- **Bend is the reference.** The meaning of every annotation is defined in `SPEC.bend`.
  Swift's engine implements it; the tests compare Swift with Bend, never the other way.
- **Pure reasons only.** A rule needs a language-design reason that holds for any grammar.
  That a particular grammar (such as `Swift.apus`, a stress test) uses or does not use a form
  is no reason; such a grammar serves only as a regression check.
- **No desugaring in Swift.** Swift's engine keeps EBNF (it is faster, and its trees are what
  users see). The Bend export translates the grammar one to one; any translation to a core
  happens inside the spec, so its meaning is specified too.
- **Rules, not implementation limits.** Where an oracle does not handle a well-formed form, the
  oracle is incomplete; that is not a reason to forbid the form.
- **Keyed facts, never lists of trees.** A cyclic grammar has infinitely many trees
  (`A = A | "a"` reads `a` as `A(a)`, `A(A(a))`, …). GLL copes by recording each descriptor, call
  and step once, keyed by slot and positions. Every algorithm of the twin that reasons about
  trees does the same: one fact per key (a symbol over a span, a segment and start), found as a
  least fixpoint. The meaning keeps every finite tree; the algorithms never list them.
- **Trees, not language equivalence.** The twin is about trees (the Oracle chooses among them;
  the tests compare tree steps). The translation from EBNF is the meaning of EBNF (section 5),
  so it must give each reading of the grammar as written exactly one tree, not merely keep the
  language. That is checked against today's specification (`Bend/core/EBNF_EX.bend`) and, in
  the tests, against Swift's steps.

## 3. The layers

| Layer | What it adds | Trees | Proved on it |
|---|---|---|---|
| L0, BNF core | productions `A = x1 … xn` over terminals and nonterminals; n = 0 is ε | leaf, node | the parsers, pruning, the oracles, LL(1), every law |
| L1, EBNF | `( )`, `[ ]`, `{ }`, `< >`, ε as an item | none of its own: the core trees of its translation | nothing: the translation (section 5) is its meaning |
| L2, annotations | guards, ranks, extent marks | — | their meaning is defined on L0 |
| L3, well-formed | the rules of section 8 | — | a hypothesis of the oracle laws only |

Well-formedness is not a hypothesis of the parser, pruning, exactness and LL(1) laws: they hold
for every grammar, and making them conditional would only weaken them.

Chomsky normal form was considered and rejected as the core: ε-removal and unit-rule removal
merge distinct trees (a cyclic grammar has infinitely many trees and its normal form finitely
many), and they destroy the alternatives and sequences the annotations are attached to. Its
useful half, binary steps, the core has already: a BSR step `(X = α · β, i, k, j)` is the
intermediate node for the prefix α.

## 4. L0: the BNF core

    Need       = Anything | Something | Nothing
    Sym        = Terminal{kind} | Nonterminal{id, need}
    Production = Production{lhs, rhs: List<Sym>}
    Tree       = Leaf{kind} | Node{production, children}
    Bsr        = Bsr{production, dot, i, k, j}   -- no path

Written in `Bend/core/CORE.bend` (step 1). `fits`, `leaves`, `steps` lose five of their seven
cases; `pathEq`, prefixes and the `seqAt`/`rpath` machinery disappear. Every proof that walks a
tree has two cases. A parse tree is defined with `reads` (the forest fits the items and matches
the input from a position, counting positions as `steps` does), which the third measurement
showed saves most position arithmetic. An occurrence's `need` carries the rules for empty
rounds (section 5); written nonterminals have `Anything`.

## 5. L1: EBNF as a translation

**Every bracket the same way.** Each bracket occurrence gets a fresh *group* nonterminal G whose
productions are its alternatives, as written. `[ ]`, `{ }` and `< >` add a fresh *shape*
nonterminal H with fixed productions around G:

    ( τ1 | … | τn )   →  G = τ1 | … | τn
    [ … ]             →  H = ε | G!
    { … }             →  H = ε | H G!                   (towards Swift)
                         H = ε | G! H                   (towards LL(1))
    < … >             →  H = G⁰ | K,  K = G! | K G!     (towards Swift)
                         H = G⁰ | G! K,  K = ε | G! K   (towards LL(1))
    ε (an item)       →  E = ε, one E for the grammar

`G!` is an occurrence that must read something, `G⁰` one that must read nothing (the need of
section 4). A loop's body is a group, as Swift Apus builds it: `{ τ }` and `{ ( τ ) }` mean the
same.

**The translation is the meaning** (step 1, 2026-11-13). An EBNF grammar has no trees of its
own: its parse trees are the core trees of its translation. So there is no second notion of
tree to relate the translation to, and no bijection theorem to prove; the 14 rewriting laws
hold by construction. Whether the translation gives each reading as written exactly one tree is
a property of its definition, checked against today's specification on examples
(`Bend/core/EBNF_EX.bend`: optional pick and skip, a loop with none and two rounds, `< >` with
its one empty round and with two rounds, an ε alternative, and that `< >` refuses an empty round
next to others) and, in the tests, against Swift's steps.

**How it is computed** (`Bend/core/EBNF.bend`). A new nonterminal is *named by where its
bracket stands* (production, path, role), so the walk through nested brackets needs no
counter; a second, flat pass numbers the names (written nonterminals keep their numbers,
productions as written keep theirs). The walk through nested brackets uses nesting fuel, as
`GLL.bend` does, because Bend has no mutual recursion; a grammar nested deeper than that has no
translation and is reported (`ok`), never translated silently wrong.

So guards and ranks always sit on G's productions, the alternatives as written. A shape
nonterminal's productions are generated: never ranked, never marked, never guarded. In
particular the ε production of `[ ]` and `{ }` is no rival of a pick: a skip makes no choice,
as today (`SPEC.bend`, `Unbeaten`; the test `avoidAloneRanksNothing`).

**Two translations of loops.** L0 is plain BNF, so no L0 definition or proof depends on the
direction of a loop; only the translation does. Each family of laws uses the direction it needs:

| Laws | Need | Loops |
|---|---|---|
| parser, exact set, the three phases | steps that are Swift's yields | left-recursive |
| LL(1) (tables, unambiguous, no dead wood, `ll1_at`), prediction | the choice "another round or stop" made after each round | right-recursive |

- *Towards Swift.* Swift's engine records a loop as Scott and Johnstone do: each round runs the
  body from the loop's start, so later rounds chain on to earlier ones (`SPEC.bend`, `walk`).
  The left-recursive translation has exactly those steps: `H = H · G` over `(i, k, j)` is the
  round's link step from the loop's start i over a round from k to j. A right-recursive one
  would need the loop's end in every round's step, which Swift's yields do not carry.
- *Towards LL(1).* A left-recursive production is never LL(1), so every grammar with a loop
  would fail. In the right-recursive translation each round's start is where "another round or
  stop" is chosen, as in `SPEC.bend`'s `choicesMade` today; for `< >`, K makes the later rounds
  and stopping choose after the round before (today's `AfterRoundAt`). *A grammar as written is
  LL(1) when its right-recursive translation is.* This is the textbook result for EBNF (Wirth's
  conditions), here a definition, and the LL(1) transforms keep working on the grammar as
  written.

The LL(1) laws speak about trees, choices and the twin's own LL(1) parser, never about Swift's
yields, so the second translation does not touch the comparison with Swift. Where an LL(1)
law speaks about the meaning of a grammar (`ll1_unambiguous`: one tree per input), it needs that
the two translations' trees correspond one to one. They differ only in the loop shapes (a chain
of H nodes built from the left or from the right), so that is one small theorem about loops,
not a theorem about all of EBNF; it belongs to plan step 6.

**How the trees correspond**, for reading the examples. A pick of `( )` is a node of G; a pick
of `[ ]` is an H node over a G node; a skip is a node of H's (or E's) empty production; a loop
with rounds r1 … rn is a chain of H (and K) nodes, each round a G node.

**The step map** (`EBNF.stepsToSwift`). Swift's yields use L1 slots (production, path); the
core's steps use (production, dot) of the translation towards Swift. Each core production
records where it came from: a sequence as written keeps its slots; a loop's shape production
gives the round's link step at one dot; shapes and E give no step of Swift's. So the map is a
function from core steps to Swift's slots that drops the core's extra steps, not a renaming.
It is the one place where the two layers meet in the tests, it is a function in the spec, not
in Swift, and it is defined for the translation towards Swift only.

**What goes away with it.**
- The oracles' loop limitations (version 1's open item, refusals C2, C4, C5): a round is an
  ordinary node of G with its own start.
- The rewriting laws (one unfold/fold pair per bracket kind, `PROOF_TREES.bend`): they hold by
  construction.
- L1 trees, and with them `roundsOk`, paths in proofs, and the bijection theorem estimated at
  1–2k lines.

**Nullable bodies: today's two rules stay** (decided 2026-11-13). When a bracket's body can
read nothing, `[ τ ]` over nothing is only the skip (a pick must read something), and the
rounds of a loop all read something, except the one round of `< τ >` over nothing. On the
core these are the needs of the generated occurrences (`G!`, `G⁰` above), checked by `reads`
and `fits` like any other part of a tree; no tags and no separate rule. Alternatives considered: one rule "keep
the readings with the fewest empty nodes" (shorter to state, but it also chooses silently
between different alternatives that read nothing, and is harder to predict), and forbidding
nullable bodies, as ANTLR 4 and tree-sitter do (explicit, but users would have to remove ε by
hand).

## 6. Cyclic grammars

A cyclic grammar (`A ⇒ … ⇒ A` over the same tokens) is legal and simply ambiguous: every finite
tree counts. The parser is unaffected (its records are keyed, section 2). What the twin needs is
also finite: the set of steps that occur in some tree is a subset of the parser's steps, however
many trees there are. So the laws stay as they are, and every algorithm that reasons about trees
works on keyed facts with a least fixpoint: the witness search (since 2026-11-10), the
certificates of the oracles (C7), and later the proof that the twin answers, whose completeness
argument is then the same kind as GLL's own (a finite set of keys that only grows).

Version 2 first proposed a rule "no node has an ancestor of the same symbol over the same
tokens" (cycle-free trees) to make the trees finite. It is not needed for that, it changed the
meaning of cyclic grammars, and for `< τ >` it did not even reproduce today's rule on empty
rounds (an empty first round slipped through with left recursion, an empty last one with right
recursion). Dropped on 2026-11-13.

## 7. L2: annotations on the core

Every annotation sits on a production or on an occurrence of the core:

| Today (L1) | On the core (L0) |
|---|---|
| guard on a production (`ProdGuard`) or a bracket alternative (`AltGuard`) | on a production (of G, for a bracket) |
| rank on a production (`ProdMark`) or a bracket alternative (`AltMark`) | on a production (of G, for a bracket) |
| extent on a nonterminal (`NtExtent`) or a bracket (`BrackExtent`) | on an occurrence: a production and a dot |

**Extent marks are on occurrences.** A mark compares readings of the sequence it stands in, so
on the core it names one item of one production. A mark on a nonterminal is shorthand for
every occurrence of it *in the grammar as written*; a mark on a bracket marks the one
occurrence of its G or H. Generated occurrences are never marked. This matters for loops: in
`H = H G` (or `G H`) the shape nonterminal occurs in its own production; marking that
occurrence too would add a rule inside the loop (for `@longest { X }`: the rounds before the
last as long as possible, so the last one as short as possible, and so on down the chain),
which today's meaning does not have.

So each kind of annotation has one form, without a separate unification step. The meanings
(admissible, unbeaten, selected) are defined once, on nodes and their sequences, with two-case
walks. They are defined on the left-recursive translation, the one the oracles compare with
Swift.

## 8. L3: well-formed grammars

### Rule 1: one extent mark per sequence (dropped, 2026-11-15)

Dropped: phase 3 on the core decides several marks in one sequence exactly, left to right,
in about 25 lines (`beatsAt`), with no refusal. Kept below as the reasoning that was weighed.


**Rule.** No sequence (the right side of a production) has more than one marked occurrence
(`@longest` or `@shortest`). A mark on a nonterminal marks every occurrence of it in the
grammar as written, so a sequence that refers to a marked nonterminal twice has two marked
occurrences. On L1 this reads: no sequence of the grammar as written, nor any alternative of a
bracket, has two marked items. Generated productions have none (section 7).

**Why.** Two marked items in one sequence compete for the same tokens. In `A B` with both
`@longest`, every token A gains is one B loses, so "A longest" and "B longest" cannot both
hold, and something must say which one decides first. Today's spec fixes an order (left to
right). A group says it explicitly, and can say more.

**The two directions.**

(a) *Every left-to-right order is a grouping.* Take a sequence with marked items at positions
p1 < p2 < … . Put everything after the first marked item into a group, and repeat inside it:

    @longest A  B  @longest C  D      ≡      @longest A ( B  @longest C  D )

The outer mark compares the readings of the outer sequence over its tokens and fixes A's
length. The group's tokens are then exactly what A left over, and the inner mark compares the
readings of the group over those fixed tokens, including every way of splitting the items
between A and C. That is "the first decides, then the next among what is left". The group
must start right after the first marked item: starting it at C would leave B outside, and C
would then be compared within one split of B only, not across all of them.

(b) *Not every grouping is a left-to-right order.* With groups, a later item can decide first:

    ( A  @longest B )  @longest C

The outer sequence has one marked item, C, which decides first; B then decides inside the
group over what C left. No left-to-right rule expresses this.

So one mark per sequence plus groups expresses every left-to-right order, and more, and the
order is visible in the grammar. Keeping the left-to-right form as sugar would need the
grouping of (a) as its definition and a step map for the inserted groups; forbidding it loses
nothing, by (a).

**Draft SPEC wording** (for approval; not in `SPEC.bend`):

    # ONE EXTENT MARK PER SEQUENCE. No right side has more than one occurrence marked
    # @longest or @shortest. Two marked items would compete for the same tokens; a group says
    # which one decides first: `@longest A ( B @longest C )` lets A decide, then C among
    # what A left, and `( A @longest B ) @longest C` lets C decide first.
    def oneMarkPerSequence(+grammar: +List<Production>, +marks: +List<ExtentMark>) -> Bool

    # A well-formed grammar keeps every rule of this section. The laws speak about
    # well-formed grammars only.
    def wellFormed(+grammar: +List<Production>, +ranks: +List<Mark>, +marks: +List<ExtentMark>) -> Bool

**Consequences of rule 1.** `ExtentBest` compares one length; `beats` goes. Swift: a load error whose
message shows the group form; `YieldGraph.extent(rank:)` back to one pass;
`documentation/Ambiguity.md`, "Several marks in one sequence", rewritten from "first come,
first served" to "why this is not allowed, and how to write it".

### Rule 2: no preference cycle

**Rule.** An alternative that outranks a sibling (`@prefer` over a plain or `@avoid` sibling, a
plain one over an `@avoid` sibling) lies on no cycle that reads no input: it cannot derive, over
its own tokens, the choice it belongs to.

**Why.** Preference compares rivals over the same tokens. A preferred rival that comes back, over
the same tokens, to the choice it competes in only says "the same again"; counting it can beat
every reading, so no tree is left. Today the spec handles this inside its meaning: a rival must
not revisit the node's nonterminal or a node above it over the same tokens (`above`, `revisits`
in `SPEC.bend`, about 700 mentions in the proofs). Ruling it out as a property of the grammar,
checked once, is the simpler of the two clean options. Cyclic grammars as such stay legal
(section 6); only an *outranking* alternative may not lie on such a cycle.

**Draft SPEC wording** (for approval; on the core, where every choice is a nonterminal):

    # NO PREFERENCE CYCLE. A production of A reaches nonterminal B when one of its items is B
    # and every other item can read nothing. A cycle that reads no input is a path of such
    # steps from a nonterminal back to itself. A production that outranks a sibling
    # (Preferred over Plain or Avoided, Plain over Avoided) lies on no such cycle: it would be
    # a rival that only comes back to where it competes, over the same tokens.
    def noPreferenceCycle(+grammar: +List<Production>, +ranks: +List<Mark>) -> Bool

On the core the definition is exact about brackets, since a bracket is a nonterminal; shape
nonterminals are never ranked, so only G's productions can be the outranking ones. Swift's
`diagnosePreferenceCycles` over-approximates there ("may report a cycle the bracket cannot
actually close") and has to be made exact, so that Swift and the spec agree.

**Done 2026-11-15** on the core: `noPreferenceCycle` in `PREFER.bend`, decided by two checked
closed sets (what can read nothing; what an outranking production reaches). The cycle clause
is gone from phase 2's meaning and its closure from the oracle, so `oracle_exact` holds on
every grammar and refusal C6 is gone (on a grammar with a preference cycle the oracle
answers, and may choose nothing). The lemma first planned, that no rival avoids the climb,
is false: the climb over-approximates (it lifts through nodes that end later), and
`P = X c | a, X = @prefer Y | a, Y = P` is well-formed but has such a rival. The true lemma
is proved instead (`no_self_rival`, `PROOF_RULE.bend`): on a well-formed grammar no rival
holds a node of its own nonterminal over all its tokens. Swift's `diagnosePreferenceCycles`
now checks a bracket's alternatives against the bracket itself, which is exact.

**Consequences of rule 2 (as planned).** `SPEC.bend` can drop the rival-cycle condition, given one lemma: in
a well-formed grammar no rival revisits the node's nonterminal, or a node above it, over the same
tokens. `PREFER.bend`'s refusal C6 and its cycle certificate (`closedFor`) become unnecessary.

## 9. What is refused, after the plan

| | Kind | Today | After |
|---|---|---|---|
| A | resource limits (fuel, time) | reported as no answer | the same, with a reason; rarer, since tree algorithms use keyed facts (section 6) |
| B | checks of untrusted parts | a failure is a bug | the same |
| C1 | several marks in one sequence | `EXTENT.bend` refuses | decided exactly (core phase 3) |
| C2, C4, C5 | loop limitations of the oracles | refused | gone: a round is a node (section 5) |
| C3 | the extent oracle's stitched-reading check | refuses | gone: the core's phase 3 decides exactly on an exact chosen set |
| C6 | a preference cycle | `PREFER.bend` refuses | not well-formed (rule 2); the core oracle answers |
| C7 | certificate searches (`Witness.solve`) | unknown verdicts | witness searches: a fixpoint, complete with enough fuel (to prove, step 8); phase 2's rival: decided by a checked closure (below) |
| D | outside the spec (lexical ambiguity, layout gates, an extent on a terminal) | not exported | the same |

The inventory was compiled from the oracles' comments; step 7 checks it is complete (every
site that returns nothing, classified).

**The inventory on the core** (step 7, 2026-11-16). Every site in `Bend/core/` that returns
`None`, `Unknown` or `OutOfFuel`:

| File | Site | Kind |
|---|---|---|
| `GLL` | `run` out of fuel | A |
| `CHECK` | `checkPick`: the final state is not closed, or lacks the root cluster | B |
| `PRUNE` | `needLoop` out of fuel | A |
| `PRUNE` | `prunePick`: the needed segments are not closed | B |
| `WITNESS` | `fixpoint` out of fuel; then `rootFor` finds no root forest | A |
| `EXACT` | `exactPick`: a witness tree fails its check (B) or a step is left uncovered (A) | A, B |
| `GUARD` | `foundPick`: the closure on w is not closed, or its forest for "q derives w" fails `reads` (decided with enough fuel, `phase1_decides`) | A, B |
| `PREFER` | `certTri`: the rival forest fails its certificate | A, B, C7 |
| `ORACLE` | `oraclePick`: some step's verdict is Unknown (from the three above) | as those |
| `EXTENT` | `coverFrom`: the chosen set is not covered by checked witness trees | A, B |
| `PREDICT` | `predictPick`: the grown tables are not closed | A, B |
| `PREDICT` | `ll1Pick`: the tables do not pass the LL(1) check | not a refusal: the LL(1) parser is for LL(1) grammars only |
| `SUPPORT`, `PREDICT` | `supportedPick`, `ll1Run`: the state is not reached within the fuel | A |
| `EBNF` | `stepOf`: a step of a hidden production | not a refusal: it has no Swift step |

Lookups that return `None` for "no mark here" (`extentOf`, `ntOf`, `productionAt`) are not
refusals. So, apart from fuel (A) and failed checks of untrusted parts (B), one algorithmic
refusal remains:

- **Phase 2's rival (C7), fixed 2026-11-16.** The certificate for "m beats q over w" took the
  first forest the witness search found for m over w, admissible or not, so `X = @prefer Y |
  a`, `Y = a >!> Z | a`, `Z = a` on `a` got no answer, and neither did `Y = a >!> Z` alone.
  Now the rival is searched among segments of the input grown Earley-style from m at i, only
  through steps phase 1 answers Yes (`RIVAL.bend`, not trusted). A whole segment of m gives the
  forest for the certificate (No); otherwise, when the segments are checked closed, no rival
  exists (Yes, `PROOF_RIVAL.bend`: one walk over the rival). Phase 2 no longer runs sub-parses.
  Both examples now get answers (`ORACLE_EX.bend`).

## 10. Plan

0. **Measure first.** Done: the walk, phase 1, and `ll1_unambiguous` (section 12).
1. **L0 and L1.** Done 2026-11-13, in `Bend/core/` (not in the gate yet): the core types and
   definitions (`CORE.bend`), both translations and the step map (`EBNF.bend`), examples
   against today's specification (`EBNF_EX.bend`). No bijection theorem: the translation is the
   meaning (section 5).
2. **The engine on L0.** `GLL.bend`, pruning and the witness search on the core (two-case
   trees); their laws restated. The engine adds return edges without looking for an existing
   one: Afroozeh's argument (proven on today's engine, kept as
   `documentation/drafts/AFROOZEH.bend`) is the reason, not a law; the engine is not trusted.
   - 2a, done 2026-11-13 (`Bend/core/GLL.bend`, `CHECK.bend`, `PROOF_GLL.bend`): the engine,
     its closedness check, and `gll_every_parse_step`, checked with `--verdict`. 1,385 lines
     against 4,061 today (whose proof also covers prediction, plan step 6). Need flags cost one
     condition in the resume rule and one lemma. On the examples the core engine's raw set has
     less dead wood than today's (it never starts an empty later round of `< >`), and today's
     exact set is contained in it.
   - 2b and 2c, done 2026-11-14 (`PRUNE.bend`, `PROOF_PRUNE.bend`, `WITNESS.bend`, `EXACT.bend`,
     `PROOF_EXACT.bend`): pruning and `prune_every_parse_step`; the witness search and
     `gll_bsr_exact`, all checked with `--verdict`. Pruning needs no round rule (the needs did
     that work in the engine). The witness search keeps one fact per segment and flag, so it
     answers on cyclic grammars (`A = A | a`), where today's failed (seed 86). On the
     examples the core's exact set, after the step map, is today's exact set.
   - The parser half in all: 2,684 lines against 9,758 today (engine, check, pruning, rounds,
     witness search, exact parser, their proofs, and the rewriting laws, which the core no
     longer needs).
   - `exact_trees_spell`, done 2026-11-14 (`PROOF_SPELL.bend`, 605 lines against 959): a tree
     that fits, uses only steps of the exact set and is as long as the input spells the
     input. Its token facts come from the exact parser's own checks (plain data), not from
     `gll_bsr_exact` (a function, which Bend's affine logic lets a proof use only once).
3. **Keyed facts.** Check that every tree-level algorithm (witness search, certificates) works
   on keyed facts with a least fixpoint.
4. **L2 on the core.** The three phases defined on L0, each proved with the one template walk.
   - Phase 1, done 2026-11-14 (`GUARD.bend`, `PROOF_DECIDE.bend`, `PROOF_GUARD.bend`). The
     meaning is step-based, not tree-based: a parse tree is admissible when each of its steps
     keeps the rules it decides. A completed step (`d = n`) decides `>?>` and `>!>` on the input
     from the node's start, and `@left` on what its last item spells; a first step (`d = 1`)
     decides `@right` on what its first item spells. Each question ("does production q derive
     w?") is answered Yes with a checked witness forest, No when the exact set over w has no
     completed step of q, and Unknown otherwise.
   - Phase 2, done 2026-11-14 (`PREFER.bend`, `PROOF_PREFER.bend`), also step-based: a
     completed step of q over i .. j is beaten when a production of q's nonterminal with a
     higher rank has a rival there. A rival is a forest over the same tokens whose steps, placed
     at i, keep their rules, with no node over all of the tokens whose nonterminal can sit over
     them at i in some admissible reading (a closure, the climb). Today's meaning uses the
     node's ancestors in its own tree instead. The two agree on every input where the oracle
     answers: a step is kept only when no higher-ranked production derives the tokens at all,
     and removed only with a rival that avoids a set C closed over the exact set, which holds
     every nonterminal of the climb in every reading. Loops need no `{ ( τ ) }` restriction:
     the translation gives each round its own production.
   - Phases 1 and 2 share one filter (`ORACLE.bend`, `PROOF_ORACLE.bend`): each step's
     verdict is the conjunction of both. The rival's steps are checked with phase 1's verdict
     directly, so phase 2 needs no phase-1 set of its own. `oracle_exact` says the oracle's set
     holds exactly the steps of the chosen trees (all steps keep their rules and complete no
     beaten node); an Unknown anywhere means no answer (section 1's escape hatch, closed by
     step 8). Both phases come to 3,515 lines of meaning, oracle and proof against 12,911
     today (`GUARD`, `PROOF_GUARD`, `PREFER`, `PROOF_PREFER`, `PROOF_SUBPARSE`).
   - Phase 3, done 2026-11-15 (`EXTENT.bend`, `PROOF_EXTENT.bend`), step-based: a step of q is
     out when it stands on a reading of q (the ends of its items) that ends at some e, and
     another reading that ends at e reads q's marked items better: the same on every marked
     item before the step's item, better on it. A reading's steps must each lie on some tree
     that phases 1 and 2 keep; they may come from different trees, the context today's
     self-check already uses. For that, the phase-1/2 set is handed out only with witness
     trees inside it, so every step of it lies on a chosen tree (the set is exact, not just
     embedding). Then the readings in the set are the readings, and the oracle decides
     exactly: no Unknown, and several marked items in one sequence need no refusal. 1,370
     lines of meaning, oracle and proof against 6,698 today (`EXTENT`, `PROOF_EXTENT`). All
     of step 4 comes to 4,885 lines against 19,609.
5. **L3.** `wellFormed` (rules 1 and 2) and the lemma that drops the rival-cycle condition;
   Swift's loader agrees (a test on the fuzz grammars, which keep
   generating every form); the extent changes of section 8.
6. **LL(1) and prediction on the core**, through the right-recursive translation: LL(1) of the
   grammar as written defined as LL(1) of that translation; the six laws (`tables_ll1_sound`,
   `ll1_unambiguous`, `ll1_no_dead_wood`, `ll1_at`, `predict_every_parse_step`,
   `predict_saves_work`) restated; the generators in `Bend/gen/` rewritten for two-case trees.
   - Started 2026-11-15. The meaning (`LL1.bend`, 52 lines; LL(1) of a grammar as written is
     LL(1) of its translation towards LL(1)) and the two laws that need only the meaning,
     `ll1_unambiguous` and `ll1_at` (`PROOF_LL1.bend`, 662 lines; today 4,652 for
     `PROOF_UNAMBIGUOUS` and 1,045 for `PROOF_LL1AT`), are done. A negative check: with
     FIRST alone in `Predicts`, the proof fails.
   - The tables and `tables_ll1_sound` are done (`TABLES.bend` 268, `PROOF_TABLES.bend` 1,024;
     today `FIRST.bend` 164, `LL1.bend` 173 and `PROOF_LL1.bend` 2,708 lines). The tables are
     grown untrusted and checked closed, so the check is a function of the grammar and fuel.
     Two negative checks fail as they must: FOLLOW without the nullable-suffix rule, and
     FIRST that does not look past a nullable item.
   - Prediction and `predict_every_parse_step` are done. The engine takes a predictor (none, or
     allowed next tokens per production) and the closedness check asks only for the seeds it
     admits; the completeness walk (`PROOF_GLL`) carries one more fact, that every node of the
     tree is admitted where it starts, which for the plain parser is trivial and for the
     predicting one follows from `predicts_node` and `predicts_in`. `PREDICT.bend` 44 and
     `PROOF_PREDICT.bend` 242 lines (today `PROOF_PRED.bend` 431, on top of the engine's
     prediction). A negative check: predict sets without FOLLOW make the proof fail.
   - Support and `predict_saves_work` are done (`SUPPORT.bend` 327 lines; today `SUPPORT.bend`
     255, `PROOF_SUPPORT.bend` 2,212 and `PROOF_SAVES.bend` 685). One induction over the
     reached facts with a goal given as data; the goal "in a closed plain state" gives the
     law. A negative check: rules that resume without the need check make the proof fail.
   - `ll1_no_dead_wood` is done, as a second goal ("on the parse tree") for the same induction.
     The LL(1) parser `ll1Steps` (`PREDICT.bend`) hands out the steps of a predicting run
     whose tables pass the LL(1) check and whose final state is closed and supported. A fact
     is on the tree when a step of the tree witnesses it (a Bool search over the tree's steps,
     no node list); a step's node gives a cursor (the children still to read), and the rules
     follow the cursor; a seed is the tree's production or a table conflict (`pairs_at`); a
     resume ends where the pop says because the tree has one node of x at a position
     (`compare`). `PROOF_HOLD.bend` 278, `PROOF_STATE.bend` 208, `PROOF_TREE.bend` 1,436 and
     `PROOF_SUPPORT.bend` 436 lines (today `PROOF_NODEAD.bend` 1,620 and `PROOF_NODEAD2.bend`
     about 4,030). A negative check: a resumed descriptor at the wrong dot fails. No generator
     was needed. Step 6 is done.
7. **The inventory, complete**, and the algorithmic refusals (C3, C7). Done 2026-11-16
   (section 9): C3 is gone on the core; C7 left phase 2's rival search, fixed in step 8.
8. **The twin answers.** On a well-formed grammar, with enough fuel, each oracle hands out a
   set (TODO.md, "Bend twin: answers"). This closes the escape hatch of section 1; its argument
   is GLL's own (a finite set of keys that only grows, section 6).
   - Phase 2's rival search, done 2026-11-16 (section 9, C7): a checked Earley-style closure
     instead of the first forest of a sub-parse. `RIVAL.bend` 203 and `PROOF_RIVAL.bend` 501
     lines. A negative check: a closedness check that skips terminal items fails the proof.
   - The worklist engine ends closed, done 2026-11-16 (`RUN.bend` 145, `PROOF_RUN.bend` 2,627
     lines): an invariant of seven Bool parts holds at every iteration (checked on example runs
     first, `RUN_EX.bend`); operations that only add descriptors and steps keep it as one
     relation, `call` and `leave` by their own lemmas. So whenever the engine finishes, with or
     without a predictor, its state is closed and has the root cluster (`engine_closed`), and
     the checked parser answers (`checked_answers`). A negative check: an engine that does not
     resume a new return edge at the pops of a known cluster fails the proof.
   - The worklist engine finishes, done 2026-11-17 (`RUN.bend` 241, `PROOF_RUN.bend` 3,106,
     `PROOF_COUNT.bend` 423 lines): the invariant gained three parts (every descriptor, return
     edge and pop lies within the grammar and the input), and every operation keeps the
     measure "unseen descriptors within bounds, plus the to-do list" from rising; taking a
     descriptor off the list lowers it. So with one unit of fuel more than there are
     descriptors within bounds, the engine finishes (`gll_finishes`) and the checked parser
     answers (`checked_always_answers`), with or without a predictor. A negative check: one
     unit of fuel less fails the proof.
   - Pruning answers, done 2026-11-17 (`PROOF_NEEDS.bend` 914, `PROOF_ANSWER.bend` 36 lines;
     `RUN.bend` 266, `PROOF_RUN.bend` 3,249, `PROOF_COUNT.bend` 483). The engine's invariant
     gained an eleventh part: every step lies within the grammar and the input. So a segment
     of the needs loop can be counted as a descriptor, and the same fuel serves both loops.
     The loop's invariant has five Bool parts. The needs still to be added are carried along
     in the invariant itself (a segment is done when its needs lie in those plus the seen
     ones), so one induction over `addSegs` keeps it. With fuel 1 + the size of the
     descriptor universe, the needs are closed (`needs_closed`), and pruning hands out its
     steps, on any steps within bounds (`pruned_answers`) and on the engine's own
     (`pruned_parser_answers`). A negative check: a loop that does not queue new segments
     fails the proof.
   - The witness search, in part, 2026-11-17 (`PROOF_WITNESS.bend` 1,535, `PROOF_WSOUND.bend`
     1,341 lines). Design agreed with the user: keep the fixpoint (ORACLE and EXTENT use it on
     filtered sets) and prove its completeness by a walk over a parse tree, so it serves them
     too. Proven: closed facts and a parse tree of kept steps containing the target give a
     root forest (`root_found`); the fixpoint ends closed with fuel 1 + twice the size of the
     descriptor universe (`witness_closed`); every forest it hands out is a parse tree of the
     input containing the target (`witness_good`); so the exact parser answers once every kept
     step lies on such a tree (`exact_from_answers`).
   - The exact parser answers, done 2026-11-18 (`PROOF_GROUND.bend` 896, `PROOF_FOUND.bend`
     876, `PROOF_ANSWER.bend` 255 lines; `RUN.bend` 389, `PROOF_NEEDS.bend` 1,058). Two order
     facts. (1) Every step, descriptor, return edge and pop rests on steps added before it
     (`groundOk`, RUN.bend; checked on the example runs first): each engine operation keeps
     it, proven directly on the state records without touching PROOF_RUN; resume and token
     match add a descriptor before its step, so a lemma swaps the two additions. (2) Every
     needed segment is a root segment or a need of an older one (`seenJust`, the needs
     loop's invariant gained two parts). Instead of building trees inside proofs, the proof
     works on witness facts: kept segments that a step completes get a fact by induction in
     the steps' order (`bottom`), and a flagged fact goes up the needs' order to a root
     (`up`, `found_root`). So with fuel 1 + twice the size of the descriptor universe the
     exact parser always answers (`exact_parser_answers`). A negative check: a witness search
     that never marks the target fails the proof.
   - The predicting parser answers, done 2026-11-19 (`PROOF_GROW.bend` 1,987, `PROOF_ANSWER.bend`
     275 lines; no definition changed). Each table round either adds a fact from a finite
     universe or changes nothing, and then the table is closed. Facts are counted as
     descriptors, reusing PROOF_COUNT: nullable left sides; FIRST pairs (left side, terminal);
     FOLLOW pairs (start or a nonterminal on a right side, the end or a terminal). FIRST and
     FOLLOW carry an invariant: every fact's token is a terminal of the grammar. The FOLLOW
     seed stays, and the start symbol's FOLLOW rule holds on any table. So with fuel
     1 + the table size, `tablesClosed` holds on every grammar (`tables_closed`). With fuel
     1 + the size of the descriptor universe + the table size, the engine with the predict
     sets finishes, and `predictedSteps` always answers (`predicted_parser_answers`). The
     LL(1) parser's table part is the same; it still refuses on a grammar that is not LL(1)
     (not a refusal, see the table above) and on support. A negative check: one unit of fuel
     less fails the proof.
   - The rival closure answers, done 2026-11-19 (`PROOF_RIVAL_GROW.bend` 1,082 lines; no
     definition changed). The hypothesis that phase 1 answers no step Unknown is a Bool,
     `decided`, over every step within bounds (Bend's function hypotheses can be used only
     once). Each round either adds a segment with a new key, counted as a descriptor, or
     changes nothing; a round that adds nothing leaves a closed set, since every step the
     check asks about is decided, and a Yes leads to a grown segment. So with fuel 1 + the
     size of the descriptor universe, the segments grown from m at i are closed and have m's
     start (`rival_closed`). A negative check: a grower that never reads a terminal fails the
     proof.
   - The rival's certificate is sound, done 2026-11-19 (`PROOF_RIVAL_SOUND.bend` 903 lines; no
     definition changed). Every grown segment's forest reads its prefix of items from its
     start to its end, and each of its steps in its node is answered Yes (`grow_ok`). So the
     forest of a segment that completes m passes `certWith`; the reading is moved from the
     input at i to the slice at 0 by spelling. With `rival_closed`, phase 2's rival verdict is
     Yes or No whenever phase 1 decides (`rival_decided`). A negative check: a completion that
     drops the child's forest fails the proof.
   - Phase 1 decides, done 2026-11-19 (reminder (a) below; `CLOSURE.bend` 172,
     `PROOF_CLOSURE.bend` 1,575, `PROOF_VERDICT.bend` 392 lines; `PROOF_DECIDE.bend` 1,448 to
     1,195, `GUARD.bend` 398 to 378). "Does q derive w" is now answered by a judge-free copy of
     the rival closure on w (`GUARD.closureTri`), not by the exact parser and the witness
     search. A first-order judge shared with RIVAL was not possible: Bend wants every
     definition before its use, so the closure, its judge and phase 1's verdict cannot call
     each other (design changed with the user the same day). Its walk, growth and soundness
     proofs are RIVAL's with the judge removed; the segments are counted against the outer
     input, so one fuel bound covers every question cut from it. `rhs_yes` and `rhs_no` keep
     their statements, so PROOF_GUARD is unchanged. With fuel 1 + the size of the input's
     descriptor universe, phase 1 decides every step (`phase1_decides`), and phase 2 decides
     every step within bounds (`phase2_decides`). A negative check: a closedness check that
     skips terminal items fails the proof. Left for step 8: the joined oracles hand out their
     sets (ORACLE, EXTENT), from these verdicts and the exact parser answering.
   - Reminder (a), done 2026-11-19 (see above): phase 1's questions are answered by the
     checked closure, every step allowed, instead of GLL sub-parses.
   - Reminder (after step 8, agreed 2026-11-16): partially LL(1) grammars, for later rewriting
     steps towards LL(1). `ll1_at` and the prediction laws are already local or need no LL(1);
     `tables_ll1_sound`, `ll1_unambiguous` and `ll1_no_dead_wood` are all-or-nothing. Add (1) a
     local table law: no conflict among x's productions in the tables gives `LL1At x`
     (`pairs_at` is per pair already); (2) a local determinism law: at a nonterminal that
     passes it, prediction seeds at most one production per cluster. Open design question for
     when rewrites are planned: each rewrite needs a law tying the new grammar's trees to the
     old one's (a cover), else LL(1) facts about the rewritten grammar say nothing about the
     original.

Each step ends with the proof gate (`bend PROOF.bend --verdict`), the examples, `BendCheck` and
a 200-seed `BendDifferential` run. Steps 1–6 replace files rather than edit them; today's files
stay until their replacements check.

**Which laws carry weight.** The tests rely on four: the exact set (`gll_bsr_exact`) and the
three phases. The LL(1) and prediction laws carry the LL(1) transforms. The rest (the rewriting
laws, locality and the swap laws, `prefer_avoid_safe`) are kept on the core only where a proof
uses them or they state something a user relies on.

## 11. Changes

During step 1 (2026-11-13):

- The translation is the meaning of EBNF: no L1 trees, so no bijection theorem, and the
  rewriting laws hold by construction (section 5). The principle "bijections" becomes "trees,
  not language equivalence", checked on examples and against Swift.
- The rules for empty rounds are needs on occurrences (`G!`, `G⁰`), checked by `reads`; `< >`
  towards Swift gets a tail K, so an empty round can only be the only one.
- New nonterminals are named by position and numbered in a flat second pass.
- A loop's body is always a group: `{ τ }` means `{ ( τ ) }`, as Swift builds it.

From version 2 to version 3 (2026-11-13):

- The LL(1) and prediction laws stay, for the LL(1) transforms. They need loops translated
  right-recursively, the oracles left-recursively; L0 does not care, so there are two
  translations, which differ only in the loop cases (section 5). Plan step 6 moves the LL(1)
  laws to the core; step 0's third measurement (section 12) did `ll1_unambiguous` there:
  682 lines against 4,652.
- Every bracket translates the same way: a group nonterminal G for its alternatives, plus a
  shape nonterminal H for `[ ]`, `{ }`, `< >` whose generated productions are never ranked,
  marked or guarded. This keeps a skip from being a rival of a pick, as today.
- Extent marks are on occurrences, not nonterminals, so that marking a loop does not also mark
  its own recursive occurrence (section 7). Rule 1 counts occurrences.
- Well-formedness is a hypothesis of the oracle laws only (section 3).
- The proof that the twin answers is plan step 8.
- The standalone Afroozeh law (return edges need no duplicate check) is retired from `Bend/`;
  its argument is the reason the L0 engine has no such check (step 2).
- Section 1 records the size and where it comes from.

From version 1 to version 2:

- The core is BNF (L0) with EBNF as a tree bijection (L1), instead of rules on today's EBNF spec.
- Loops are translated left-recursively, to match Swift's round steps.
- The loop limitations (C2, C4, C5) are resolved by the core, not left open.
- The unified addressing of annotations, dropped in version 1 as cosmetic, now comes for free.
- Revised 2026-11-13: nullable bracket bodies keep today's two rules; cyclic grammars are handled
  by keyed facts (section 6), not by cycle-free trees, which an earlier draft of version 2
  proposed; version 1's rule 2 (no preference cycle) is back as L3's second rule.

## 12. Measurement (step 0, 2026-11-11)

A draft of the core and the generic walk, checked by the kernel (`ALL PROOFS CHECK`), kept
outside `Bend/` (in `documentation/drafts/CORE_L0_measurement.bend`; the later stage in `CORE_L0_walk.bend` and `PHASE1_L0_partial.bend`):

| Part | Draft on L0 | Today on L1 |
|---|---|---|
| tree and step definitions (types, `fits`, `leaves`, `walk`/`steps`, `at`, the empty step, the round rules, path equality) | 86 lines | about 150 lines in `SPEC.bend` |
| the walk of one phase, both directions | 57 lines, once, for every phase | `PROOF_GUARD`: 883 lines (`adm_*` 408, `keep_*` 475); eight such copies, 3.6k lines |
| list-append lemmas for steps | 49 lines | already in `PROOF_ROUNDS`/`PROOF_GLL` |

How the walk is written: a phase is a rule `P` on nodes (production, children, start) and an
oracle on step sets; the phase supplies two per-node lemmas, `d1` (a node whose own steps are
kept keeps `P`) and `d2` (a node that keeps `P`, with its own steps in the parser's set, has
them kept). The walk then proves, for every forest: its steps are all kept exactly when every
node keeps `P`. A node's steps are its own steps followed by its children's, so each direction
has two cases (leaf, node) and splits a list three ways.

**What the measurement shows.**
- The walk itself shrinks from about 450 lines per direction per phase to 57 lines in all.
  That is the 3.6k lines of copies replaced by one template plus a few lines per phase.
- On the core, the tree definitions are about half today's size, and every path goes away.

**What it does not show yet.**
- The per-node lemmas. Today's equivalent for phase 1 is `PROOF_GUARD`'s "one rule at one own
  step" (about 1k lines) plus "where the children are" (336). On the core they lose paths and
  bracket cases, but how much smaller they get is unmeasured. This is the largest remaining
  uncertainty, and the next measurement.
- What the real phases pass to the per-node lemmas: the tree must fit the grammar, and a
  rule reads the tokens after the node. The walk would carry the `fits` facts and the input
  along; an estimated 30–50 more lines, once.
- The cost of L1: the translation, the bijection theorem and the step map. New work, not
  measured; a guess is 1–2k lines, most of it for loops.
- The engine proofs (`GLL.bend`, pruning, the witness search) on the core.

**A Bend detail.** A template proof is checked through its instances: a template that nothing
instantiates is reported as "no model". The generic walk is therefore checked once per phase
that uses it, which is cheap, and every phase must instantiate it through a law.

**Effect on the plan.** Step 0 supports the direction. Before step 1, one more measurement:
phase 1's per-node lemmas on the core (`d1`, `d2` for lookahead, `@left` and `@right`),
instantiating the walk. If they come out well below today's 1.3k lines, the remaining plan
stands as written.

### Second measurement (phase 1, 2026-11-13)

Built on the core and checked: the walk carrying a context, `reads` (fits *and* matches the
input at a position) and an oracle precondition; phase 1's meaning; its per-step oracle with
the "does N derive w?" decider as a template parameter; and the soundness of every rule's Yes
and No answers.

| Part | Core | Today |
|---|---|---|
| core definitions and the walk (context, `reads`, both directions) | 361 lines; the walk itself about 130, once for all phases | 883 in `PROOF_GUARD`; 3.6k over eight copies |
| phase 1's meaning | 122 | about 180 in `SPEC.bend`, plus bracket variants |
| per-step oracle | 106 | 290 in `GUARD.bend` |
| three-valued lemmas | 196 | in `GUARD.bend` and `LEMMAS.bend` |
| per-rule soundness (edge rules; lookahead with its split search) | 243 | 191 in `PROOF_GUARD`, plus derivation reasoning elsewhere |
| node wiring (which own step decides which rule; child positions) | not built; estimated 300–400 | about 1.1k (765 + 336) |

Findings:
- The per-rule reasoning does not shrink: it was already free of paths.
- The gain is the walk (3.6k of copies become one template) and, by estimate, the node wiring,
  which today carries the paths and bracket cases.
- Templates can take dependent proof functions and Type-valued predicates, but are checked only
  through instances; a phase's lemmas are instantiated through laws.

### Third measurement (LL(1), 2026-11-13)

`ll1_unambiguous` on the core, written by hand and checked by the kernel (`--verdict`), in
`documentation/drafts/LL1_L0_unambiguous.bend` (on `CORE_L0_walk.bend`). It was chosen over
`PROOF_NODEAD.bend`, the first idea, because it depends on the spec alone: porting
`PROOF_NODEAD` would have meant porting the engine, the tables and support first. And it is the
largest LL(1) proof today.

| Part | Core | Today |
|---|---|---|
| meaning: parse tree, nullable, FIRST, FOLLOW, predict, LL(1), clash | 46 | about 220 in `SPEC.bend` (choice points, choices, bracket alternatives, paths) |
| small facts about lists, `reads`, the end step, the first token, `allIn` | 358 | spread over `PROOF_LL1`, `PROOF_ROUNDS`, `PROOF_SUBPARSE`, `FITS`, `LEMMAS` |
| the comparison of two forests and the law | 267 | 4,652 in `PROOF_UNAMBIGUOUS.bend`, generated |
| in all | 682 | 4,652 plus the shared files it imports |

Findings:
- About seven times smaller, and no generator: the comparison has two real cases (leaf, node)
  instead of one per pair of tree shapes, and a choice is always "which production".
- Writing the meaning with `reads` (fits *and* matches the input from a position, with
  positions as `steps` counts them) instead of `fits` plus slices of the input removed most of
  the position arithmetic. The core's other definitions should use it too.
- A negative check: dropping FOLLOW from `Predicts` makes the proof fail, as it must (a
  production that reads nothing is told apart only by what follows).
- Not included: the right-recursive translation and the transfer to the grammar as written
  (plan steps 1 and 6). Since step 1 there is no bijection theorem (the translation is the
  meaning); what remains is relating the two translations, which differ only in their loop
  shapes (section 5).
- The other LL(1) laws depend on the engine, the tables or support, so they will shrink less
  than this one. A revised estimate for the 14.8k of LL(1) proofs: 3–5k.

## 13. Questions raised on version 2 (2026-11-13)

**Is matching Swift the only reason for left recursion?** Yes, and since version 3 it applies
only to the translation the oracles use; the LL(1) laws use a right-recursive one (section 5).
Left and right recursion are both tree bijections. Left recursion makes the core's steps the same as Swift's loop steps (rounds
chained from the loop's start), so the step map is a renaming; with right recursion it would
also have to move positions. For the empty-round question (under the cycle-free rule an earlier
draft proposed, section 6) the direction only moved the leak: `{ τ }` is exact either way; for `< τ >`, left recursion lets an empty *first* round
through (`H(i,i) = G(i,i)`, then `H = H G`), right recursion (`H = G | G H`) forbids that one (a
repeated `H` over the same tokens) and lets an empty *last* round through instead.

**Without "skip" and "pick", would the nullable brackets be resolved differently?** Probably,
and more uniformly. Read plainly, `[ τ ]` is `( τ | ε )` and `< τ >` is `τ { τ }`. The extra trees
are then ordinary ambiguities over the same tokens, and the only difference between the rivals
is how much structure they give to reading nothing: the skip has one empty node, an empty pick
has two or more; `( )( a )( a )` has one more empty round than `( a )( a )`. One general rule
would cover both, and nothing else: *among the readings of a node over the same tokens, keep
those with the fewest empty nodes.* It is local (a same-span rule, like `@prefer`), keeps genuine
ambiguities (`S = A B` with nullable A and B over one token still has two readings, each with one
empty node), and replaces both special rules of section 5. Its cost: it also
silently decides between different alternatives that both read nothing
(`A = B | C`, `B = ε`, `C = D`, `D = ε`), which is arguably the same kind of non-choice, but the
trees differ. Decided 2026-11-13: today's two rules stay (section 5); they are easier to predict
from the grammar as written.

**Can GLL's trick for left recursion handle cyclic grammars?** Yes; it already does in the
parser, and the same trick (one fact per key, a least fixpoint) serves every algorithm that
reasons about trees. Section 6 now rests on it, and the cycle-free rule is dropped.

**Would it be simpler to allow annotations only at the start of an alternative?** For the spec,
no: on the core every annotation already sits on a production (guards, ranks) or on a
nonterminal (extent marks), because each bracket becomes a nonterminal of its own. Predicates
already stand only at an alternative's start. Extent marks cannot move there without changing
their meaning: they mark an occurrence in a sequence, not a choice. Restricting the surface
syntax would only simplify Swift's parser and Oracle (no bracket-level marks), at the cost of
naming a nonterminal for every marked bracket (`@longest { word }`).

# 

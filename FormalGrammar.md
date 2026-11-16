# Formal grammar: a layered specification

Version 3, 2026-11-13. A plan in progress: step 0 (measurements), step 1 (the core and the
translation) and step 2 (the parser, pruning and the exact set) are done, in `Bend/core/`, and
so are step 4 (all three phases) and step 5 (rule 2; rule 1 dropped).
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
| C3 | the extent oracle's stitched-reading check | refuses | to measure; algorithmic |
| C6 | a preference cycle | `PREFER.bend` refuses | not well-formed (rule 2); the core oracle answers |
| C7 | certificate searches (`Witness.solve`) | unknown verdicts | fixpoint search; finite trees help |
| D | outside the spec (lexical ambiguity, layout gates, an extent on a terminal) | not exported | the same |

The inventory was compiled from the oracles' comments; step 6 checks it is complete (every
site that returns nothing, classified).

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
   - Support and `predict_saves_work` are done (`SUPPORT.bend` 327, `PROOF_SUPPORT.bend` 580
     lines; today `SUPPORT.bend` 255, `PROOF_SUPPORT.bend` 2,212 and `PROOF_SAVES.bend` 685).
     One induction over the reached facts with a goal given as data; the goal "in a closed
     plain state" gives the law. A negative check: rules that resume without the need check
     make the proof fail.
   - Left: `ll1_no_dead_wood`, as a second goal ("on the parse tree") for the same induction.
     No generator is needed so far.
7. **The inventory, complete**, and the algorithmic refusals (C3, C7).
8. **The twin answers.** On a well-formed grammar, with enough fuel, each oracle hands out a
   set (TODO.md, "Bend twin: answers"). This closes the escape hatch of section 1; its argument
   is GLL's own (a finite set of keys that only grows, section 6).

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

# 14. next steps
Grammar transformations towards LL(1) while preserving semantics.
Reading assignments (from Grok)


Rewriting CFGs to LL1 grammars and non-rewritable constructs
is it possible to rewrite every CFG grammar in LL(1) form, and if not which grammar constructs are not rewriteable?  Be very precise

Thought for 30s
No. Not every CFG can be rewritten as an equivalent LL(1) grammar (one generating exactly the same language).

Precise reasons
LL(1) languages form a proper subset of the deterministic context-free languages (DCFLs), which in turn are a proper subset of the context-free languages. Consequently:

There exist CFLs that are not LL(k) for any finite k.
There exist DCFLs (hence LR(1) languages) that are not LL(k) for any k.
LL(1) grammars are always unambiguous, so any inherently ambiguous CFL has no LL(1) grammar.
Canonical non-LL constructs / languages
The classic example (due to Rosenkrantz & Stearns and widely repeated in the literature) is

L
=
{
a
i
b
j
∣
i
≥
j
≥
0
}
.
L={a 
i
 b 
j
 ∣i≥j≥0}.
This language is deterministic (it has a simple SLR(1)/LR(1) grammar) but is not LL(k) for any k. A top-down parser must, on seeing an 
a
a, decide whether that 
a
a will later be matched by a 
b
b or is an “extra” unmatched 
a
a. With only a fixed amount of lookahead consisting of further 
a
as, the decision cannot always be made correctly.

The classic “dangling-else” / optional-else construct is essentially isomorphic to the same language (the number of if-then must be 
≥
≥ the number of elses) and likewise admits no LL(k) grammar, although it has an unambiguous LR(1) grammar.

Another simple unambiguous but non-LL(k) language is generated by

S → A | B
A → a A b | ε
B → a B bb | ε
What can be rewritten, and what cannot
The two standard local transformations

elimination of left recursion (direct and indirect), and
left factoring (elimination of common prefixes)
are necessary for a grammar to be LL(1), but they are not sufficient. After performing them one may still have FIRST/FOLLOW conflicts that are intrinsic to the language rather than to the particular grammar. There is no general algorithm that converts an arbitrary CFG into an equivalent LL(1) grammar, because it is undecidable whether a given CFG generates an LL(k) language for some k.

In short:

Left recursion and common prefixes are “rewriteable” (they can be removed while preserving the language).
Inherent ambiguity, the 
a
i
b
j
a 
i
 b 
j
  (
i
≥
j
i≥j) pattern, and the dangling-else pattern are not rewriteable into LL(1) form.
Even when the language is LL(1), a given grammar for it may require non-trivial restructuring beyond the two classical transformations, and the original derivation structure is not always preservable.





53 sources
Thank you but that is not what I wanted to know, let me rephrase.  Given a CFG we can apply transforms to make the grammar 'almost' LL(1) -- I am specifying LL(1), not LL(k) -- but for a few remaining constructs that are never going to be tranformable.  You've mentioned the aibj pattern as an example.  What is the exhuative list of grammar constructions that cannot be transformed.

Thought for 24s
There is no exhaustive finite list of local syntactic “constructions” that are forever non-transformable into LL(1).

After the two standard, language-preserving rewrites

elimination of left recursion (immediate and indirect), and
left factoring
a grammar is still not LL(1) precisely when it still contains at least one residual FIRST/FOLLOW conflict:

two alternatives 
A
→
α
∣
β
A→α∣β with 
FIRST
⁡
(
α
)
∩
FIRST
⁡
(
β
)
≠
∅
FIRST(α)∩FIRST(β)=∅, or
a nullable alternative whose FIRST set intersects 
FOLLOW
⁡
(
A
)
FOLLOW(A).
These residual conflicts cannot be removed by any further local rewriting exactly when the language generated by the grammar is not an LL(1) language. Because it is undecidable whether an arbitrary CFG generates an LL(1) language (Rosenkrantz & Stearns, 1970), there cannot exist a complete, effective catalogue of “bad constructs.”

The known infinite families that survive the standard transformations are:

Inherently ambiguous languages
Any grammar for them remains ambiguous; LL(1) grammars are always unambiguous.
Languages of the form 
{
a
i
b
j
∣
i
≥
j
}
{a 
i
 b 
j
 ∣i≥j} and its close relatives
(including the classic dangling-else / optional-else construct).
These are deterministic (LR(1)) yet not LL(
k
k) for any 
k
k. After left-recursion elimination and left factoring one still obtains a nullable non-terminal whose FIRST and FOLLOW sets intersect, and no further local rewrite eliminates the conflict.
Languages that require distinguishing two alternatives after an unbounded common prefix of identical symbols
Classic example:

S → A | B
A → a A b | ε
B → a B bb | ε
The grammar is unambiguous, left-recursion-free and left-factored, yet the two alternatives for 
S
S have identical FIRST sets; the conflict is intrinsic.

In short, once left recursion and common prefixes have been eliminated, the only remaining non-transformable phenomena are residual FIRST/FOLLOW conflicts that witness that the language itself is not LL(1). There is no deeper, finite list of local patterns.





46 sources
what is the main argument from Rosenkrantz for concluding that it's undecidable?

Thought for 27s
The main result is Theorem 11 of Rosenkrantz & Stearns (1970): it is undecidable whether there exists some 
k
k such that a given CFG is LL(
k
k).

The proof is by reduction from the halting problem. They construct, from an arbitrary Turing machine 
M
M, two special LL(3) grammars 
G
1
G 
1
​
  and 
G
2
G 
2
​
  whose languages encode sequences of instantaneous descriptions of 
M
M. They then form a third grammar 
G
3
G 
3
​
  that essentially takes the union of the productions of 
G
1
G 
1
​
  and 
G
2
G 
2
​
 . By the way the constructions are arranged,

G
3
 is LL
(
k
)
 for some 
k
⟺
M
 halts
.
G 
3
​
  is LL(k) for some k⟺M halts.
Because the halting problem is undecidable, it is undecidable whether an arbitrary CFG is LL(
k
k) for some 
k
k.

(A related result, their Theorem 13, shows that it is already undecidable whether a given CFG generates an LL(
k
k) language even when 
k
k is fixed.)

Thus the undecidability rests on a direct reduction from the classic undecidable problem of Turing-machine halting, via a careful encoding of computations into the conflict structure of an LL grammar.





56 sources
OK.  So it's undecidable, but my question was an engineering question, not a logic question.  Given a grammar and after transformations to "make it more LL(1)", what set of non-LL(1) grammar constructs are we left with.  As you mentioned, elimination of left-recursion and left-factoring are two methods that 'move' a grammar into the direction of LL(1).  Two questions:  besides these two, which other ones are there?  And: which patterns are not transformable, and here I am looking for more of a taxonomy than general statement about first/follow overlap

Thought for 29s
Engineering answer (practical taxonomy)

Other useful transformations (beyond left-recursion elimination & left factoring)
These are the additional rewrites that practitioners actually apply when trying to push a grammar toward LL(1):

Substitution / nonterminal expansion (inlining)
Replace a leftmost nonterminal by its productions. This exposes hidden common prefixes or FIRST/FOLLOW conflicts that left factoring alone cannot see.
(Especially useful after left-recursion elimination.)
Unit-production elimination + removal of useless/unreachable symbols
Cleaning step that often makes subsequent factoring and substitution more effective.
Layering for precedence and associativity
Split a single expression nonterminal into a hierarchy (Expr → Term → Factor …). This both removes ambiguity and creates the classic right-recursive form that left-recursion elimination turns into LL(1).
Relocation of ε-productions into “tail” nonterminals
After left-recursion elimination you already have tails; further manual refactoring keeps nullable alternatives only on the tails so that FIRST/FOLLOW conflicts become local and sometimes disappear.
Disambiguation by restructuring
Classic example: the dangling-else is rewritten with “closed statement” / “open statement” nonterminals. This removes ambiguity but frequently leaves a residual FIRST/FOLLOW conflict; it is therefore only a partial win for pure LL(1).
These five, together with the two classical ones, constitute essentially the complete practical toolkit. None of them is a general algorithm that always succeeds.

Taxonomy of residual non-transformable patterns
(after the transformations above have been applied)

The remaining obstacles fall into three concrete, recurring families:

Family	Characteristic pattern	Why it survives	Typical example
Nullable self-conflict	A nullable nonterminal 
A
A whose FIRST set intersects its own FOLLOW set, and the conflict cannot be moved away by further substitution or factoring	The decision “consume the next token now or stop” depends on information that has not yet been seen	Dangling-else after left factoring; the language 
{
a
i
b
j
∣
i
≥
j
}
{a 
i
 b 
j
 ∣i≥j}
Unbounded identical-prefix discrimination	Two (or more) alternatives that share arbitrarily long identical prefixes of the same terminal symbols before they diverge	Finite left factoring only peels off a fixed-length prefix; the distinguishing information can be arbitrarily far to the right	S → A | B
A → aAb | ε
B → aBbb | ε
Intrinsic ambiguity that rewriting cannot remove	Multiple leftmost derivations for the same string that cannot be eliminated by any of the language-preserving local rewrites above	LL(1) grammars are always unambiguous; if the language is inherently ambiguous, or the grammar encodes an associativity/precedence ambiguity that layering does not capture, the conflict remains	Classic inherently ambiguous languages; certain operator grammars that have not been fully layered
Practical observation
After left-recursion elimination, left factoring, substitution, and the other rewrites listed above, virtually every remaining conflict you will meet in real grammars belongs to one of the three families in the table. The first two families are the ones that appear most often in programming-language work; the third is rarer once precedence layering has been done carefully.

There is no deeper finite catalogue of local syntactic shapes—these three cover the residual cases that the standard engineering transformations cannot eliminate.





33 sources
This statement is way to fuzzy for me "virtually every remaining conflict you will meet in real grammars belongs to one of the three families"

I would like to study the academic state-of-the-art of grammar hacking in this area

Thought for 13s
Academic state of the art on “grammar hacking” toward LL(1)

The literature that treats this rigorously is the theory of grammatical covers, developed mainly by Anton Nijholt (late 1970s–early 1980s) and building on Gray & Harrison (1972). A cover is a stronger relation than mere language equivalence: the parse trees (or leftmost/rightmost derivations) of the transformed grammar are related to those of the original by a simple homomorphism. This is exactly the formal counterpart of “the transformation is useful for parsing.”

Core classical results
Result	Source	What it gives you
Every cycle-free CFG is left-to-left-corner covered by a non-left-recursive grammar	Nijholt (1976/77)	Generalises ordinary left-recursion elimination while preserving parse structure
Every LL-regular grammar can be transformed into an LL(1) grammar that covers it	Nijholt (1982), RAIRO Inform. Théor.	The strongest pure-LL transformation known; any LL(k) grammar is LL-regular, so this applies to all of them
Predictive LR(k) grammars (a proper superclass of LC(k)) transform into LL(k) grammars that left-to-right cover them	Soisalon-Soininen & Ukkonen (1979)	Gives a systematic route from a useful subclass of bottom-up grammars into top-down form
Normal-form covers for LL(k), strict deterministic and LR(k) grammars	Nijholt, Context-Free Grammars: Covers, Normal Forms, and Parsing (LNCS 93, 1980)	The standard monograph; Chapters 8–10 and 12 are the definitive treatment
These results show that left-recursion elimination and left factoring are special cases of more general, structure-preserving transformations studied in the cover literature. The transformations are algorithmic for the classes above, but the classes themselves are proper subsets of the deterministic context-free languages.

What remains non-transformable (precise characterisation)
After all cover-preserving transformations have been applied, a residual conflict exists precisely when the language is not LL(1). The known infinite families that survive every such transformation are still exactly the ones already identified:

languages requiring unbounded lookahead of the form 
{
a
i
b
j
∣
i
≥
j
}
{a 
i
 b 
j
 ∣i≥j} (and the dangling-else construct isomorphic to it),
languages whose alternatives share arbitrarily long identical prefixes before diverging (the classic 
A
→
a
A
b
∣
ε
A→aAb∣ε vs. 
B
→
a
B
b
b
∣
ε
B→aBbb∣ε),
inherently ambiguous languages.
No finer syntactic taxonomy of residual “local patterns” exists beyond these families, because the property “is the language LL(1)?” is already undecidable (Rosenkrantz & Stearns, Theorem 13).

Modern (2020s) work
Bilyk (Onward! 2025): semantics-preserving transformation of CFGs into LL(1) form using a typed-tree representation so that the original semantic actions are retained.
GramTrans (2025): hierarchical conflict-elimination algorithm that produces an LL(1) representation together with translators between the original and the new grammar, with an explicit trade-off between syntactic simplicity and token length.
These are engineering-oriented refinements of the classical cover idea; they do not enlarge the class of languages that can be made LL(1).

Bottom line for study
Start with Nijholt’s 1980 monograph (especially the chapters on deterministically parsable grammars and the survey of parsing strategies). Then read the 1982 LL-regular → LL(1) paper and the 1979 predictive-LR paper. That is the academic core of “grammar hacking” toward LL(1). Everything practical that is known reduces to special cases or applications of those results.

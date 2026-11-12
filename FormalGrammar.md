# Formal grammar: a layered specification

Version 2, 2026-11-11. A draft plan; nothing in it is implemented yet. Version 1 (the same
day) proposed well-formedness rules on today's specification; version 2 puts them on a
smaller core. Section 11 lists the changes.

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
  proofs (3.6k lines), and paths and their prefixes run through all 49k proof lines.

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
- **Bijections, not language equivalence.** The twin is about trees (the Oracle chooses among
  them; the tests compare tree steps). A translation between layers must map trees one to one,
  not merely keep the language.

## 3. The layers

| Layer | What it adds | Trees | Proved on it |
|---|---|---|---|
| L0, BNF core | productions `A = x1 … xn` over terminals and nonterminals; n = 0 is ε | leaf, node | the parsers, pruning, the oracles, every law |
| L1, EBNF | `( )`, `[ ]`, `{ }`, `< >`, ε as an item | today's seven shapes | one theorem: the translation to L0 is a tree bijection |
| L2, annotations | guards, ranks, extent marks | — | their meaning is defined on L0 |
| L3, well-formed | the rules of sections 7 and 8 | — | a hypothesis of every law |

Chomsky normal form was considered and rejected as the core: ε-removal and unit-rule removal
merge distinct trees (a cyclic grammar has infinitely many trees and its normal form finitely
many), and they destroy the alternatives and sequences the annotations are attached to. Its
useful half, binary steps, the core has already: a BSR step `(X = α · β, i, k, j)` is the
intermediate node for the prefix α.

## 4. L0: the BNF core

    Sym        = Terminal{kind} | Nonterminal{id}
    Production = Production{lhs, rhs: List<Sym>}
    Tree       = Leaf{kind} | Node{production, children}
    Slot       = Slot{production, dot}           -- no path
    Bsr        = Bsr{slot, i, k, j}

`fits`, `leaves`, `walk`/`steps` lose five of their seven cases; `pathEq`, prefixes and the
`seqAt`/`rpath` machinery disappear. Every proof that walks a tree has two cases.

## 5. L1: EBNF as a translation

Each bracket occurrence gets a fresh nonterminal of its own; each of its alternatives becomes
one production:

    ( τ1 | … | τn )   →  H = τ1 | … | τn
    [ τ1 | … | τn ]   →  H = ε | τ1 | … | τn
    { τ }             →  H = ε | H G,   G = ( τ )
    < τ >             →  H = G | H G,   G = ( τ )
    ε (an item)       →  E = ε

**Loops are left-recursive.** Swift's engine records a loop as Scott and Johnstone do: each
round runs the body from the loop's start, so later rounds chain on to earlier ones
(`SPEC.bend`, `walk`). The left-recursive translation has exactly those steps:
`H = H · G` over `(i, k, j)` is the round's link step from the loop's start i over a round from
k to j. A right-recursive translation would record different positions.

**The bijection.** A pick is a node of its bracket's H; a loop with rounds r1 … rn is the chain
of H nodes with children r1 … rn; a skip is a node of H's (or E's) empty production. The
theorem: a forest fits an L1 sequence and spells w exactly when its translation fits the
translated sequence and spells w, and the translation is one to one on forests.

**The step map.** Swift's yields use L1 slots (production, path); the twin's steps use L0
slots (production, dot) of the translated grammar. The map between them is fixed and
mechanical (a bracket's path prefix names its H; a round's link step is H's `H · G` step).
It is the one place where the two layers meet in the tests, and it is a function in the spec,
not in Swift.

**What goes away with it.**
- The oracles' loop limitations (version 1's open item, refusals C2, C4, C5): a round is an
  ordinary node of G with its own start.
- The rewriting laws (one unfold/fold pair per bracket kind) become one theorem.

**Open: the optional's pick.** Today `[ τ ]` over nothing is only a skip; its pick must read
something. The translation `H = ε | τ` gives two trees when τ can read nothing. Either the
translation keeps that rule (section 6 may cover it), or the ambiguity is left to the
annotations, as for any other grammar. To decide on the merits.

## 6. Cycle-free trees

**Rule.** A parse tree has no node with an ancestor of the same symbol over the same tokens.

**Why.** Such a node only says "the same again": `A ⇒ … ⇒ A` over the same tokens. Without the
rule a cyclic grammar has infinitely many trees, and every algorithm that lists or certifies
trees must bound itself somehow (the witness search on `BendDifferential` seed 86 did, and
missed trees). With it the trees of an input are finite. The rule is general and pure; it is
the standard notion of a cycle-free derivation.

**What it replaces** (to be confirmed in step 3 of the plan):
- *The rule on empty rounds* (`roundsOk`), almost. Under the left-recursive translation an
  empty round after another round, or an empty first round of `{ τ }`, is a node `H` with a
  child `H` over the same tokens, which the rule forbids; the one empty round of `< τ >` over
  nothing is `H = G` with no repetition, which it allows. One shape slips through: an empty
  *first* round of `< τ >` followed by rounds that read something (`H(i,i) = G(i,i)`, then
  `H(i,j) = H(i,i) G(i,j)`; no node repeats). Today's rule forbids it ("the rounds of `< τ >`
  all consume, or there is just one"). So either the positive loop keeps a rule of its own, or
  that extra reading is accepted as an ordinary ambiguity (it only arises when τ can read
  nothing). To decide on the merits, together with the optional's pick (section 5).
- *The rival-cycle condition* of `@prefer`/`@avoid` (`above`, `revisits` in `SPEC.bend`,
  about 700 mentions in the proofs). A rival is judged in the place of the node it competes
  with; a rival that comes back over the same tokens to that node's nonterminal, or to a node
  above it, makes the tree in place cyclic. Requiring the tree in place to be cycle-free is
  that condition.
- *Version 1's rule 2* (no preference cycle) may then be unnecessary: the meaning is
  well-defined without it, because a cyclic rival is no tree. Whether a grammar with such a
  cycle still deserves a warning is a separate, tool-level question.

## 7. L2: annotations on the core

Every annotation sits on a production or on a nonterminal of the core:

| Today (L1) | On the core (L0) |
|---|---|
| guard on a production (`ProdGuard`) or a bracket alternative (`AltGuard`) | on a production |
| rank on a production (`ProdMark`) or a bracket alternative (`AltMark`) | on a production |
| extent on a nonterminal (`NtExtent`) or a bracket (`BrackExtent`) | on a nonterminal; a bracket's H has one reference, so marking H marks that one occurrence |

So each kind of annotation has one form, without a separate unification step. The meanings
(admissible, unbeaten, selected) are defined once, on nodes and their sequences, with two-case
walks.

## 8. L3: one extent mark per sequence

**Rule.** No sequence (the right side of a production) has more than one item marked
`@longest` or `@shortest`. A mark on a nonterminal marks every reference to it, so a sequence
that refers to a marked nonterminal twice has two marked items. On L1 this reads: no sequence
of the grammar as written, nor any alternative of a bracket, has two marked items.

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

    # ONE EXTENT MARK PER SEQUENCE. No right side has more than one item with @longest
    # or @shortest. Two marked items would compete for the same tokens; a group says
    # which one decides first: `@longest A ( B @longest C )` lets A decide, then C among
    # what A left, and `( A @longest B ) @longest C` lets C decide first.
    def oneMarkPerSequence(+grammar: +List<Production>, +marks: +List<ExtentMark>) -> Bool

    # A well-formed grammar keeps every rule of this section. The laws speak about
    # well-formed grammars only.
    def wellFormed(+grammar: +List<Production>, +marks: +List<ExtentMark>) -> Bool

**Consequences.** `ExtentBest` compares one length; `beats` goes. Swift: a load error whose
message shows the group form; `YieldGraph.extent(rank:)` back to one pass;
`documentation/Ambiguity.md`, "Several marks in one sequence", rewritten from "first come,
first served" to "why this is not allowed, and how to write it".

## 9. What is refused, after the plan

| | Kind | Today | After |
|---|---|---|---|
| A | resource limits (fuel, time) | reported as no answer | the same, with a reason; rarer, since trees are finite (section 6) |
| B | checks of untrusted parts | a failure is a bug | the same |
| C1 | several marks in one sequence | `EXTENT.bend` refuses | not well-formed (section 8) |
| C2, C4, C5 | loop limitations of the oracles | refused | gone: a round is a node (section 5) |
| C3 | the extent oracle's stitched-reading check | refuses | to measure; algorithmic |
| C6 | a preference cycle | `PREFER.bend` refuses | gone or a warning (section 6) |
| C7 | certificate searches (`Witness.solve`) | unknown verdicts | fixpoint search; finite trees help |
| D | outside the spec (lexical ambiguity, layout gates, an extent on a terminal) | not exported | the same |

The inventory was compiled from the oracles' comments; step 6 checks it is complete (every
site that returns nothing, classified).

## 10. Plan

0. **Measure first.** In a scratch copy: the L0 types, `fits`, `leaves`, `walk`, `steps`, and
   the two walks of one phase (phase 1, `GUARD`), with the walk written once as a template
   over a per-step verdict. Compare its size with today's. Section 12 records the result.
1. **L0 and L1.** The core types and definitions; the translation; the bijection theorem; the
   step map. The rewriting laws are restated as consequences.
2. **The engine on L0.** `GLL.bend`, pruning and the witness search on the core (two-case
   trees); their laws restated.
3. **Cycle-free trees.** The rule of section 6; check that it reproduces `roundsOk` and the
   rival-cycle condition; decide version 1's rule 2.
4. **L2 on the core.** The three phases defined on L0, each proved with the one template walk.
5. **L3.** `wellFormed`; Swift's loader agrees (a test on the fuzz grammars, which keep
   generating every form); the extent changes of section 8.
6. **The inventory, complete**, and the algorithmic refusals (C3, C7).

Each step ends with the proof gate (`bend PROOF.bend --verdict`), the examples, `BendCheck` and
a 200-seed `BendDifferential` run. Steps 1–4 replace files rather than edit them; today's files
stay until their replacements check.

## 11. Changes from version 1

- The core is BNF (L0) with EBNF as a tree bijection (L1), instead of rules on today's EBNF spec.
- Loops are translated left-recursively, to match Swift's round steps.
- The loop limitations (C2, C4, C5) are resolved by the core, not left open.
- Cycle-free trees (section 6) are new; they may replace `roundsOk`, the rival-cycle condition
  and version 1's rule 2.
- The unified addressing of annotations, dropped in version 1 as cosmetic, now comes for free.

## 12. Measurement (step 0, 2026-11-11)

A draft of the core and the generic walk, checked by the kernel (`ALL PROOFS CHECK`), kept
outside `Bend/` (in `documentation/drafts/CORE_L0_measurement.bend`):

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

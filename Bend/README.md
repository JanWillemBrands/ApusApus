# Apus in Bend

A formally checked specification of EBNF parsing, with a GLL parser whose output
is checked against it. Written in [Bend 2](<Bend Guide.md>).

## What to read

Only two files are trusted. Everything else is either checked by the machine or
there for intuition.

| File | What it is | Read? |
|---|---|---|
| `SPEC.bend` | What parsing means: grammars (EBNF right sides with `( ) [ ] { } < >`), parse trees, `fits`, `leaves`, the steps of a tree as BSR elements, exact BSR sets, and which trees `@prefer` and `@avoid` select; at the end, derived notions (nullable, FIRST, FOLLOW, predict, choice points, LL(1)) used only by the LL(1) laws | **yes** |
| `LAWS.bend` | Every claim, nothing else | **yes** |
| `EXAMPLES.bend` | The paper's examples, the engine on them, the check catching broken states | for intuition |
| `GLL.bend` | The GLL engine, after tinyGLL and ApusApus, plain or with prediction (Scott's predict sets) | optional: not trusted |
| `FIRST.bend` | The nullable, FIRST and FOLLOW tables prediction reads, and their closedness check | optional: not trusted |
| `CHECK.bend` | The closedness check on the engine's final state, and `checkedSteps`; with prediction, `predictedSteps` | optional |
| `PRUNE.bend` | The round rule on link steps, and pruning to the steps a parse tree needs, with its closedness check | optional |
| `WITNESS.bend` | A search for parse trees built from the kept steps | optional: not trusted |
| `EXACT.bend` | The exact parser `exactSteps`: pruned steps, handed out only when witness trees cover them all | optional |
| `GUARD.bend` | The guard oracle `guardSteps` (phase 1): the exact set without the steps of nodes that break a lookahead, `@left` or `@right` rule, every answer checked | optional |
| `EXTENT.bend` | The joined extent oracle `extentSteps` (phase 3 on top of phases 1 and 2): the preference oracle's set, pruned from below, without the steps on no best reading; best lengths come with certificates from the set, and a self-check rules out stitched readings | optional |
| `UNBEATEN.bend` | The joined preference oracle `unbeatenSteps` (phase 2 on top of phase 1): the guard oracle's set without the steps of choices outranked by an admissible rival | optional |
| `PREFER.bend` | The preference oracle `preferSteps`: the exact set without the steps of outranked choices, each removal with a checked certificate | optional |
| `COMPARE.bend` | Sets Swift Apus's BSR yields next to the exact set, or after `@prefer`/`@avoid` next to the steps of the unbeaten trees: what is missing, what is dead wood | optional |
| `swift/` | Cases exported from Swift Apus by `ApusApusTests/BendExport.swift`; generated | run |
| `PROOF.bend` | The gate | run, don't read |
| `PROOF_TREES.bend` | Proofs of the rewriting laws | no |
| `PROOF_GLL.bend` | Proof that the checked parser misses nothing, plain and with prediction | no |
| `PROOF_PRED.bend` | What the walk needs from prediction: admitted descriptors, and what may come after a sequence | no |
| `PROOF_ADMIT.bend` | A parse tree's descriptor is admitted; the FOLLOW check carried into a slot and a bracket | no |
| `PROOF_TABLES.bend` | Closed tables are sound: a forest that reads nothing makes its items nullable, its first token is in FIRST | no |
| `PROOF_SETS.bend` | Facts about lookahead sets: union, subset | no |
| `PROOF_SAVES.bend` | Proof that a supported state is within a closed plain one | no |
| `PROOF_LL1.bend` | Proof that no conflict by the tables means LL(1) | no |
| `PROOF_UNAMBIGUOUS.bend` | Proof that an LL(1) grammar is unambiguous (generated case code) | no |
| `PSUPPORT.bend` | Support with prediction, and the checked LL(1) parser `llSteps` | optional: not trusted |
| `PROOF_NODEAD.bend` | No dead wood for grammars without brackets (first stage, used by PROOF_NODEAD2) | no |
| `PROOF_NODEAD2.bend` | Proof that the checked LL(1) parser has no dead wood: `ll1_no_dead_wood` | no |
| `PROOF_LL1AT.bend` | Proof that LL(1) at one choice point decides the choice there: `ll1_at` | no |
| `gen/` | Generators of the long proofs (PROOF_TABLES, PROOF_LL1, PROOF_UNAMBIGUOUS, PROOF_NODEAD, PROOF_NODEAD2, PROOF_LL1AT): change them there and rebuild; `python3 gen/build.py --check-all` (gen/README.md) | no |
| `LL_EX.bend` | `llSteps` against the exact set on the examples | optional: not trusted |
| `PREDICT_EX.bend` | Prediction on the examples: facts of the plain and predicting engines, and their sets | run |
| `SUPPORT.bend` | Is a state supported: every fact derivable from the root by the engine's rules, within the state | optional: not trusted |
| `LL1.bend` | LL(1) by the tables: the conflicts at every choice point, read from FIRST.bend's tables | optional: not trusted |
| `COST.bend` | What a parse costs: descriptors (work), steps (memory), lexer questions (a lexer answering on demand) | a measure, not a claim |
| `COST_EX.bend` | The cost of the plain and predicting parser on the examples and the `swift/` cases, with the counts left out | run |
| `PROOF_ROUNDS.bend` | Proof that the round rule keeps every step of every parse tree | no |
| `PROOF_PRUNE.bend` | Proof that pruning keeps every step of every parse tree | no |
| `PROOF_EXACT.bend` | Proof that the exact parser's set is exact | no |
| `PROOF_SPELL.bend` | Proof that trees built from the exact set spell the input | no |
| `PROOF_GUARD.bend` | Proof that the guard oracle's set embeds exactly the admissible trees | no |
| `PROOF_PREFER.bend` | Proof that the joined preference oracle's set embeds exactly the admissible unbeaten trees | no |
| `PROOF_SUPPORT.bend` | Proof that a no from the admissible sub-parse leaves no admissible rival in place | no |
| `PROOF_SUBPARSE.bend` | What a sub-parse and the exact set say about trees; shared by the oracle proofs | no |
| `PROOF_EXTENT.bend` | Proof that the joined extent oracle's set embeds exactly the selected trees | no |
| `PROOF_PLUG.bend` | Plugging: a forest swapped into a tree, where it fits, reads the same tokens and keeps phases 1 and 2, leaves the tree unbeaten, and its steps are the tree's | no |
| `FITS.bend` | Facts about `fits`: of a list, of its head and tail, of a join | no |
| `LEMMAS.bend` | Facts about Bool, Nat and lists | no |
| `core/` | Work in progress: the specification on a BNF core, as planned in `FormalGrammar.md` (core/README.md); not in the gate yet | optional |
| `bnf/` | The earlier BNF specification with a proven CYK parser, frozen | history |

## How to check

```
bend PROOF.bend             # ALL PROOFS CHECK when every law holds
bend PROOF.bend --verdict   # the same, with the Lean-proven kernel
bend EXAMPLES.bend          # the examples
bend bnf/PROOF.bend         # the frozen BNF and CYK work
bend swift/split.bend       # one Swift Apus case against the exact set
```

## Checking Swift Apus

`ApusApusTests/BendExport.swift` translates a grammar, its tokens and Swift's BSR
yields into a Bend file. Swift's extra completion yields `(lhs, i, i, j)` are left
out, as in `SPEC.bend`. It refuses a case rather than guess: for example
boundaries, lookaround, an alternate with no item at all, ambiguous lexing or a
rejected input. Running such a file gives a report from `COMPARE.bend`:

| Report | Meaning |
|---|---|
| `Agree{n}` | Swift has exactly the n steps of the parse trees |
| `Differ{e, s, missing, extra}` | `missing`: parse-tree steps Swift lacks; `extra`: Swift steps in no parse tree (dead wood) |
| `NoAnswer{}` | the exact parser ran out of fuel or a check failed |

The trust is in `gll_bsr_exact`: the set Swift is compared with is proven to be
exactly the steps of the parse trees.

Two opt-in suites use it (set the variable in the test plan, or as
`TEST_RUNNER_<name>` via xcodebuild):

| Suite | Variable | What it does |
|---|---|---|
| Bend check | `APUS_BEND=1` (or the path to `bend`) | runs Bend on every accepted message of the `TestCase` tables in `CoreGrammarTests`, plus the cases below; fails when Swift misses a parse-tree step; a second test does the same after the Oracle, and a third compares grammars with `@prefer`/`@avoid`, and a fourth grammars with `>?>`/`>!>`/`@left`/`@right` (below); attaches a report per case, and the Bend file of every difference |
| Bend export | `APUS_EXPORT_BEND=<path to Bend/swift>` | writes a few cases to `swift/`, to run by hand |

Results (2026-10-27), 341 accepted messages:

| | Messages |
|---|---|
| agree exactly | 202 |
| differ: dead wood only | 137 |
| refused | 2 (one grammar with two lexings) |
| missing steps | 0 |
| no answer | 0 |

Of Swift's 1963 steps, 406 (21%) are dead wood. Since the bracket rule (below), this includes the empty rounds Swift records, such as the `[ τ ]` taken over nothing. The most is in ambiguous and
nested loops: for example 12 of 21 steps for `even brackets` on `aaaa`. A simple
case is `split` (`X = { "a" | "a" "a" }` on `aaa`). It has 4 dead-wood steps:
the loop ending at 0, 1 and 2, and a round `"a" "a"` started at 2 that can't
finish. Swift's one-token lookahead can't prune them, because the next token is
always an `a`.

### After the Oracle's phase 1

The Bend check also compares the yields after `Oracle.disambiguate()`. The test
grammars carry no annotations, so only phase 1 acts: it removes yields on no
complete derivation. Its contract, as its own comments state it:

1. the root still spans the input: it never removes the last parse;
2. it removes no parse step that consumes input;
3. it leaves no dead wood, also not at loops. (Until 2026-11-09 it kept every loop
   iteration end on purpose, for `@longest` to compare with, and the check allowed them;
   the Oracle's graph rewrite dropped that, and since 2026-11-10 the check allows nothing.)

Results (2026-11-10), the same 341 messages, of which the exporter refuses 2:

| | Raw yields | After phase 1 |
|---|---|---|
| agree exactly | 207 | 339 |
| dead wood | 132 messages | 0 |
| missing steps | 0 | 0 |
| parse lost | 0 | 0 |

The check found three bugs in phase 1, each fixed, each with a regression test in
`OracleDisambiguationTests`:

- **A zero-width `< >` lost its parse** (`S = < "x" | "" >` on the empty input).
  Phase 1 treated it like a `{ }`, as the skip, but a `< >` has no skip: over an
  empty span it is one empty round. Fixed in `YieldNavigator.endPositions` and in
  `visitBracket`. Test: "zero-width < … > keeps its one empty round".
- **An `""` inside a longer body lost its parse** (`S = "a" ""` on `a`). The walk
  tiled alternates without their EPS symbols, so their yields were never marked,
  and the sweep deleted them. Fixed in `visitAlternates`. Test: "EPS inside a
  longer body keeps its parse".
- **A zero-width `[ ]` kept dead wood**. Over nothing a `[ ]` is the skip, so
  `visitBracket` no longer walks its round.

### After `@prefer` and `@avoid`

A third test runs 20 grammars with `@prefer`/`@avoid`, from `OracleDisambiguationTests`,
through Swift's Oracle and compares the yields with the steps of the unbeaten trees
(`COMPARE.bend`, `preferReport`: the witness trees of the preference oracle's set that
use only its steps).

Results (2026-11-10), 28 messages: all agree exactly. No step of an unbeaten tree is
missing, and no step of an outranked choice survives.

### After lookahead, `@left` and `@right`

A fourth test runs 19 grammars with `>?>`/`>!>`/`@left`/`@right` through
Swift's Oracle and compares the yields with the steps of the admissible trees
(`COMPARE.bend`, `guardReport`). The cases cover bare and listed `@left`/`@right`, both
on productions and in groups, lookahead that removes every parse, ambiguous lookahead,
lookahead on a nonterminal GLL never predicts at that position, on one the parse did not
call at that position, and on one that derives by reading nothing. Swift answers the parse
predicates `>?>`/`>!>` in the parser, by probing the target (`documentation/Oracle.md` § 4),
so it means the language, as `Ahead`/`NotAhead` do.

Results (2026-11-10), all messages agree exactly. Where a rule removes every parse, Swift
and Bend both leave nothing.

## Design choices: where Swift Apus and the spec meet

Bare `@left`/`@right` means plain "derives", as `SPEC.bend` `EdgeOk` says (2026-11-10;
before, Swift Apus asked "derives admissibly, one level deep"). This makes Swift.apus forbid
the chain `f(1) {}⏎{}` that swift-syntax accepts (TODO.md, "Grammar rework for the Oracle").

`@longest`/`@shortest` are local for brackets and nonterminals alike, as `SPEC.bend`
`ExtentBest` says (2026-11-10; before, Swift Apus kept a marked nonterminal's best completion
per start, whatever enclosed it). Swift Apus and the spec now mean the same thing everywhere;
`documentation/Oracle.md` § 5 lists the remaining choices, which the spec makes too.

## What the laws promise

Every law about an algorithm says what an answer means: "whenever `exactSteps` hands out
a set, it holds exactly the steps of the parse trees", and likewise for the checked and
predicting parsers and the guard, preference and extent oracles. No law says that the
algorithm hands out an answer. An algorithm that always said "no answer" would keep every
law. So the proofs are proofs of partial correctness: what you get is right, but you may
get nothing.

An algorithm hands out nothing when it runs out of fuel, when a check of an untrusted
part fails (the GLL state is not closed, pruning's needs are not closed, the witness trees
do not cover the kept steps, a certificate is missing), or when an oracle refuses a
grammar it was not built for. Fuel bounds the depth of the recursion, not the total work,
so a run always ends but may take very long.

For the comparisons with Swift Apus this means: a case without an answer was not
compared. `BendCheck` and `BendDifferential` therefore fail such a case, so it cannot pass
unnoticed. Until 2026-11-10 the witness search listed every tree, which is exponential
and on a cyclic grammar incomplete (`BendDifferential` seed 86: no answer after minutes);
it now builds one tree per uncovered step from a least fixpoint. That an answer always
comes, with enough fuel, is not proven (TODO.md, "Bend twin: answers").

## What is proven

- **Rewriting laws**: each bracket means its usual BNF rewriting, without helper
  nonterminals. `{τ} η` derives what `η` or `(τ) {τ} η` derives, and so on.
- **The checked GLL parser misses nothing** (`gll_every_parse_step`): whenever
  `checkedSteps` hands out a set, every step of every parse tree of the input is
  in it.
- **The exact parser is exact** (`gll_bsr_exact`): whenever `exactSteps` hands out
  a set, it holds exactly the steps of the parse trees of the input. Nothing is
  missing, and there is no dead wood.
- **Trees from the exact set spell the input** (`exact_trees_spell`): a tree that
  fits, uses only steps of the exact set, and is as long as the input, spells the
  input. An oracle choosing from the set cannot produce a non-parse.
- **Lookahead, `@left` and `@right` keep exactly the admissible trees**
  (`guards_exact`, phase 1): whenever `guardSteps` hands out a set, a parse tree of
  the input uses only its steps exactly when every node, pick and round keeps the rules
  of the alternative it chose (`SPEC.bend`, `Admissible`). The oracle refuses rules on
  the alternatives of a loop.
- **`@longest` and `@shortest` keep exactly the selected trees** (`extent_exact`,
  phase 3 joined to phases 1 and 2): whenever `extentSteps` hands out a set, a parse tree
  of the input uses only its steps exactly when it is admissible, unbeaten, and no node,
  pick or round has a rival reading of the same children's tokens, kept by phases 1 and 2
  where it stands, whose marked item is longer (`@longest`) or shorter (`@shortest`)
  (`SPEC.bend`, `ExtentBest`, `Selected`). A longer reading that breaks a hard rule or is
  outranked beats nothing. The comparison is local, within the one sequence the
  mark sits in. The oracle refuses two marks in one sequence and a mark on the
  alternative of a loop. Its self-check (a kept step of a marked item, at each end of
  its sequence, either lies on no reading or has the best length there) rules out
  readings stitched together from different trees.
- **`@prefer` and `@avoid` choose exactly the unbeaten trees, among the admissible
  ones** (`prefer_avoid_exact`, phase 2 joined to phase 1): whenever `unbeatenSteps`
  hands out a set, a parse tree of the input uses only its steps exactly when it is
  admissible and no node of it is outranked by an admissible rival (`SPEC.bend`,
  `UnbeatenTree`). A preferred alternative that breaks a hard rule beats nothing. The
  set may keep steps inside a removed choice; they make no tree.
- **An answer leaves a reading** (`prefer_avoid_safe`): whenever `unbeatenSteps` hands
  out a set and the input has an admissible tree, some admissible tree is unbeaten. The proof
  builds it: it repairs any parse tree from the top, keeping each node the oracle kept
  and putting a removed node's certified rival in its place.
  Not proven: the same without the oracle's answer, that preferences never remove every
  parse tree. Its classical proof ("it is impossible that no tree is unbeaten") uses a
  hypothesis twice, which Bend's affine logic does not allow (`¬¬(P ∨ ¬P)` is not
  provable in Bend); it would need a verified recogniser instead.

- **Prediction misses nothing** (`predict_every_parse_step`): whenever the checked
  parser with prediction (`predictedSteps`) hands out a set, every step of every parse
  tree of the input is in it. A descriptor is started only where the token at its
  position can begin what follows it: FIRST of the rest of its sequence, and when that
  can be empty, what may follow the sequence (another round of a loop, the rest after a
  bracket, or FOLLOW of the production's nonterminal). The tables are computed in
  FIRST.bend and handed out only when closed. The proof is the one for plain GLL, with
  three more facts carried along the walk: where the current sequence ends, that the
  token there may follow it, and the FOLLOW check for it. Without prediction all three
  hold trivially, so `gll_every_parse_step` is the special case. On the examples the
  predicting parser starts 10–36% fewer descriptors; on an LL(1) expression grammar its
  steps are exactly the exact set.

- **Prediction saves work** (`predict_saves_work`): whenever the plain parser's final
  state is closed and the parser's final state in any mode is supported (every fact of
  it derivable from the root by the engine's rules, SUPPORT.bend), every fact of the
  second is in the first. So the predicting parser has no descriptor and no step the
  plain one lacks: by the cost below, it never does more work and never uses more memory.
  The proof grows the facts reached round by round and shows each round stays inside the
  closed state, because closed means the rules add nothing new. Lexer questions are not
  covered: prediction can ask more of them.

- **LL(1) by the tables is LL(1)** (`tables_ll1_sound`): when LL1.bend's check finds no
  conflict in closed tables, the grammar is LL(1) in SPEC.bend's exact sense: at no choice
  point can two different choices begin with the same next token. The proof walks a parse
  tree to show that wherever a sequence ends, the next token is in the tables' context for
  it; so the exact FIRST, FOLLOW and PREDICT sets lie inside the tables' sets. It then shows
  the check visits every choice point (every nonterminal, every bracket at any depth, and
  after a round of `< >`), or reports running out of nesting fuel. The converse fails on
  purpose: the tables may report a conflict that no sentence has.

- **An LL(1) grammar is unambiguous** (`ll1_unambiguous`): under SPEC.bend's `LL1`, any
  two parse trees of the same input are the same tree. `LL1` is a function, and Bend lets a
  proof call a function only once, so the proof first shows, without LL(1), that two parse
  trees of one input are equal or give a clash (`trees_same`): a choice point where the
  trees choose differently and both choices predict the token there (by FIRST when the
  chosen part reads something, else by nullable and FOLLOW, taken from the tree's own
  steps). The law then rules out the clash with one call of `LL1`.

- **No dead wood for LL(1)** (`ll1_no_dead_wood`): when
  the input is a sentence and the tables pass LL1.bend's check, the checked LL(1) parser
  (`llSteps` in PSUPPORT.bend: the predicting engine's state must be closed, and supported
  by the engine's rules with prediction) hands out exactly the steps of the parse tree. The
  proof fixes the tree and shows every fact grown from the root lies on it: only the tree's
  production gets past prediction at a cluster (another would be a conflict of the table
  check), and a pop matches every caller, since two nodes of one nonterminal at one position
  are the same (`compare` of PROOF_UNAMBIGUOUS, on one tree). PROOF_NODEAD.bend does this
  for grammars without brackets (its first stage, `ll1_no_dead_wood_bnf`, kept as a lemma);
  PROOF_NODEAD2.bend adds brackets: a round's descriptors are on the tree when the round is,
  and at a bracket only the tree's choice gets past prediction (entering, skipping, another
  round, leaving), else the table check would have found a conflict at its `BracketAt` or
  `AfterRoundAt`. Two callers of one bracket at one position have the same forest from
  there on, so a round's pop resumes only the tree's caller.

- **LL(1) at one choice point decides it** (`ll1_at`): where the grammar is LL(1) at one
  choice point (`LL1At` at that point only), two parse trees, of any inputs, that make a
  choice there at the same position with the same token next make the same choice. The
  choices a tree makes are listed by `choicesMade` at SPEC's end (a node, a Pick or Skip of
  `( )` `[ ]`, each round of a loop and stopping it; examples in EXAMPLES.bend). The proof
  (PROOF_LL1AT.bend) walks one tree and shows every choice it makes predicts the token where
  it is made, with the pieces of PROOF_UNAMBIGUOUS; then two different choices would break
  `LL1At`. So a parser may predict by one token at such a point even when the grammar is not
  LL(1) elsewhere.

## What a parse costs

`COST.bend` measures a run of the engine by three counts of distinct facts of its final
state, each one unit, none depending on the order the engine worked in. They follow Scott
and Johnstone's reporting: in the LCNP paper only the descriptor set |U| and the BSR set
|ϒ| ("an implementation independent measure of the work done by a GLL-style parser is the
number of descriptors created ... memory usage is dominated by the size of the output
derivation representation").

| Count | Measures | Bound | Ideal |
|---|---|---|---|
| `descriptors` | the work: one execution of the engine's outer loop each | | about the input length times the grammar size, for an LL(1) grammar |
| `steps` | the memory: the output BSR set | at least the exact set (the rest is dead wood) | the exact set |
| `lexerQuestions` | the lexer's work, for a lexer that answers on demand and remembers its answers: the distinct pairs (position, terminal) it is asked | at least one per position visited | one per position (a lexer that answers per position) |

A descriptor before a terminal asks about that terminal; with prediction, every candidate
descriptor also asks about each terminal of its predict set. The same count is the lex
cache's size in Swift Apus (about 65 questions per position on `Oracle.swift`).

Left out, after checking on the 32 runs of `COST_EX.bend` (16 cases, plain and
predicting) that they follow the descriptors: clusters (correlation 0.93), return edges
(0.93; 0.998 with clusters), pops (0.96), and candidates, Scott's "descriptor finds"
(0.98; at most 3 more than the descriptors without prediction). Steps also follow the
descriptors (0.97), since each is made with one, but stay as the memory and dead-wood
measure; lexer questions do not (0.81) and can grow with prediction (22 → 25 on the
expression grammar, while descriptors fall 70 → 45).

`COST_EX.bend` imports every case in `swift/`; after a re-export with other cases, update
its list.

## How the exact parser is built

None of the algorithms is trusted. Each one's output is checked, and the proofs are
about the checks:

1. `GLL.bend` parses; `CHECK.bend` checks that its final state is closed. A closed
   state misses no step of any parse tree.
2. The round rule (`PRUNE.bend`) removes the link steps of rounds that read nothing,
   unless the rule below allows them. A loop is written `{ ( τ ) }`, so a round's
   link step records the loop's start, the round's start and its end, and the rule
   needs nothing else. A parse tree's rounds all pass it.
3. `PRUNE.bend` keeps the steps a parse tree of the whole input needs, and checks
   that its needs are closed. Closed needs keep every step of every parse tree. A
   `[ ]` that reads nothing needs none of its alternatives: it is the skip.
   A round that starts after its loop's start needs the round before it to have
   ended there; the first round needs nothing, because a parse tree has no empty
   round before another one.
4. `WITNESS.bend` builds parse trees from the kept steps; `EXACT.bend` checks each
   one with `SPEC.bend`'s own `fits`, `leaves` and `steps`, and that together they
   cover every kept step. So every kept step is a step of a parse tree.

If a check fails, or an algorithm runs out of fuel, the parser hands out nothing.

## How the guard oracle works

`GUARD.bend` starts from the exact set and decides each rule from one step of the
node, because of how a sequence's steps are recorded: the last step has the node's
start i and its last child's span k..j, and the first step has the first child's span.
Lookahead depends only on the choice and i, `@left` on the choice and k..j, `@right`
on the choice and the first span. Two trees that share a step share these values, so
removing the step takes out the nodes that break a rule, and only those; no pruning
is needed. Every answer is checked: "N derives w" with a forest that `SPEC.bend`'s
`fits` and `leaves` accept, "N does not derive w" when the checked parser finds no
tree. A lookahead tries every prefix length of the rest of the input. Anything the
oracle can't decide makes it hand out nothing.

In the proof, a rule's Holds can be used only once (affine logic), while a node's own
steps are visited one by one. Each rule is decided by exactly one own step, so the
rules are split up front: the `@right` part goes to the first step, the rest to the
last.

## How the extent oracle works

`EXTENT.bend` runs on the preference oracle's set (phase 2), pruned from below as
UNBEATEN.bend prunes its sub-parses (a rule that fails at a node leaves the step above
it, and a chain through such a step is no reading). A sequence's readings are looked for
in the set itself: chains of its own steps from the start i to an end e. That is enough
because of plugging (PROOF_PLUG.bend): a rival reading that phases 1 and 2 keep where the
children stand takes their place in an unbeaten tree, so its steps are in the set. A best
length is used only with a certificate, a forest built from the set (WITNESS.bend) that
fits the items, spells the tokens, reads the marked item with that length, and whose
steps are all in the set; such a forest keeps phases 1 and 2 where it stands
(PROOF_GUARD's and PROOF_PREFER's walks), so it is a genuine rival. Without one the
oracle hands out nothing.

## How the preference oracle works

`UNBEATEN.bend` runs on the guard oracle's set (phase 1), with PREFER.bend's machinery
and one change in step 1 below: the sub-parse's steps are moved back to where they
stand in the input (shifted by the choice's start, the extra production's slots read
as the rival's own), judged there by the guard oracle with the whole input to look
ahead in, and pruned from below to the steps that what is kept supports (a loop that
is not trusted, and a closure check that is). A rival is found only when the end of
its sequence survives, so only admissible rivals count. Certificates are drawn from
the guard oracle's set, so a certified rival is admissible (PROOF_GUARD's walks).
What follows describes PREFER.bend, the unjoined original.

`PREFER.bend` starts from the exact set. A step that completes a choice (the end of a
production's right side, or of a bracket's alternative) reads the tokens from its i
to its j. For each sibling of higher rank:

1. **Keep** needs proof that the sibling cannot read those tokens. The checked GLL
   parser runs on just those tokens, with the sibling's items as one extra
   production. If its set has no end of that production over all of them,
   `gll_every_parse_step` says no tree exists, so no rival exists.
2. **Remove** needs a certificate from some sibling of higher rank, checked with
   `SPEC.bend`'s own definitions: a forest for the sibling over the same tokens, made
   of kept steps only, and a set C of nonterminals with no node in the forest over
   those tokens. (Kept steps only: then the forest can take the removed node's place in
   a tree of kept steps, which is how `prefer_avoid_safe` builds an unbeaten tree. Any
   sibling may give the certificate: the first one found may be outranked itself.) C holds every nonterminal that can be above
   the choice over the same tokens: it is grown from the choice's nonterminal along
   steps that start a sequence with a member of C, and checked to be closed. That is
   SPEC's rival, which may not go round a cycle back to a node above it.

Without a certificate, or when the parser runs out of fuel, the oracle hands out
nothing. That is the case for a grammar whose preferences go round a cycle (Swift
Apus refuses those too), and for a loop not written `{ ( τ ) }`, whose rounds the
steps cannot tell apart.

## Design choices in SPEC.bend

Some definitions in the spec are choices, not consequences. They were validated on
examples, not proven right; nothing could prove them right. The reasoning:

**The step convention** (which BSR elements a tree records), copied from Swift Apus:
every child of a sequence records its slot, the first one too; every bracket is a
context of its own, like an anonymous nonterminal; the rounds of a loop are counted
from the loop's start, so each round records where the earlier rounds ended. A loop
is written `{ ( τ ) }`: its one alternative is a group, so each round is one item,
whose step records the loop's start, the round's start and its end, and the group's
own sequence starts where the round starts. Swift Apus builds every loop this way
(`ApusParser.loopRound`).

| Alternative | Better at | Why not chosen |
|---|---|---|
| Scott's binarisation: skip the first child's element | fewer elements, same information | Swift records it; one uniform rule kept the proofs simple |
| Scott's EBNF slots: `( )` and `[ ]` inside the surrounding sequence | fewer contexts | a bracket's choice then has no element of its own for an oracle to prefer |
| Rounds counted from the loop's start, without the group | one element less per round | a round's own start is then in no element, so nothing that compares rounds can work: `@prefer` among a loop's alternatives compared loop prefixes instead of rounds. Chosen at first, replaced by the group (Scott and Johnstone's "local root node" for a closure, one per round) |
| Swift's completion elements `(lhs, i, i, j)` too | direct span lookup | redundant with the last child's element; dropped when comparing |

Because every child records an element, every leaf's token is written in the set.
That is what makes `exact_trees_spell` true (the exact parser also checks that each
terminal's step matches the input token at its position): a fitting tree built only from steps of
the exact set, as long as the input, spells the input. An oracle choosing a tree from
the set cannot produce nonsense. (The length condition matters: for `S ::= S S | a`
on `aa`, the tree `S -> a` uses only steps of the exact set, but spells `a`.)

What a finite set cannot do is tell infinitely many trees apart: trees that differ
only in repeated cycles like `A ::= A | a` have the same steps. Telling trees apart
is therefore a job for the oracle.

**ε is an item**: `Eps{}`, matched by a `Skip`. It
records a step like any other item, the slot after it with (sequence start, k, k),
which is the yield Swift Apus records for an EPS node.

**No removable empty rounds**. Every bracket repeats its body:
`( τ )` exactly once, `[ τ ]` at most once, `{ τ }` any number of times, `< τ >` at
least once. The rule (`roundsOk`):

> A bracket has at least its minimum number of rounds, and an empty round only when
> it has exactly its minimum.

| Bracket over nothing | Its tree |
|---|---|
| `[ τ ]` | a `Skip`, never a `Pick` whose τ derives ε |
| `{ τ }` | no rounds |
| `< τ >` | exactly one empty round, the τ of `< τ > = ( τ ) { τ }` |
| `( τ )` | its one round; a choice between empty alternatives stays |

A bracket that reads something has no empty round.

Trees that differ only in how often nothing was repeated are one reading. Trees
that differ in which alternative or production was chosen are different readings,
even when nothing is read: `( ε | A )` with `A ::= ε`, or `A A` with a nullable `A`
on one token. Those are for the oracle to resolve. The language is unchanged; only
which trees count, and so which steps are in the exact set.

**Grammar cycles** (`A ::= A | a`): allowed, with infinitely many trees. The
alternative is cycle-free trees only (no node with the nonterminal and span of one
of its ancestors), as in Scott and Johnstone's work on cycle breaking.

**Empty rounds and LL(1).** Scott and Johnstone's EBNF parsers keep every empty round: a
closure with a nullable body has infinitely many derivations, folded into SPPF loops, and an
optional with a nullable body is a genuine ambiguity (in their Java study they rewrote such
rules). Here those readings are no trees, so the LL(1) notions at the end of SPEC.bend follow
the bracket rule: the rounds of `[ ]` and `{ }`, and the later rounds of `< >`, always read
something, so their alternates are told apart by FIRST alone. Only an alternate of a
nonterminal, the round of `( )`, the first round of `< >`, and leaving a bracket may read
nothing, and so also predict through FOLLOW. A `< >` has two choice points: entering (a round
must be taken, and it may be empty) and after a round (another round, which reads
something, or leave). With this, `[A] b` with `A ::= a | ε` is LL(1): `b` skips, `a` takes.
The predicting engine follows the same rule (`Gll.predictFor`): it starts a round of `[ ]`
or `{ }`, or a round of `< >` that does not start where the loop starts, only when the next
token is in FIRST of the round, so it never enters a removable empty round. Before, it used
FOLLOW there too, and `{ a | ε } b` on input `b` left the empty round's step as dead wood.

**Swift Apus** keeps the present-but-empty readings of `[ τ ]` in its raw yields, and
phase 1 of the Oracle removes them. It also reports no ambiguity for `( "" | A )`
with `A = ""`, which is a genuine one. Its prediction (`viable`) and its LL(1) diagnostic
(`verifyLL1`) use the textbook rule (FIRST, and FOLLOW where nullable) for every bracket, so
they enter the empty reading of a nullable `[ ]` or `{ }` alternate; the bracket rule would
let both engines skip it.

## Still to do

- Done: LL(1) laws, on the derived notions at the end of SPEC.bend (`Nullable`, `First`,
  `FollowAt` read from parse trees, `Predicts`, `ChoicePoint`, `choiceOf`, strong `LL1At`
  and `LL1`): `ll1_unambiguous` (an LL(1) grammar has at most one parse tree per input),
  then a computable check "LL(1) by the tables" in FIRST.bend with the law that it implies
  `LL1` (`tables_ll1_sound`), then `ll1_no_dead_wood` (with that check, the predicting
  parser's set is exactly the steps of the parse tree), and last `ll1_at` (two trees reaching
  an LL(1) choice point at the same position choose the same there).

- Once the whole Oracle is proven: review the edifice and simplify it.

- Preferences never remove every parse tree, without the premise that the oracle
  answered: needs a verified recogniser for "do these items derive these tokens
  without going round a cycle?" (see `prefer_avoid_safe`).

- A law that enough fuel always gives an answer (today a failure is safe: no answer).
- Larger grammars in the Bend check: the language fixtures, and the `fail` messages.
- Done 2026-11-09: Swift Apus no longer keeps loop iteration ends for `@longest`.

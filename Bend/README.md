# Apus in Bend

A formally checked specification of EBNF parsing, with a GLL parser whose output
is checked against it. Written in [Bend 2](<Bend Guide.md>).

## What to read

Only two files are trusted. Everything else is either checked by the machine or
there for intuition.

| File | What it is | Read? |
|---|---|---|
| `SPEC.bend` | What parsing means: grammars (EBNF right sides with `( ) [ ] { } < >`), parse trees, `fits`, `leaves`, the steps of a tree as BSR elements, exact BSR sets, and which trees `@prefer` and `@avoid` select | **yes** |
| `LAWS.bend` | Every claim, nothing else | **yes** |
| `EXAMPLES.bend` | The paper's examples, the engine on them, the check catching broken states | for intuition |
| `GLL.bend` | The GLL engine, after tinyGLL and ApusApus | optional: not trusted |
| `CHECK.bend` | The closedness check on the engine's final state, and `checkedSteps` | optional |
| `PRUNE.bend` | The round rule on link steps, and pruning to the steps a parse tree needs, with its closedness check | optional |
| `WITNESS.bend` | A search for parse trees built from the kept steps | optional: not trusted |
| `EXACT.bend` | The exact parser `exactSteps`: pruned steps, handed out only when witness trees cover them all | optional |
| `GUARD.bend` | The guard oracle `guardSteps` (phase 1): the exact set without the steps of nodes that break a lookahead, `@left` or `@right` rule, every answer checked | optional |
| `EXTENT.bend` | The extent oracle `extentSteps` (phase 3, `@longest`/`@shortest`): the exact set without the steps on no best reading, with a self-check against stitched readings | optional |
| `UNBEATEN.bend` | The joined preference oracle `unbeatenSteps` (phase 2 on top of phase 1): the guard oracle's set without the steps of choices outranked by an admissible rival | optional |
| `PREFER.bend` | The preference oracle `preferSteps`: the exact set without the steps of outranked choices, each removal with a checked certificate | optional |
| `COMPARE.bend` | Sets Swift Apus's BSR yields next to the exact set, or after `@prefer`/`@avoid` next to the steps of the unbeaten trees: what is missing, what is dead wood | optional |
| `swift/` | Cases exported from Swift Apus by `ApusApusTests/BendExport.swift`; generated | run |
| `PROOF.bend` | The gate | run, don't read |
| `PROOF_TREES.bend` | Proofs of the rewriting laws | no |
| `PROOF_GLL.bend` | Proof that the checked parser misses nothing | no |
| `PROOF_ROUNDS.bend` | Proof that the round rule keeps every step of every parse tree | no |
| `PROOF_PRUNE.bend` | Proof that pruning keeps every step of every parse tree | no |
| `PROOF_EXACT.bend` | Proof that the exact parser's set is exact | no |
| `PROOF_SPELL.bend` | Proof that trees built from the exact set spell the input | no |
| `PROOF_GUARD.bend` | Proof that the guard oracle's set embeds exactly the admissible trees | no |
| `PROOF_PREFER.bend` | Proof that the joined preference oracle's set embeds exactly the admissible unbeaten trees | no |
| `PROOF_SUPPORT.bend` | Proof that a no from the admissible sub-parse leaves no admissible rival in place | no |
| `PROOF_SUBPARSE.bend` | What a sub-parse and the exact set say about trees; shared by the oracle proofs | no |
| `PROOF_EXTENT.bend` | Proof that the extent oracle's set embeds exactly the best-extent trees | no |
| `FITS.bend` | Facts about `fits`: of a list, of its head and tail, of a join | no |
| `LEMMAS.bend` | Facts about Bool, Nat and lists | no |
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
| Bend check | `APUS_BEND=1` (or the path to `bend`) | runs Bend on every accepted message of the `TestCase` tables in `CoreGrammarTests`, plus the cases below; fails when Swift misses a parse-tree step; a second test does the same after the Oracle, and a third compares grammars with `@prefer`/`@avoid`, and a fourth grammars with `@canParse`/`@cannotParse`/`@left`/`@right` (below); attaches a report per case, and the Bend file of every difference |
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
3. it leaves no dead wood, except at loops. Phase 1 keeps every loop iteration end
   on purpose, for `@longest` to compare with (`pruneUnproductive`, TODO.md).

Results (2026-10-27), the same 341 messages:

| | Raw yields | After phase 1 |
|---|---|---|
| agree exactly | 202 | 304 |
| dead wood | 406 | 0, apart from 71 loop iteration ends (35 messages) |
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

Results (2026-10-30), 35 messages: 32 agree exactly; 3 differ only by one loop
iteration end each (the phase 1 exception above). No step of an unbeaten tree is
missing, and no step of an outranked choice survives.

### After lookahead, `@left` and `@right`

A fourth test runs 13 grammars with `@canParse`/`@cannotParse`/`@left`/`@right` through
Swift's Oracle and compares the yields with the steps of the admissible trees
(`COMPARE.bend`, `guardReport`). The cases cover bare and listed `@left`/`@right`, both
on productions and in groups, lookahead that removes every parse, ambiguous lookahead,
and lookahead on a nonterminal GLL never predicts at that position.

Results (2026-10-31), 17 messages: all 17 agree exactly. Where a rule removes every
parse, Swift and Bend both leave nothing.

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
- **`@longest` and `@shortest` keep exactly the best-extent trees** (`extent_exact`,
  phase 3): whenever `extentSteps` hands out a set, a parse tree of the input uses only
  its steps exactly when no node, pick or round has a rival reading of the same
  children's tokens whose marked item is longer (`@longest`) or shorter (`@shortest`)
  (`SPEC.bend`, `ExtentBest`). The comparison is local, within the one sequence the
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

**Swift Apus** keeps the present-but-empty readings of `[ τ ]` in its raw yields, and
phase 1 of the Oracle removes them. It also reports no ambiguity for `( "" | A )`
with `A = ""`, which is a genuine one.

## Still to do

- Join phase 3: `@longest`/`@shortest` rivals must be admissible and unbeaten. The same
  route as phase 2: EXTENT.bend's rival search would run on the phase 2 set.
- Decide whether Apus's token lookaround `>+>`/`>->` (and `<+<`/`<-<`) should take
  nonterminals, replacing `@canParse`/`@cannotParse` (SPEC.bend `Ahead`/`NotAhead`).
  This changes the grammar language: Swift Apus, Swift.apus and the docs.
- Once the whole Oracle is proven: review the edifice and simplify it.

- Preferences never remove every parse tree, without the premise that the oracle
  answered: needs a verified recogniser for "do these items derive these tokens
  without going round a cycle?" (see `prefer_avoid_safe`).

- A law that enough fuel always gives an answer (today a failure is safe: no answer).
- Larger grammars in the Bend check: the language fixtures, and the `fail` messages.
- Swift Apus: phase 1 keeps loop iteration ends on purpose, for `@longest`; make that
  dependency explicit (TODO.md).

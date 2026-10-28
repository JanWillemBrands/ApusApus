# Apus in Bend

A formally checked specification of EBNF parsing, with a GLL parser whose output
is checked against it. Written in [Bend 2](<Bend Guide.md>).

## What to read

Only two files are trusted. Everything else is either checked by the machine or
there for intuition.

| File | What it is | Read? |
|---|---|---|
| `SPEC.bend` | What parsing means: grammars (EBNF right sides with `( ) [ ] { } < >`), parse trees, `fits`, `leaves`, the steps of a tree as BSR elements, and exact BSR sets | **yes** |
| `LAWS.bend` | Every claim, nothing else | **yes** |
| `EXAMPLES.bend` | The paper's examples, the engine on them, the check catching broken states | for intuition |
| `GLL.bend` | The GLL engine, after tinyGLL and ApusApus | optional: not trusted |
| `CHECK.bend` | The closedness check on the engine's final state, and `checkedSteps` | optional |
| `PRUNE.bend` | The round rule on link steps, and pruning to the steps a parse tree needs, with its closedness check | optional |
| `WITNESS.bend` | A search for parse trees built from the kept steps | optional: not trusted |
| `EXACT.bend` | The exact parser `exactSteps`: pruned steps, handed out only when witness trees cover them all | optional |
| `COMPARE.bend` | Sets Swift Apus's BSR yields next to the exact set: what is missing, what is dead wood | optional |
| `swift/` | Cases exported from Swift Apus by `ApusApusTests/BendExport.swift`; generated | run |
| `PROOF.bend` | The gate | run, don't read |
| `PROOF_TREES.bend` | Proofs of the rewriting laws | no |
| `PROOF_GLL.bend` | Proof that the checked parser misses nothing | no |
| `PROOF_ROUNDS.bend` | Proof that the round rule keeps every step of every parse tree | no |
| `PROOF_PRUNE.bend` | Proof that pruning keeps every step of every parse tree | no |
| `PROOF_EXACT.bend` | Proof that the exact parser's set is exact | no |
| `PROOF_SPELL.bend` | Proof that trees built from the exact set spell the input | no |
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
| Bend check | `APUS_BEND=1` (or the path to `bend`) | runs Bend on every accepted message of the `TestCase` tables in `CoreGrammarTests`, plus the cases below; fails when Swift misses a parse-tree step; a second test does the same after the Oracle (below); attaches a `bend report.txt` per case, and the Bend file of every difference |
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

- A law that enough fuel always gives an answer (today a failure is safe: no answer).
- Larger grammars in the Bend check: the language fixtures, and the `fail` messages.
- Swift Apus: phase 1 keeps loop iteration ends on purpose, for `@longest`; make that
  dependency explicit (TODO.md).

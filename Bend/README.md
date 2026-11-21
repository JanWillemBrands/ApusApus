# Apus in Bend

A specification of Apus grammars and their parse trees, with proven algorithms: the GLL
parser, the exact set of parse-tree steps, the three phases of the Oracle (lookahead,
`@left`/`@right`; `@prefer`/`@avoid`; `@longest`/`@shortest`), and the LL(1) and prediction
laws. A grammar as written (`SYNTAX.bend`) means its translation to a small BNF core
(`EBNF.bend`, `CORE.bend`); every definition and proof works on the core (see "The design"
below). Swift Apus is tested against it (`TESTING.md` § 8d).

## How to check

```
bend PROOF.bend             # ALL PROOFS CHECK when every law in LAWS.bend holds
bend PROOF.bend --verdict   # the same, with the Lean-proven kernel
bend EXAMPLES.bend          # the examples
bend swift/split.bend       # one Swift Apus case against the exact set
```

`LAWS.bend` states the claims and nothing else; `PROOF.bend` proves each one (`def
Laws.<name>`) and imports every proof file, so the gate checks them all. Checked on its own,
`LAWS.bend` reports its claims as open.

## What to read

To see what is specified and claimed, read `LAWS.bend` (the claims), then the meaning in
`SYNTAX.bend`, `CORE.bend`, `EBNF.bend`, `GUARD.bend`, `PREFER.bend`, `ORACLE.bend`,
`EXTENT.bend` and `LL1.bend` (in each, the part headed "THE MEANING" or the definitions with
capital-letter type names). The proof files and the algorithms need not be read: the gate
checks them.

**Reading Bend.** `type T is Data:` lists the shapes of a value. `def f(x: A) -> B:` is a
function; one returning `Bool` is a check. A definition returning `Type` is a statement, and
these forms build them:

| Written | Read |
|---|---|
| `{a == b : T}` | a equals b (`{c == True{} : Bool}`: the check c holds) |
| `P & Q` | P and Q |
| `P -> Q` | if P, then Q (`P -> Empty`: P is impossible) |
| `@x: T -> P` | for every x of type T, P |
| `&x: T -> P` | there is an x of type T with P |
| `Unit` | nothing to show |
| `Some{x}`, `None{}` | an answer x; no answer |
| `[a, b]`, `x <> xs` | a list; x in front of the list xs |
| `0n`, `1n+n` | the numbers 0 and n + 1 |

A `+` before a name or type only tells Bend that the value may be used more than once.

| File | What it is |
|---|---|
| `LAWS.bend` | The claims: the exact set, the phases, the answer laws, LL(1) and prediction |
| `PROOF.bend` | The gate: each claim's proof, and every proof file |
| `SYNTAX.bend` | The grammar as written: productions, items, brackets, the marks, and Swift's steps (slots in the grammar as written) |
| `CORE.bend` | L0: productions over terminals and nonterminals, trees of leaves and nodes, `reads`, steps, the exact set |
| `EBNF.bend` | L1: what an EBNF grammar means, as its translation to the core (towards Swift, and towards LL(1)), and the map from core steps to Swift's slots |
| `EBNF_EX.bend` | The translation on examples: core trees read the input, and their steps, mapped to Swift's slots, are the expected steps, written out |
| `GLL.bend` | The GLL engine on the core (not trusted); return edges are added without a duplicate check (Afroozeh). It takes a predictor: none, or a set of allowed next tokens per production (Scott's predict sets) |
| `CHECK.bend` | The closedness check on the engine's final state (for the descriptors a predictor admits), and the checked parser `checkedSteps` |
| `PROOF_GLL.bend` | Proof that the checked parser misses no step of any parse tree: `gll_every_parse_step` |
| `GLL_EX.bend` | The engine on the examples' translations, against the expected checked and exact sets, written out |
| `RUN.bend` | The engine's invariant (every seen descriptor done or still to do, clusters seeded, return edges met with every pop, everything belonging to a known cluster, to-do descriptors seen, every descriptor, return edge, pop and step within the grammar and the input), the relation an adding operation keeps, the measure (unseen descriptors within bounds, plus the to-do list), and what the steps rest on (`groundOk`) |
| `RUN_EX.bend` | The invariant evaluated at every iteration of example runs (left recursion, an optional, a cyclic nullable grammar) |
| `PROOF_RUN.bend` | Every operation and every iteration of the worklist engine keeps the invariant, so a finished run is closed: `engine_closed`, and the checked parser answers whenever the engine finishes (`checked_answers`); no iteration raises the measure, so the engine finishes with enough fuel (`gll_finishes`) and the checked parser always answers (`checked_always_answers`); a finished run's steps lie within bounds (`final_steps_bounded`) |
| `PROOF_COUNT.bend` | Counting for the measure: every descriptor within bounds lies in the universe, and seeing a new one lowers the count of unseen ones; small facts about step lists |
| `PROOF_NEEDS.bend` | Pruning's needs loop on steps within bounds: with the same fuel it finishes with closed needs (`needs_closed`), so pruning hands out its steps (`pruned_answers`) |
| `PROOF_WITNESS.bend` | The witness search finds what is there: on facts closed under the rules of the kept steps, a parse tree of kept steps that contains the target gives the root search a forest (`root_found`, by a walk over the tree); with fuel 1 + twice the size of the descriptor universe the fixpoint ends closed (`witness_closed`) |
| `PROOF_WSOUND.bend` | The witness search is sound: every fact's forest reads its segment, and a flagged one contains the target, so the root search hands out only parse trees of the input that contain the target (`witness_good`); with a witness for every kept step the exact parser answers (`exact_from_answers`) |
| `PROOF_GROUND.bend` | Every engine operation keeps every step, descriptor, return edge and pop resting on earlier steps (`groundOk`, RUN.bend): `ground_step`, `initial_ground` |
| `PROOF_FOUND.bend` | On grounded steps and needs reached from the root in order, closed witness facts give every kept step a witness: `found_root` |
| `PROOF_GROW.bend` | The grown tables close: each round adds a fact from a finite universe or changes nothing (`nulls_closed`, `firsts_closed`, `follows_fix`), so with fuel 1 + the table size `tablesClosed` holds on every grammar (`tables_closed`) |
| `PROOF_ANSWER.bend` | The twin answers, stage by stage: the pruned parser with fuel 1 + the size of the descriptor universe (`pruned_parser_answers`), the engine's final state is grounded (`final_ground`), the exact parser with fuel 1 + twice that size (`exact_parser_answers`), and the predicting parser with fuel 1 + that size + the table size (`predicted_parser_answers`) |
| `PRUNE.bend` | Pruning to the steps a parse tree of the whole input needs, with its closedness check |
| `PROOF_PRUNE.bend` | Proof that pruning keeps every step of every parse tree: `prune_every_parse_step` |
| `WITNESS.bend` | The covering witness search (not trusted): one fact per segment and flag, a least fixpoint, grown until the facts are closed (at most `fuel` rounds); a node of an empty right side is found only from its empty step, so trees use only the given steps |
| `EXACT.bend` | The exact parser `exactSteps`: pruned steps, handed out only when checked witness trees cover them |
| `PROOF_EXACT.bend` | Proof that the exact parser's set is exact: `gll_bsr_exact` |
| `PROOF_SPELL.bend` | Proof that a tree which fits, uses only exact steps and is as long as the input spells it: `exact_trees_spell` |
| `EXACT_EX.bend` | The exact parser on the examples against the expected sets, written out, and on a cyclic grammar |
| `SETS.bend` | Sets of naturals and the nullable nonterminals (grown, checked closed), shared by the rule on preference cycles and the LL(1) tables |
| `LEMMAS.bend` | Facts about Bool, Nat and lists |
| `PROOF_BASICS.bend` | Small facts about Bool, Nat and lists shared by the core's proofs |
| `GUARD.bend` | Phase 1 on the core: what lookahead, @left and @right mean, step by step (a tree is admissible when each of its steps keeps the rules it decides), the rules as written moved onto core productions, and phase 1's three-valued verdict on a step; "does q derive w" is judged by the closure of `CLOSURE.bend` |
| `PREFER.bend` | Phase 2 on the core: what @prefer and @avoid mean, step by step (a completed step is beaten when a higher-ranked production of its nonterminal has a rival over the same tokens whose steps keep their rules), the marks as written moved onto core productions, phase 2's verdict on a step, and the rule `noPreferenceCycle` (an outranking production lies on no cycle that reads no input; nullable sets from `SETS.bend`) |
| `ORACLE.bend` | The oracle: the exact set, filtered by both verdicts at once; any Unknown means no answer. A chosen tree is one whose steps all keep their rules and complete no beaten node |
| `CLOSURE.bend` | "Does q derive w" without sub-parses: segments of w grown Earley-style with every step allowed, each with a forest (not trusted), until they are closed, and the check that they are |
| `PROOF_CLOSURE.bend` | The closure decides derivation: a closed set without q's whole segment leaves no forest (`walk`), the growth ends closed (`closure_closed`), and a completing segment's forest reads w (`closure_found`) |
| `PROOF_DECIDE.bend` | The questions phase 1 asks are answered soundly: Yes only with a checked forest, No only when the closed segments do not complete q |
| `PROOF_GUARD.bend` | Phase 1's verdict is right: a step answered Yes keeps its rules, one answered No does not |
| `RIVAL.bend` | Phase 2's rival search: segments of the input grown Earley-style through steps phase 1 answers Yes, each with a forest (not trusted), until they are closed, and the check that they are |
| `PROOF_RIVAL.bend` | A rival completes its segment in a closed set (`walk`), so a closed set without it leaves no rival |
| `PROOF_RIVAL_GROW.bend` | The rival closure answers: when phase 1 decides every step within bounds (`decided`), with fuel 1 + the size of the descriptor universe the segments grown from m at i are closed and have m's start (`rival_closed`); segment keys are counted as descriptors |
| `PROOF_RIVAL_SOUND.bend` | The rival's certificate is sound: every grown segment's forest reads its prefix of items and has only steps phase 1 answers Yes (`grow_ok`), so a segment that completes m passes `certWith`; with `rival_closed`, phase 2's rival verdict is never Unknown when phase 1 decides (`rival_decided`) |
| `PROOF_LIVE.bend` | Dropping dead wood keeps exactly the chosen trees: a step is dropped only when no tree found so far covers it and its closed witness search finds no tree inside the oracle's set (`live_embeds`) |
| `PROOF_WINSIDE.bend` | The witness search stays inside its steps: every forest and every tree it or the cover loop hands out uses only the given steps (`witness_in`, `cover_in`) |
| `PROOF_ORACLE_ANSWERS.bend` | The oracle answers: with fuel 1 + twice the size of the descriptor universe, the exact set lies within bounds and no verdict on it is Unknown (`oracle_answers`) |
| `PROOF_EXTENT_ANSWERS.bend` | The chosen set and the selecting oracle answer with that fuel (`chosen_answers`, `extent_answers`) |
| `PROOF_VERDICT.bend` | The verdicts are decided: with fuel 1 + the size of the descriptor universe, phase 1 answers every step Yes or No (`phase1_decides`), and phase 2 every step within bounds (`phase2_decides`) |
| `PROOF_PREFER.bend` | Phase 2's verdict is right: a step answered Yes is not beaten, one answered No is (its certificate is a rival) |
| `PROOF_ORACLE.bend` | Proof that the oracle's set is exactly the steps of the chosen parse trees: `oracle_exact` |
| `ORACLE_EX.bend` | The oracle on @left, @right, @prefer and @avoid; the rule on cyclic and acyclic grammars, and the cycle `A = @prefer A \| a`, where nothing is chosen; phase 2 with rivals that are admissible only through a later production, or never |
| `PROOF_RULE.bend` | On a grammar without a preference cycle no rival comes back to its own choice: `no_self_rival` |
| `EXTENT.bend` | Phase 3 on the core: what @longest and @shortest mean, step by step (a step is out when it stands on a reading of its production that another reading to the same end beats on the marked items; readings may be stitched from steps of chosen trees), the marks as written moved onto core items, the chosen set (the oracle's set without dead wood: one pass keeps the trees it finds, searches only for steps none of them covers, and drops a step only when its search is closed, `liveFrom`) handed out only with witness trees inside it, and the selecting oracle (exact, no Unknown) |
| `PROOF_EXTENT.bend` | Proof that the chosen set is exact (every step lies on a chosen tree) and that the selecting oracle's set is exactly the steps of the selected trees: `extent_exact` |
| `EXTENT_EX.bend` | The selecting oracle on @longest and @shortest, on an item and on a nonterminal |
| `LL1.bend` | LL(1) on the core: nullable, FIRST and FOLLOW read from trees, what a production predicts, LL(1) at a nonterminal and everywhere; LL(1) of a grammar as written is LL(1) of its translation towards LL(1) |
| `PROOF_LL1.bend` | An LL(1) grammar is unambiguous (`ll1_unambiguous`), and LL(1) at one nonterminal decides it (`ll1_at`) |
| `TABLES.bend` | The LL(1) tables (nullable, FIRST, FOLLOW) grown untrusted and checked closed, the predict sets, the check `ll1ByTables`, and the check at one nonterminal `ll1AtByTables` |
| `TABLES_EX.bend` | The LL(1) check on examples, including clashes only FOLLOW shows |
| `PROOF_TABLES.bend` | LL(1) by the tables is LL(1): `tables_ll1_sound` |
| `PROOF_LL1_AT_TABLES.bend` | Partially LL(1) grammars: the check at x gives LL(1) at x (`tables_ll1_at`), and prediction then admits at most one production of x per next token (`seeds_one_at`) |
| `PREDICT.bend` | The predicting parser `predictedSteps`: predict sets from the checked tables, the engine run with them, the final state checked closed for what prediction admits; the LL(1) parser `ll1Steps`: tables that pass the LL(1) check, and a final state also supported |
| `PROOF_PREDICT.bend` | Prediction admits every node of every parse tree, so the predicting parser misses nothing: `predict_every_parse_step` |
| `PREDICT_EX.bend` | The predicting parser on examples, including a production predicted only by FOLLOW; the LL(1) parser's set is exactly the tree's steps where the plain parser has dead wood, and a grammar that is not LL(1) gets no answer |
| `SUPPORT.bend` | Support: the facts of an engine state, the engine's rules on facts (with its predictor), the facts reached from the root, and `supported` (every fact of the state is reached) |
| `SUPPORT_EX.bend` | Support on examples: plain and predicting runs are supported, and the predicting run's facts lie inside the plain run |
| `PROOF_HOLD.bend` | Goals for the facts reached: in a closed plain state, or on a parse tree (a Bool search over the tree's steps); lists of facts |
| `PROOF_STATE.bend` | Every rule keeps the goal "in a closed plain state" |
| `PROOF_TREE.bend` | Every rule of the predicting engine keeps the goal "on a parse tree of an LL(1) grammar": the node of a step, cursors, seeds by table conflicts, resumes by `compare` |
| `PROOF_SUPPORT.bend` | Every fact of a supported state holds the goal (one induction): `predict_saves_work`, and `ll1_no_dead_wood` (the LL(1) parser's set is exact) |
| `EXAMPLES.bend` | Every example file above, checked at once |
| `COMPARE.bend` | Swift Apus against the core: a grammar as written, its marks, an input and Swift's steps (exported by `ApusApusTests/BendExport.swift`), next to the core's exact, chosen or selected set mapped to Swift's slots; the dead wood of the oracles' sets is dropped first. It tries small fuels first and doubles them, up to the fuel with which each set is proven to come, so it always answers |

Run each with `bend <file>`; each prints ALL PROOFS CHECK. The growth loops (`WITNESS.bend`,
`CLOSURE.bend`, `RIVAL.bend`) stop as soon as their facts are closed: their fuel is only a
bound, so the proven fuel (about twice the descriptor universe) costs no more than needed.

## The design

### Principles

- **Bend is the reference.** The meaning of every annotation is defined here. Swift's engine
  implements it; the tests compare Swift with Bend, never the other way.
- **Pure reasons only.** A rule needs a language-design reason that holds for any grammar. That
  a particular grammar (such as `Swift.apus`) uses a form or not is no reason; such a grammar
  serves only as a regression check.
- **No desugaring in Swift.** Swift's engine keeps EBNF (it is faster, and its trees are what
  users see). The export to Bend is one to one; the translation to the core happens inside the
  spec, so its meaning is specified too.
- **Rules, not implementation limits.** Where an oracle does not handle a well-formed form, the
  oracle is incomplete; that is no reason to forbid the form.
- **Keyed facts, never lists of trees.** A cyclic grammar has infinitely many trees
  (`A = A | "a"` reads `a` as `A(a)`, `A(A(a))`, …). GLL records each descriptor, call and step
  once, keyed by slot and positions, and every algorithm here that reasons about trees does the
  same: one fact per key, found as a least fixpoint. The meaning keeps every finite tree; the
  algorithms never list them.
- **Trees, not language equivalence.** The Oracle chooses among trees and the tests compare tree
  steps, so the translation must give each reading of the grammar as written exactly one tree,
  not merely keep the language (`EBNF_EX.bend`, and Swift's steps in the tests).

### The layers

| Layer | What it adds | Trees | Proved on it |
|---|---|---|---|
| L0, BNF core (`CORE.bend`) | productions `A = x1 … xn` over terminals and nonterminals; n = 0 is ε | leaf, node | the parsers, pruning, the oracles, LL(1), every law |
| L1, EBNF (`SYNTAX.bend`, `EBNF.bend`) | `( )`, `[ ]`, `{ }`, `< >`, ε as an item | none of its own: the core trees of its translation | nothing: the translation is its meaning |
| L2, annotations | guards, ranks, extent marks | — | their meaning is defined on L0 |
| L3, well-formed | no preference cycle | — | a hypothesis of `no_self_rival` only |

The parser, pruning, exactness and LL(1) laws hold for every grammar; making them conditional
on well-formedness would only weaken them.

Chomsky normal form is not the core: ε-removal and unit-rule removal merge distinct trees (a
cyclic grammar has infinitely many trees and its normal form finitely many), and they destroy
the alternatives and sequences the annotations are attached to. Its useful half, binary steps,
the core has: a step `(X = α · β, i, k, j)` is the intermediate node for the prefix α.

### The core

    Need       = Anything | Something | Nothing
    Sym        = Terminal{kind} | Nonterminal{id, need}
    Production = Production{lhs, rhs: List<Sym>}
    Tree       = Leaf{kind} | Node{production, children}
    Bsr        = Bsr{production, dot, i, k, j}

Every proof that walks a tree has two cases. A parse tree is defined with `reads` (the forest
fits the items and matches the input from a position). An occurrence's `need` carries the rules
for empty rounds (below); written nonterminals have `Anything`.

### EBNF as a translation

Each bracket occurrence gets a fresh *group* nonterminal G whose productions are its
alternatives, as written. `[ ]`, `{ }` and `< >` add a fresh *shape* nonterminal H with fixed
productions around G:

    ( τ1 | … | τn )   →  G = τ1 | … | τn
    [ … ]             →  H = ε | G!
    { … }             →  H = ε | H G!                   (towards Swift)
                         H = ε | G! H                   (towards LL(1))
    < … >             →  H = G⁰ | K,  K = G! | K G!     (towards Swift)
                         H = G⁰ | G! K,  K = ε | G! K   (towards LL(1))
    ε (an item)       →  E = ε, one E for the grammar

`G!` is an occurrence that must read something, `G⁰` one that must read nothing. A loop's body
is a group, as Swift Apus builds it: `{ τ }` and `{ ( τ ) }` mean the same.

**The translation is the meaning.** An EBNF grammar has no trees of its own: its parse trees
are the core trees of its translation, so the rewriting laws of EBNF hold by construction.
New nonterminals are named by where their bracket stands (production, path, role) and numbered
in a second, flat pass; written nonterminals and productions keep their numbers. The walk
through nested brackets uses nesting fuel, as Bend has no mutual recursion; a grammar nested
deeper has no translation and is reported (`ok`), never translated silently wrong.

Guards and ranks sit on G's productions, the alternatives as written. A shape nonterminal's
productions are generated: never ranked, marked or guarded. So the ε production of `[ ]` and
`{ }` is no rival of a pick: a skip makes no choice.

**Nullable bodies.** When a bracket's body can read nothing, `[ τ ]` over nothing is only the
skip (a pick must read something), and the rounds of a loop all read something, except the one
round of `< τ >` over nothing. These are the needs of the generated occurrences (`G!`, `G⁰`),
checked by `reads` like any other part of a tree.

**Two translations of loops.** No L0 definition or proof depends on the direction of a loop;
only the translation does, and each family of laws uses the direction it needs:

| Laws | Need | Loops |
|---|---|---|
| parser, exact set, the three phases | steps that are Swift's yields | left-recursive |
| LL(1) (tables, unambiguous, no dead wood, `ll1_at`), prediction | the choice "another round or stop" made after each round | right-recursive |

Towards Swift, each round runs from the loop's start, as Swift records it: `H = H · G` over
`(i, k, j)` is the round's link step from the loop's start i over a round from k to j. Towards
LL(1), each round's start is where "another round or stop" is chosen; a left-recursive
production is never LL(1). A grammar as written is LL(1) when its right-recursive translation
is (Wirth's conditions, here a definition).

**The step map** (`EBNF.stepsToSwift`). Swift's yields use slots in the grammar as written
(production, path); the core's steps use (production, dot) of the translation towards Swift.
Each core production records where it came from: a sequence as written keeps its slots, a
loop's shape production gives the round's link step, and the other shapes and E give no step
of Swift's. So the map is a function from core steps to Swift's slots that drops the core's
extra steps. It is the one place where the two layers meet in the tests.

### Cyclic grammars

A cyclic grammar (`A ⇒ … ⇒ A` over the same tokens) is legal and simply ambiguous: every finite
tree counts. The set of steps that occur in some tree is finite however many trees there are,
so the laws need no exception, and every algorithm that reasons about trees (the witness search,
the oracles' closures and certificates) works on keyed facts with a least fixpoint.

### Annotations on the core

| As written | On the core |
|---|---|
| guard on a production (`ProdGuard`) or a bracket alternative (`AltGuard`) | on a production (of G, for a bracket) |
| rank on a production (`ProdMark`) or a bracket alternative (`AltMark`) | on a production (of G, for a bracket) |
| extent on a nonterminal (`NtExtent`) or a bracket (`BrackExtent`) | on an occurrence: a production and a dot |

An extent mark compares readings of the sequence it stands in, so on the core it names one item
of one production. A mark on a nonterminal is shorthand for every occurrence of it in the
grammar as written; a mark on a bracket marks the one occurrence of its G or H. Generated
occurrences are never marked: in `H = H G` the shape nonterminal occurs in its own production,
and marking it there would add a rule inside the loop. Several marks in one sequence are served
left to right (`EXTENT.bend`, `beatsAt`).

### Well-formed grammars: no preference cycle

An alternative that outranks a sibling (`@prefer` over a plain or `@avoid` sibling, a plain one
over an `@avoid` sibling) lies on no cycle that reads no input: it cannot derive, over its own
tokens, the choice it belongs to. A preferred rival that comes back to the choice it competes
in only says "the same again"; counting it could beat every reading, so that no tree is left.
The rule is a property of the grammar, checked once (`PREFER.bend`, `noPreferenceCycle`, by two
checked closed sets); cyclic grammars as such stay legal. On a well-formed grammar no rival holds
a node of its own nonterminal over all its tokens (`no_self_rival`). Swift Apus refuses such a
grammar at load time (`GrammarDiagnostics.diagnosePreferenceCycles`, exact for brackets too).

### What can go unanswered

Every algorithm answers with the fuel of the answer laws. The untrusted parts (the engine, the
pruning loop, the witness search, the closures) are checked before anything is handed out; a
failed check would be a bug, and the answer laws show none happens. The LL(1) parser
(`PREDICT.bend`, `ll1Steps`) is for LL(1) grammars only: on another grammar it answers nothing,
by design. Outside the spec, and so not exported to Bend: lexical ambiguity, layout gates, an
extent on a terminal, and an extent mark on one occurrence of a nonterminal.

## Design choices: where Swift Apus and the spec meet

Bare `@left`/`@right` means plain "derives", as `GUARD.bend` says. This makes Swift.apus forbid
the chain `f(1) {}⏎{}` that swift-syntax accepts (TODO.md, "Grammar rework for the Oracle").

`@longest`/`@shortest` are local for brackets and nonterminals alike, as `EXTENT.bend` says,
and several marks in one sequence are served left to right. Swift
Apus and the spec mean the same thing everywhere; `documentation/Oracle.md` § 5 lists the
remaining choices, which the spec makes too. A mark on one occurrence of a nonterminal is
not compared: Swift Apus reads only the mark on the nonterminal's own rule.

## What the laws promise

A law about an algorithm says what an answer means: "whenever `exactSteps` hands out a set,
it holds exactly the steps of the parse trees", and likewise for the checked and predicting
parsers and the oracles. On its own, such a law also holds for an algorithm that never
answers. The answer laws close that gap: with fuel 1 + twice the size of the descriptor
universe, the checked, pruned, exact and predicting parsers and the oracles always hand out
their sets (`checked_always_answers`, `exact_parser_answers`, `predicted_parser_answers`,
`oracle_answers`, `chosen_answers`, `extent_answers`). Fuel is only a bound: every loop stops
when it is done.

For the comparisons with Swift Apus (`COMPARE.bend`) this means a case always gets an answer;
only the time limit of a test run can leave one uncompared, and `BendCheck` and
`BendDifferential` fail such a case, so it cannot pass unnoticed.


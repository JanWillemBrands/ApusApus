# core/: the specification on a BNF core (work in progress)

The replacement for today's `SPEC.bend` and its proofs, built step by step as planned in
`FormalGrammar.md` (repo root). Nothing here is part of the gate (`PROOF.bend`) yet; today's
files stay until their replacements check.

| File | What it is |
|---|---|
| `CORE.bend` | L0: productions over terminals and nonterminals, trees of leaves and nodes, `reads`, steps, the exact set |
| `EBNF.bend` | L1: what an EBNF grammar means, as its translation to the core (towards Swift, and towards LL(1)), and the map from core steps to Swift's slots |
| `EBNF_EX.bend` | The translation against today's `SPEC.bend`: core trees read the input, and their steps, mapped to Swift's slots, are today's steps |
| `GLL.bend` | The GLL engine on the core (not trusted); return edges are added without a duplicate check (Afroozeh). It takes a predictor: none, or a set of allowed next tokens per production (Scott's predict sets) |
| `CHECK.bend` | The closedness check on the engine's final state (for the descriptors a predictor admits), and the checked parser `checkedSteps` |
| `PROOF_GLL.bend` | Proof that the checked parser misses no step of any parse tree: `gll_every_parse_step` |
| `GLL_EX.bend` | The engine on the examples' translations, against today's checked and exact parsers |
| `PRUNE.bend` | Pruning to the steps a parse tree of the whole input needs, with its closedness check |
| `PROOF_PRUNE.bend` | Proof that pruning keeps every step of every parse tree: `prune_every_parse_step` |
| `WITNESS.bend` | The covering witness search (not trusted): one fact per segment and flag, a least fixpoint |
| `EXACT.bend` | The exact parser `exactSteps`: pruned steps, handed out only when checked witness trees cover them |
| `PROOF_EXACT.bend` | Proof that the exact parser's set is exact: `gll_bsr_exact` |
| `PROOF_SPELL.bend` | Proof that a tree which fits, uses only exact steps and is as long as the input spells it: `exact_trees_spell` |
| `EXACT_EX.bend` | The exact parser on the examples against today's, and on a cyclic grammar |
| `GUARD.bend` | Phase 1 on the core: what lookahead, @left and @right mean, step by step (a tree is admissible when each of its steps keeps the rules it decides), the rules as written moved onto core productions, and phase 1's three-valued verdict on a step |
| `PREFER.bend` | Phase 2 on the core: what @prefer and @avoid mean, step by step (a completed step is beaten when a higher-ranked production of its nonterminal has a rival over the same tokens whose steps keep their rules), the marks as written moved onto core productions, phase 2's verdict on a step, and the rule `noPreferenceCycle` (an outranking production lies on no cycle that reads no input) |
| `ORACLE.bend` | The oracle: the exact set, filtered by both verdicts at once; any Unknown means no answer. A chosen tree is one whose steps all keep their rules and complete no beaten node |
| `PROOF_DECIDE.bend` | The questions phase 1 asks are answered soundly: Yes only with a checked witness, No only when the exact set has no such step |
| `PROOF_GUARD.bend` | Phase 1's verdict is right: a step answered Yes keeps its rules, one answered No does not |
| `PROOF_PREFER.bend` | Phase 2's verdict is right: a step answered Yes is not beaten, one answered No is (its certificate is a rival) |
| `PROOF_ORACLE.bend` | Proof that the oracle's set is exactly the steps of the chosen parse trees: `oracle_exact` |
| `ORACLE_EX.bend` | The oracle on @left, @right, @prefer and @avoid; the rule on cyclic and acyclic grammars, and the cycle `A = @prefer A \| a`, where nothing is chosen |
| `PROOF_RULE.bend` | On a grammar without a preference cycle no rival comes back to its own choice: `no_self_rival` |
| `EXTENT.bend` | Phase 3 on the core: what @longest and @shortest mean, step by step (a step is out when it stands on a reading of its production that another reading to the same end beats on the marked items; readings may be stitched from steps of chosen trees), the marks as written moved onto core items, the chosen set handed out only with witness trees inside it, and the selecting oracle (exact, no Unknown) |
| `PROOF_EXTENT.bend` | Proof that the chosen set is exact (every step lies on a chosen tree) and that the selecting oracle's set is exactly the steps of the selected trees: `extent_exact` |
| `EXTENT_EX.bend` | The selecting oracle on @longest and @shortest, on an item and on a nonterminal |
| `LL1.bend` | LL(1) on the core: nullable, FIRST and FOLLOW read from trees, what a production predicts, LL(1) at a nonterminal and everywhere; LL(1) of a grammar as written is LL(1) of its translation towards LL(1) |
| `PROOF_LL1.bend` | An LL(1) grammar is unambiguous (`ll1_unambiguous`), and LL(1) at one nonterminal decides it (`ll1_at`) |
| `TABLES.bend` | The LL(1) tables (nullable, FIRST, FOLLOW) grown untrusted and checked closed, the predict sets, and the check `ll1ByTables` |
| `TABLES_EX.bend` | The LL(1) check on examples, including clashes only FOLLOW shows |
| `PROOF_TABLES.bend` | LL(1) by the tables is LL(1): `tables_ll1_sound` |
| `PREDICT.bend` | The predicting parser `predictedSteps`: predict sets from the checked tables, the engine run with them, the final state checked closed for what prediction admits |
| `PROOF_PREDICT.bend` | Prediction admits every node of every parse tree, so the predicting parser misses nothing: `predict_every_parse_step` |
| `PREDICT_EX.bend` | The predicting parser on examples, including a production predicted only by FOLLOW |
| `SUPPORT.bend` | Support: the facts of an engine state, the engine's rules on facts (with its predictor), the facts reached from the root, and `supported` (every fact of the state is reached) |
| `SUPPORT_EX.bend` | Support on examples: plain and predicting runs are supported, and the predicting run's facts lie inside the plain run |
| `PROOF_SUPPORT.bend` | Every fact of a supported state keeps what the rules keep; with the goal "in a closed plain state": `predict_saves_work` |

Run each with `bend <file>`; each prints ALL PROOFS CHECK.

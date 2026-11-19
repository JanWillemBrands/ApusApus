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
| `WITNESS.bend` | The covering witness search (not trusted): one fact per segment and flag, a least fixpoint |
| `EXACT.bend` | The exact parser `exactSteps`: pruned steps, handed out only when checked witness trees cover them |
| `PROOF_EXACT.bend` | Proof that the exact parser's set is exact: `gll_bsr_exact` |
| `PROOF_SPELL.bend` | Proof that a tree which fits, uses only exact steps and is as long as the input spells it: `exact_trees_spell` |
| `EXACT_EX.bend` | The exact parser on the examples against today's, and on a cyclic grammar |
| `SETS.bend` | Sets of naturals and the nullable nonterminals (grown, checked closed), shared by the rule on preference cycles and the LL(1) tables |
| `PROOF_BASICS.bend` | Small facts about Bool, Nat and lists shared by the core's proofs |
| `GUARD.bend` | Phase 1 on the core: what lookahead, @left and @right mean, step by step (a tree is admissible when each of its steps keeps the rules it decides), the rules as written moved onto core productions, and phase 1's three-valued verdict on a step; "does q derive w" is judged by the closure of `CLOSURE.bend` |
| `PREFER.bend` | Phase 2 on the core: what @prefer and @avoid mean, step by step (a completed step is beaten when a higher-ranked production of its nonterminal has a rival over the same tokens whose steps keep their rules), the marks as written moved onto core productions, phase 2's verdict on a step, and the rule `noPreferenceCycle` (an outranking production lies on no cycle that reads no input; nullable sets from `SETS.bend`) |
| `ORACLE.bend` | The oracle: the exact set, filtered by both verdicts at once; any Unknown means no answer. A chosen tree is one whose steps all keep their rules and complete no beaten node |
| `CLOSURE.bend` | "Does q derive w" without sub-parses: segments of w grown Earley-style with every step allowed, each with a forest (not trusted), and the check that they are closed |
| `PROOF_CLOSURE.bend` | The closure decides derivation: a closed set without q's whole segment leaves no forest (`walk`), the growth ends closed (`closure_closed`), and a completing segment's forest reads w (`closure_found`) |
| `PROOF_DECIDE.bend` | The questions phase 1 asks are answered soundly: Yes only with a checked forest, No only when the closed segments do not complete q |
| `PROOF_GUARD.bend` | Phase 1's verdict is right: a step answered Yes keeps its rules, one answered No does not |
| `RIVAL.bend` | Phase 2's rival search: segments of the input grown Earley-style through steps phase 1 answers Yes, each with a forest (not trusted), and the check that they are closed |
| `PROOF_RIVAL.bend` | A rival completes its segment in a closed set (`walk`), so a closed set without it leaves no rival |
| `PROOF_RIVAL_GROW.bend` | The rival closure answers: when phase 1 decides every step within bounds (`decided`), with fuel 1 + the size of the descriptor universe the segments grown from m at i are closed and have m's start (`rival_closed`); segment keys are counted as descriptors |
| `PROOF_RIVAL_SOUND.bend` | The rival's certificate is sound: every grown segment's forest reads its prefix of items and has only steps phase 1 answers Yes (`grow_ok`), so a segment that completes m passes `certWith`; with `rival_closed`, phase 2's rival verdict is never Unknown when phase 1 decides (`rival_decided`) |
| `PROOF_VERDICT.bend` | The verdicts are decided: with fuel 1 + the size of the descriptor universe, phase 1 answers every step Yes or No (`phase1_decides`), and phase 2 every step within bounds (`phase2_decides`) |
| `PROOF_PREFER.bend` | Phase 2's verdict is right: a step answered Yes is not beaten, one answered No is (its certificate is a rival) |
| `PROOF_ORACLE.bend` | Proof that the oracle's set is exactly the steps of the chosen parse trees: `oracle_exact` |
| `ORACLE_EX.bend` | The oracle on @left, @right, @prefer and @avoid; the rule on cyclic and acyclic grammars, and the cycle `A = @prefer A \| a`, where nothing is chosen; phase 2 with rivals that are admissible only through a later production, or never |
| `PROOF_RULE.bend` | On a grammar without a preference cycle no rival comes back to its own choice: `no_self_rival` |
| `EXTENT.bend` | Phase 3 on the core: what @longest and @shortest mean, step by step (a step is out when it stands on a reading of its production that another reading to the same end beats on the marked items; readings may be stitched from steps of chosen trees), the marks as written moved onto core items, the chosen set handed out only with witness trees inside it, and the selecting oracle (exact, no Unknown) |
| `PROOF_EXTENT.bend` | Proof that the chosen set is exact (every step lies on a chosen tree) and that the selecting oracle's set is exactly the steps of the selected trees: `extent_exact` |
| `EXTENT_EX.bend` | The selecting oracle on @longest and @shortest, on an item and on a nonterminal |
| `LL1.bend` | LL(1) on the core: nullable, FIRST and FOLLOW read from trees, what a production predicts, LL(1) at a nonterminal and everywhere; LL(1) of a grammar as written is LL(1) of its translation towards LL(1) |
| `PROOF_LL1.bend` | An LL(1) grammar is unambiguous (`ll1_unambiguous`), and LL(1) at one nonterminal decides it (`ll1_at`) |
| `TABLES.bend` | The LL(1) tables (nullable, FIRST, FOLLOW) grown untrusted and checked closed, the predict sets, and the check `ll1ByTables` |
| `TABLES_EX.bend` | The LL(1) check on examples, including clashes only FOLLOW shows |
| `PROOF_TABLES.bend` | LL(1) by the tables is LL(1): `tables_ll1_sound` |
| `PREDICT.bend` | The predicting parser `predictedSteps`: predict sets from the checked tables, the engine run with them, the final state checked closed for what prediction admits; the LL(1) parser `ll1Steps`: tables that pass the LL(1) check, and a final state also supported |
| `PROOF_PREDICT.bend` | Prediction admits every node of every parse tree, so the predicting parser misses nothing: `predict_every_parse_step` |
| `PREDICT_EX.bend` | The predicting parser on examples, including a production predicted only by FOLLOW; the LL(1) parser's set is exactly the tree's steps where the plain parser has dead wood, and a grammar that is not LL(1) gets no answer |
| `SUPPORT.bend` | Support: the facts of an engine state, the engine's rules on facts (with its predictor), the facts reached from the root, and `supported` (every fact of the state is reached) |
| `SUPPORT_EX.bend` | Support on examples: plain and predicting runs are supported, and the predicting run's facts lie inside the plain run |
| `PROOF_HOLD.bend` | Goals for the facts reached: in a closed plain state, or on a parse tree (a Bool search over the tree's steps); lists of facts |
| `PROOF_STATE.bend` | Every rule keeps the goal "in a closed plain state" |
| `PROOF_TREE.bend` | Every rule of the predicting engine keeps the goal "on a parse tree of an LL(1) grammar": the node of a step, cursors, seeds by table conflicts, resumes by `compare` |
| `PROOF_SUPPORT.bend` | Every fact of a supported state holds the goal (one induction): `predict_saves_work`, and `ll1_no_dead_wood` (the LL(1) parser's set is exact) |

Run each with `bend <file>`; each prints ALL PROOFS CHECK.

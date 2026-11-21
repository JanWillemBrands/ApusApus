import Base
import ./LAWS.bend as Laws
import ./PROOF_ANSWER.bend as ProofAnswer
import ./PROOF_BASICS.bend as ProofBasics
import ./PROOF_CLOSURE.bend as ProofClosure
import ./PROOF_COUNT.bend as ProofCount
import ./PROOF_DECIDE.bend as ProofDecide
import ./PROOF_EXACT.bend as ProofExact
import ./PROOF_EXTENT.bend as ProofExtent
import ./PROOF_EXTENT_ANSWERS.bend as ProofExtentAnswers
import ./PROOF_FOUND.bend as ProofFound
import ./PROOF_GLL.bend as ProofGll
import ./PROOF_GROUND.bend as ProofGround
import ./PROOF_GROW.bend as ProofGrow
import ./PROOF_GUARD.bend as ProofGuard
import ./PROOF_HOLD.bend as ProofHold
import ./PROOF_LIVE.bend as ProofLive
import ./PROOF_LL1.bend as ProofLl1
import ./PROOF_LL1_AT_TABLES.bend as ProofLl1AtTables
import ./PROOF_NEEDS.bend as ProofNeeds
import ./PROOF_ORACLE.bend as ProofOracle
import ./PROOF_ORACLE_ANSWERS.bend as ProofOracleAnswers
import ./PROOF_PREDICT.bend as ProofPredict
import ./PROOF_PREFER.bend as ProofPrefer
import ./PROOF_PRUNE.bend as ProofPrune
import ./PROOF_RIVAL.bend as ProofRival
import ./PROOF_RIVAL_GROW.bend as ProofRivalGrow
import ./PROOF_RIVAL_SOUND.bend as ProofRivalSound
import ./PROOF_RULE.bend as ProofRule
import ./PROOF_RUN.bend as ProofRun
import ./PROOF_SPELL.bend as ProofSpell
import ./PROOF_STATE.bend as ProofState
import ./PROOF_SUPPORT.bend as ProofSupport
import ./PROOF_TABLES.bend as ProofTables
import ./PROOF_TREE.bend as ProofTree
import ./PROOF_VERDICT.bend as ProofVerdict
import ./PROOF_WINSIDE.bend as ProofWinside
import ./PROOF_WITNESS.bend as ProofWitness
import ./PROOF_WSOUND.bend as ProofWsound

# THE GATE. `bend PROOF.bend` checks every law in LAWS.bend, each proven by a def of the same
# name below, and every law of every proof file it imports: it prints ALL PROOFS CHECK only
# when each one is proven; `--verdict` checks again with the Lean-proven kernel. A law is
# proven in its file, where it is stated again; LAWS.bend states the claims (README.md has
# every file):
#
#   The exact set
#     PROOF_GLL      the checked parser misses no step of any parse tree: gll_every_parse_step
#     PROOF_PRUNE    pruning keeps every step of every parse tree: prune_every_parse_step
#     PROOF_EXACT    the exact parser's set is exactly the steps of the parse trees: gll_bsr_exact
#     PROOF_SPELL    trees of exact steps as long as the input spell it: exact_trees_spell
#   The phases
#     PROOF_ORACLE   lookahead, @left, @right (phase 1) and @prefer, @avoid (phase 2): the
#                    oracle's set embeds exactly the chosen trees: oracle_exact
#     PROOF_EXTENT   the chosen set is exact, and @longest, @shortest (phase 3) keep exactly the
#                    selected trees: extent_exact
#     PROOF_RULE     on a grammar without a preference cycle no rival comes back: no_self_rival
#   The twin answers (with fuel 1 + twice the size of the descriptor universe)
#     PROOF_RUN      the engine finishes and the checked parser answers: checked_always_answers
#     PROOF_ANSWER   the pruned, exact and predicting parsers answer: exact_parser_answers,
#                    predicted_parser_answers
#     PROOF_ORACLE_ANSWERS, PROOF_EXTENT_ANSWERS  the oracles answer: oracle_answers,
#                    chosen_answers, extent_answers
#   LL(1) and prediction
#     PROOF_PREDICT  prediction misses no step of any parse tree: predict_every_parse_step
#     PROOF_SUPPORT  a supported state is within a closed one, and the LL(1) parser has no
#                    dead wood: predict_saves_work, ll1_no_dead_wood
#     PROOF_TABLES   no conflict by the tables means LL(1): tables_ll1_sound
#     PROOF_LL1      an LL(1) grammar is unambiguous, LL(1) at x decides x: ll1_unambiguous, ll1_at
#     PROOF_LL1_AT_TABLES  the same at one nonterminal: tables_ll1_at, seeds_one_at
#
#
# The rest are the steps of these proofs.

def Laws.gll_every_parse_step(fuel, grammar, start, input, set, got):
  ProofGll.gll_every_parse_step(fuel, grammar, start, input, set, got)

def Laws.prune_every_parse_step(fuel, grammar, start, input, set, got):
  ProofPrune.prune_every_parse_step(fuel, grammar, start, input, set, got)

def Laws.gll_bsr_exact(fuel, grammar, start, input, set, got):
  ProofExact.gll_bsr_exact(fuel, grammar, start, input, set, got)

def Laws.exact_trees_spell(fuel, grammar, start, input, set, got, tree, fitting, inSet, long):
  ProofSpell.exact_trees_spell(fuel, grammar, start, input, set, got, tree, fitting, inSet, long)

def Laws.oracle_exact(fuel, grammar, gmarks, rmarks, start, input, set, got):
  ProofOracle.oracle_exact(fuel, grammar, gmarks, rmarks, start, input, set, got)

def Laws.extent_exact(fuel, grammar, gmarks, rmarks, emarks, start, input, set3, got):
  ProofExtent.extent_exact(fuel, grammar, gmarks, rmarks, emarks, start, input, set3, got)

def Laws.no_self_rival(grammar, marks, q, m, ch, real, o, wf, fit, full):
  ProofRule.no_self_rival(grammar, marks, q, m, ch, real, o, wf, fit, full)

def Laws.checked_always_answers(pred, grammar, start, input):
  ProofRun.checked_always_answers(pred, grammar, start, input)

def Laws.exact_parser_answers(grammar, start, input):
  ProofAnswer.exact_parser_answers(grammar, start, input)

def Laws.predicted_parser_answers(grammar, start, input):
  ProofAnswer.predicted_parser_answers(grammar, start, input)

def Laws.oracle_answers(grammar, gmarks, rmarks, start, input):
  ProofOracleAnswers.oracle_answers(grammar, gmarks, rmarks, start, input)

def Laws.chosen_answers(grammar, gmarks, rmarks, start, input):
  ProofExtentAnswers.chosen_answers(grammar, gmarks, rmarks, start, input)

def Laws.extent_answers(grammar, gmarks, rmarks, emarks, start, input):
  ProofExtentAnswers.extent_answers(grammar, gmarks, rmarks, emarks, start, input)

def Laws.predict_every_parse_step(fuel, grammar, start, input, set, got):
  ProofPredict.predict_every_parse_step(fuel, grammar, start, input, set, got)

def Laws.predict_saves_work(fuelPlain, fuelOther, pr, grammar, start, input, plain, other, gotPlain, gotOther):
  ProofSupport.predict_saves_work(fuelPlain, fuelOther, pr, grammar, start, input, plain, other, gotPlain, gotOther)

def Laws.ll1_no_dead_wood(fuel, grammar, start, input, set, tree, pt, got):
  ProofSupport.ll1_no_dead_wood(fuel, grammar, start, input, set, tree, pt, got)

def Laws.tables_ll1_sound(fuel, grammar, start, ok):
  ProofTables.tables_ll1_sound(fuel, grammar, start, ok)

def Laws.ll1_unambiguous(grammar, start, input, tree1, tree2, ll1, rr1, rl1, rr2, rl2):
  ProofLl1.ll1_unambiguous(grammar, start, input, tree1, tree2, ll1, rr1, rl1, rr2, rl2)

def Laws.ll1_at(grammar, start, input1, input2, tree1, tree2, x, q1, q2, k, ll1, rr1, rl1, rr2, rl2, l1, l2, n1, n2, same):
  ProofLl1.ll1_at(grammar, start, input1, input2, tree1, tree2, x, q1, q2, k, ll1, rr1, rl1, rr2, rl2, l1, l2, n1, n2, same)

def Laws.tables_ll1_at(fuel, grammar, start, x, ok):
  ProofLl1AtTables.tables_ll1_at(fuel, grammar, start, x, ok)

def Laws.seeds_one_at(fuel, grammar, start, x, q1, q2, tok, ok, neq, l1, l2, a1, a2):
  ProofLl1AtTables.seeds_one_at(fuel, grammar, start, x, q1, q2, tok, ok, neq, l1, l2, a1, a2)

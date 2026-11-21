import Base
import ./CORE.bend as Core
import ./GLL.bend as Gll
import ./CHECK.bend as Check
import ./RUN.bend as Run
import ./PRUNE.bend as Prune
import ./EXACT.bend as Exact
import ./GUARD.bend as Guard
import ./PREFER.bend as Prefer
import ./ORACLE.bend as Oracle
import ./EXTENT.bend as Extent
import ./SETS.bend as Sets
import ./LL1.bend as LL
import ./TABLES.bend as T
import ./PREDICT.bend as Pr
import ./SUPPORT.bend as Sup
import ./PROOF_RUN.bend as R
import ./PROOF_NEEDS.bend as N
import ./PROOF_GROW.bend as GW
import ./PROOF_RULE.bend as Rule

# THE LAWS: every claim, and nothing else. `bend PROOF.bend` checks that each one is proven.
#
# HOW TO READ A LAW. `law name:` is followed by lines `for x: T`, one per input or assumption,
# and ends with the conclusion. Read it as: "for every x of type T, ..., the conclusion holds".
# An assumption is an input too: `for got: {f(...) == Some{set} : ...}` means "suppose f handed
# out the answer `set`". `{a == b : T}` says that a equals b; `{c == True{} : Bool}` says that
# the check c holds. A conclusion `Empty` means the assumptions cannot all hold at once.
#
# THE WORDS. A grammar is a list of productions on the BNF core (CORE.bend); a grammar as
# written means its translation to the core (EBNF.bend). A parse tree reads the whole input
# from the start symbol. A step (`Bsr`) is one link of a tree: "production q, after its first
# d items, reads the input from i to j, its last item from k". The exact set of an input is
# the set of steps of all its parse trees. Fuel bounds how long an algorithm may run; the
# descriptor universe (`Run.univ`) is every parser task the grammar and input allow, so its
# size is a bound that never runs out. The parsers and oracles themselves are not trusted:
# what they hand out has passed a check.
#
# WHAT A LAW PROMISES. Most laws say what an answer means ("whenever `exactSteps` hands out a
# set, ..."); the answer laws (below) say that an answer always comes, with the fuel given.
# Four statements use a small predicate from a proof file: `R.isAnswer` and `N.isSteps` (an
# answer came), `GW.tableSize` (the size of the LL(1) tables) and `Rule.FullAt` (a node over
# all the tokens).

# ======== THE EXACT SET ========

# THE CHECKED PARSER MISSES NOTHING. Whenever the checked GLL parser hands out a set of steps,
# every step of every parse tree of the input is in it.
law gll_every_parse_step:
  for fuel: Nat
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Core.Bsr>
  for +got: {Check.checkedSteps(fuel, grammar, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>}
  Core.EveryParseStep(grammar, start, input, set)

# PRUNING KEEPS EVERY TREE STEP. Whenever the pruned parser hands out a set of steps, every
# step of every parse tree of the input is in it.
law prune_every_parse_step:
  for fuel: Nat
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Core.Bsr>
  for +got: {Prune.prunedSteps(fuel, grammar, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>}
  Core.EveryParseStep(grammar, start, input, set)

# THE EXACT PARSER IS EXACT. Whenever `exactSteps` hands out a set, it holds the steps of the
# parse trees of the input, and nothing else.
law gll_bsr_exact:
  for fuel: Nat
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Core.Bsr>
  for +got: {Exact.exactSteps(fuel, grammar, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>}
  Core.IsExact(grammar, start, input, set)

# TREES FROM THE EXACT SET SPELL THE INPUT. A tree that fits the start symbol, uses only steps
# of the exact set and has as many leaves as the input has tokens, has exactly the input as
# its leaves. So whatever tree an oracle picks from the set is a parse tree.
law exact_trees_spell:
  for fuel: Nat
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Core.Bsr>
  for +got: {Exact.exactSteps(fuel, grammar, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>}
  for +tree: Core.Tree
  for +fitting: {Core.fits([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}]) == True{} : Bool}
  for +inSet: {Core.allIn(Core.steps([tree], 0n), set) == True{} : Bool}
  for +long: {List.length(&2, Nat, Core.leaves([tree])) == List.length(&2, Nat, input) : Nat}
  {Core.leaves([tree]) == input : +List<Nat>}

# ======== THE PHASES ========

# THE ORACLE KEEPS EXACTLY THE CHOSEN TREES (phases 1 and 2). Whenever the oracle hands out a
# set, a parse tree uses only steps of that set exactly when it is chosen: every one of its
# steps keeps the lookahead, @left and @right rules it decides (GUARD.bend), and none
# completes a node beaten by @prefer or @avoid (PREFER.bend).
law oracle_exact:
  for fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +rmarks: +List<Prefer.RankMark>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Core.Bsr>
  for +got: {Oracle.oracleSteps(fuel, grammar, gmarks, rmarks, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>}
  Oracle.EmbedsChosen(grammar, gmarks, rmarks, start, input, set)

# THE MARKS SELECT EXACTLY THE SELECTED TREES (phase 3). Whenever the selecting oracle hands
# out a set, a parse tree uses only steps of that set exactly when it is chosen and no step
# of it loses to a longer (@longest) or shorter (@shortest) reading (EXTENT.bend).
law extent_exact:
  for fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +rmarks: +List<Prefer.RankMark>
  for +emarks: +List<Extent.ExtentMark>
  for +start: Nat
  for +input: +List<Nat>
  for +set3: +List<Core.Bsr>
  for +got: {Extent.selectedSteps(fuel, grammar, gmarks, rmarks, emarks, start, input) == Some{set3} : Maybe<&2, +List<Core.Bsr>>}
  Extent.EmbedsSelected(grammar, gmarks, rmarks, emarks, start, input, set3)

# NO RIVAL COMES BACK TO ITS OWN CHOICE. On a grammar without a preference cycle
# (PREFER.bend, `noPreferenceCycle`): when production m outranks production q, children for
# m never hold a node of m's own nonterminal over all their tokens. So a rival can never be
# "the same choice again".
law no_self_rival:
  for +grammar: +List<Core.Production>
  for +marks: +List<Prefer.RankMark>
  for +q: Nat
  for +m: Nat
  for +ch: +List<Core.Tree>
  for +real: {Core.lhsIs(grammar, q, Gll.lhsOf(grammar, q)) == True{} : Bool}
  for +o: {Prefer.outranking(grammar, marks, q, m) == True{} : Bool}
  for +wf: {Prefer.noPreferenceCycle(grammar, marks) == True{} : Bool}
  for +fit: {Core.fits(ch, grammar, Core.rhsOf(grammar, m)) == True{} : Bool}
  for full: Rule.FullAt(grammar, ch, List.length(&2, Nat, Core.leaves(ch)), Gll.lhsOf(grammar, m))
  Empty

# ======== THE TWIN ANSWERS ========

# THE CHECKED PARSER ALWAYS ANSWERS. With fuel 1 + the size of the descriptor universe, the
# checked parser (with or without prediction) hands out its steps.
law checked_always_answers:
  for +pred: Gll.Pred
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  {R.isAnswer(Check.runCheckedWith(pred, Gll.parseWith(1n+List.length(&2, Gll.Desc, Run.univ(grammar, input)), pred, grammar, start, input), grammar, start, input)) == True{} : Bool}

# THE EXACT PARSER ALWAYS ANSWERS. With fuel 1 + twice the size of the descriptor universe,
# `exactSteps` hands out its steps.
law exact_parser_answers:
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  {N.isSteps(Exact.exactSteps(1n+Nat.add(List.length(&2, Gll.Desc, Run.univ(grammar, input)), List.length(&2, Gll.Desc, Run.univ(grammar, input))), grammar, start, input)) == True{} : Bool}

# THE PREDICTING PARSER ALWAYS ANSWERS. With fuel 1 + the size of the descriptor universe +
# the size of the LL(1) tables, `predictedSteps` hands out its steps.
law predicted_parser_answers:
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  {R.isAnswer(Pr.predictedSteps(1n+Nat.add(List.length(&2, Gll.Desc, Run.univ(grammar, input)), GW.tableSize(grammar, start)), grammar, start, input)) == True{} : Bool}

# THE ORACLE ALWAYS ANSWERS. With fuel 1 + twice the size of the descriptor universe,
# `oracleSteps` hands out its set, whatever the grammar, marks and input.
law oracle_answers:
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +rmarks: +List<Prefer.RankMark>
  for +start: Nat
  for +input: +List<Nat>
  {R.isAnswer(Oracle.oracleSteps(1n+Nat.add(List.length(&2, Gll.Desc, Run.univ(grammar, input)), List.length(&2, Gll.Desc, Run.univ(grammar, input))), grammar, gmarks, rmarks, start, input)) == True{} : Bool}

# THE CHOSEN SET ALWAYS COMES. With the same fuel, `chosenSteps` (the oracle's set without
# dead wood) hands out its set.
law chosen_answers:
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +rmarks: +List<Prefer.RankMark>
  for +start: Nat
  for +input: +List<Nat>
  {R.isAnswer(Extent.chosenSteps(1n+Nat.add(List.length(&2, Gll.Desc, Run.univ(grammar, input)), List.length(&2, Gll.Desc, Run.univ(grammar, input))), grammar, gmarks, rmarks, start, input)) == True{} : Bool}

# THE SELECTING ORACLE ALWAYS ANSWERS. With the same fuel, `selectedSteps` hands out its set.
law extent_answers:
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +rmarks: +List<Prefer.RankMark>
  for +emarks: +List<Extent.ExtentMark>
  for +start: Nat
  for +input: +List<Nat>
  {R.isAnswer(Extent.selectedSteps(1n+Nat.add(List.length(&2, Gll.Desc, Run.univ(grammar, input)), List.length(&2, Gll.Desc, Run.univ(grammar, input))), grammar, gmarks, rmarks, emarks, start, input)) == True{} : Bool}

# ======== LL(1) AND PREDICTION ========

# PREDICTION MISSES NOTHING. Whenever the predicting parser (it starts only the productions
# the next token allows) hands out a set of steps, every step of every parse tree is in it.
law predict_every_parse_step:
  for fuel: Nat
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Core.Bsr>
  for +got: {Pr.predictedSteps(fuel, grammar, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>}
  Core.EveryParseStep(grammar, start, input, set)

# PREDICTION ONLY SAVES WORK. When the plain parser ends in a closed state and a parser with
# any prediction ends in a supported state (every fact in it is needed, SUPPORT.bend), every
# fact of the second run is also in the first: prediction adds no task, step or edge.
law predict_saves_work:
  for fuelPlain: Nat
  for fuelOther: Nat
  for +pr: Gll.Pred
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +plain: Gll.GState
  for +other: Gll.GState
  for +gotPlain: {Sup.closedState(fuelPlain, grammar, start, input) == Some{plain} : Maybe<&2, Gll.GState>}
  for +gotOther: {Sup.supportedState(fuelOther, pr, grammar, start, input) == Some{other} : Maybe<&2, Gll.GState>}
  {Sup.factsWithin(Sup.factsOf(other), plain) == True{} : Bool}

# AN LL(1) GRAMMAR LEAVES NO DEAD WOOD. When the input has a parse tree and the LL(1) parser
# (PREDICT.bend, `ll1Steps`) hands out a set of steps, that set is exact: the steps of the
# parse trees and nothing else.
law ll1_no_dead_wood:
  for fuel: Nat
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Core.Bsr>
  for +tree: Core.Tree
  for pt: Core.ParseTree(grammar, start, input, tree)
  for +got: {Pr.ll1Steps(fuel, grammar, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>}
  Core.IsExact(grammar, start, input, set)

# THE LL(1) CHECK IS SOUND. When the check on the FIRST/FOLLOW tables finds no conflict, the
# grammar is LL(1): no two productions of one nonterminal can begin with the same next token.
law tables_ll1_sound:
  for fuel: Nat
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +ok: {T.ll1ByTables(fuel, grammar, start) == True{} : Bool}
  LL.LL1(grammar, start)

# AN LL(1) GRAMMAR IS UNAMBIGUOUS. Two parse trees of the same input are the same tree.
law ll1_unambiguous:
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +tree1: Core.Tree
  for +tree2: Core.Tree
  for ll1: LL.LL1(grammar, start)
  for +rr1: {Core.reads([tree1], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool}
  for +rl1: {List.length(&2, Nat, Core.leaves([tree1])) == List.length(&2, Nat, input) : Nat}
  for +rr2: {Core.reads([tree2], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool}
  for +rl2: {List.length(&2, Nat, Core.leaves([tree2])) == List.length(&2, Nat, input) : Nat}
  {tree1 == tree2 : Core.Tree}

# LL(1) AT ONE NONTERMINAL DECIDES IT. Where the grammar is LL(1) at x, two parse trees (of
# any inputs) with a node of x at the same position and the same next token use the same
# production of x there. So a parser may decide x by one token, even where the rest of the
# grammar is not LL(1).
law ll1_at:
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input1: +List<Nat>
  for +input2: +List<Nat>
  for +tree1: Core.Tree
  for +tree2: Core.Tree
  for +x: Nat
  for +q1: Nat
  for +q2: Nat
  for +k: Nat
  for ll1: LL.LL1At(grammar, start, x)
  for +rr1: {Core.reads([tree1], grammar, [Core.Nonterminal{start, Core.Anything{}}], input1, 0n) == True{} : Bool}
  for +rl1: {List.length(&2, Nat, Core.leaves([tree1])) == List.length(&2, Nat, input1) : Nat}
  for +rr2: {Core.reads([tree2], grammar, [Core.Nonterminal{start, Core.Anything{}}], input2, 0n) == True{} : Bool}
  for +rl2: {List.length(&2, Nat, Core.leaves([tree2])) == List.length(&2, Nat, input2) : Nat}
  for +l1: {Core.lhsIs(grammar, q1, x) == True{} : Bool}
  for +l2: {Core.lhsIs(grammar, q2, x) == True{} : Bool}
  for n1: LL.NodeAt(grammar, input1, tree1, q1, k)
  for n2: LL.NodeAt(grammar, input2, tree2, q2, k)
  for +same: {Core.tokAt(input1, k) == Core.tokAt(input2, k) : Maybe<&2, Nat>}
  {q1 == q2 : Nat}

# THE LL(1) CHECK AT ONE NONTERMINAL IS SOUND. When the check finds no conflict among x's
# productions, the grammar is LL(1) at x, whatever the rest of the grammar does.
law tables_ll1_at:
  for fuel: Nat
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +x: Nat
  for +ok: {T.ll1AtByTables(fuel, grammar, start, x) == True{} : Bool}
  LL.LL1At(grammar, start, x)

# PREDICTION STARTS AT MOST ONE PRODUCTION OF x. When x passes that check, the predicting
# parser admits no two different productions of x for the same next token.
law seeds_one_at:
  for fuel: Nat
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +x: Nat
  for +q1: Nat
  for +q2: Nat
  for +tok: Maybe<&2, Nat>
  for +ok: {T.ll1AtByTables(fuel, grammar, start, x) == True{} : Bool}
  for +neq: {Nat.is_eq(q1, q2) == False{} : Bool}
  for +l1: {Core.lhsIs(grammar, q1, x) == True{} : Bool}
  for +l2: {Core.lhsIs(grammar, q2, x) == True{} : Bool}
  for +a1: {Gll.admits(Gll.Allowed{Pr.predictSets(grammar, T.growFirsts(fuel, grammar, Sets.growNulls(fuel, grammar, []), []), T.growFollows(fuel, grammar, T.growFirsts(fuel, grammar, Sets.growNulls(fuel, grammar, []), []), Sets.growNulls(fuel, grammar, []), [T.FollowFact{start, None{}}]), Sets.growNulls(fuel, grammar, []))}, q1, tok) == True{} : Bool}
  for +a2: {Gll.admits(Gll.Allowed{Pr.predictSets(grammar, T.growFirsts(fuel, grammar, Sets.growNulls(fuel, grammar, []), []), T.growFollows(fuel, grammar, T.growFirsts(fuel, grammar, Sets.growNulls(fuel, grammar, []), []), Sets.growNulls(fuel, grammar, []), [T.FollowFact{start, None{}}]), Sets.growNulls(fuel, grammar, []))}, q2, tok) == True{} : Bool}
  Empty

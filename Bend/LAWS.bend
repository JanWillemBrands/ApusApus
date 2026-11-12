import Base
import ./SPEC.bend as Spec
import ./GLL.bend as Gll
import ./CHECK.bend as Check
import ./EXACT.bend as Exact
import ./PREFER.bend as Prefer
import ./GUARD.bend as Guard
import ./UNBEATEN.bend as Unb
import ./EXTENT.bend as Ext
import ./SUPPORT.bend as Support
import ./LL1.bend as LL1
import ./PSUPPORT.bend as PS
import ./FIRST.bend as First

# THE LAWS: every claim, and nothing else. `bend PROOF.bend` checks them all.
#
# What the laws talk about is defined in SPEC.bend. The parser (GLL.bend), the
# pruning (PRUNE.bend) and the witness search (WITNESS.bend) are not trusted: their
# output is only handed out after a check (CHECK.bend, PRUNE.bend, EXACT.bend). The same
# goes for the preference oracle (PREFER.bend).
#
# WHAT A LAW PROMISES. A law about an algorithm says what its answer means ("whenever
# `exactSteps` hands out a set, ..."), not that it hands one out: each such law also holds
# for an algorithm that never answers. An algorithm hands out nothing when it runs out of
# fuel, when a check fails, or when an oracle refuses a grammar; that it answers at all is
# not claimed here (README.md, "What the laws promise").

# REWRITING LAWS. Each bracket means its usual BNF rewriting, stated on sentential
# forms (items followed by `rest`), without ever making a helper nonterminal:
#   ( τ1 | .. | τn ) η   derives what some  τa η  derives
#   [ τ ] η              derives what  η  or  ( τ ) η  derives
#   { τ } η              derives what  η  or  ( τ ) { τ } η  derives
#   < τ > η              derives what  ( τ ) { τ } η  derives
#   ε η                  derives what  η  derives
# together with the BNF steps for symbols. Proofs of algorithms reason with these.

# NOTHING DERIVES NOTHING. An empty sequence of items derives only the empty input.
law empty_derives:
  for +grammar: +List<Spec.Production>
  for +w: +List<Nat>
  for d: Spec.Derives(grammar, [], w)
  {w == [] : +List<Nat>}

# A TERMINAL FIRST. If terminal k followed by `rest` derives w, then w starts with the
# token k, and `rest` derives the remainder w2.
law terminal_unfold:
  for +grammar: +List<Spec.Production>
  for +k: Nat
  for +rest: +List<Spec.Item>
  for +w: +List<Nat>
  for d: Spec.Derives(grammar, Spec.Sym{Spec.Terminal{k}} <> rest, w)
  exs w2: +List<Nat>
  {w == k <> w2 : +List<Nat>} & Spec.Derives(grammar, rest, w2)

# A NONTERMINAL FIRST, UNFOLDED. If nonterminal a followed by `rest` derives w, then one
# of a's productions p can take its place: p's right side followed by `rest` derives w.
# This is the BNF step a ⇒ rhs.
law nonterminal_unfold:
  for +grammar: +List<Spec.Production>
  for +a: Nat
  for +rest: +List<Spec.Item>
  for +w: +List<Nat>
  for d: Spec.Derives(grammar, Spec.Sym{Spec.Nonterminal{a}} <> rest, w)
  exs p: Nat
  {Spec.lhsIs(grammar, p, a) == True{} : Bool} & Spec.Derives(grammar, List.append(&2, Spec.Item, Spec.rhsOf(grammar, p), rest), w)

# A NONTERMINAL FIRST, FOLDED. The converse: if the right side of a production p of a,
# followed by `rest`, derives w, then a followed by `rest` derives w.
law nonterminal_fold:
  for +grammar: +List<Spec.Production>
  for +a: Nat
  for +p: Nat
  for +rest: +List<Spec.Item>
  for +w: +List<Nat>
  for lhsOk: {Spec.lhsIs(grammar, p, a) == True{} : Bool}
  for d: Spec.Derives(grammar, List.append(&2, Spec.Item, Spec.rhsOf(grammar, p), rest), w)
  Spec.Derives(grammar, Spec.Sym{Spec.Nonterminal{a}} <> rest, w)

# A GROUP, UNFOLDED. If ( τ1 | .. | τn ) followed by `rest` derives w, then one of its
# alternatives τa, written in its place, derives w.
law group_unfold:
  for +grammar: +List<Spec.Production>
  for +alts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Item>
  for +w: +List<Nat>
  for d: Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> rest, w)
  exs a: Nat
  {Spec.isAlt(alts, a) == True{} : Bool} & Spec.Derives(grammar, List.append(&2, Spec.Item, Spec.altOf(alts, a), rest), w)

# A GROUP, FOLDED. The converse: if an alternative τa followed by `rest` derives w, then
# the group followed by `rest` derives w.
law group_fold:
  for +grammar: +List<Spec.Production>
  for +alts: +List<+List<Spec.Item>>
  for +a: Nat
  for +rest: +List<Spec.Item>
  for +w: +List<Nat>
  for isA: {Spec.isAlt(alts, a) == True{} : Bool}
  for d: Spec.Derives(grammar, List.append(&2, Spec.Item, Spec.altOf(alts, a), rest), w)
  Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> rest, w)

# AN OPTIONAL, UNFOLDED. If [ τ ] followed by `rest` derives w, then either `rest` alone
# derives w (the optional matched nothing), or ( τ ) followed by `rest` does (it matched
# once).
law optional_unfold:
  for +grammar: +List<Spec.Production>
  for +alts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Item>
  for +w: +List<Nat>
  for d: Spec.Derives(grammar, Spec.Brack{Spec.Optional{}, alts} <> rest, w)
  Either<Spec.Derives(grammar, rest, w), Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> rest, w)>

# AN OPTIONAL, FOLDED. The converse: either way of deriving w also derives it through [
# τ ]. When τ matches nothing, the tree uses the skip, because a pick of [ τ ] must read
# something; the input derived is the same.
law optional_fold:
  for +grammar: +List<Spec.Production>
  for +alts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Item>
  for +w: +List<Nat>
  for d: Either<Spec.Derives(grammar, rest, w), Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> rest, w)>
  Spec.Derives(grammar, Spec.Brack{Spec.Optional{}, alts} <> rest, w)

# A CLOSURE, UNFOLDED. If { τ } followed by `rest` derives w, then either `rest` alone
# derives w (no rounds), or one round ( τ ), then the closure again, then `rest` does.
law closure_unfold:
  for +grammar: +List<Spec.Production>
  for +alts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Item>
  for +w: +List<Nat>
  for d: Spec.Derives(grammar, Spec.Brack{Spec.Closure{}, alts} <> rest, w)
  Either<Spec.Derives(grammar, rest, w), Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> Spec.Brack{Spec.Closure{}, alts} <> rest, w)>

# A CLOSURE, FOLDED. The converse: either way of deriving w also derives it through { τ
# }. A round that matches nothing is dropped, so the tree has no removable empty round;
# the input derived is the same.
law closure_fold:
  for +grammar: +List<Spec.Production>
  for +alts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Item>
  for +w: +List<Nat>
  for d: Either<Spec.Derives(grammar, rest, w), Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> Spec.Brack{Spec.Closure{}, alts} <> rest, w)>
  Spec.Derives(grammar, Spec.Brack{Spec.Closure{}, alts} <> rest, w)

# A POSITIVE CLOSURE, UNFOLDED. If < τ > followed by `rest` derives w, then one round (
# τ ), then the closure { τ }, then `rest` derives w.
law positive_unfold:
  for +grammar: +List<Spec.Production>
  for +alts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Item>
  for +w: +List<Nat>
  for d: Spec.Derives(grammar, Spec.Brack{Spec.Positive{}, alts} <> rest, w)
  Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> Spec.Brack{Spec.Closure{}, alts} <> rest, w)

# A POSITIVE CLOSURE, FOLDED. The converse: ( τ ) followed by { τ } and `rest` derives
# what < τ > followed by `rest` derives. When every round matches nothing, the tree
# keeps exactly one empty round, as the bracket rule wants.
law positive_fold:
  for +grammar: +List<Spec.Production>
  for +alts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Item>
  for +w: +List<Nat>
  for d: Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> Spec.Brack{Spec.Closure{}, alts} <> rest, w)
  Spec.Derives(grammar, Spec.Brack{Spec.Positive{}, alts} <> rest, w)

# ε, UNFOLDED. ε reads nothing: if ε followed by `rest` derives w, then `rest` alone
# derives w.
law epsilon_unfold:
  for +grammar: +List<Spec.Production>
  for +rest: +List<Spec.Item>
  for +w: +List<Nat>
  for d: Spec.Derives(grammar, Spec.Eps{} <> rest, w)
  Spec.Derives(grammar, rest, w)

# ε, FOLDED. The converse: if `rest` derives w, then ε followed by `rest` derives w.
law epsilon_fold:
  for +grammar: +List<Spec.Production>
  for +rest: +List<Spec.Item>
  for +w: +List<Nat>
  for d: Spec.Derives(grammar, rest, w)
  Spec.Derives(grammar, Spec.Eps{} <> rest, w)

# THE CHECKED GLL PARSER MISSES NOTHING. Whenever the checked GLL parser hands out a set of steps, no
# step of any parse tree of the input is missing from it. The engine itself is not
# trusted: what it hands out passed the closedness check.
law gll_every_parse_step:
  for fuel: Nat
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for got: {Check.checkedSteps(fuel, grammar, start, input) == Some{set} : Maybe<&2, +List<Spec.Bsr>>}
  Spec.EveryParseStep(grammar, start, input, set)

# THE PREDICTING GLL PARSER MISSES NOTHING. The checked parser with prediction (Scott's
# predict sets: a descriptor is started only where the token there can begin what follows
# it) hands out a set only when its tables are closed and its final state is closed for
# the descriptors prediction admits. Prediction never removes a step of a parse tree.
law predict_every_parse_step:
  for fuel: Nat
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for got: {Check.predictedSteps(fuel, grammar, start, input) == Some{set} : Maybe<&2, +List<Spec.Bsr>>}
  Spec.EveryParseStep(grammar, start, input, set)

# PREDICTION SAVES WORK. A state is supported when each of its facts can be derived from
# the root by the engine's rules (SUPPORT.bend). Whenever the plain parser's final state is
# closed and the parser's final state in any mode is supported, every fact of the second
# is in the first: its descriptors and steps among them, so it has no more of either
# (COST.bend). For the predicting parser: prediction never does more work.
law predict_saves_work:
  for fuelPlain: Nat
  for fuelOther: Nat
  for +pr: Gll.Pred
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +plain: Gll.GState
  for +other: Gll.GState
  for gotPlain: {Support.closedState(fuelPlain, grammar, start, input) == Some{plain} : Maybe<&2, Gll.GState>}
  for gotOther: {Support.supportedState(fuelOther, pr, grammar, start, input) == Some{other} : Maybe<&2, Gll.GState>}
  {Support.factsWithin(Support.factsOf(other), plain) == True{} : Bool}

# LL(1) BY THE TABLES IS LL(1): when the check of LL1.bend finds no conflict in the tables
# of FIRST.bend, the grammar is LL(1) in SPEC.bend's sense (`LL1`): at no choice point can
# two different choices begin with the same next token. The tables may be larger than the
# exact sets, so the check may report a conflict the grammar does not have; never the
# other way round.
law tables_ll1_sound:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +ok: {LL1.ll1ByTables(grammar, start, t) == True{} : Bool}
  Spec.LL1(grammar, start)

# AN LL(1) GRAMMAR IS UNAMBIGUOUS: under SPEC.bend's `LL1`, two parse trees of the same
# input are the same tree. Where two trees first differ, both choices there would predict
# the same next token, which LL(1) forbids.
law ll1_unambiguous:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for tree1: Spec.Tree
  for tree2: Spec.Tree
  for ll1: Spec.LL1(grammar, start)
  for +fit1: {Spec.fits([tree1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +fit2: {Spec.fits([tree2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +sp1: {Spec.leaves([tree1]) == input : +List<Nat>}
  for +sp2: {Spec.leaves([tree2]) == input : +List<Nat>}
  {tree1 == tree2 : Spec.Tree}

# NO DEAD WOOD FOR AN LL(1) GRAMMAR: when the input is a sentence and the tables of
# FIRST.bend pass LL1.bend's check, the checked LL(1) parser (PSUPPORT.bend: closed, and
# supported with prediction) hands out exactly the steps of the parse tree. Brackets
# included; the engine predicts the rounds of [ ] { } and the later rounds of < > by FIRST
# only (GLL.bend, predictFor).
law ll1_no_dead_wood:
  for fuel: Nat
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for +t: Gll.Tables
  for +tablesEq: {First.tablesOf(Nat.add(Nat.mul(First.ntCount(grammar), 4n), 4n), grammar, start) == Some{t} : Maybe<&2, Gll.Tables>}
  for +ll1: {LL1.ll1ByTables(grammar, start, t) == True{} : Bool}
  for +tree: Spec.Tree
  for +fit: {Spec.fits([tree], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +sp: {Spec.leaves([tree]) == input : +List<Nat>}
  for got: {PS.llSteps(fuel, grammar, start, input) == Some{set} : Maybe<&2, +List<Spec.Bsr>>}
  Spec.IsExactBsr(grammar, start, input, set)

# LL(1) AT ONE CHOICE POINT DECIDES IT: where the grammar is LL(1) at a choice point (SPEC's
# LL1At, at that point only), two parse trees, of any inputs, that make a choice there at the
# same position with the same token next make the same choice (SPEC's choicesMade). So a
# parser may predict by one token at that point, even where the grammar is not LL(1)
# elsewhere.
law ll1_at:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input1: +List<Nat>
  for +input2: +List<Nat>
  for +tree1: Spec.Tree
  for +tree2: Spec.Tree
  for +point: Spec.ChoicePoint
  for +pos: Nat
  for +choice1: Nat
  for +choice2: Nat
  for ll1: Spec.LL1At(grammar, start, point)
  for +fit1: {Spec.fits([tree1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +sp1: {Spec.leaves([tree1]) == input1 : +List<Nat>}
  for +fit2: {Spec.fits([tree2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +sp2: {Spec.leaves([tree2]) == input2 : +List<Nat>}
  for +next: {List.get(&2, Nat, input1, pos) == List.get(&2, Nat, input2, pos) : Maybe<&2, Nat>}
  for made1: Spec.Among(Spec.Made{point, pos, choice1}, Spec.choicesMade(grammar, start, tree1))
  for made2: Spec.Among(Spec.Made{point, pos, choice2}, Spec.choicesMade(grammar, start, tree2))
  {choice1 == choice2 : Nat}

# THE EXACT PARSER IS EXACT: whenever `exactSteps` hands out a set, it holds exactly
# the steps of the parse trees of the input. Nothing is missing, and every element
# is a step of some parse tree, so an oracle choosing from the set chooses among all
# parse trees, and only those.
law gll_bsr_exact:
  for fuel: Nat
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for got: {Exact.exactSteps(fuel, grammar, start, input) == Some{set} : Maybe<&2, +List<Spec.Bsr>>}
  Spec.IsExactBsr(grammar, start, input, set)

# TREES FROM THE EXACT SET SPELL THE INPUT: a tree that 1: fits the start symbol, 2: uses
# only steps of the exact parser's set, and 3: is as long as the input, spells the input.
# An oracle that picks a tree from the set cannot produce something that is not a
# parse tree. (Without the length condition this fails: for S ::= S S | a on aa, the
# tree S -> a uses only steps of the set, but spells a.)
law exact_trees_spell:
  for fuel: Nat
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for got: {Exact.exactSteps(fuel, grammar, start, input) == Some{set} : Maybe<&2, +List<Spec.Bsr>>}
  for +tree: Spec.Tree
  for fitting: {Spec.fits([tree], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for inSet: {Spec.allIn(Spec.steps(tree, 0n), set) == True{} : Bool}
  for long: {List.length(&2, Nat, Spec.leaves([tree])) == List.length(&2, Nat, input) : Nat}
  {Spec.leaves([tree]) == input : +List<Nat>}

# DISAMBIGUATION, IN THE THREE PHASES OF SPEC.bend: 1. admissible (lookahead,
# @left, @right), 2. unbeaten (@prefer, @avoid), 3. selected (@longest,
# @shortest). Each phase's oracle gets an exactness law: its set embeds exactly the
# trees of that phase.
#
# PHASE 1, ADMISSIBLE.
#
# THE RULES KEEP EXACTLY THE ADMISSIBLE TREES. Whenever the guard oracle hands out a set,
# a parse tree of the input uses only steps of that set exactly when it is admissible:
# every node, pick and round keeps the lookahead, @left and @right rules of the
# alternative it chose. So a tree read from the set breaks no rule, and no tree that
# keeps them all is lost. The oracle refuses rules on the alternatives of a loop.
law guards_exact:
  for fuel: Nat
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for got: {Guard.guardSteps(fuel, grammar, guards, start, input) == Some{set} : Maybe<&2, +List<Spec.Bsr>>}
  Spec.EmbedsAdmissible(grammar, guards, start, input, set)
#
# PHASE 2, UNBEATEN.
#
# @prefer AND @avoid CHOOSE EXACTLY THE UNBEATEN TREES. Whenever the preference oracle
# hands out a set, a parse tree of the input uses only steps of that set exactly when it
# is admissible and unbeaten: no node of it is outranked by an admissible rival. So a tree
# read from the set keeps every hard rule and made every choice the annotations ask for,
# and no tree that did is lost. The oracle runs on the guard oracle's set. It refuses a
# grammar whose preferences go round a cycle, and a loop not written { ( τ ) }.
law prefer_avoid_exact:
  for fuel: Nat
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for got: {Unb.unbeatenSteps(fuel, grammar, guards, marks, start, input) == Some{set} : Maybe<&2, +List<Spec.Bsr>>}
  Spec.EmbedsUnbeaten(grammar, guards, marks, start, input, set)

# @prefer AND @avoid LEAVE A READING. Whenever the preference oracle hands out a set and
# the input has an admissible tree, some admissible tree is unbeaten. The oracle's answer
# never throws every reading away. (Stronger, and not proven here: that preferences never
# remove every admissible tree, answer or not. Its classical proof, "it is impossible that
# no tree is unbeaten", uses a hypothesis twice, which Bend's affine logic does not allow.)
law prefer_avoid_safe:
  for fuel: Nat
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for got: {Unb.unbeatenSteps(fuel, grammar, guards, marks, start, input) == Some{set} : Maybe<&2, +List<Spec.Bsr>>}
  for tree: Spec.Tree
  for admissible: Spec.AdmissibleTree(grammar, guards, start, input, tree)
  Spec.SomeUnbeaten(grammar, guards, marks, start, input)
#
# LOCALITY. The phases judge a node by what it reads, not by how its children read it:
# a node's rules look only at its first and last child's tokens and the tokens ahead,
# its rivals only at its tokens and context, and an extent only at its children's
# lengths. So a node's children can be swapped for another forest over the same tokens
# that keeps the phases where it stands, and the tree still keeps them. Grammar
# transforms that preserve the selected trees rest on this.

# The rules on a sequence's children depend on their first and last spelling only.
law holds_local:
  for +grammar: +List<Spec.Production>
  for gs: +List<Spec.Guard>
  for +items: +List<Spec.Item>
  for +f: +List<Spec.Tree>
  for +f2: +List<Spec.Tree>
  for +ahead: +List<Nat>
  for +eF: {Spec.firstSpell(f2) == Spec.firstSpell(f) : Maybe<&2, +List<Nat>>}
  for +eL: {Spec.lastSpell(f2) == Spec.lastSpell(f) : Maybe<&2, +List<Nat>>}
  for h: Spec.AllHold(grammar, gs, items, f, ahead)
  Spec.AllHold(grammar, gs, items, f2, ahead)

# Swapping a tree for one that spells the same keeps the first and last spelling.
law spells_swap:
  for +t: Spec.Tree
  for +t2: Spec.Tree
  for +ts: +List<Spec.Tree>
  for +lv: {Spec.leaves([t2]) == Spec.leaves([t]) : +List<Nat>}
  {Spec.firstSpell(t2 <> ts) == Spec.firstSpell(t <> ts) : Maybe<&2, +List<Nat>>} & {Spec.lastSpell(t2 <> ts) == Spec.lastSpell(t <> ts) : Maybe<&2, +List<Nat>>}

# ... and the lengths an extent compares.
law measures_swap:
  for +marks: +List<Spec.ExtentMark>
  for +t: Spec.Tree
  for +t2: Spec.Tree
  for +ts: +List<Spec.Tree>
  for +items: +List<Spec.Item>
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +lv: {Spec.leaves([t2]) == Spec.leaves([t]) : +List<Nat>}
  {Spec.measures(marks, t2 <> ts, items, index, prefix, dot) == Spec.measures(marks, t <> ts, items, index, prefix, dot) : +List<Spec.Measure>}

# A node's children swapped for an admissible forest over the same tokens: still admissible.
law admissible_swap_node:
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +q: Nat
  for +ch: +List<Spec.Tree>
  for +ch2: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +x: Nat
  for +rest: +List<Spec.Item>
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +after: +List<Nat>
  for +lv: {Spec.leaves(ch2) == Spec.leaves(ch) : +List<Nat>}
  for hold2: Spec.AllHold(grammar, Spec.prodGuards(guards, q), Spec.rhsOf(grammar, q), ch2, List.append(&2, Nat, Spec.leaves(ch2), List.append(&2, Nat, Spec.leaves(ts), after)))
  for adm2: Spec.Admissible(grammar, guards, ch2, Spec.rhsOf(grammar, q), q, [], 0n, List.append(&2, Nat, Spec.leaves(ts), after))
  for adm: Spec.Admissible(grammar, guards, Spec.Node{q, ch} <> ts, Spec.Sym{Spec.Nonterminal{x}} <> rest, index, prefix, dot, after)
  Spec.Admissible(grammar, guards, Spec.Node{q, ch2} <> ts, Spec.Sym{Spec.Nonterminal{x}} <> rest, index, prefix, dot, after)

law admissible_swap_pick:
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +ch2: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Item>
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +after: +List<Nat>
  for +lv: {Spec.leaves(ch2) == Spec.leaves(ch) : +List<Nat>}
  for hold2: Spec.AllHold(grammar, Spec.altGuards(guards, index, List.append(&2, Nat, prefix, [dot]), a), Spec.altOf(alts, a), ch2, List.append(&2, Nat, Spec.leaves(ch2), List.append(&2, Nat, Spec.leaves(ts), after)))
  for adm2: Spec.Admissible(grammar, guards, ch2, Spec.altOf(alts, a), index, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a]), 0n, List.append(&2, Nat, Spec.leaves(ts), after))
  for adm: Spec.Admissible(grammar, guards, Spec.Pick{a, ch} <> ts, Spec.Brack{kind, alts} <> rest, index, prefix, dot, after)
  Spec.Admissible(grammar, guards, Spec.Pick{a, ch2} <> ts, Spec.Brack{kind, alts} <> rest, index, prefix, dot, after)

# A node's children swapped for an unbeaten forest over the same tokens: still unbeaten.
law unbeaten_swap_node:
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +q: Nat
  for +ch: +List<Spec.Tree>
  for +ch2: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +x: Nat
  for +rest: +List<Spec.Item>
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +after: +List<Nat>
  for +lv: {Spec.leaves(ch2) == Spec.leaves(ch) : +List<Nat>}
  for unb2: Spec.Unbeaten(grammar, guards, marks, ch2, Spec.rhsOf(grammar, q), q, [], 0n, x <> Spec.sameAbove(above, span, Spec.leaves(ch)), Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(ts), after))
  for unb: Spec.Unbeaten(grammar, guards, marks, Spec.Node{q, ch} <> ts, Spec.Sym{Spec.Nonterminal{x}} <> rest, index, prefix, dot, above, span, after)
  Spec.Unbeaten(grammar, guards, marks, Spec.Node{q, ch2} <> ts, Spec.Sym{Spec.Nonterminal{x}} <> rest, index, prefix, dot, above, span, after)

law unbeaten_swap_pick:
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +ch2: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Item>
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +after: +List<Nat>
  for +lv: {Spec.leaves(ch2) == Spec.leaves(ch) : +List<Nat>}
  for unb2: Spec.Unbeaten(grammar, guards, marks, ch2, Spec.altOf(alts, a), index, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a]), 0n, Spec.sameAbove(above, span, Spec.leaves(ch)), Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(ts), after))
  for unb: Spec.Unbeaten(grammar, guards, marks, Spec.Pick{a, ch} <> ts, Spec.Brack{kind, alts} <> rest, index, prefix, dot, above, span, after)
  Spec.Unbeaten(grammar, guards, marks, Spec.Pick{a, ch2} <> ts, Spec.Brack{kind, alts} <> rest, index, prefix, dot, above, span, after)
#
# PHASE 3, SELECTED.
#
# @longest AND @shortest KEEP EXACTLY THE SELECTED TREES. Whenever the extent oracle
# hands out a set, a parse tree of the input uses only steps of that set exactly when it
# is admissible, unbeaten, and has the best extent: at every node, pick and round, no
# other reading of the same children's tokens that phases 1 and 2 keep there gives the
# marked item a longer span (@longest) or a shorter one (@shortest). The comparison is
# local: it looks at the one sequence the mark sits in. So a tree read from the set took
# the extent the annotation asks for everywhere, and no tree that did is lost. The
# oracle refuses two marks in one sequence and a mark on the alternative of a loop.
law extent_exact:
  for fuel: Nat
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +pmarks: +List<Spec.Mark>
  for +marks: +List<Spec.ExtentMark>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for got: {Ext.extentSteps(fuel, grammar, guards, pmarks, marks, start, input) == Some{set} : Maybe<&2, +List<Spec.Bsr>>}
  Spec.EmbedsExtentBest(grammar, guards, pmarks, marks, start, input, set)

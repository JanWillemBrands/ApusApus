import Base
import ./SPEC.bend as Spec
import ./GLL.bend as Gll
import ./CHECK.bend as Check
import ./EXACT.bend as Exact
import ./PREFER.bend as Prefer

# THE LAWS: every claim, and nothing else. `bend PROOF.bend` checks them all.
#
# What the laws talk about is defined in SPEC.bend. The parser (GLL.bend), the
# pruning (PRUNE.bend) and the witness search (WITNESS.bend) are not trusted: their
# output is only handed out after a check (CHECK.bend, PRUNE.bend, EXACT.bend). The same
# goes for the preference oracle (PREFER.bend).

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

# @prefer AND @avoid CHOOSE EXACTLY THE SELECTED TREES. Whenever the preference oracle
# hands out a set, a parse tree of the input uses only steps of that set exactly when it
# is selected: no node of it is outranked. So a tree read from the set made every choice
# the annotations ask for, and no tree that did is lost. The oracle refuses a grammar
# whose preferences go round a cycle, and a loop not written { ( τ ) }.
law prefer_avoid_exact:
  for fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.Mark>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for got: {Prefer.preferSteps(fuel, grammar, marks, start, input) == Some{set} : Maybe<&2, +List<Spec.Bsr>>}
  Spec.EmbedsSelected(grammar, marks, start, input, set)

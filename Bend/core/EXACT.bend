import Base
import ./CORE.bend as Core
import ./PRUNE.bend as Prune
import ./WITNESS.bend as Witness

# THE EXACT PARSER: the checked GLL parser, pruned, with witness trees for every kept step.
# It hands out the pruned steps only when every witness is a parse tree of the input (by
# CORE.bend's own `reads`) and every kept step is a step of one of them (by CORE.bend's own
# `steps`).

def treeOk(+grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +t: Core.Tree) -> Bool:
  Bool.and(Core.reads([t], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n), Nat.is_eq(List.length(&2, Nat, Core.leaves([t])), List.length(&2, Nat, input)))

def allTreesOk(ws: +List<Core.Tree>, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Con{+t, rest}:
      Bool.and(treeOk(grammar, start, input, t), allTreesOk(rest, grammar, start, input))

def allCovered(ps: +List<Core.Bsr>, +ws: +List<Core.Tree>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Con{+e, rest}:
      Bool.and(Witness.coveredBy(e, ws), allCovered(rest, ws))

def exactPick(ok: Bool, +ps: +List<Core.Bsr>) -> Maybe<&2, +List<Core.Bsr>>:
  match ok:
    case True{}:
      Some{ps}
    case False{}:
      None{}

def exactFrom(found: Maybe<&2, +List<Core.Bsr>>, +fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>) -> Maybe<&2, +List<Core.Bsr>>:
  match found:
    case Some{+ps}:
      +ws = Witness.witnesses(fuel, grammar, start, input, ps)
      exactPick(Bool.and(allTreesOk(ws, grammar, start, input), allCovered(ps, ws)), ps)
    case None{}:
      None{}

def exactSteps(fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>) -> Maybe<&2, +List<Core.Bsr>>:
  +f = fuel
  exactFrom(Prune.prunedSteps(f, grammar, start, input), f, grammar, start, input)

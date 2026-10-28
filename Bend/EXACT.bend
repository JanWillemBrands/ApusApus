import Base
import ./SPEC.bend as Spec
import ./GLL.bend as Gll
import ./PRUNE.bend as Prune
import ./WITNESS.bend as Witness

# THE EXACT PARSER: the checked GLL parser, pruned, with witness trees for every kept
# step. It hands out the pruned steps only when every witness is a parse tree of the
# input (by SPEC.bend's own `fits` and `leaves`), every kept step is a step of one of
# them (by SPEC.bend's own `steps`), and every step after a terminal matches the input
# token at its position.

def treeOk(+grammar: +List<Spec.Production>, +start: Nat, +input: +List<Nat>, +t: Spec.Tree) -> Bool:
  Bool.and(Spec.fits([t], grammar, [Spec.Sym{Spec.Nonterminal{start}}]), Gll.natsEq(Spec.leaves([t]), input))

def allTreesOk(ws: +List<Spec.Tree>, +grammar: +List<Spec.Production>, +start: Nat, +input: +List<Nat>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Con{+t, rest}:
      Bool.and(treeOk(grammar, start, input, t), allTreesOk(rest, grammar, start, input))

# Is the step a step of one of the trees?
def coveredBy(+e: Spec.Bsr, ws: +List<Spec.Tree>) -> Bool:
  match ws:
    case Nil{}:
      False{}
    case Con{+t, rest}:
      Bool.or(Spec.bsrMember(e, Spec.steps(t, 0n)), coveredBy(e, rest))

def allCovered(ps: +List<Spec.Bsr>, +ws: +List<Spec.Tree>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Con{+e, rest}:
      Bool.and(coveredBy(e, ws), allCovered(rest, ws))

def witnessed(+grammar: +List<Spec.Production>, +start: Nat, +input: +List<Nat>, +ps: +List<Spec.Bsr>, +ws: +List<Spec.Tree>) -> Bool:
  Bool.and(allTreesOk(ws, grammar, start, input), allCovered(ps, ws))

# Does every step after a terminal match the input token at its position?
def tokenItemOk(item: Maybe<&2, Spec.Item>, +input: +List<Nat>, +k: Nat, +j: Nat) -> Bool:
  match item:
    case Some{Spec.Sym{Spec.Terminal{+t}}}:
      Bool.and(Gll.tokenIs(List.get(&2, Nat, input, k), t), Nat.is_eq(j, 1n+k))
    case _:
      True{}

def tokenOkAt(rev: +List<Nat>, +grammar: +List<Spec.Production>, +input: +List<Nat>, +index: Nat, +k: Nat, +j: Nat) -> Bool:
  match rev:
    case Con{1n+(+d), +rp}:
      tokenItemOk(Gll.nthItem(Gll.seqAt(grammar, index, rp), d), input, k, j)
    case _:
      True{}

def tokenOk(+grammar: +List<Spec.Production>, +input: +List<Nat>, e: Spec.Bsr) -> Bool:
  match e:
    case Spec.Bsr{Spec.Slot{+index, path}, i, +k, +j}:
      tokenOkAt(Gll.reverseOnto(path, []), grammar, input, index, k, j)

def allTokensOk(ps: +List<Spec.Bsr>, +grammar: +List<Spec.Production>, +input: +List<Nat>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Con{+e, rest}:
      Bool.and(tokenOk(grammar, input, e), allTokensOk(rest, grammar, input))

def exactPick(ok: Bool, +ps: +List<Spec.Bsr>) -> Maybe<&2, +List<Spec.Bsr>>:
  match ok:
    case True{}:
      Some{ps}
    case False{}:
      None{}

def exactFrom(found: Maybe<&2, +List<Spec.Bsr>>, fuel: Nat, +grammar: +List<Spec.Production>, +start: Nat, +input: +List<Nat>) -> Maybe<&2, +List<Spec.Bsr>>:
  match found:
    case Some{+ps}:
      exactPick(Bool.and(witnessed(grammar, start, input, ps, Witness.witnesses(fuel, grammar, start, input, ps)), allTokensOk(ps, grammar, input)), ps)
    case None{}:
      None{}

def exactSteps(fuel: Nat, +grammar: +List<Spec.Production>, +start: Nat, +input: +List<Nat>) -> Maybe<&2, +List<Spec.Bsr>>:
  +f = fuel
  exactFrom(Prune.prunedSteps(f, grammar, start, input), f, grammar, start, input)

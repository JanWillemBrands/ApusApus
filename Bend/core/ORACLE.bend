import Base
import ./CORE.bend as Core
import ./EXACT.bend as Exact
import ./GUARD.bend as Guard
import ./PREFER.bend as Prefer

# THE ORACLE ON THE CORE: the exact set, filtered a step at a time. A step is kept when it
# keeps the rules it decides (phase 1, GUARD.bend) and completes no beaten node (phase 2,
# PREFER.bend); the oracle answers nothing when some verdict is Unknown.

# ======== THE MEANING ========

def StepOk(+grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +start: Nat, +input: +List<Nat>, +x: Core.Bsr) -> Type:
  Guard.StepOk(grammar, gmarks, input, x) & Prefer.Free(grammar, gmarks, rmarks, input, x)

def AllStepsOk(+grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +start: Nat, +input: +List<Nat>, xs: +List<Core.Bsr>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{+x, rest}:
      StepOk(grammar, gmarks, rmarks, start, input, x) & AllStepsOk(grammar, gmarks, rmarks, start, input, rest)

# A chosen tree: each of its steps keeps its rules and completes no beaten node.
def Chosen(+grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +start: Nat, +input: +List<Nat>, +tree: Core.Tree) -> Type:
  AllStepsOk(grammar, gmarks, rmarks, start, input, Core.steps([tree], 0n))

# A set that embeds exactly the chosen trees: a parse tree of the input uses only steps of
# the set when, and only when, it is chosen. (The set may hold other steps too.)
def EmbedsChosen(+grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>) -> Type:
  @tree: Core.Tree -> Core.ParseTree(grammar, start, input, tree) ->
    ({Core.allIn(Core.steps([tree], 0n), set) == True{} : Bool} -> Chosen(grammar, gmarks, rmarks, start, input, tree)) &
    (Chosen(grammar, gmarks, rmarks, start, input, tree) -> {Core.allIn(Core.steps([tree], 0n), set) == True{} : Bool})

# ======== THE FILTER ========

def stepTri(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +start: Nat, +input: +List<Nat>, +x: Core.Bsr) -> Guard.Tri:
  Guard.andTri(Guard.stepTri(fuel, grammar, gmarks, input, x), Prefer.rankTri(fuel, grammar, gmarks, rmarks, input, x))

def anyUnknown(set: +List<Core.Bsr>, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +start: Nat, +input: +List<Nat>) -> Bool:
  match set:
    case Nil{}:
      False{}
    case Con{+e, rest}:
      Bool.or(Guard.isUnknown(stepTri(fuel, grammar, gmarks, rmarks, start, input, e)), anyUnknown(rest, fuel, grammar, gmarks, rmarks, start, input))

def keepIf(b: Bool, +e: Core.Bsr, es: +List<Core.Bsr>) -> +List<Core.Bsr>:
  match b:
    case True{}:
      e <> es
    case False{}:
      es

def keepYes(set: +List<Core.Bsr>, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +start: Nat, +input: +List<Nat>) -> +List<Core.Bsr>:
  match set:
    case Nil{}:
      []
    case Con{+e, rest}:
      keepIf(Guard.isYes(stepTri(fuel, grammar, gmarks, rmarks, start, input, e)), e, keepYes(rest, fuel, grammar, gmarks, rmarks, start, input))

def oraclePick(unknown: Bool, +ex: +List<Core.Bsr>, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +start: Nat, +input: +List<Nat>) -> Maybe<&2, +List<Core.Bsr>>:
  match unknown:
    case True{}:
      None{}
    case False{}:
      Some{keepYes(ex, fuel, grammar, gmarks, rmarks, start, input)}

def oracleFrom(found: Maybe<&2, +List<Core.Bsr>>, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +start: Nat, +input: +List<Nat>) -> Maybe<&2, +List<Core.Bsr>>:
  match found:
    case Some{+ex}:
      oraclePick(anyUnknown(ex, fuel, grammar, gmarks, rmarks, start, input), ex, fuel, grammar, gmarks, rmarks, start, input)
    case None{}:
      None{}

# THE ORACLE: the exact set without the steps that break a rule or complete a beaten node.
def oracleSteps(fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +start: Nat, +input: +List<Nat>) -> Maybe<&2, +List<Core.Bsr>>:
  +f = fuel
  oracleFrom(Exact.exactSteps(f, grammar, start, input), f, grammar, gmarks, rmarks, start, input)

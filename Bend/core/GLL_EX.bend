import Base
import ../SPEC.bend as Spec
import ../CHECK.bend as Old
import ../EXACT.bend as OldExact
import ./CORE.bend as Core
import ./EBNF.bend as E
import ./CHECK.bend as Check
import ./EBNF_EX.bend as X

# The core engine on the examples' translations: the check accepts its final state, and its
# steps, mapped to Swift's slots, contain the example tree's steps.

def holds(m: Maybe<&2, +List<Core.Bsr>>, +origins: +List<E.Origin>, +want: +List<Spec.Bsr>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{+set}:
      Spec.allIn(want, E.stepsToSwift(origins, set))

def runs(+g: +List<Spec.Production>, +input: +List<Nat>, +written: Spec.Tree) -> Bool:
  +tr = E.towardsSwift(g)
  holds(Check.checkedSteps(200n, E.coreOf(tr), 0n, input), E.originsIn(tr), Spec.steps(written, 0n))

# The same set as today's checked parser, after the step map?
def same(m: Maybe<&2, +List<Core.Bsr>>, +origins: +List<E.Origin>, old: Maybe<&2, +List<Spec.Bsr>>) -> Bool:
  match m old:
    case Some{+set} Some{+o}:
      Spec.sameSet(E.stepsToSwift(origins, set), o)
    case _ _:
      False{}

def sameAsToday(+g: +List<Spec.Production>, +input: +List<Nat>) -> Bool:
  +tr = E.towardsSwift(g)
  same(Check.checkedSteps(200n, E.coreOf(tr), 0n, input), E.originsIn(tr), Old.checkedSteps(200n, g, 0n, input))

law optional_runs:
  {Bool.and(runs(X.optional(), [1n, 2n], Spec.Node{0n, [Spec.Leaf{1n}, Spec.Pick{0n, [Spec.Leaf{2n}]}]}), runs(X.optional(), [1n], Spec.Node{0n, [Spec.Leaf{1n}, Spec.Skip{}]})) == True{} : Bool}

def optional_runs():
  {==}

law closure_runs:
  {runs(X.closure(), [3n, 3n], Spec.Node{0n, [Spec.Loop{[Spec.Pick{0n, [Spec.Pick{0n, [Spec.Leaf{3n}]}]}, Spec.Pick{0n, [Spec.Pick{0n, [Spec.Leaf{3n}]}]}]}]}) == True{} : Bool}

def closure_runs():
  {==}

law positive_runs:
  {Bool.and(runs(X.positive(), [], Spec.Node{0n, [Spec.Loop{[Spec.Pick{0n, [Spec.Pick{1n, [Spec.Skip{}]}]}]}]}),
    runs(X.positive(), [4n, 4n], Spec.Node{0n, [Spec.Loop{[Spec.Pick{0n, [Spec.Pick{0n, [Spec.Leaf{4n}]}]}, Spec.Pick{0n, [Spec.Pick{0n, [Spec.Leaf{4n}]}]}]}]})) == True{} : Bool}

def positive_runs():
  {==}

law today_optional:
  {Bool.and(sameAsToday(X.optional(), [1n, 2n]), sameAsToday(X.optional(), [1n])) == True{} : Bool}

def today_optional():
  {==}

law today_closure:
  {Bool.and(sameAsToday(X.closure(), [3n, 3n]), sameAsToday(X.closure(), [])) == True{} : Bool}

def today_closure():
  {==}

def coreIn(m: Maybe<&2, +List<Core.Bsr>>, +origins: +List<E.Origin>, old: Maybe<&2, +List<Spec.Bsr>>) -> Bool:
  match m old:
    case Some{+set} Some{+o}:
      Spec.allIn(E.stepsToSwift(origins, set), o)
    case _ _:
      False{}

def oldIn(m: Maybe<&2, +List<Core.Bsr>>, +origins: +List<E.Origin>, old: Maybe<&2, +List<Spec.Bsr>>) -> Bool:
  match m old:
    case Some{+set} Some{+o}:
      Spec.allIn(o, E.stepsToSwift(origins, set))
    case _ _:
      False{}

law p_empty_core_in_old:
  {coreIn(Check.checkedSteps(200n, E.coreOf(E.towardsSwift(X.positive())), 0n, []), E.originsIn(E.towardsSwift(X.positive())), Old.checkedSteps(200n, X.positive(), 0n, [])) == True{} : Bool}

def p_empty_core_in_old():
  {==}

law p_empty_old_in_core:
  {oldIn(Check.checkedSteps(200n, E.coreOf(E.towardsSwift(X.positive())), 0n, []), E.originsIn(E.towardsSwift(X.positive())), Old.checkedSteps(200n, X.positive(), 0n, [])) == True{} : Bool}

def p_empty_old_in_core():
  {==}

law p_two_core_in_old:
  {coreIn(Check.checkedSteps(200n, E.coreOf(E.towardsSwift(X.positive())), 0n, [4n, 4n]), E.originsIn(E.towardsSwift(X.positive())), Old.checkedSteps(200n, X.positive(), 0n, [4n, 4n])) == True{} : Bool}

def p_two_core_in_old():
  {==}

# Today's raw set has more dead wood here (it starts empty later rounds, which its pruning
# removes); its exact set is in the core's raw set.
law p_two_exact_in_core:
  {oldIn(Check.checkedSteps(200n, E.coreOf(E.towardsSwift(X.positive())), 0n, [4n, 4n]), E.originsIn(E.towardsSwift(X.positive())), OldExact.exactSteps(200n, X.positive(), 0n, [4n, 4n])) == True{} : Bool}

def p_two_exact_in_core():
  {==}

law today_group:
  {sameAsToday(X.group(), [2n]) == True{} : Bool}

def today_group():
  {==}

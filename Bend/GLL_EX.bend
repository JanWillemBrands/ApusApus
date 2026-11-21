import Base
import ./SYNTAX.bend as Spec
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

def runs(+g: +List<Spec.Production>, +input: +List<Nat>, +want: +List<Spec.Bsr>) -> Bool:
  +tr = E.towardsSwift(g)
  holds(Check.checkedSteps(200n, E.coreOf(tr), 0n, input), E.originsIn(tr), want)

law optional_runs:
  {Bool.and(runs(X.optional(), [1n, 2n], X.stepsOf_optional_pick()), runs(X.optional(), [1n], X.stepsOf_optional_skip())) == True{} : Bool}

def optional_runs():
  {==}

law closure_runs:
  {runs(X.closure(), [3n, 3n], X.stepsOf_closure_two()) == True{} : Bool}

def closure_runs():
  {==}

law positive_runs:
  {Bool.and(runs(X.positive(), [], X.stepsOf_positive_empty()),
    runs(X.positive(), [4n, 4n], X.stepsOf_positive_two())) == True{} : Bool}

def positive_runs():
  {==}

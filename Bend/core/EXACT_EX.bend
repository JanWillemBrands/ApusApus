import Base
import ../SPEC.bend as Spec
import ../EXACT.bend as OldExact
import ./CORE.bend as Core
import ./EBNF.bend as E
import ./PRUNE.bend as Prune
import ./EXACT.bend as Exact
import ./EBNF_EX.bend as X

# The core's exact parser, mapped to Swift's slots, gives today's exact set on the examples.

def same(m: Maybe<&2, +List<Core.Bsr>>, +origins: +List<E.Origin>, old: Maybe<&2, +List<Spec.Bsr>>) -> Bool:
  match m old:
    case Some{+set} Some{+o}:
      Spec.sameSet(E.stepsToSwift(origins, set), o)
    case _ _:
      False{}

def agrees(+g: +List<Spec.Production>, +input: +List<Nat>) -> Bool:
  +tr = E.towardsSwift(g)
  same(Exact.exactSteps(30n, E.coreOf(tr), 0n, input), E.originsIn(tr), OldExact.exactSteps(300n, g, 0n, input))

law optional_exact:
  {Bool.and(agrees(X.optional(), [1n, 2n]), agrees(X.optional(), [1n])) == True{} : Bool}

def optional_exact():
  {==}

law closure_exact:
  {Bool.and(agrees(X.closure(), [3n, 3n]), agrees(X.closure(), [])) == True{} : Bool}

def closure_exact():
  {==}

law positive_exact:
  {Bool.and(agrees(X.positive(), []), agrees(X.positive(), [4n, 4n])) == True{} : Bool}

def positive_exact():
  {==}

law group_exact:
  {agrees(X.group(), [2n]) == True{} : Bool}

def group_exact():
  {==}

# A cyclic grammar, A = A | a: infinitely many trees over "a", one finite set of steps. The
# exact parser answers (keyed facts, no list of trees), with both steps of A.
def cyclic() -> +List<Core.Production>:
  [Core.Production{0n, [Core.Nonterminal{0n, Core.Anything{}}]}, Core.Production{0n, [Core.Terminal{1n}]}]

def answers(m: Maybe<&2, +List<Core.Bsr>>) -> Bool:
  match m:
    case Some{+set}:
      Bool.and(Core.member(Core.Bsr{0n, 1n, 0n, 0n, 1n}, set), Core.member(Core.Bsr{1n, 1n, 0n, 0n, 1n}, set))
    case None{}:
      False{}

law cyclic_answers:
  {answers(Exact.exactSteps(30n, cyclic(), 0n, [1n])) == True{} : Bool}

def cyclic_answers():
  {==}

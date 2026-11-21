import Base
import ./SYNTAX.bend as Spec
import ./CORE.bend as Core
import ./EBNF.bend as E
import ./PRUNE.bend as Prune
import ./EXACT.bend as Exact
import ./EBNF_EX.bend as X

# The core's exact parser, mapped to Swift's slots, gives the expected exact set on the
# examples: the steps of their parse trees.

# THE EXPECTED EXACT SETS, IN SWIFT'S SLOTS.

def exact_closure_3_3() -> Maybe<&2, +List<Spec.Bsr>>:
  Some{[Spec.Bsr{Spec.Slot{0n, [1n]}, 0n, 0n, 2n}, Spec.Bsr{Spec.Slot{0n, [0n, 0n, 1n]}, 0n, 1n, 2n}, Spec.Bsr{Spec.Slot{0n, [0n, 0n, 0n, 0n, 1n]}, 1n, 1n, 2n}, Spec.Bsr{Spec.Slot{0n, [0n, 0n, 1n]}, 0n, 0n, 1n}, Spec.Bsr{Spec.Slot{0n, [0n, 0n, 0n, 0n, 1n]}, 0n, 0n, 1n}]}

def exact_closure_none() -> Maybe<&2, +List<Spec.Bsr>>:
  Some{[Spec.Bsr{Spec.Slot{0n, [1n]}, 0n, 0n, 0n}]}

def exact_group_2() -> Maybe<&2, +List<Spec.Bsr>>:
  Some{[Spec.Bsr{Spec.Slot{0n, [2n]}, 0n, 0n, 1n}, Spec.Bsr{Spec.Slot{0n, [1n]}, 0n, 0n, 0n}, Spec.Bsr{Spec.Slot{0n, [0n, 1n, 1n]}, 0n, 0n, 0n}]}

def exact_optional_1() -> Maybe<&2, +List<Spec.Bsr>>:
  Some{[Spec.Bsr{Spec.Slot{0n, [2n]}, 0n, 1n, 1n}, Spec.Bsr{Spec.Slot{0n, [1n]}, 0n, 0n, 1n}]}

def exact_optional_1_2() -> Maybe<&2, +List<Spec.Bsr>>:
  Some{[Spec.Bsr{Spec.Slot{0n, [2n]}, 0n, 1n, 2n}, Spec.Bsr{Spec.Slot{0n, [1n, 0n, 1n]}, 1n, 1n, 2n}, Spec.Bsr{Spec.Slot{0n, [1n]}, 0n, 0n, 1n}]}

def exact_positive_4_4() -> Maybe<&2, +List<Spec.Bsr>>:
  Some{[Spec.Bsr{Spec.Slot{0n, [1n]}, 0n, 0n, 2n}, Spec.Bsr{Spec.Slot{0n, [0n, 0n, 1n]}, 0n, 1n, 2n}, Spec.Bsr{Spec.Slot{0n, [0n, 0n, 0n, 0n, 1n]}, 1n, 1n, 2n}, Spec.Bsr{Spec.Slot{0n, [0n, 0n, 1n]}, 0n, 0n, 1n}, Spec.Bsr{Spec.Slot{0n, [0n, 0n, 0n, 0n, 1n]}, 0n, 0n, 1n}]}

def exact_positive_none() -> Maybe<&2, +List<Spec.Bsr>>:
  Some{[Spec.Bsr{Spec.Slot{0n, [1n]}, 0n, 0n, 0n}, Spec.Bsr{Spec.Slot{0n, [0n, 0n, 1n]}, 0n, 0n, 0n}, Spec.Bsr{Spec.Slot{0n, [0n, 0n, 0n, 1n, 1n]}, 0n, 0n, 0n}]}

def same(m: Maybe<&2, +List<Core.Bsr>>, +origins: +List<E.Origin>, old: Maybe<&2, +List<Spec.Bsr>>) -> Bool:
  match m old:
    case Some{+set} Some{+o}:
      Spec.sameSet(E.stepsToSwift(origins, set), o)
    case _ _:
      False{}

def agrees(+g: +List<Spec.Production>, +input: +List<Nat>, old: Maybe<&2, +List<Spec.Bsr>>) -> Bool:
  +tr = E.towardsSwift(g)
  same(Exact.exactSteps(30n, E.coreOf(tr), 0n, input), E.originsIn(tr), old)

law optional_exact:
  {Bool.and(agrees(X.optional(), [1n, 2n], exact_optional_1_2()), agrees(X.optional(), [1n], exact_optional_1())) == True{} : Bool}

def optional_exact():
  {==}

law closure_exact:
  {Bool.and(agrees(X.closure(), [3n, 3n], exact_closure_3_3()), agrees(X.closure(), [], exact_closure_none())) == True{} : Bool}

def closure_exact():
  {==}

law positive_exact:
  {Bool.and(agrees(X.positive(), [], exact_positive_none()), agrees(X.positive(), [4n, 4n], exact_positive_4_4())) == True{} : Bool}

def positive_exact():
  {==}

law group_exact:
  {agrees(X.group(), [2n], exact_group_2()) == True{} : Bool}

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

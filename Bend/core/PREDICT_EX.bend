import Base
import ./CORE.bend as Core
import ./PREDICT.bend as Pr
import ./CHECK.bend as Check

# THE PREDICTING PARSER ON EXAMPLES.

def t(+k: Nat) -> Core.Sym:
  Core.Terminal{k}

def n(+x: Nat) -> Core.Sym:
  Core.Nonterminal{x, Core.Anything{}}

def kept(m: Maybe<&2, +List<Core.Bsr>>, +tr: Core.Tree) -> Bool:
  match m:
    case Some{+set}:
      Core.allIn(Core.steps([tr], 0n), set)
    case None{}:
      False{}

def has(m: Maybe<&2, +List<Core.Bsr>>, +x: Core.Bsr) -> Bool:
  match m:
    case Some{+set}:
      Core.member(x, set)
    case None{}:
      False{}

# S = X | Y, X = a, Y = b, on a: Y is not started, and the tree is found.
def choice() -> +List<Core.Production>:
  [Core.Production{0n, [n(1n)]}, Core.Production{0n, [n(2n)]}, Core.Production{1n, [t(1n)]}, Core.Production{2n, [t(2n)]}]

law choice_kept:
  {kept(Pr.predictedSteps(20n, choice(), 0n, [1n]), Core.Node{0n, [Core.Node{2n, [Core.Leaf{1n}]}]}) == True{} : Bool}

def choice_kept():
  {==}

# S = A b, A = a | ε, on b: A -> ε is predicted by FOLLOW, so the tree is found.
def follows() -> +List<Core.Production>:
  [Core.Production{0n, [n(1n), t(2n)]}, Core.Production{1n, [t(1n)]}, Core.Production{1n, []}]

law follow_kept:
  {kept(Pr.predictedSteps(20n, follows(), 0n, [2n]), Core.Node{0n, [Core.Node{2n, []}, Core.Leaf{2n}]}) == True{} : Bool}

def follow_kept():
  {==}

# On b the production A -> a is never started, so its step is not there.
law not_started:
  {has(Pr.predictedSteps(20n, follows(), 0n, [2n]), Core.Bsr{1n, 1n, 0n, 0n, 1n}) == False{} : Bool}

def not_started():
  {==}

# ======== THE LL(1) PARSER ========

def exact(m: Maybe<&2, +List<Core.Bsr>>, +tr: Core.Tree) -> Bool:
  match m:
    case Some{+set}:
      Bool.and(Core.allIn(Core.steps([tr], 0n), set), Core.allIn(set, Core.steps([tr], 0n)))
    case None{}:
      False{}

def isNone(m: Maybe<&2, +List<Core.Bsr>>) -> Bool:
  match m:
    case Some{set}:
      False{}
    case None{}:
      True{}

# S = X a | Y b, X = ε, Y = ε, on b. The plain parser also completes X -> ε at 0 (dead
# wood); the LL(1) parser starts only S -> Y b, and its set is the tree's steps.
def empties() -> +List<Core.Production>:
  [Core.Production{0n, [n(1n), t(1n)]}, Core.Production{0n, [n(2n), t(2n)]}, Core.Production{1n, []}, Core.Production{2n, []}]

def emptiesTree() -> Core.Tree:
  Core.Node{1n, [Core.Node{3n, []}, Core.Leaf{2n}]}

law ll1_exact:
  {exact(Pr.ll1Steps(30n, empties(), 0n, [2n]), emptiesTree()) == True{} : Bool}

def ll1_exact():
  {==}

law plain_dead_wood:
  {has(Check.checkedSteps(30n, empties(), 0n, [2n]), Core.Bsr{2n, 0n, 0n, 0n, 0n}) == True{} : Bool}

def plain_dead_wood():
  {==}

# On b, the follow example's LL(1) set is exactly its tree's steps too.
law ll1_follow_exact:
  {exact(Pr.ll1Steps(30n, follows(), 0n, [2n]), Core.Node{0n, [Core.Node{2n, []}, Core.Leaf{2n}]}) == True{} : Bool}

def ll1_follow_exact():
  {==}

# S = a | a is not LL(1): the LL(1) parser gives no answer.
def twice() -> +List<Core.Production>:
  [Core.Production{0n, [t(1n)]}, Core.Production{0n, [t(1n)]}]

law not_ll1:
  {isNone(Pr.ll1Steps(30n, twice(), 0n, [1n])) == True{} : Bool}

def not_ll1():
  {==}

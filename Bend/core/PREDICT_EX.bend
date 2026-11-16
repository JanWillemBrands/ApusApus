import Base
import ./CORE.bend as Core
import ./PREDICT.bend as Pr

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

import Base
import ./CORE.bend as Core
import ./GLL.bend as Gll
import ./SUPPORT.bend as Sup
import ./PREFER.bend as Prefer
import ./TABLES.bend as T
import ./PREDICT.bend as Pr

# SUPPORT ON EXAMPLES: the plain and the predicting runs are supported, and the predicting
# run's facts are all facts of the plain run.

def t(+k: Nat) -> Core.Sym:
  Core.Terminal{k}

def n(+x: Nat) -> Core.Sym:
  Core.Nonterminal{x, Core.Anything{}}

# S = A b, A = a | ε.
def g() -> +List<Core.Production>:
  [Core.Production{0n, [n(1n), t(2n)]}, Core.Production{1n, [t(1n)]}, Core.Production{1n, []}]

def pred() -> Gll.Pred:
  +nulls = Prefer.growNulls(10n, g(), [])
  +firsts = T.growFirsts(10n, g(), nulls, [])
  Gll.Allowed{Pr.predictSets(g(), firsts, T.growFollows(10n, g(), firsts, nulls, [T.FollowFact{0n, None{}}]), nulls)}

def answered(m: Maybe<&2, Gll.GState>) -> Bool:
  match m:
    case Some{s}:
      True{}
    case None{}:
      False{}

def within2(+sa: Gll.GState, b: Maybe<&2, Gll.GState>) -> Bool:
  match b:
    case Some{+sb}:
      Sup.factsWithin(Sup.factsOf(sa), sb)
    case None{}:
      False{}

def within(a: Maybe<&2, Gll.GState>, +b: Maybe<&2, Gll.GState>) -> Bool:
  match a:
    case Some{+sa}:
      within2(sa, b)
    case None{}:
      False{}

law plain_supported:
  {answered(Sup.supportedState(20n, Gll.NoPred{}, g(), 0n, [2n])) == True{} : Bool}

def plain_supported():
  {==}

law predicted_supported:
  {answered(Sup.supportedState(20n, pred(), g(), 0n, [2n])) == True{} : Bool}

def predicted_supported():
  {==}

law saves:
  {within(Sup.supportedState(20n, pred(), g(), 0n, [2n]), Sup.closedState(20n, g(), 0n, [2n])) == True{} : Bool}

def saves():
  {==}

# The plain run starts A -> a at 0 on b; the predicting one does not.
law plain_does_more:
  {within(Sup.closedState(20n, g(), 0n, [2n]), Sup.supportedState(20n, pred(), g(), 0n, [2n])) == False{} : Bool}

def plain_does_more():
  {==}

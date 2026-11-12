import Base
import ./SPEC.bend as Spec
import ./GLL.bend as Gll
import ./CHECK.bend as Check
import ./FIRST.bend as First
import ./SUPPORT.bend as Support

# IS A STATE SUPPORTED WITH PREDICTION? As SUPPORT.bend, but a rule gives a descriptor (and
# the step that comes with it) only when prediction admits it, as the engine's withDescP
# and withPairP do. Not trusted: it is a check. With NoPred it is SUPPORT.bend's check.

def descWhen(+pr: Gll.Pred, +grammar: +List<Spec.Production>, +input: +List<Nat>, +d: Gll.Desc) -> +List<Support.Fact>:
  Support.whenTrue(Gll.admits(pr, grammar, input, d), [Support.FactDescriptor{d}])

def descsWhen(+pr: Gll.Pred, +grammar: +List<Spec.Production>, +input: +List<Nat>, ds: +List<Gll.Desc>) -> +List<Support.Fact>:
  match ds:
    case Nil{}:
      []
    case Con{+d, rest}:
      List.append(&2, Support.Fact, descWhen(pr, grammar, input, d), descsWhen(pr, grammar, input, rest))

def pairWhen(+pr: Gll.Pred, +grammar: +List<Spec.Production>, +input: +List<Nat>, +d: Gll.Desc, +y: Spec.Bsr) -> +List<Support.Fact>:
  Support.whenTrue(Gll.admits(pr, grammar, input, d), [Support.FactDescriptor{d}, Support.FactStep{y}])

# What a seen descriptor gives, by the item at its dot.
def itemGives(item: Maybe<&2, Spec.Item>, +pr: Gll.Pred, +grammar: +List<Spec.Production>, +input: +List<Nat>, +index: Nat, +rpath: +List<Nat>, +dot: Nat, +k: Nat, +i: Nat) -> +List<Support.Fact>:
  match item:
    case Some{Spec.Sym{Spec.Terminal{+t}}}:
      Support.whenTrue(Gll.tokenIs(List.get(&2, Nat, input, i), t), pairWhen(pr, grammar, input, Gll.Desc{index, rpath, 1n+dot, k, 1n+i}, Gll.stepAt(index, rpath, 1n+dot, k, i, 1n+i)))
    case Some{Spec.Sym{Spec.Nonterminal{+x}}}:
      [Support.FactCluster{Gll.CKey{Gll.TNt{x}, i}}, Support.FactReturn{Gll.CKey{Gll.TNt{x}, i}, Gll.Edge{index, rpath, dot, k}}]
    case Some{Spec.Brack{+kind, alts}}:
      Support.FactCluster{Gll.CKey{Gll.TBr{index, dot <> rpath}, i}} <> Support.FactReturn{Gll.CKey{Gll.TBr{index, dot <> rpath}, i}, Gll.Edge{index, rpath, dot, k}} <>
        Support.whenTrue(Gll.isSkippable(kind), pairWhen(pr, grammar, input, Gll.Desc{index, rpath, 1n+dot, k, i}, Gll.stepAt(index, rpath, 1n+dot, k, i, i)))
    case Some{Spec.Eps{}}:
      pairWhen(pr, grammar, input, Gll.Desc{index, rpath, 1n+dot, k, i}, Gll.stepAt(index, rpath, 1n+dot, k, i, i))
    case None{}:
      Support.FactPop{Check.endKey(grammar, index, rpath, k), i} <> Support.emptyStep(dot, index, rpath, k, i)

def resumeGives(+pr: Gll.Pred, +grammar: +List<Spec.Production>, +input: +List<Nat>, +key: Gll.CKey, edge: Gll.Edge, +end: Nat) -> +List<Support.Fact>:
  match edge:
    case Gll.Edge{+index, +rpath, +dot, +k}:
      pairWhen(pr, grammar, input, Gll.Desc{index, rpath, 1n+dot, k, end}, Gll.stepAt(index, rpath, 1n+dot, k, Check.keyStart(key), end))

def edgeGives(+pr: Gll.Pred, +grammar: +List<Spec.Production>, +input: +List<Nat>, reached: +List<Support.Fact>, +key: Gll.CKey, +edge: Gll.Edge) -> +List<Support.Fact>:
  match reached:
    case Nil{}:
      []
    case Con{Support.FactPop{+popKey, +end}, rest}:
      List.append(&2, Support.Fact, Support.whenTrue(Gll.keyEq(key, popKey), resumeGives(pr, grammar, input, key, edge, end)), edgeGives(pr, grammar, input, rest, key, edge))
    case Con{other, rest}:
      edgeGives(pr, grammar, input, rest, key, edge)

def popGives(+pr: Gll.Pred, +grammar: +List<Spec.Production>, +input: +List<Nat>, reached: +List<Support.Fact>, +key: Gll.CKey, +end: Nat) -> +List<Support.Fact>:
  match reached:
    case Nil{}:
      []
    case Con{Support.FactReturn{+edgeKey, +edge}, rest}:
      List.append(&2, Support.Fact, Support.whenTrue(Gll.keyEq(edgeKey, key), resumeGives(pr, grammar, input, edgeKey, edge, end)), popGives(pr, grammar, input, rest, key, end))
    case Con{other, rest}:
      popGives(pr, grammar, input, rest, key, end)

def factGives(fact: Support.Fact, +pr: Gll.Pred, +grammar: +List<Spec.Production>, +input: +List<Nat>, +reached: +List<Support.Fact>) -> +List<Support.Fact>:
  match fact:
    case Support.FactDescriptor{Gll.Desc{+index, +rpath, +dot, +k, +i}}:
      itemGives(Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), pr, grammar, input, index, rpath, dot, k, i)
    case Support.FactCluster{+key}:
      descsWhen(pr, grammar, input, Check.seedsOf(grammar, key))
    case Support.FactReturn{+key, +edge}:
      edgeGives(pr, grammar, input, reached, key, edge)
    case Support.FactPop{+key, +end}:
      List.append(&2, Support.Fact, popGives(pr, grammar, input, reached, key, end), descsWhen(pr, grammar, input, Check.againOfKey(grammar, key, end)))
    case Support.FactStep{y}:
      []

def allGive(facts: +List<Support.Fact>, +pr: Gll.Pred, +grammar: +List<Spec.Production>, +input: +List<Nat>, +reached: +List<Support.Fact>) -> +List<Support.Fact>:
  match facts:
    case Nil{}:
      []
    case Con{+fact, rest}:
      List.append(&2, Support.Fact, factGives(fact, pr, grammar, input, reached), allGive(rest, pr, grammar, input, reached))

def round(+pr: Gll.Pred, +grammar: +List<Spec.Production>, +input: +List<Nat>, +s: Gll.GState, +reached: +List<Support.Fact>) -> +List<Support.Fact>:
  Support.addWithin(allGive(reached, pr, grammar, input, reached), s, reached)

def grow(n: Nat, +pr: Gll.Pred, +grammar: +List<Spec.Production>, +input: +List<Nat>, +s: Gll.GState, reached: +List<Support.Fact>) -> +List<Support.Fact>:
  match n:
    case 0n:
      reached
    case 1n+m:
      grow(m, pr, grammar, input, s, round(pr, grammar, input, s, reached))

# The root: the start symbol's cluster at 0 and the seeds prediction admits.
def roots(+pr: Gll.Pred, +grammar: +List<Spec.Production>, +input: +List<Nat>, +start: Nat) -> +List<Support.Fact>:
  Support.FactCluster{Gll.CKey{Gll.TNt{start}, 0n}} <> descsWhen(pr, grammar, input, Gll.productionsOf(grammar, start, 0n, 0n))

def supportedWith(+pr: Gll.Pred, +grammar: +List<Spec.Production>, +start: Nat, +input: +List<Nat>, +s: Gll.GState) -> Bool:
  +facts = Support.factsOf(s)
  +reached = grow(List.length(&2, Support.Fact, facts), pr, grammar, input, s, Support.addWithin(roots(pr, grammar, input, start), s, []))
  Support.allReached(facts, reached)

# THE CHECKED LL(1) PARSER: the predicting engine's steps, handed out only when its final
# state is closed for the descriptors prediction admits (nothing missing, CHECK.bend) and
# supported with prediction (nothing the engine's rules could not give).
def runLL(r: Gll.GRun, +pr: Gll.Pred, +grammar: +List<Spec.Production>, +start: Nat, +input: +List<Nat>) -> Maybe<&2, +List<Spec.Bsr>>:
  match r:
    case Gll.GDone{+s}:
      Check.checkPick(Bool.and(Bool.and(Check.closedWith(pr, grammar, input, s), Check.clusterIn(Gll.CKey{Gll.TNt{start}, 0n}, s)), supportedWith(pr, grammar, start, input, s)), s)
    case Gll.OutOfFuel{s}:
      None{}

def llPick(tables: Maybe<&2, Gll.Tables>, fuel: Nat, +grammar: +List<Spec.Production>, +start: Nat, +input: +List<Nat>) -> Maybe<&2, +List<Spec.Bsr>>:
  match tables:
    case Some{+t}:
      runLL(Gll.parseWith(fuel, Gll.Predict{t}, grammar, start, input), Gll.Predict{t}, grammar, start, input)
    case None{}:
      None{}

def llSteps(fuel: Nat, +grammar: +List<Spec.Production>, +start: Nat, +input: +List<Nat>) -> Maybe<&2, +List<Spec.Bsr>>:
  llPick(First.tablesOf(Nat.add(Nat.mul(First.ntCount(grammar), 4n), 4n), grammar, start), fuel, grammar, start, input)

# A grammar without brackets: every item is a token, a nonterminal or ε.
def itemsPlain(items: +List<Spec.Item>) -> Bool:
  match items:
    case Nil{}:
      True{}
    case Con{Spec.Brack{kind, alts}, rest}:
      False{}
    case Con{Spec.Sym{s}, rest}:
      itemsPlain(rest)
    case Con{Spec.Eps{}, rest}:
      itemsPlain(rest)

def withoutBrackets(grammar: +List<Spec.Production>) -> Bool:
  match grammar:
    case Nil{}:
      True{}
    case Con{Spec.Production{lhs, rhs}, rest}:
      Bool.and(itemsPlain(rhs), withoutBrackets(rest))

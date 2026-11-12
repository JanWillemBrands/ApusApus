import Base
import ./SPEC.bend as Spec
import ./GLL.bend as Gll
import ./CHECK.bend as Check

# IS A STATE SUPPORTED? Every fact of it can be derived from the root by the engine's rules
# (the rules of the closedness check, CHECK.bend), using only facts of the state. Not
# trusted: the facts reached are grown here round by round, and the state is supported
# when they include all of its facts. Prediction plays no part: the predicting engine
# applies the same rules, only fewer of them, so its state is supported too.

# One fact of a state, of any kind.
type Fact is Data:
  FactDescriptor{descriptor: Gll.Desc}
  FactCluster{key: Gll.CKey}
  FactReturn{key: Gll.CKey, edge: Gll.Edge}
  FactPop{key: Gll.CKey, end: Nat}
  FactStep{step: Spec.Bsr}

def factEqual(a: Fact, b: Fact) -> Bool:
  match a b:
    case FactDescriptor{x} FactDescriptor{y}:
      Gll.descEq(x, y)
    case FactCluster{x} FactCluster{y}:
      Gll.keyEq(x, y)
    case FactReturn{k1, e1} FactReturn{k2, e2}:
      Bool.and(Gll.keyEq(k1, k2), Gll.edgeEq(e1, e2))
    case FactPop{k1, j1} FactPop{k2, j2}:
      Bool.and(Gll.keyEq(k1, k2), Nat.is_eq(j1, j2))
    case FactStep{x} FactStep{y}:
      Spec.bsrMember(x, [y])
    case _ _:
      False{}

def factIn(+fact: Fact, facts: +List<Fact>) -> Bool:
  match facts:
    case Nil{}:
      False{}
    case Con{other, rest}:
      Bool.or(factEqual(fact, other), factIn(fact, rest))

# Is the fact in the state?
def inState(fact: Fact, +s: Gll.GState) -> Bool:
  match fact:
    case FactDescriptor{+d}:
      Check.descSeen(d, s)
    case FactCluster{+key}:
      Check.clusterIn(key, s)
    case FactReturn{+key, +edge}:
      Check.returnIn(key, edge, s)
    case FactPop{+key, +end}:
      Check.popIn(key, end, s)
    case FactStep{+y}:
      Check.stepIn(y, s)

def descriptorFacts(descriptors: +List<Gll.Desc>) -> +List<Fact>:
  match descriptors:
    case Nil{}:
      []
    case Con{+d, rest}:
      FactDescriptor{d} <> descriptorFacts(rest)

def clusterFacts(clusters: +List<Gll.CKey>) -> +List<Fact>:
  match clusters:
    case Nil{}:
      []
    case Con{+key, rest}:
      FactCluster{key} <> clusterFacts(rest)

def returnFacts(returns: +List<Gll.Ret>) -> +List<Fact>:
  match returns:
    case Nil{}:
      []
    case Con{Gll.Ret{+key, +edge}, rest}:
      FactReturn{key, edge} <> returnFacts(rest)

def popFacts(pops: +List<Gll.Pop>) -> +List<Fact>:
  match pops:
    case Nil{}:
      []
    case Con{Gll.Pop{+key, +end}, rest}:
      FactPop{key, end} <> popFacts(rest)

def stepFacts(steps: +List<Spec.Bsr>) -> +List<Fact>:
  match steps:
    case Nil{}:
      []
    case Con{+y, rest}:
      FactStep{y} <> stepFacts(rest)

# All facts of a state.
def factsOf(s: Gll.GState) -> +List<Fact>:
  match s:
    case Gll.GState{seen, todo, clusters, returns, pops, steps}:
      List.append(&2, Fact, descriptorFacts(seen), List.append(&2, Fact, clusterFacts(clusters), List.append(&2, Fact, returnFacts(returns), List.append(&2, Fact, popFacts(pops), stepFacts(steps)))))

# ---- The rules: what a fact gives, with the facts reached so far ----

def whenTrue(condition: Bool, +facts: +List<Fact>) -> +List<Fact>:
  match condition:
    case True{}:
      facts
    case False{}:
      []

# The step of an empty sequence.
def emptyStep(dot: Nat, +index: Nat, +rpath: +List<Nat>, +k: Nat, +i: Nat) -> +List<Fact>:
  match dot:
    case 0n:
      [FactStep{Gll.stepAt(index, rpath, 0n, k, i, i)}]
    case 1n+d:
      []

# What a seen descriptor gives, by the item at its dot (as in Check.itemOk).
def itemGives(item: Maybe<&2, Spec.Item>, +grammar: +List<Spec.Production>, +input: +List<Nat>, +index: Nat, +rpath: +List<Nat>, +dot: Nat, +k: Nat, +i: Nat) -> +List<Fact>:
  match item:
    case Some{Spec.Sym{Spec.Terminal{+t}}}:
      whenTrue(Gll.tokenIs(List.get(&2, Nat, input, i), t), [FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, 1n+i}}, FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, 1n+i)}])
    case Some{Spec.Sym{Spec.Nonterminal{+x}}}:
      [FactCluster{Gll.CKey{Gll.TNt{x}, i}}, FactReturn{Gll.CKey{Gll.TNt{x}, i}, Gll.Edge{index, rpath, dot, k}}]
    case Some{Spec.Brack{+kind, alts}}:
      FactCluster{Gll.CKey{Gll.TBr{index, dot <> rpath}, i}} <> FactReturn{Gll.CKey{Gll.TBr{index, dot <> rpath}, i}, Gll.Edge{index, rpath, dot, k}} <> whenTrue(Gll.isSkippable(kind), [FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, i}}, FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, i)}])
    case Some{Spec.Eps{}}:
      [FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, i}}, FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, i)}]
    case None{}:
      FactPop{Check.endKey(grammar, index, rpath, k), i} <> emptyStep(dot, index, rpath, k, i)

# A return edge resumes at a pop of its cluster.
def resumeGives(+key: Gll.CKey, edge: Gll.Edge, +end: Nat) -> +List<Fact>:
  match edge:
    case Gll.Edge{+index, +rpath, +dot, +k}:
      [FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, end}}, FactStep{Gll.stepAt(index, rpath, 1n+dot, k, Check.keyStart(key), end)}]

# A return edge against the pops reached.
def edgeGives(reached: +List<Fact>, +key: Gll.CKey, +edge: Gll.Edge) -> +List<Fact>:
  match reached:
    case Nil{}:
      []
    case Con{FactPop{+popKey, +end}, rest}:
      List.append(&2, Fact, whenTrue(Gll.keyEq(key, popKey), resumeGives(key, edge, end)), edgeGives(rest, key, edge))
    case Con{other, rest}:
      edgeGives(rest, key, edge)

# A pop against the return edges reached.
def popGives(reached: +List<Fact>, +key: Gll.CKey, +end: Nat) -> +List<Fact>:
  match reached:
    case Nil{}:
      []
    case Con{FactReturn{+edgeKey, +edge}, rest}:
      List.append(&2, Fact, whenTrue(Gll.keyEq(edgeKey, key), resumeGives(edgeKey, edge, end)), popGives(rest, key, end))
    case Con{other, rest}:
      popGives(rest, key, end)

def factGives(fact: Fact, +grammar: +List<Spec.Production>, +input: +List<Nat>, +reached: +List<Fact>) -> +List<Fact>:
  match fact:
    case FactDescriptor{Gll.Desc{+index, +rpath, +dot, +k, +i}}:
      itemGives(Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), grammar, input, index, rpath, dot, k, i)
    case FactCluster{+key}:
      descriptorFacts(Check.seedsOf(grammar, key))
    case FactReturn{+key, +edge}:
      edgeGives(reached, key, edge)
    case FactPop{+key, +end}:
      List.append(&2, Fact, popGives(reached, key, end), descriptorFacts(Check.againOfKey(grammar, key, end)))
    case FactStep{y}:
      []

def allGive(facts: +List<Fact>, +grammar: +List<Spec.Production>, +input: +List<Nat>, +reached: +List<Fact>) -> +List<Fact>:
  match facts:
    case Nil{}:
      []
    case Con{+fact, rest}:
      List.append(&2, Fact, factGives(fact, grammar, input, reached), allGive(rest, grammar, input, reached))

# ---- Growing the facts reached, within the state ----

def keepPick(keep: Bool, +fact: Fact, facts: +List<Fact>) -> +List<Fact>:
  match keep:
    case True{}:
      fact <> facts
    case False{}:
      facts

# Add the new facts that are in the state and not reached yet.
def addWithin(new: +List<Fact>, +s: Gll.GState, +reached: +List<Fact>) -> +List<Fact>:
  match new:
    case Nil{}:
      reached
    case Con{+fact, rest}:
      addWithin(rest, s, keepPick(Bool.and(inState(fact, s), Bool.not(factIn(fact, reached))), fact, reached))

def round(+grammar: +List<Spec.Production>, +input: +List<Nat>, +s: Gll.GState, +reached: +List<Fact>) -> +List<Fact>:
  addWithin(allGive(reached, grammar, input, reached), s, reached)

def grow(n: Nat, +grammar: +List<Spec.Production>, +input: +List<Nat>, +s: Gll.GState, reached: +List<Fact>) -> +List<Fact>:
  match n:
    case 0n:
      reached
    case 1n+m:
      grow(m, grammar, input, s, round(grammar, input, s, reached))

# The root: the start symbol's cluster at 0 and its seeds.
def roots(+grammar: +List<Spec.Production>, +start: Nat) -> +List<Fact>:
  FactCluster{Gll.CKey{Gll.TNt{start}, 0n}} <> descriptorFacts(Gll.productionsOf(grammar, start, 0n, 0n))

def allReached(facts: +List<Fact>, +reached: +List<Fact>) -> Bool:
  match facts:
    case Nil{}:
      True{}
    case Con{+fact, rest}:
      Bool.and(factIn(fact, reached), allReached(rest, reached))

# Every fact of the state is reached from the roots within as many rounds as it has facts.
def supported(+grammar: +List<Spec.Production>, +start: Nat, +input: +List<Nat>, +s: Gll.GState) -> Bool:
  +facts = factsOf(s)
  +reached = grow(List.length(&2, Fact, facts), grammar, input, s, addWithin(roots(grammar, start), s, []))
  allReached(facts, reached)

# ---- The states the laws talk about ----

def statePick(ok: Bool, +s: Gll.GState) -> Maybe<&2, Gll.GState>:
  match ok:
    case True{}:
      Some{s}
    case False{}:
      None{}

def closedPick(r: Gll.GRun, +grammar: +List<Spec.Production>, +start: Nat, +input: +List<Nat>) -> Maybe<&2, Gll.GState>:
  match r:
    case Gll.GDone{+s}:
      statePick(Bool.and(Check.closed(grammar, input, s), Check.clusterIn(Gll.CKey{Gll.TNt{start}, 0n}, s)), s)
    case Gll.OutOfFuel{s}:
      None{}

# The plain parser's final state, when it is closed and has the root cluster.
def closedState(fuel: Nat, +grammar: +List<Spec.Production>, +start: Nat, +input: +List<Nat>) -> Maybe<&2, Gll.GState>:
  closedPick(Gll.parse(fuel, grammar, start, input), grammar, start, input)

def supportedPick(r: Gll.GRun, +grammar: +List<Spec.Production>, +start: Nat, +input: +List<Nat>) -> Maybe<&2, Gll.GState>:
  match r:
    case Gll.GDone{+s}:
      statePick(supported(grammar, start, input, s), s)
    case Gll.OutOfFuel{s}:
      None{}

# The engine's final state in the given mode, when it is supported.
def supportedState(fuel: Nat, +pr: Gll.Pred, +grammar: +List<Spec.Production>, +start: Nat, +input: +List<Nat>) -> Maybe<&2, Gll.GState>:
  supportedPick(Gll.parseWith(fuel, pr, grammar, start, input), grammar, start, input)

# Every fact of `smaller` is in `larger`.
def factsWithin(facts: +List<Fact>, +larger: Gll.GState) -> Bool:
  match facts:
    case Nil{}:
      True{}
    case Con{+fact, rest}:
      Bool.and(inState(fact, larger), factsWithin(rest, larger))

import Base
import ./CORE.bend as Core
import ./GLL.bend as Gll
import ./CHECK.bend as Check

# IS A STATE SUPPORTED? Every fact of it can be derived from the root by the engine's rules,
# with the engine's predictor. Not trusted: the facts reached are grown here round by
# round from the root, and the state is supported when they include all of its facts. A
# supported state holds nothing the rules cannot give; laws about every derivable fact
# (PROOF_SUPPORT.bend) then hold for every fact of it.

type Fact is Data:
  FDesc{d: Gll.Desc}
  FCluster{key: Gll.CKey}
  FRet{key: Gll.CKey, edge: Gll.Edge}
  FPop{key: Gll.CKey, j: Nat}
  FStep{y: Core.Bsr}

def factEq(a: Fact, b: Fact) -> Bool:
  match a b:
    case FDesc{x} FDesc{y}:
      Gll.descEq(x, y)
    case FCluster{x} FCluster{y}:
      Gll.keyEq(x, y)
    case FRet{k1, e1} FRet{k2, e2}:
      Bool.and(Gll.keyEq(k1, k2), Check.edgeEq(e1, e2))
    case FPop{k1, j1} FPop{k2, j2}:
      Bool.and(Gll.keyEq(k1, k2), Nat.is_eq(j1, j2))
    case FStep{x} FStep{y}:
      Core.bsrEq(x, y)
    case FDesc{x} FCluster{y}:
      False{}
    case FDesc{x} FRet{k, e}:
      False{}
    case FDesc{x} FPop{k, j}:
      False{}
    case FDesc{x} FStep{y}:
      False{}
    case FCluster{x} FDesc{y}:
      False{}
    case FCluster{x} FRet{k, e}:
      False{}
    case FCluster{x} FPop{k, j}:
      False{}
    case FCluster{x} FStep{y}:
      False{}
    case FRet{k, e} FDesc{y}:
      False{}
    case FRet{k, e} FCluster{y}:
      False{}
    case FRet{k, e} FPop{k2, j}:
      False{}
    case FRet{k, e} FStep{y}:
      False{}
    case FPop{k, j} FDesc{y}:
      False{}
    case FPop{k, j} FCluster{y}:
      False{}
    case FPop{k, j} FRet{k2, e}:
      False{}
    case FPop{k, j} FStep{y}:
      False{}
    case FStep{x} FDesc{y}:
      False{}
    case FStep{x} FCluster{y}:
      False{}
    case FStep{x} FRet{k, e}:
      False{}
    case FStep{x} FPop{k, j}:
      False{}

def factIn(+f: Fact, fs: +List<Fact>) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case Con{+g, rest}:
      Bool.or(factEq(f, g), factIn(f, rest))

def allFactsIn(fs: +List<Fact>, +reached: +List<Fact>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case Con{+f, rest}:
      Bool.and(factIn(f, reached), allFactsIn(rest, reached))

def joinFacts(a: +List<Fact>, +b: +List<Fact>) -> +List<Fact>:
  match a:
    case Nil{}:
      b
    case Con{+x, rest}:
      x <> joinFacts(rest, b)

# ======== THE FACTS OF A STATE ========

def descFacts(ds: +List<Gll.Desc>) -> +List<Fact>:
  match ds:
    case Nil{}:
      []
    case Con{+d, rest}:
      FDesc{d} <> descFacts(rest)

def clusterFacts(cs: +List<Gll.CKey>) -> +List<Fact>:
  match cs:
    case Nil{}:
      []
    case Con{+c, rest}:
      FCluster{c} <> clusterFacts(rest)

def retFacts(rs: +List<Gll.Ret>) -> +List<Fact>:
  match rs:
    case Nil{}:
      []
    case Con{Gll.Ret{+key, +edge}, rest}:
      FRet{key, edge} <> retFacts(rest)

def popFacts(ps: +List<Gll.Pop>) -> +List<Fact>:
  match ps:
    case Nil{}:
      []
    case Con{Gll.Pop{+key, +j}, rest}:
      FPop{key, j} <> popFacts(rest)

def stepFacts(ys: +List<Core.Bsr>) -> +List<Fact>:
  match ys:
    case Nil{}:
      []
    case Con{+y, rest}:
      FStep{y} <> stepFacts(rest)

def factsOf(s: Gll.GState) -> +List<Fact>:
  match s:
    case Gll.GState{+seen, todo, +cs, +rs, +ps, +ys}:
      joinFacts(descFacts(seen), joinFacts(clusterFacts(cs), joinFacts(retFacts(rs), joinFacts(popFacts(ps), stepFacts(ys)))))

# Is the fact in the state?
def inState(f: Fact, +s: Gll.GState) -> Bool:
  match f:
    case FDesc{+d}:
      Check.seenIn(d, s)
    case FCluster{+key}:
      Gll.keyIn(key, Check.clustersOf(s))
    case FRet{+key, +edge}:
      Check.retIn(key, edge, Check.returnsOf(s))
    case FPop{+key, +j}:
      Gll.popIn(key, j, Check.popsOf(s))
    case FStep{+y}:
      Check.stepIn(y, s)

# ======== THE RULES ========

def tokenGives(ok: Bool, +q: Nat, +d: Nat, +k: Nat, +i: Nat) -> +List<Fact>:
  match ok:
    case True{}:
      [FDesc{Gll.Desc{q, 1n+d, k, 1n+i}}, FStep{Core.Bsr{q, 1n+d, k, i, 1n+i}}]
    case False{}:
      []

def emptyGives(d: Nat, +q: Nat, +k: Nat, +i: Nat) -> +List<Fact>:
  match d:
    case 0n:
      [FStep{Core.Bsr{q, 0n, k, i, i}}]
    case 1n+e:
      []

def itemGives(item: Maybe<&2, Core.Sym>, +grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +d: Nat, +k: Nat, +i: Nat) -> +List<Fact>:
  match item:
    case Some{Core.Terminal{+t}}:
      tokenGives(Core.tokIs(Core.tokAt(input, i), t), q, d, k, i)
    case Some{Core.Nonterminal{+x, need}}:
      [FCluster{Gll.CKey{x, i}}, FRet{Gll.CKey{x, i}, Gll.Edge{q, d, k}}]
    case None{}:
      FPop{Gll.CKey{Gll.lhsOf(grammar, q), k}, i} <> emptyGives(d, q, k, i)

def descGives(d: Gll.Desc, +grammar: +List<Core.Production>, +input: +List<Nat>) -> +List<Fact>:
  match d:
    case Gll.Desc{+q, +dot, +k, +i}:
      itemGives(Gll.nthSym(Core.rhsOf(grammar, q), dot), grammar, input, q, dot, k, i)

def resumeOk(ok: Bool, +q: Nat, +dot: Nat, +k: Nat, +kc: Nat, +j: Nat) -> +List<Fact>:
  match ok:
    case True{}:
      [FDesc{Gll.Desc{q, 1n+dot, k, j}}, FStep{Core.Bsr{q, 1n+dot, k, kc, j}}]
    case False{}:
      []

# The caller of `edge` resumed after its callee, which started at kc and ended at j.
def resumeGives(edge: Gll.Edge, +grammar: +List<Core.Production>, +kc: Nat, +j: Nat) -> +List<Fact>:
  match edge:
    case Gll.Edge{+q, +dot, +k}:
      resumeOk(Gll.needHolds(Gll.needAt(grammar, q, dot), kc, j), q, dot, k, kc, j)

def keyPos(k: Gll.CKey) -> Nat:
  match k:
    case Gll.CKey{x, +i}:
      i

def factsIf(b: Bool, +fs: +List<Fact>) -> +List<Fact>:
  match b:
    case True{}:
      fs
    case False{}:
      []

# A return edge against every pop of its cluster reached so far.
def retGives(reached: +List<Fact>, +grammar: +List<Core.Production>, +key: Gll.CKey, +edge: Gll.Edge) -> +List<Fact>:
  match reached:
    case Nil{}:
      []
    case Con{FPop{+k2, +j}, rest}:
      joinFacts(factsIf(Gll.keyEq(key, k2), resumeGives(edge, grammar, keyPos(key), j)), retGives(rest, grammar, key, edge))
    case Con{FDesc{d}, rest}:
      retGives(rest, grammar, key, edge)
    case Con{FCluster{c}, rest}:
      retGives(rest, grammar, key, edge)
    case Con{FRet{k2, e2}, rest}:
      retGives(rest, grammar, key, edge)
    case Con{FStep{y}, rest}:
      retGives(rest, grammar, key, edge)

# A pop against every return edge of its cluster reached so far.
def popGives(reached: +List<Fact>, +grammar: +List<Core.Production>, +key: Gll.CKey, +j: Nat) -> +List<Fact>:
  match reached:
    case Nil{}:
      []
    case Con{FRet{+k2, +edge}, rest}:
      joinFacts(factsIf(Gll.keyEq(key, k2), resumeGives(edge, grammar, keyPos(key), j)), popGives(rest, grammar, key, j))
    case Con{FDesc{d}, rest}:
      popGives(rest, grammar, key, j)
    case Con{FCluster{c}, rest}:
      popGives(rest, grammar, key, j)
    case Con{FPop{k2, j2}, rest}:
      popGives(rest, grammar, key, j)
    case Con{FStep{y}, rest}:
      popGives(rest, grammar, key, j)

def seedFacts(ds: +List<Gll.Desc>) -> +List<Fact>:
  descFacts(ds)

# What one fact gives, with the facts reached so far.
def factGives(f: Fact, +pred: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, +reached: +List<Fact>) -> +List<Fact>:
  match f:
    case FDesc{+d}:
      descGives(d, grammar, input)
    case FCluster{Gll.CKey{+x, +i}}:
      seedFacts(Gll.productionsOf(grammar, pred, Core.tokAt(input, i), x, 0n, i))
    case FRet{+key, +edge}:
      retGives(reached, grammar, key, edge)
    case FPop{+key, +j}:
      popGives(reached, grammar, key, j)
    case FStep{y}:
      []

def allGive(fs: +List<Fact>, +pred: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, +reached: +List<Fact>) -> +List<Fact>:
  match fs:
    case Nil{}:
      []
    case Con{+f, rest}:
      joinFacts(factGives(f, pred, grammar, input, reached), allGive(rest, pred, grammar, input, reached))

def addPick(have: Bool, +f: Fact, +acc: +List<Fact>) -> +List<Fact>:
  match have:
    case True{}:
      acc
    case False{}:
      f <> acc

# The new facts not reached yet, added to the reached ones.
def addNew(new: +List<Fact>, +acc: +List<Fact>) -> +List<Fact>:
  match new:
    case Nil{}:
      acc
    case Con{+f, rest}:
      addNew(rest, addPick(factIn(f, acc), f, acc))

def growReached(n: Nat, +pred: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, +reached: +List<Fact>) -> +List<Fact>:
  match n:
    case 0n:
      reached
    case 1n+(+p):
      growReached(p, pred, grammar, input, addNew(allGive(reached, pred, grammar, input, reached), reached))

def roots(+start: Nat) -> +List<Fact>:
  [FCluster{Gll.CKey{start, 0n}}]

# Supported: every fact of the state is reached from the root within `fuel` rounds.
def supported(+fuel: Nat, +pred: Gll.Pred, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +s: Gll.GState) -> Bool:
  allFactsIn(factsOf(s), growReached(fuel, pred, grammar, input, roots(start)))

# Every fact of the state is in the other state.
def factsWithin(fs: +List<Fact>, +larger: Gll.GState) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case Con{+f, rest}:
      Bool.and(inState(f, larger), factsWithin(rest, larger))

# ======== THE STATES THE LAWS SPEAK ABOUT ========

def statePick(ok: Bool, +s: Gll.GState) -> Maybe<&2, Gll.GState>:
  match ok:
    case True{}:
      Some{s}
    case False{}:
      None{}

# The plain engine's final state, when it is closed and has the start symbol's cluster.
def closedPick(r: Gll.GRun, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>) -> Maybe<&2, Gll.GState>:
  match r:
    case Gll.GDone{+s}:
      statePick(Bool.and(Check.closed(grammar, input, s), Gll.keyIn(Gll.CKey{start, 0n}, Check.clustersOf(s))), s)
    case Gll.OutOfFuel{s}:
      None{}

def closedState(fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>) -> Maybe<&2, Gll.GState>:
  closedPick(Gll.parse(fuel, grammar, start, input), grammar, start, input)

# The engine's final state with a predictor, when it is supported.
def supportedPick(r: Gll.GRun, +fuel: Nat, +pred: Gll.Pred, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>) -> Maybe<&2, Gll.GState>:
  match r:
    case Gll.GDone{+s}:
      statePick(supported(fuel, pred, grammar, start, input, s), s)
    case Gll.OutOfFuel{s}:
      None{}

def supportedState(fuel: Nat, +pred: Gll.Pred, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>) -> Maybe<&2, Gll.GState>:
  +f = fuel
  supportedPick(Gll.parseWith(f, pred, grammar, start, input), f, pred, grammar, start, input)

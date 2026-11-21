import Base
import ./CORE.bend as Core
import ./GLL.bend as Gll

# IS A GLL STATE CLOSED? Every rule of the engine, applied to the state, adds nothing new:
# - a seen descriptor before a terminal that matches has its successor and its step;
# - one before a nonterminal has its cluster and its return edge;
# - one at the end of its production has its empty step (for an empty right side) and its pop;
# - every cluster has the descriptors that start its productions;
# - every return edge, for every pop of its cluster that keeps the occurrence's need, has its
#   resumed descriptor and step.
# The proof that a closed state holds every step of every parse tree uses nothing else.

def edgeEq(a: Gll.Edge, b: Gll.Edge) -> Bool:
  match a b:
    case Gll.Edge{q1, d1, k1} Gll.Edge{q2, d2, k2}:
      Bool.and(Nat.is_eq(q1, q2), Bool.and(Nat.is_eq(d1, d2), Nat.is_eq(k1, k2)))

def retIn(+key: Gll.CKey, +edge: Gll.Edge, xs: +List<Gll.Ret>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{Gll.Ret{k2, e2}, rest}:
      Bool.or(Bool.and(Gll.keyEq(key, k2), edgeEq(edge, e2)), retIn(key, edge, rest))

def seenOf(s: Gll.GState) -> +List<Gll.Desc>:
  match s:
    case Gll.GState{seen, todo, cs, rs, ps, ys}:
      seen

def clustersOf(s: Gll.GState) -> +List<Gll.CKey>:
  match s:
    case Gll.GState{seen, todo, cs, rs, ps, ys}:
      cs

def returnsOf(s: Gll.GState) -> +List<Gll.Ret>:
  match s:
    case Gll.GState{seen, todo, cs, rs, ps, ys}:
      rs

def popsOf(s: Gll.GState) -> +List<Gll.Pop>:
  match s:
    case Gll.GState{seen, todo, cs, rs, ps, ys}:
      ps

def stepsOf(s: Gll.GState) -> +List<Core.Bsr>:
  match s:
    case Gll.GState{seen, todo, cs, rs, ps, ys}:
      ys

def seenIn(+d: Gll.Desc, +s: Gll.GState) -> Bool:
  Gll.descIn(d, seenOf(s))

def stepIn(+y: Core.Bsr, +s: Gll.GState) -> Bool:
  Core.member(y, stepsOf(s))

def allSeen(ds: +List<Gll.Desc>, +s: Gll.GState) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case Con{+d, rest}:
      Bool.and(seenIn(d, s), allSeen(rest, s))

def tokenOk(ok: Bool, +index: Nat, +dot: Nat, +k: Nat, +i: Nat, +s: Gll.GState) -> Bool:
  match ok:
    case True{}:
      Bool.and(seenIn(Gll.Desc{index, 1n+dot, k, 1n+i}, s), stepIn(Core.Bsr{index, 1n+dot, k, i, 1n+i}, s))
    case False{}:
      True{}

def emptyOk(dot: Nat, +index: Nat, +k: Nat, +i: Nat, +s: Gll.GState) -> Bool:
  match dot:
    case 0n:
      stepIn(Core.Bsr{index, 0n, k, i, i}, s)
    case 1n+d:
      True{}

def itemOk(item: Maybe<&2, Core.Sym>, +grammar: +List<Core.Production>, +input: +List<Nat>, +index: Nat, +dot: Nat, +k: Nat, +i: Nat, +s: Gll.GState) -> Bool:
  match item:
    case Some{Core.Terminal{+t}}:
      tokenOk(Core.tokIs(Core.tokAt(input, i), t), index, dot, k, i, s)
    case Some{Core.Nonterminal{+x, need}}:
      Bool.and(Gll.keyIn(Gll.CKey{x, i}, clustersOf(s)), retIn(Gll.CKey{x, i}, Gll.Edge{index, dot, k}, returnsOf(s)))
    case None{}:
      Bool.and(emptyOk(dot, index, k, i, s), Gll.popIn(Gll.CKey{Gll.lhsOf(grammar, index), k}, i, popsOf(s)))

def descOk(d: Gll.Desc, +grammar: +List<Core.Production>, +input: +List<Nat>, +s: Gll.GState) -> Bool:
  match d:
    case Gll.Desc{+index, +dot, +k, +i}:
      itemOk(Gll.nthSym(Core.rhsOf(grammar, index), dot), grammar, input, index, dot, k, i, s)

def resumeOk(ok: Bool, +index: Nat, +dot: Nat, +k: Nat, +kc: Nat, +j: Nat, +s: Gll.GState) -> Bool:
  match ok:
    case True{}:
      Bool.and(seenIn(Gll.Desc{index, 1n+dot, k, j}, s), stepIn(Core.Bsr{index, 1n+dot, k, kc, j}, s))
    case False{}:
      True{}

def edgeOk(edge: Gll.Edge, +grammar: +List<Core.Production>, +kc: Nat, +j: Nat, +s: Gll.GState) -> Bool:
  match edge:
    case Gll.Edge{+index, +dot, +k}:
      resumeOk(Gll.needHolds(Gll.needAt(grammar, index, dot), kc, j), index, dot, k, kc, j, s)

def hitOk(hit: Bool, +edge: Gll.Edge, +grammar: +List<Core.Production>, +kc: Nat, +j: Nat, +s: Gll.GState) -> Bool:
  match hit:
    case True{}:
      edgeOk(edge, grammar, kc, j, s)
    case False{}:
      True{}

# A return edge against every pop of its cluster.
def edgePops(pops: +List<Gll.Pop>, +grammar: +List<Core.Production>, key: Gll.CKey, +edge: Gll.Edge, +s: Gll.GState) -> Bool:
  match pops key:
    case Nil{} _:
      True{}
    case Con{Gll.Pop{+k2, +j}, rest} Gll.CKey{+x, +kc}:
      Bool.and(hitOk(Gll.keyEq(Gll.CKey{x, kc}, k2), edge, grammar, kc, j, s), edgePops(rest, grammar, Gll.CKey{x, kc}, edge, s))

def allDescs(ds: +List<Gll.Desc>, +grammar: +List<Core.Production>, +input: +List<Nat>, +s: Gll.GState) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case Con{d, rest}:
      Bool.and(descOk(d, grammar, input, s), allDescs(rest, grammar, input, s))

def allClusters(cs: +List<Gll.CKey>, +pred: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, +s: Gll.GState) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{Gll.CKey{+x, +i}, rest}:
      Bool.and(allSeen(Gll.productionsOf(grammar, pred, Core.tokAt(input, i), x, 0n, i), s), allClusters(rest, pred, grammar, input, s))

def allReturns(rs: +List<Gll.Ret>, +grammar: +List<Core.Production>, +pops: +List<Gll.Pop>, +s: Gll.GState) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Con{Gll.Ret{+key, +edge}, rest}:
      Bool.and(edgePops(pops, grammar, key, edge, s), allReturns(rest, grammar, pops, s))

# Closed for the descriptors the predictor admits.
def closedWith(+pred: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, +s: Gll.GState) -> Bool:
  Bool.and(allDescs(seenOf(s), grammar, input, s), Bool.and(allClusters(clustersOf(s), pred, grammar, input, s), allReturns(returnsOf(s), grammar, popsOf(s), s)))

def closed(+grammar: +List<Core.Production>, +input: +List<Nat>, +s: Gll.GState) -> Bool:
  closedWith(Gll.NoPred{}, grammar, input, s)

# THE CHECKED PARSER: run the engine, and hand out its steps only when the final state is
# closed and has the start symbol's cluster at 0.
def checkPick(ok: Bool, +s: Gll.GState) -> Maybe<&2, +List<Core.Bsr>>:
  match ok:
    case True{}:
      Some{stepsOf(s)}
    case False{}:
      None{}

def runCheckedWith(+pred: Gll.Pred, r: Gll.GRun, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>) -> Maybe<&2, +List<Core.Bsr>>:
  match r:
    case Gll.GDone{+s}:
      checkPick(Bool.and(closedWith(pred, grammar, input, s), Gll.keyIn(Gll.CKey{start, 0n}, clustersOf(s))), s)
    case Gll.OutOfFuel{s}:
      None{}

def runChecked(r: Gll.GRun, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>) -> Maybe<&2, +List<Core.Bsr>>:
  runCheckedWith(Gll.NoPred{}, r, grammar, start, input)

# Every node of the forest is admitted by the predictor where it starts.
def admitsAll(f: +List<Core.Tree>, +pred: Gll.Pred, +input: +List<Nat>, +k: Nat) -> Bool:
  match f:
    case Nil{}:
      True{}
    case Con{Core.Leaf{a}, +ts}:
      admitsAll(ts, pred, input, 1n+k)
    case Con{Core.Node{+q, +ch}, +ts}:
      Bool.and(Gll.admits(pred, q, Core.tokAt(input, k)), Bool.and(admitsAll(ch, pred, input, k), admitsAll(ts, pred, input, Nat.add(k, Core.width(Core.Node{q, ch})))))

def checkedSteps(fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>) -> Maybe<&2, +List<Core.Bsr>>:
  runChecked(Gll.parse(fuel, grammar, start, input), grammar, start, input)

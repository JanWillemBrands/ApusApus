import Base
import ./SPEC.bend as Spec
import ./GLL.bend as Gll

# IS A GLL STATE CLOSED? Every rule of the engine, applied to the state, adds nothing
# new. The conditions mirror the engine one to one:
# - a seen descriptor before a terminal that matches has its successor and its step;
# - one before a nonterminal or a bracket has its cluster and its return edge, and a
#   skippable bracket also has the skip;
# - one at the end of a sequence has its ε step (for an empty sequence) and its pop;
# - every cluster has the descriptors that start its alternatives;
# - every return edge, for every pop of its cluster, has its resumed descriptor and step;
# - every pop of a loop has the descriptors that start the loop again.
# The proof that a closed state holds every step of every parse tree uses nothing else.

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

def stepsOf(s: Gll.GState) -> +List<Spec.Bsr>:
  match s:
    case Gll.GState{seen, todo, cs, rs, ps, ys}:
      ys

def descSeen(+d: Gll.Desc, +s: Gll.GState) -> Bool:
  Gll.descIn(d, seenOf(s))

def stepIn(+y: Spec.Bsr, +s: Gll.GState) -> Bool:
  Spec.bsrMember(y, stepsOf(s))

def clusterIn(+key: Gll.CKey, +s: Gll.GState) -> Bool:
  Gll.keyIn(key, clustersOf(s))

def returnIn(+key: Gll.CKey, +edge: Gll.Edge, +s: Gll.GState) -> Bool:
  Gll.retIn(key, edge, returnsOf(s))

def popIn(+key: Gll.CKey, +j: Nat, +s: Gll.GState) -> Bool:
  Gll.popIn(key, j, popsOf(s))

def allSeen(ds: +List<Gll.Desc>, +s: Gll.GState) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case Con{+d, rest}:
      Bool.and(descSeen(d, s), allSeen(rest, s))

def tokenOk(ok: Bool, +index: Nat, +rpath: +List<Nat>, +dot: Nat, +k: Nat, +i: Nat, +s: Gll.GState) -> Bool:
  match ok:
    case True{}:
      Bool.and(descSeen(Gll.Desc{index, rpath, 1n+dot, k, 1n+i}, s), stepIn(Gll.stepAt(index, rpath, 1n+dot, k, i, 1n+i), s))
    case False{}:
      True{}

def skipOk(skip: Bool, +index: Nat, +rpath: +List<Nat>, +dot: Nat, +k: Nat, +i: Nat, +s: Gll.GState) -> Bool:
  match skip:
    case True{}:
      Bool.and(descSeen(Gll.Desc{index, rpath, 1n+dot, k, i}, s), stepIn(Gll.stepAt(index, rpath, 1n+dot, k, i, i), s))
    case False{}:
      True{}

def emptyOk(dot: Nat, +index: Nat, +rpath: +List<Nat>, +k: Nat, +i: Nat, +s: Gll.GState) -> Bool:
  match dot:
    case 0n:
      stepIn(Gll.stepAt(index, rpath, 0n, k, i, i), s)
    case 1n+d:
      True{}

# The cluster a sequence ends: its production's nonterminal, or its bracket.
def endKey(+grammar: +List<Spec.Production>, +index: Nat, rpath: +List<Nat>, +k: Nat) -> Gll.CKey:
  match rpath:
    case Con{a, Con{m, outer}}:
      Gll.CKey{Gll.TBr{index, m <> outer}, k}
    case _:
      Gll.CKey{Gll.TNt{Gll.lhsOf(grammar, index)}, k}

def itemOk(item: Maybe<&2, Spec.Item>, +grammar: +List<Spec.Production>, +input: +List<Nat>, +index: Nat, +rpath: +List<Nat>, +dot: Nat, +k: Nat, +i: Nat, +s: Gll.GState) -> Bool:
  match item:
    case Some{Spec.Sym{Spec.Terminal{+t}}}:
      tokenOk(Gll.tokenIs(List.get(&2, Nat, input, i), t), index, rpath, dot, k, i, s)
    case Some{Spec.Sym{Spec.Nonterminal{+x}}}:
      +key = {Gll.CKey{Gll.TNt{x}, i} : Gll.CKey}
      Bool.and(clusterIn(key, s), returnIn(key, Gll.Edge{index, rpath, dot, k}, s))
    case Some{Spec.Brack{+kind, alts}}:
      +key = {Gll.CKey{Gll.TBr{index, dot <> rpath}, i} : Gll.CKey}
      Bool.and(clusterIn(key, s), Bool.and(returnIn(key, Gll.Edge{index, rpath, dot, k}, s), skipOk(Gll.isSkippable(kind), index, rpath, dot, k, i, s)))
    case Some{Spec.Eps{}}:
      skipOk(True{}, index, rpath, dot, k, i, s)
    case None{}:
      Bool.and(emptyOk(dot, index, rpath, k, i, s), popIn(endKey(grammar, index, rpath, k), i, s))

def descOk(d: Gll.Desc, +grammar: +List<Spec.Production>, +input: +List<Nat>, +s: Gll.GState) -> Bool:
  match d:
    case Gll.Desc{+index, +rpath, +dot, +k, +i}:
      itemOk(Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), grammar, input, index, rpath, dot, k, i, s)

def altCount(item: Maybe<&2, Spec.Item>) -> Nat:
  match item:
    case Some{Spec.Brack{kind, alts}}:
      List.length(&2, +List<Spec.Item>, alts)
    case _:
      0n

def bracketSeeds(rpath: +List<Nat>, +grammar: +List<Spec.Production>, +index: Nat, +i: Nat) -> +List<Gll.Desc>:
  match rpath:
    case Con{+m, +outer}:
      Gll.alternatives(altCount(Gll.nthItem(Gll.seqAt(grammar, index, outer), m)), index, m <> outer, i, i)
    case Nil{}:
      []

# The descriptors that start a cluster's alternatives.
def seedsOf(+grammar: +List<Spec.Production>, key: Gll.CKey) -> +List<Gll.Desc>:
  match key:
    case Gll.CKey{Gll.TNt{+x}, +i}:
      Gll.productionsOf(grammar, x, 0n, i)
    case Gll.CKey{Gll.TBr{+index, rpath}, +i}:
      bracketSeeds(rpath, grammar, index, i)

# What a pop of a loop starts again.
def againOfKey(+grammar: +List<Spec.Production>, key: Gll.CKey, +j: Nat) -> +List<Gll.Desc>:
  match key:
    case Gll.CKey{Gll.TBr{+index, Con{+m, +outer}}, +k}:
      Gll.againOf(Gll.nthItem(Gll.seqAt(grammar, index, outer), m), index, m <> outer, k, j)
    case _:
      []

def keyStart(key: Gll.CKey) -> Nat:
  match key:
    case Gll.CKey{t, k}:
      k

def resumeOk(edge: Gll.Edge, +kc: Nat, +j: Nat, +s: Gll.GState) -> Bool:
  match edge:
    case Gll.Edge{+index, +rpath, +dot, +k}:
      Bool.and(descSeen(Gll.Desc{index, rpath, 1n+dot, k, j}, s), stepIn(Gll.stepAt(index, rpath, 1n+dot, k, kc, j), s))

def resumeIfOk(hit: Bool, +edge: Gll.Edge, +kc: Nat, +j: Nat, +s: Gll.GState) -> Bool:
  match hit:
    case True{}:
      resumeOk(edge, kc, j, s)
    case False{}:
      True{}

# A return edge against every pop.
def edgePops(pops: +List<Gll.Pop>, +key: Gll.CKey, +edge: Gll.Edge, +s: Gll.GState) -> Bool:
  match pops:
    case Nil{}:
      True{}
    case Con{Gll.Pop{+k2, +j}, rest}:
      Bool.and(resumeIfOk(Gll.keyEq(key, k2), edge, keyStart(key), j, s), edgePops(rest, key, edge, s))

def allDescs(ds: +List<Gll.Desc>, +grammar: +List<Spec.Production>, +input: +List<Nat>, +s: Gll.GState) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case Con{d, rest}:
      Bool.and(descOk(d, grammar, input, s), allDescs(rest, grammar, input, s))

def allClusters(cs: +List<Gll.CKey>, +grammar: +List<Spec.Production>, +s: Gll.GState) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{+key, rest}:
      Bool.and(allSeen(seedsOf(grammar, key), s), allClusters(rest, grammar, s))

def allReturns(rs: +List<Gll.Ret>, +pops: +List<Gll.Pop>, +s: Gll.GState) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Con{Gll.Ret{+key, +edge}, rest}:
      Bool.and(edgePops(pops, key, edge, s), allReturns(rest, pops, s))

def allPops(ps: +List<Gll.Pop>, +grammar: +List<Spec.Production>, +s: Gll.GState) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Con{Gll.Pop{+key, +j}, rest}:
      Bool.and(allSeen(againOfKey(grammar, key, j), s), allPops(rest, grammar, s))

def closed(+grammar: +List<Spec.Production>, +input: +List<Nat>, +s: Gll.GState) -> Bool:
  Bool.and(allDescs(seenOf(s), grammar, input, s), Bool.and(allClusters(clustersOf(s), grammar, s), Bool.and(allReturns(returnsOf(s), popsOf(s), s), allPops(popsOf(s), grammar, s))))

# THE CHECKED PARSER: run the engine, and hand out its steps only when the final
# state is closed and has the start symbol's cluster at 0.
def checkPick(ok: Bool, +s: Gll.GState) -> Maybe<&2, +List<Spec.Bsr>>:
  match ok:
    case True{}:
      Some{stepsOf(s)}
    case False{}:
      None{}

def runChecked(r: Gll.GRun, +grammar: +List<Spec.Production>, +start: Nat, +input: +List<Nat>) -> Maybe<&2, +List<Spec.Bsr>>:
  match r:
    case Gll.GDone{+s}:
      checkPick(Bool.and(closed(grammar, input, s), clusterIn(Gll.CKey{Gll.TNt{start}, 0n}, s)), s)
    case Gll.OutOfFuel{s}:
      None{}

def checkedSteps(fuel: Nat, +grammar: +List<Spec.Production>, +start: Nat, +input: +List<Nat>) -> Maybe<&2, +List<Spec.Bsr>>:
  runChecked(Gll.parse(fuel, grammar, start, input), grammar, start, input)

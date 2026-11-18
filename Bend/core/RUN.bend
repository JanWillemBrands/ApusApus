import Base
import ./CORE.bend as Core
import ./GLL.bend as Gll
import ./CHECK.bend as Check

# THE ENGINE'S INVARIANT: what holds after every iteration of the worklist loop, so that the
# final state, with nothing left to do, is closed (CHECK.bend). Proven in PROOF_RUN.bend.
# - every seen descriptor is still to do, or its rule has done its work;
# - every cluster has its seeds; every return edge has met every pop of its cluster;
# - every pop, every seen descriptor and every return edge belongs to a known cluster;
# - every descriptor still to do has been seen;
# - every descriptor, return edge, pop and step lies within the grammar and the input.

def todoOf(s: Gll.GState) -> +List<Gll.Desc>:
  match s:
    case Gll.GState{seen, todo, cs, rs, ps, ys}:
      todo

# ======== GROWTH ========
# The engine only adds facts: a later state holds every fact of an earlier one.

def subDescs(xs: +List<Gll.Desc>, +ys: +List<Gll.Desc>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, rest}:
      Bool.and(Gll.descIn(x, ys), subDescs(rest, ys))

def subKeys(xs: +List<Gll.CKey>, +ys: +List<Gll.CKey>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, rest}:
      Bool.and(Gll.keyIn(x, ys), subKeys(rest, ys))

def subRets(xs: +List<Gll.Ret>, +ys: +List<Gll.Ret>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{Gll.Ret{+k, +e}, rest}:
      Bool.and(Check.retIn(k, e, ys), subRets(rest, ys))

def subPops(xs: +List<Gll.Pop>, +ys: +List<Gll.Pop>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{Gll.Pop{+k, +j}, rest}:
      Bool.and(Gll.popIn(k, j, ys), subPops(rest, ys))

def queuedOk(ds: +List<Gll.Desc>, +todo: +List<Gll.Desc>, +grammar: +List<Core.Production>, +input: +List<Nat>, +s: Gll.GState) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case Con{+d, rest}:
      Bool.and(Bool.or(Gll.descIn(d, todo), Check.descOk(d, grammar, input, s)), queuedOk(rest, todo, grammar, input, s))

def popsKeyed(ps: +List<Gll.Pop>, +cs: +List<Gll.CKey>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Con{Gll.Pop{+key, j}, rest}:
      Bool.and(Gll.keyIn(key, cs), popsKeyed(rest, cs))

def descsKeyed(ds: +List<Gll.Desc>, +grammar: +List<Core.Production>, +cs: +List<Gll.CKey>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case Con{Gll.Desc{+q, dot, +k, i}, rest}:
      Bool.and(Gll.keyIn(Gll.CKey{Gll.lhsOf(grammar, q), k}, cs), descsKeyed(rest, grammar, cs))

def retsKeyed(rs: +List<Gll.Ret>, +grammar: +List<Core.Production>, +cs: +List<Gll.CKey>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Con{Gll.Ret{key, Gll.Edge{+q, dot, +k}}, rest}:
      Bool.and(Gll.keyIn(Gll.CKey{Gll.lhsOf(grammar, q), k}, cs), retsKeyed(rest, grammar, cs))

def grows(s: Gll.GState, +t: Gll.GState) -> Bool:
  match s t:
    case Gll.GState{+seen, todo, +cs, +rs, +ps, +ys} Gll.GState{+seen2, todo2, +cs2, +rs2, +ps2, +ys2}:
      Bool.and(subDescs(seen, seen2), Bool.and(subKeys(cs, cs2), Bool.and(subRets(rs, rs2), Bool.and(subPops(ps, ps2), Core.allIn(ys, ys2)))))

# ======== WHAT AN ADDING OPERATION KEEPS ========
# An operation that only adds descriptors and steps: the state grows, the to-do list only
# grows, every new descriptor is on the to-do list and belongs to a known cluster.

def newQueued(ds: +List<Gll.Desc>, +old: +List<Gll.Desc>, +todo: +List<Gll.Desc>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case Con{+d, rest}:
      Bool.and(Bool.or(Gll.descIn(d, old), Gll.descIn(d, todo)), newQueued(rest, old, todo))

def keyedDesc(d: Gll.Desc, +grammar: +List<Core.Production>, +cs: +List<Gll.CKey>) -> Bool:
  match d:
    case Gll.Desc{+q, dot, +k, i}:
      Gll.keyIn(Gll.CKey{Gll.lhsOf(grammar, q), k}, cs)

def newKeyed(ds: +List<Gll.Desc>, +old: +List<Gll.Desc>, +grammar: +List<Core.Production>, +cs: +List<Gll.CKey>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case Con{+d, rest}:
      Bool.and(Bool.or(Gll.descIn(d, old), keyedDesc(d, grammar, cs)), newKeyed(rest, old, grammar, cs))

# After a new pop of `key` at j: every return edge of the list has resumed there.
def retsHit(rets: +List<Gll.Ret>, +grammar: +List<Core.Production>, key: Gll.CKey, +j: Nat, +s: Gll.GState) -> Bool:
  match rets key:
    case Nil{} _:
      True{}
    case Con{Gll.Ret{+k2, +e2}, rest} Gll.CKey{+x, +kc}:
      Bool.and(Check.hitOk(Gll.keyEq(Gll.CKey{x, kc}, k2), e2, grammar, kc, j, s), retsHit(rest, grammar, Gll.CKey{x, kc}, j, s))

def keyedEdge(e: Gll.Edge, +grammar: +List<Core.Production>, +cs: +List<Gll.CKey>) -> Bool:
  match e:
    case Gll.Edge{+q, dot, +k}:
      Gll.keyIn(Gll.CKey{Gll.lhsOf(grammar, q), k}, cs)

# ======== THE DESCRIPTORS THERE CAN BE ========
# Every descriptor the engine adds names a production of the grammar, a dot within its right
# side, and positions within the input. They are finitely many: the universe below. The
# measure (unseen descriptors of the universe, plus the to-do list) drops at every iteration.

def descBound(d: Gll.Desc, +grammar: +List<Core.Production>, +input: +List<Nat>) -> Bool:
  match d:
    case Gll.Desc{+q, +dot, +k, +i}:
      Bool.and(Nat.is_le(1n+q, List.length(&2, Core.Production, grammar)), Bool.and(Nat.is_le(dot, List.length(&2, Core.Sym, Core.rhsOf(grammar, q))),
        Bool.and(Nat.is_le(k, List.length(&2, Nat, input)), Nat.is_le(i, List.length(&2, Nat, input)))))

def uI(+q: Nat, +d: Nat, +k: Nat, m: Nat) -> +List<Gll.Desc>:
  match m:
    case 0n:
      [Gll.Desc{q, d, k, 0n}]
    case 1n+(+p):
      Gll.Desc{q, d, k, 1n+p} <> uI(q, d, k, p)

def uK(+q: Nat, +d: Nat, m: Nat, +n: Nat) -> +List<Gll.Desc>:
  match m:
    case 0n:
      uI(q, d, 0n, n)
    case 1n+(+p):
      List.append(&2, Gll.Desc, uI(q, d, 1n+p, n), uK(q, d, p, n))

def uD(+q: Nat, m: Nat, +n: Nat) -> +List<Gll.Desc>:
  match m:
    case 0n:
      uK(q, 0n, n, n)
    case 1n+(+p):
      List.append(&2, Gll.Desc, uK(q, 1n+p, n, n), uD(q, p, n))

def uQ(+grammar: +List<Core.Production>, c: Nat, +n: Nat) -> +List<Gll.Desc>:
  match c:
    case 0n:
      []
    case 1n+(+p):
      List.append(&2, Gll.Desc, uD(p, List.length(&2, Core.Sym, Core.rhsOf(grammar, p)), n), uQ(grammar, p, n))

def univ(+grammar: +List<Core.Production>, +input: +List<Nat>) -> +List<Gll.Desc>:
  uQ(grammar, List.length(&2, Core.Production, grammar), List.length(&2, Nat, input))

def notPick(b: Bool) -> Nat:
  match b:
    case True{}:
      0n
    case False{}:
      1n

def countNot(us: +List<Gll.Desc>, +seen: +List<Gll.Desc>) -> Nat:
  match us:
    case Nil{}:
      0n
    case Con{+u, rest}:
      Nat.add(notPick(Gll.descIn(u, seen)), countNot(rest, seen))

def meas(+grammar: +List<Core.Production>, +input: +List<Nat>, +s: Gll.GState) -> Nat:
  Nat.add(countNot(univ(grammar, input), Check.seenOf(s)), List.length(&2, Gll.Desc, todoOf(s)))

def edgeBound(e: Gll.Edge, +grammar: +List<Core.Production>, +input: +List<Nat>) -> Bool:
  match e:
    case Gll.Edge{+q, +dot, +k}:
      Bool.and(Nat.is_le(1n+q, List.length(&2, Core.Production, grammar)), Bool.and(Nat.is_le(1n+dot, List.length(&2, Core.Sym, Core.rhsOf(grammar, q))), Nat.is_le(k, List.length(&2, Nat, input))))

def descsBounded(ds: +List<Gll.Desc>, +grammar: +List<Core.Production>, +input: +List<Nat>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case Con{+d, rest}:
      Bool.and(descBound(d, grammar, input), descsBounded(rest, grammar, input))

def retsBounded(rs: +List<Gll.Ret>, +grammar: +List<Core.Production>, +input: +List<Nat>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Con{Gll.Ret{key, +e}, rest}:
      Bool.and(edgeBound(e, grammar, input), retsBounded(rest, grammar, input))

def popsBounded(ps: +List<Gll.Pop>, +input: +List<Nat>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Con{Gll.Pop{key, +j}, rest}:
      Bool.and(Nat.is_le(j, List.length(&2, Nat, input)), popsBounded(rest, input))

def newBounded(ds: +List<Gll.Desc>, +old: +List<Gll.Desc>, +grammar: +List<Core.Production>, +input: +List<Nat>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case Con{+d, rest}:
      Bool.and(Bool.or(Gll.descIn(d, old), descBound(d, grammar, input)), newBounded(rest, old, grammar, input))

def keyBound(key: Gll.CKey, +input: +List<Nat>) -> Bool:
  match key:
    case Gll.CKey{+x, +k}:
      Nat.is_le(k, List.length(&2, Nat, input))

# A step lies within bounds when its descriptor does and so does its middle.
def stepBound(e: Core.Bsr, +grammar: +List<Core.Production>, +input: +List<Nat>) -> Bool:
  match e:
    case Core.Bsr{+q, +d, +i, +k, +j}:
      Bool.and(descBound(Gll.Desc{q, d, i, j}, grammar, input), Nat.is_le(k, List.length(&2, Nat, input)))

def stepsBounded(ys: +List<Core.Bsr>, +grammar: +List<Core.Production>, +input: +List<Nat>) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{+y, rest}:
      Bool.and(stepBound(y, grammar, input), stepsBounded(rest, grammar, input))

def newStepsBounded(ys: +List<Core.Bsr>, +old: +List<Core.Bsr>, +grammar: +List<Core.Production>, +input: +List<Nat>) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{+y, rest}:
      Bool.and(Bool.or(Core.member(y, old), stepBound(y, grammar, input)), newStepsBounded(rest, old, grammar, input))

def addsB(+grammar: +List<Core.Production>, +input: +List<Nat>, +s: Gll.GState, +t: Gll.GState) -> Bool:
  Bool.and(grows(s, t), Bool.and(subDescs(todoOf(s), todoOf(t)), Bool.and(newQueued(Check.seenOf(t), Check.seenOf(s), todoOf(t)), Bool.and(newKeyed(Check.seenOf(t), Check.seenOf(s), grammar, Check.clustersOf(s)), Bool.and(newQueued(todoOf(t), todoOf(s), Check.seenOf(t)),
    Bool.and(newBounded(Check.seenOf(t), Check.seenOf(s), grammar, input), Bool.and(newStepsBounded(Check.stepsOf(t), Check.stepsOf(s), grammar, input), Nat.is_le(meas(grammar, input, t), meas(grammar, input, s)))))))))

# `extra`: descriptors taken off the to-do list whose work is still being done.
def invWith(+extra: +List<Gll.Desc>, +pred: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, +s: Gll.GState) -> Bool:
  Bool.and(queuedOk(Check.seenOf(s), List.append(&2, Gll.Desc, extra, todoOf(s)), grammar, input, s),
    Bool.and(Check.allClusters(Check.clustersOf(s), pred, grammar, input, s),
      Bool.and(Check.allReturns(Check.returnsOf(s), grammar, Check.popsOf(s), s),
        Bool.and(popsKeyed(Check.popsOf(s), Check.clustersOf(s)),
          Bool.and(descsKeyed(Check.seenOf(s), grammar, Check.clustersOf(s)), Bool.and(retsKeyed(Check.returnsOf(s), grammar, Check.clustersOf(s)), Bool.and(subDescs(todoOf(s), Check.seenOf(s)),
            Bool.and(descsBounded(Check.seenOf(s), grammar, input), Bool.and(retsBounded(Check.returnsOf(s), grammar, input), Bool.and(popsBounded(Check.popsOf(s), input), stepsBounded(Check.stepsOf(s), grammar, input)))))))))))

def inv(+pred: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, +s: Gll.GState) -> Bool:
  invWith([], pred, grammar, input, s)

# ======== CHECKING THE INVARIANT ALONG A RUN (examples only) ========

def invAlong(fuel: Nat, +pred: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, s: Gll.GState) -> Bool:
  match fuel s:
    case 0n +st:
      inv(pred, grammar, input, st)
    case 1n+f Gll.GState{+seen, Nil{}, +cs, +rs, +ps, +ys}:
      inv(pred, grammar, input, Gll.GState{seen, [], cs, rs, ps, ys})
    case 1n+f Gll.GState{+seen, Con{+d, +rest}, +cs, +rs, +ps, +ys}:
      Bool.and(inv(pred, grammar, input, Gll.GState{seen, d <> rest, cs, rs, ps, ys}),
        invAlong(f, pred, grammar, input, Gll.step(d, pred, grammar, input, Gll.GState{seen, rest, cs, rs, ps, ys})))

def initial(+pred: Gll.Pred, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>) -> Gll.GState:
  Gll.withDescs(Gll.productionsOf(grammar, pred, Core.tokAt(input, 0n), start, 0n, 0n), Gll.GState{[], [], [Gll.CKey{start, 0n}], [], [], []})


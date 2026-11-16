import Base
import ../LEMMAS.bend as Lemma
import ./CORE.bend as Core
import ./GLL.bend as Gll
import ./CHECK.bend as Check

# A CLOSED STATE HAS EVERY STEP OF EVERY PARSE TREE.
#
# Walk a parse tree. At each node, the descriptor that starts its production is seen; each
# child then leads, by one closedness condition, to the next descriptor and to the child's
# step: a leaf by the token rule, a node through its cluster, the seeds of its production,
# the node's own walk (which ends in a pop), and the return edge resumed at that pop. At the
# end of a production its descriptor gives the pop. Nothing else of the check is used.

# ======== EQUAL BY ==, SO EQUAL ========

law desc_eq_sound:
  for a: Gll.Desc
  for b: Gll.Desc
  for +e: {Gll.descEq(a, b) == True{} : Bool}
  {a == b : Gll.Desc}

def desc_eq_sound(a, b, e):
  match a b:
    case Gll.Desc{+q1, +d1, +k1, +i1} Gll.Desc{+q2, +d2, +k2, +i2}:
      +r1 = {Bool.and(Nat.is_eq(d1, d2), Bool.and(Nat.is_eq(k1, k2), Nat.is_eq(i1, i2))) : Bool}
      +r2 = {Bool.and(Nat.is_eq(k1, k2), Nat.is_eq(i1, i2)) : Bool}
      +e1 = Lemma.and_true_right_side(Nat.is_eq(q1, q2), r1, e)
      +e2 = Lemma.and_true_right_side(Nat.is_eq(d1, d2), r2, e1)
      +eq = Lemma.nat_eq_sound(q1, q2, Lemma.and_true_left(Nat.is_eq(q1, q2), r1, e))
      +ed = Lemma.nat_eq_sound(d1, d2, Lemma.and_true_left(Nat.is_eq(d1, d2), r2, e1))
      +ek = Lemma.nat_eq_sound(k1, k2, Lemma.and_true_left(Nat.is_eq(k1, k2), Nat.is_eq(i1, i2), e2))
      +ei = Lemma.nat_eq_sound(i1, i2, Lemma.and_true_right_side(Nat.is_eq(k1, k2), Nat.is_eq(i1, i2), e2))
      %eq : {Gll.Desc{q1, d1, k1, i1} == Gll.Desc{_, d2, k2, i2} : Gll.Desc}
      %ed : {Gll.Desc{q1, d1, k1, i1} == Gll.Desc{q1, _, k2, i2} : Gll.Desc}
      %ek : {Gll.Desc{q1, d1, k1, i1} == Gll.Desc{q1, d1, _, i2} : Gll.Desc}
      %ei : {Gll.Desc{q1, d1, k1, i1} == Gll.Desc{q1, d1, k1, _} : Gll.Desc}
      {==}

law key_eq_sound:
  for a: Gll.CKey
  for b: Gll.CKey
  for +e: {Gll.keyEq(a, b) == True{} : Bool}
  {a == b : Gll.CKey}

def key_eq_sound(a, b, e):
  match a b:
    case Gll.CKey{+x1, +i1} Gll.CKey{+x2, +i2}:
      +ex = Lemma.nat_eq_sound(x1, x2, Lemma.and_true_left(Nat.is_eq(x1, x2), Nat.is_eq(i1, i2), e))
      +ei = Lemma.nat_eq_sound(i1, i2, Lemma.and_true_right_side(Nat.is_eq(x1, x2), Nat.is_eq(i1, i2), e))
      %ex : {Gll.CKey{x1, i1} == Gll.CKey{_, i2} : Gll.CKey}
      %ei : {Gll.CKey{x1, i1} == Gll.CKey{x1, _} : Gll.CKey}
      {==}

law edge_eq_sound:
  for a: Gll.Edge
  for b: Gll.Edge
  for +e: {Check.edgeEq(a, b) == True{} : Bool}
  {a == b : Gll.Edge}

def edge_eq_sound(a, b, e):
  match a b:
    case Gll.Edge{+q1, +d1, +k1} Gll.Edge{+q2, +d2, +k2}:
      +r1 = {Bool.and(Nat.is_eq(d1, d2), Nat.is_eq(k1, k2)) : Bool}
      +e1 = Lemma.and_true_right_side(Nat.is_eq(q1, q2), r1, e)
      +eq = Lemma.nat_eq_sound(q1, q2, Lemma.and_true_left(Nat.is_eq(q1, q2), r1, e))
      +ed = Lemma.nat_eq_sound(d1, d2, Lemma.and_true_left(Nat.is_eq(d1, d2), Nat.is_eq(k1, k2), e1))
      +ek = Lemma.nat_eq_sound(k1, k2, Lemma.and_true_right_side(Nat.is_eq(d1, d2), Nat.is_eq(k1, k2), e1))
      %eq : {Gll.Edge{q1, d1, k1} == Gll.Edge{_, d2, k2} : Gll.Edge}
      %ed : {Gll.Edge{q1, d1, k1} == Gll.Edge{q1, _, k2} : Gll.Edge}
      %ek : {Gll.Edge{q1, d1, k1} == Gll.Edge{q1, d1, _} : Gll.Edge}
      {==}

# ======== FROM THE CHECK TO SINGLE FACTS ========

law closed_descs:
  for +pred: Gll.Pred
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for +hc: {Check.closedWith(pred, grammar, input, s) == True{} : Bool}
  {Check.allDescs(Check.seenOf(s), grammar, input, s) == True{} : Bool}

def closed_descs(pred, grammar, input, s, hc):
  Lemma.and_true_left(Check.allDescs(Check.seenOf(s), grammar, input, s), Bool.and(Check.allClusters(Check.clustersOf(s), pred, grammar, input, s), Check.allReturns(Check.returnsOf(s), grammar, Check.popsOf(s), s)), hc)

law closed_clusters:
  for +pred: Gll.Pred
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for +hc: {Check.closedWith(pred, grammar, input, s) == True{} : Bool}
  {Check.allClusters(Check.clustersOf(s), pred, grammar, input, s) == True{} : Bool}

def closed_clusters(pred, grammar, input, s, hc):
  +rest = Lemma.and_true_right_side(Check.allDescs(Check.seenOf(s), grammar, input, s), Bool.and(Check.allClusters(Check.clustersOf(s), pred, grammar, input, s), Check.allReturns(Check.returnsOf(s), grammar, Check.popsOf(s), s)), hc)
  Lemma.and_true_left(Check.allClusters(Check.clustersOf(s), pred, grammar, input, s), Check.allReturns(Check.returnsOf(s), grammar, Check.popsOf(s), s), rest)

law closed_returns:
  for +pred: Gll.Pred
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for +hc: {Check.closedWith(pred, grammar, input, s) == True{} : Bool}
  {Check.allReturns(Check.returnsOf(s), grammar, Check.popsOf(s), s) == True{} : Bool}

def closed_returns(pred, grammar, input, s, hc):
  +rest = Lemma.and_true_right_side(Check.allDescs(Check.seenOf(s), grammar, input, s), Bool.and(Check.allClusters(Check.clustersOf(s), pred, grammar, input, s), Check.allReturns(Check.returnsOf(s), grammar, Check.popsOf(s), s)), hc)
  Lemma.and_true_right_side(Check.allClusters(Check.clustersOf(s), pred, grammar, input, s), Check.allReturns(Check.returnsOf(s), grammar, Check.popsOf(s), s), rest)

# ---- A seen descriptor is ok ----

def desc_ok_pick(+d: Gll.Desc, +y: Gll.Desc, +rest: +List<Gll.Desc>, +grammar: +List<Core.Production>, +input: +List<Nat>, +s: Gll.GState,
  cases: Either<{Gll.descEq(d, y) == True{} : Bool}, {Gll.descIn(d, rest) == True{} : Bool}>,
  +here: {Check.descOk(y, grammar, input, s) == True{} : Bool},
  later: {Gll.descIn(d, rest) == True{} : Bool} -> {Check.descOk(d, grammar, input, s) == True{} : Bool})
  -> {Check.descOk(d, grammar, input, s) == True{} : Bool}:
  match cases:
    case Inl{e}:
      %Equal.sym(Gll.Desc, d, y, desc_eq_sound(d, y, e)) : {Check.descOk(_, grammar, input, s) == True{} : Bool}
      here
    case Inr{m}:
      later(m)

law desc_ok:
  for ds: +List<Gll.Desc>
  for +d: Gll.Desc
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for +all: {Check.allDescs(ds, grammar, input, s) == True{} : Bool}
  for +m: {Gll.descIn(d, ds) == True{} : Bool}
  {Check.descOk(d, grammar, input, s) == True{} : Bool}

def desc_ok(ds, d, grammar, input, s, all, m):
  match ds:
    case Nil{}:
      Empty.absurd({Check.descOk(d, grammar, input, s) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{+y, +rest}:
      desc_ok_pick(d, y, rest, grammar, input, s, Lemma.or_true_cases(Gll.descEq(d, y), Gll.descIn(d, rest), m),
        Lemma.and_true_left(Check.descOk(y, grammar, input, s), Check.allDescs(rest, grammar, input, s), all),
        later => desc_ok(rest, d, grammar, input, s, Lemma.and_true_right_side(Check.descOk(y, grammar, input, s), Check.allDescs(rest, grammar, input, s), all), later))

# ---- A cluster has its seeds ----

def seeds_pick(+x: Nat, +i: Nat, +x2: Nat, +i2: Nat, +rest: +List<Gll.CKey>, +pred: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, +s: Gll.GState,
  cases: Either<{Gll.keyEq(Gll.CKey{x, i}, Gll.CKey{x2, i2}) == True{} : Bool}, {Gll.keyIn(Gll.CKey{x, i}, rest) == True{} : Bool}>,
  +here: {Check.allSeen(Gll.productionsOf(grammar, pred, Core.tokAt(input, i2), x2, 0n, i2), s) == True{} : Bool},
  later: {Gll.keyIn(Gll.CKey{x, i}, rest) == True{} : Bool} -> {Check.allSeen(Gll.productionsOf(grammar, pred, Core.tokAt(input, i), x, 0n, i), s) == True{} : Bool})
  -> {Check.allSeen(Gll.productionsOf(grammar, pred, Core.tokAt(input, i), x, 0n, i), s) == True{} : Bool}:
  match cases:
    case Inl{+e}:
      +ex = Lemma.nat_eq_sound(x, x2, Lemma.and_true_left(Nat.is_eq(x, x2), Nat.is_eq(i, i2), e))
      +ei = Lemma.nat_eq_sound(i, i2, Lemma.and_true_right_side(Nat.is_eq(x, x2), Nat.is_eq(i, i2), e))
      %Equal.sym(Nat, x, x2, ex) : {Check.allSeen(Gll.productionsOf(grammar, pred, Core.tokAt(input, i), _, 0n, i), s) == True{} : Bool}
      %Equal.sym(Nat, i, i2, ei) : {Check.allSeen(Gll.productionsOf(grammar, pred, Core.tokAt(input, _), x2, 0n, _), s) == True{} : Bool}
      here
    case Inr{m}:
      later(m)

law cluster_seeds:
  for cs: +List<Gll.CKey>
  for +x: Nat
  for +i: Nat
  for +pred: Gll.Pred
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for +all: {Check.allClusters(cs, pred, grammar, input, s) == True{} : Bool}
  for +m: {Gll.keyIn(Gll.CKey{x, i}, cs) == True{} : Bool}
  {Check.allSeen(Gll.productionsOf(grammar, pred, Core.tokAt(input, i), x, 0n, i), s) == True{} : Bool}

def cluster_seeds(cs, x, i, pred, grammar, input, s, all, m):
  match cs:
    case Nil{}:
      Empty.absurd({Check.allSeen(Gll.productionsOf(grammar, pred, Core.tokAt(input, i), x, 0n, i), s) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{Gll.CKey{+x2, +i2}, +rest}:
      +mine = {Check.allSeen(Gll.productionsOf(grammar, pred, Core.tokAt(input, i2), x2, 0n, i2), s) : Bool}
      seeds_pick(x, i, x2, i2, rest, pred, grammar, input, s, Lemma.or_true_cases(Gll.keyEq(Gll.CKey{x, i}, Gll.CKey{x2, i2}), Gll.keyIn(Gll.CKey{x, i}, rest), m),
        Lemma.and_true_left(mine, Check.allClusters(rest, pred, grammar, input, s), all),
        later => cluster_seeds(rest, x, i, pred, grammar, input, s, Lemma.and_true_right_side(mine, Check.allClusters(rest, pred, grammar, input, s), all), later))

# ---- A return edge at a pop of its cluster resumes ----

def ret_pick(+key: Gll.CKey, +edge: Gll.Edge, +k2: Gll.CKey, +e2: Gll.Edge, +rest: +List<Gll.Ret>, +grammar: +List<Core.Production>, +pops: +List<Gll.Pop>, +s: Gll.GState,
  cases: Either<{Bool.and(Gll.keyEq(key, k2), Check.edgeEq(edge, e2)) == True{} : Bool}, {Check.retIn(key, edge, rest) == True{} : Bool}>,
  +here: {Check.edgePops(pops, grammar, k2, e2, s) == True{} : Bool},
  later: {Check.retIn(key, edge, rest) == True{} : Bool} -> {Check.edgePops(pops, grammar, key, edge, s) == True{} : Bool})
  -> {Check.edgePops(pops, grammar, key, edge, s) == True{} : Bool}:
  match cases:
    case Inl{+e}:
      +ek = key_eq_sound(key, k2, Lemma.and_true_left(Gll.keyEq(key, k2), Check.edgeEq(edge, e2), e))
      +ee = edge_eq_sound(edge, e2, Lemma.and_true_right_side(Gll.keyEq(key, k2), Check.edgeEq(edge, e2), e))
      %Equal.sym(Gll.CKey, key, k2, ek) : {Check.edgePops(pops, grammar, _, edge, s) == True{} : Bool}
      %Equal.sym(Gll.Edge, edge, e2, ee) : {Check.edgePops(pops, grammar, k2, _, s) == True{} : Bool}
      here
    case Inr{m}:
      later(m)

law ret_ok:
  for rs: +List<Gll.Ret>
  for +key: Gll.CKey
  for +edge: Gll.Edge
  for +grammar: +List<Core.Production>
  for +pops: +List<Gll.Pop>
  for +s: Gll.GState
  for +all: {Check.allReturns(rs, grammar, pops, s) == True{} : Bool}
  for +m: {Check.retIn(key, edge, rs) == True{} : Bool}
  {Check.edgePops(pops, grammar, key, edge, s) == True{} : Bool}

def ret_ok(rs, key, edge, grammar, pops, s, all, m):
  match rs:
    case Nil{}:
      Empty.absurd({Check.edgePops(pops, grammar, key, edge, s) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{Gll.Ret{+k2, +e2}, +rest}:
      +mine = {Check.edgePops(pops, grammar, k2, e2, s) : Bool}
      ret_pick(key, edge, k2, e2, rest, grammar, pops, s, Lemma.or_true_cases(Bool.and(Gll.keyEq(key, k2), Check.edgeEq(edge, e2)), Check.retIn(key, edge, rest), m),
        Lemma.and_true_left(mine, Check.allReturns(rest, grammar, pops, s), all),
        later => ret_ok(rest, key, edge, grammar, pops, s, Lemma.and_true_right_side(mine, Check.allReturns(rest, grammar, pops, s), all), later))

law hit_true:
  for b: Bool
  for +edge: Gll.Edge
  for +grammar: +List<Core.Production>
  for +kc: Nat
  for +j: Nat
  for +s: Gll.GState
  for +eb: {b == True{} : Bool}
  for +h: {Check.hitOk(b, edge, grammar, kc, j, s) == True{} : Bool}
  {Check.edgeOk(edge, grammar, kc, j, s) == True{} : Bool}

def hit_true(b, edge, grammar, kc, j, s, eb, h):
  match b:
    case True{}:
      h
    case False{}:
      Empty.absurd({Check.edgeOk(edge, grammar, kc, j, s) == True{} : Bool}, Lemma.false_is_not_true(eb))

def pop_pick(+x: Nat, +kc: Nat, +edge: Gll.Edge, +j: Nat, +k2: Gll.CKey, +j2: Nat, +rest: +List<Gll.Pop>, +grammar: +List<Core.Production>, +s: Gll.GState,
  cases: Either<{Bool.and(Gll.keyEq(Gll.CKey{x, kc}, k2), Nat.is_eq(j, j2)) == True{} : Bool}, {Gll.popIn(Gll.CKey{x, kc}, j, rest) == True{} : Bool}>,
  +here: {Check.hitOk(Gll.keyEq(Gll.CKey{x, kc}, k2), edge, grammar, kc, j2, s) == True{} : Bool},
  later: {Gll.popIn(Gll.CKey{x, kc}, j, rest) == True{} : Bool} -> {Check.edgeOk(edge, grammar, kc, j, s) == True{} : Bool})
  -> {Check.edgeOk(edge, grammar, kc, j, s) == True{} : Bool}:
  match cases:
    case Inl{+e}:
      +hk = Lemma.and_true_left(Gll.keyEq(Gll.CKey{x, kc}, k2), Nat.is_eq(j, j2), e)
      +ej = Lemma.nat_eq_sound(j, j2, Lemma.and_true_right_side(Gll.keyEq(Gll.CKey{x, kc}, k2), Nat.is_eq(j, j2), e))
      %Equal.sym(Nat, j, j2, ej) : {Check.edgeOk(edge, grammar, kc, _, s) == True{} : Bool}
      hit_true(Gll.keyEq(Gll.CKey{x, kc}, k2), edge, grammar, kc, j2, s, hk, here)
    case Inr{m}:
      later(m)

law pop_ok:
  for ps: +List<Gll.Pop>
  for +x: Nat
  for +kc: Nat
  for +edge: Gll.Edge
  for +j: Nat
  for +grammar: +List<Core.Production>
  for +s: Gll.GState
  for +all: {Check.edgePops(ps, grammar, Gll.CKey{x, kc}, edge, s) == True{} : Bool}
  for +m: {Gll.popIn(Gll.CKey{x, kc}, j, ps) == True{} : Bool}
  {Check.edgeOk(edge, grammar, kc, j, s) == True{} : Bool}

def pop_ok(ps, x, kc, edge, j, grammar, s, all, m):
  match ps:
    case Nil{}:
      Empty.absurd({Check.edgeOk(edge, grammar, kc, j, s) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{Gll.Pop{+k2, +j2}, +rest}:
      +mine = {Check.hitOk(Gll.keyEq(Gll.CKey{x, kc}, k2), edge, grammar, kc, j2, s) : Bool}
      pop_pick(x, kc, edge, j, k2, j2, rest, grammar, s, Lemma.or_true_cases(Bool.and(Gll.keyEq(Gll.CKey{x, kc}, k2), Nat.is_eq(j, j2)), Gll.popIn(Gll.CKey{x, kc}, j, rest), m),
        Lemma.and_true_left(mine, Check.edgePops(rest, grammar, Gll.CKey{x, kc}, edge, s), all),
        later => pop_ok(rest, x, kc, edge, j, grammar, s, Lemma.and_true_right_side(mine, Check.edgePops(rest, grammar, Gll.CKey{x, kc}, edge, s), all), later))

# ---- The seeds of a cluster ----

law keep_rest:
  for b: Bool
  for +d: Gll.Desc
  for +ds: +List<Gll.Desc>
  for +s: Gll.GState
  for +h: {Check.allSeen(Gll.keepDesc(b, d, ds), s) == True{} : Bool}
  {Check.allSeen(ds, s) == True{} : Bool}

def keep_rest(b, d, ds, s, h):
  match b:
    case True{}:
      Lemma.and_true_right_side(Check.seenIn(d, s), Check.allSeen(ds, s), h)
    case False{}:
      h

law keep_here:
  for b: Bool
  for +d: Gll.Desc
  for +ds: +List<Gll.Desc>
  for +s: Gll.GState
  for +eb: {b == True{} : Bool}
  for +h: {Check.allSeen(Gll.keepDesc(b, d, ds), s) == True{} : Bool}
  {Check.seenIn(d, s) == True{} : Bool}

def keep_here(b, d, ds, s, eb, h):
  match b:
    case True{}:
      Lemma.and_true_left(Check.seenIn(d, s), Check.allSeen(ds, s), h)
    case False{}:
      Empty.absurd({Check.seenIn(d, s) == True{} : Bool}, Lemma.false_is_not_true(eb))

law seed_seen:
  for g: +List<Core.Production>
  for q: Nat
  for +x: Nat
  for +base: Nat
  for +i: Nat
  for +s: Gll.GState
  for +pred: Gll.Pred
  for +tok: Maybe<&2, Nat>
  for +h: {Core.lhsIs(g, q, x) == True{} : Bool}
  for +ha: {Gll.admits(pred, Nat.add(base, q), tok) == True{} : Bool}
  for +all: {Check.allSeen(Gll.productionsOf(g, pred, tok, x, base, i), s) == True{} : Bool}
  {Check.seenIn(Gll.Desc{Nat.add(base, q), 0n, i, i}, s) == True{} : Bool}

def seed_seen(g, q, x, base, i, s, pred, tok, h, ha, all):
  match g q:
    case Nil{} +q0:
      Empty.absurd({Check.seenIn(Gll.Desc{Nat.add(base, q0), 0n, i, i}, s) == True{} : Bool}, Lemma.false_is_not_true(h))
    case Con{Core.Production{+lhs, +rhs}, +rest} 0n:
      +ha0 = {(%Lemma.add_zero_right(base) : {Gll.admits(pred, _, tok) == True{} : Bool}
        ha) : {Gll.admits(pred, base, tok) == True{} : Bool}}
      %Equal.sym(Nat, Nat.add(base, 0n), base, Lemma.add_zero_right(base)) : {Check.seenIn(Gll.Desc{_, 0n, i, i}, s) == True{} : Bool}
      keep_here(Bool.and(Gll.admits(pred, base, tok), Nat.is_eq(lhs, x)), Gll.Desc{base, 0n, i, i}, Gll.productionsOf(rest, pred, tok, x, 1n+base, i), s,
        Lemma.and_true_intro(Gll.admits(pred, base, tok), Nat.is_eq(lhs, x), ha0, h), all)
    case Con{Core.Production{+lhs, +rhs}, +rest} 1n+(+n):
      +ha1 = {(%Lemma.add_succ_right(base, n) : {Gll.admits(pred, _, tok) == True{} : Bool}
        ha) : {Gll.admits(pred, 1n+Nat.add(base, n), tok) == True{} : Bool}}
      %Equal.sym(Nat, Nat.add(base, 1n+n), 1n+Nat.add(base, n), Lemma.add_succ_right(base, n)) : {Check.seenIn(Gll.Desc{_, 0n, i, i}, s) == True{} : Bool}
      seed_seen(rest, n, x, 1n+base, i, s, pred, tok, h, ha1, keep_rest(Bool.and(Gll.admits(pred, base, tok), Nat.is_eq(lhs, x)), Gll.Desc{base, 0n, i, i}, Gll.productionsOf(rest, pred, tok, x, 1n+base, i), s, all))

law lhs_of:
  for g: +List<Core.Production>
  for q: Nat
  for +x: Nat
  for +h: {Core.lhsIs(g, q, x) == True{} : Bool}
  {Gll.lhsOf(g, q) == x : Nat}

def lhs_of(g, q, x, h):
  match g q:
    case Nil{} +q0:
      Empty.absurd({Gll.lhsOf([], q0) == x : Nat}, Lemma.false_is_not_true(h))
    case Con{Core.Production{+lhs, +rhs}, +rest} 0n:
      Lemma.nat_eq_sound(lhs, x, h)
    case Con{+p, +rest} 1n+(+n):
      lhs_of(rest, n, x, h)

# ======== POSITIONS IN THE GRAMMAR ========

# The items of a sequence from the dot on.
def dropFrom(n: Nat, items: +List<Core.Sym>) -> +List<Core.Sym>:
  match n items:
    case 0n _:
      items
    case 1n+m Nil{}:
      []
    case 1n+m Con{x, rest}:
      dropFrom(m, rest)

def symHead(xs: +List<Core.Sym>, +d: Core.Sym) -> Core.Sym:
  match xs:
    case Nil{}:
      d
    case Con{x, rest}:
      x

def symTail(xs: +List<Core.Sym>) -> +List<Core.Sym>:
  match xs:
    case Nil{}:
      []
    case Con{x, rest}:
      rest

law syms_cons_not_nil:
  for +y: Core.Sym
  for +r: +List<Core.Sym>
  for +e: {[] == y <> r : +List<Core.Sym>}
  Empty

def syms_cons_not_nil(y, r, e):
  Lemma.true_is_not_false(Equal.cong(+List<Core.Sym>, Bool, v => List.is_empty(&2, Core.Sym, v), [], y <> r, e))

law nth_drop:
  for items: +List<Core.Sym>
  for d: Nat
  for +y: Core.Sym
  for +rest: +List<Core.Sym>
  for +e: {dropFrom(d, items) == y <> rest : +List<Core.Sym>}
  {Gll.nthSym(items, d) == Some{y} : Maybe<&2, Core.Sym>}

def nth_drop(items, d, y, rest, e):
  match items d:
    case Nil{} 0n:
      Empty.absurd({Gll.nthSym([], 0n) == Some{y} : Maybe<&2, Core.Sym>}, syms_cons_not_nil(y, rest, e))
    case Nil{} 1n+(+m):
      Empty.absurd({Gll.nthSym([], 1n+m) == Some{y} : Maybe<&2, Core.Sym>}, syms_cons_not_nil(y, rest, e))
    case Con{+x, +xs} 0n:
      Equal.cong(Core.Sym, Maybe<&2, Core.Sym>, v => Some{v}, x, y, Equal.cong(+List<Core.Sym>, Core.Sym, v => symHead(v, x), x <> xs, y <> rest, e))
    case Con{+x, +xs} 1n+(+m):
      nth_drop(xs, m, y, rest, e)

law drop_next:
  for items: +List<Core.Sym>
  for d: Nat
  for +y: Core.Sym
  for +rest: +List<Core.Sym>
  for +e: {dropFrom(d, items) == y <> rest : +List<Core.Sym>}
  {dropFrom(1n+d, items) == rest : +List<Core.Sym>}

def drop_next(items, d, y, rest, e):
  match items d:
    case Nil{} 0n:
      Empty.absurd({dropFrom(1n, []) == rest : +List<Core.Sym>}, syms_cons_not_nil(y, rest, e))
    case Nil{} 1n+(+m):
      Empty.absurd({dropFrom(2n+m, []) == rest : +List<Core.Sym>}, syms_cons_not_nil(y, rest, e))
    case Con{+x, +xs} 0n:
      Equal.cong(+List<Core.Sym>, +List<Core.Sym>, v => symTail(v), x <> xs, y <> rest, e)
    case Con{+x, +xs} 1n+(+m):
      drop_next(xs, m, y, rest, e)

law nth_none:
  for items: +List<Core.Sym>
  for d: Nat
  for +e: {dropFrom(d, items) == [] : +List<Core.Sym>}
  {Gll.nthSym(items, d) == None{} : Maybe<&2, Core.Sym>}

def nth_none(items, d, e):
  match items d:
    case Nil{} +m:
      {==}
    case Con{+x, +xs} 0n:
      Empty.absurd({Gll.nthSym(x <> xs, 0n) == None{} : Maybe<&2, Core.Sym>}, syms_cons_not_nil(x, xs, Equal.sym(+List<Core.Sym>, x <> xs, [], e)))
    case Con{+x, +xs} 1n+(+m):
      nth_none(xs, m, e)

# ======== POSITIONS IN THE INPUT ========

# Where a forest that starts at k ends, counted as `steps` and `reads` count.
def endOf(forest: +List<Core.Tree>, +k: Nat) -> Nat:
  match forest:
    case Nil{}:
      k
    case Con{Core.Leaf{kind}, ts}:
      endOf(ts, 1n+k)
    case Con{Core.Node{+q, +ch}, ts}:
      endOf(ts, Nat.add(k, Core.width(Core.Node{q, ch})))

law end_eq:
  for f: +List<Core.Tree>
  for +k: Nat
  {endOf(f, k) == Nat.add(k, List.length(&2, Nat, Core.leaves(f))) : Nat}

def end_eq(f, k):
  match f:
    case Nil{}:
      Equal.sym(Nat, Nat.add(k, 0n), k, Lemma.add_zero_right(k))
    case Con{Core.Leaf{+a}, +ts}:
      +n = {List.length(&2, Nat, Core.leaves(ts)) : Nat}
      Equal.trans(Nat, endOf(ts, 1n+k), 1n+Nat.add(k, n), Nat.add(k, 1n+n), end_eq(ts, 1n+k), Equal.sym(Nat, Nat.add(k, 1n+n), 1n+Nat.add(k, n), Lemma.add_succ_right(k, n)))
    case Con{Core.Node{+q, +ch}, +ts}:
      +w = {Core.width(Core.Node{q, ch}) : Nat}
      +lc = {List.length(&2, Nat, Core.leaves(ch)) : Nat}
      +lt = {List.length(&2, Nat, Core.leaves(ts)) : Nat}
      +wl = Equal.cong(+List<Nat>, Nat, v => List.length(&2, Nat, v), List.append(&2, Nat, Core.leaves(ch), []), Core.leaves(ch), Lemma.append_nil_right(Core.leaves(ch)))
      Equal.trans(Nat, endOf(ts, Nat.add(k, w)), Nat.add(Nat.add(k, w), lt), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, Core.leaves(ch), Core.leaves(ts)))), end_eq(ts, Nat.add(k, w)),
        Equal.trans(Nat, Nat.add(Nat.add(k, w), lt), Nat.add(k, Nat.add(w, lt)), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, Core.leaves(ch), Core.leaves(ts)))), Lemma.add_assoc(k, w, lt),
          Equal.trans(Nat, Nat.add(k, Nat.add(w, lt)), Nat.add(k, Nat.add(lc, lt)), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, Core.leaves(ch), Core.leaves(ts)))),
            Equal.cong(Nat, Nat, v => Nat.add(k, Nat.add(v, lt)), w, lc, wl),
            Equal.cong(Nat, Nat, v => Nat.add(k, v), Nat.add(lc, lt), List.length(&2, Nat, List.append(&2, Nat, Core.leaves(ch), Core.leaves(ts))), Equal.sym(Nat, List.length(&2, Nat, List.append(&2, Nat, Core.leaves(ch), Core.leaves(ts))), Nat.add(lc, lt), Lemma.length_append(Core.leaves(ch), Core.leaves(ts)))))))

# A node's children end where the node does.
law end_node:
  for +q: Nat
  for +ch: +List<Core.Tree>
  for +k: Nat
  {endOf(ch, k) == Nat.add(k, Core.width(Core.Node{q, ch})) : Nat}

def end_node(q, ch, k):
  Equal.trans(Nat, endOf(ch, k), Nat.add(k, List.length(&2, Nat, Core.leaves(ch))), Nat.add(k, Core.width(Core.Node{q, ch})), end_eq(ch, k),
    Equal.cong(+List<Nat>, Nat, v => Nat.add(k, List.length(&2, Nat, v)), Core.leaves(ch), List.append(&2, Nat, Core.leaves(ch), []), Equal.sym(+List<Nat>, List.append(&2, Nat, Core.leaves(ch), []), Core.leaves(ch), Lemma.append_nil_right(Core.leaves(ch)))))

# ======== NEEDS ========

law need_holds:
  for need: Core.Need
  for w: Nat
  for +k: Nat
  for +h: {Core.needOk(need, w) == True{} : Bool}
  {Gll.needHolds(need, k, Nat.add(k, w)) == True{} : Bool}

def need_holds(need, w, k, h):
  match need w:
    case Core.Anything{} +w0:
      {==}
    case Core.Something{} 0n:
      Empty.absurd({Gll.needHolds(Core.Something{}, k, Nat.add(k, 0n)) == True{} : Bool}, Lemma.false_is_not_true(h))
    case Core.Something{} 1n+(+n):
      +far = {Nat.add(k, 1n+n) : Nat}
      %Equal.sym(Bool, Nat.is_eq(k, far), False{}, Equal.trans(Bool, Nat.is_eq(k, far), Nat.is_eq(far, k), False{}, Lemma.nat_eq_symm(k, far), Lemma.add_succ_ne(k, n))) : {Bool.not(_) == True{} : Bool}
      {==}
    case Core.Nothing{} 0n:
      %Equal.sym(Nat, Nat.add(k, 0n), k, Lemma.add_zero_right(k)) : {Nat.is_eq(k, _) == True{} : Bool}
      Lemma.nat_eq_refl(k)
    case Core.Nothing{} 1n+(+n):
      Empty.absurd({Gll.needHolds(Core.Nothing{}, k, Nat.add(k, 1n+n)) == True{} : Bool}, Lemma.false_is_not_true(h))

law need_at:
  for +grammar: +List<Core.Production>
  for +q: Nat
  for +d: Nat
  for +x: Nat
  for +need: Core.Need
  for +rest: +List<Core.Sym>
  for +ie: {dropFrom(d, Core.rhsOf(grammar, q)) == Core.Nonterminal{x, need} <> rest : +List<Core.Sym>}
  {Gll.needAt(grammar, q, d) == need : Core.Need}

def need_at(grammar, q, d, x, need, rest, ie):
  %Equal.sym(Maybe<&2, Core.Sym>, Gll.nthSym(Core.rhsOf(grammar, q), d), Some{Core.Nonterminal{x, need}}, nth_drop(Core.rhsOf(grammar, q), d, Core.Nonterminal{x, need}, rest, ie)) : {Gll.needOf(_) == need : Core.Need}
  {==}

# ======== THE WALK ========

# What a closed state holds for a forest read from k, the rest of production q from dot d,
# in a node that started at ks: the node's own steps for these children, all steps below
# them, and the pop of the node's cluster where the forest ends.
def Walked(+grammar: +List<Core.Production>, +s: Gll.GState, +q: Nat, +ks: Nat, +f: +List<Core.Tree>, +d: Nat, +k: Nat) -> Type:
  {Core.allIn(Core.own(q, f, d, ks, k), Check.stepsOf(s)) == True{} : Bool} &
  {Core.allIn(Core.steps(f, k), Check.stepsOf(s)) == True{} : Bool} &
  {Gll.popIn(Gll.CKey{Gll.lhsOf(grammar, q), ks}, endOf(f, k), Check.popsOf(s)) == True{} : Bool}

law all_in_app:
  for xs: +List<Core.Bsr>
  for +ys: +List<Core.Bsr>
  for +set: +List<Core.Bsr>
  for +hx: {Core.allIn(xs, set) == True{} : Bool}
  for +hy: {Core.allIn(ys, set) == True{} : Bool}
  {Core.allIn(List.append(&2, Core.Bsr, xs, ys), set) == True{} : Bool}

def all_in_app(xs, ys, set, hx, hy):
  match xs:
    case Nil{}:
      hy
    case Con{+x, +rest}:
      Lemma.and_true_intro(Core.member(x, set), Core.allIn(List.append(&2, Core.Bsr, rest, ys), set),
        Lemma.and_true_left(Core.member(x, set), Core.allIn(rest, set), hx),
        all_in_app(rest, ys, set, Lemma.and_true_right_side(Core.member(x, set), Core.allIn(rest, set), hx), hy))

# The descriptor's item, as the check reads it.
law desc_item:
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for +q: Nat
  for +d: Nat
  for +ks: Nat
  for +k: Nat
  for +y: Core.Sym
  for +rest: +List<Core.Sym>
  for +ie: {dropFrom(d, Core.rhsOf(grammar, q)) == y <> rest : +List<Core.Sym>}
  for +h: {Check.descOk(Gll.Desc{q, d, ks, k}, grammar, input, s) == True{} : Bool}
  {Check.itemOk(Some{y}, grammar, input, q, d, ks, k, s) == True{} : Bool}

def desc_item(grammar, input, s, q, d, ks, k, y, rest, ie, h):
  %nth_drop(Core.rhsOf(grammar, q), d, y, rest, ie) : {Check.itemOk(_, grammar, input, q, d, ks, k, s) == True{} : Bool}
  h

law desc_end:
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for +q: Nat
  for +d: Nat
  for +ks: Nat
  for +k: Nat
  for +ie: {dropFrom(d, Core.rhsOf(grammar, q)) == [] : +List<Core.Sym>}
  for +h: {Check.descOk(Gll.Desc{q, d, ks, k}, grammar, input, s) == True{} : Bool}
  {Check.itemOk(None{}, grammar, input, q, d, ks, k, s) == True{} : Bool}

def desc_end(grammar, input, s, q, d, ks, k, ie, h):
  %nth_none(Core.rhsOf(grammar, q), d, ie) : {Check.itemOk(_, grammar, input, q, d, ks, k, s) == True{} : Bool}
  h

law empty_own:
  for dot: Nat
  for +q: Nat
  for +ks: Nat
  for +k: Nat
  for +s: Gll.GState
  for +h: {Check.emptyOk(dot, q, ks, k, s) == True{} : Bool}
  {Core.allIn(Core.emptyAt(dot, q, ks, k), Check.stepsOf(s)) == True{} : Bool}

def empty_own(dot, q, ks, k, s, h):
  match dot:
    case 0n:
      Lemma.and_true_intro(Core.member(Core.Bsr{q, 0n, ks, k, k}, Check.stepsOf(s)), True{}, h, {==})
    case 1n+(+n):
      {==}

law token_parts:
  for b: Bool
  for +q: Nat
  for +d: Nat
  for +ks: Nat
  for +k: Nat
  for +s: Gll.GState
  for +eb: {b == True{} : Bool}
  for +h: {Check.tokenOk(b, q, d, ks, k, s) == True{} : Bool}
  {Bool.and(Check.seenIn(Gll.Desc{q, 1n+d, ks, 1n+k}, s), Check.stepIn(Core.Bsr{q, 1n+d, ks, k, 1n+k}, s)) == True{} : Bool}

def token_parts(b, q, d, ks, k, s, eb, h):
  match b:
    case True{}:
      h
    case False{}:
      Empty.absurd({Bool.and(Check.seenIn(Gll.Desc{q, 1n+d, ks, 1n+k}, s), Check.stepIn(Core.Bsr{q, 1n+d, ks, k, 1n+k}, s)) == True{} : Bool}, Lemma.false_is_not_true(eb))

law resume_parts:
  for b: Bool
  for +q: Nat
  for +d: Nat
  for +ks: Nat
  for +kc: Nat
  for +j: Nat
  for +s: Gll.GState
  for +eb: {b == True{} : Bool}
  for +h: {Check.resumeOk(b, q, d, ks, kc, j, s) == True{} : Bool}
  {Bool.and(Check.seenIn(Gll.Desc{q, 1n+d, ks, j}, s), Check.stepIn(Core.Bsr{q, 1n+d, ks, kc, j}, s)) == True{} : Bool}

def resume_parts(b, q, d, ks, kc, j, s, eb, h):
  match b:
    case True{}:
      h
    case False{}:
      Empty.absurd({Bool.and(Check.seenIn(Gll.Desc{q, 1n+d, ks, j}, s), Check.stepIn(Core.Bsr{q, 1n+d, ks, kc, j}, s)) == True{} : Bool}, Lemma.false_is_not_true(eb))

law token_here:
  for +input: +List<Nat>
  for +k: Nat
  for +a: Nat
  for +t: Nat
  for +ea: {a == t : Nat}
  for +h: {Core.tokIs(Core.tokAt(input, k), a) == True{} : Bool}
  {Core.tokIs(Core.tokAt(input, k), t) == True{} : Bool}

def token_here(input, k, a, t, ea, h):
  %ea : {Core.tokIs(Core.tokAt(input, k), _) == True{} : Bool}
  h

law leaf_own:
  for +s: Gll.GState
  for +q: Nat
  for +ks: Nat
  for +a: Nat
  for +ts: +List<Core.Tree>
  for +d: Nat
  for +k: Nat
  for +step: {Check.stepIn(Core.Bsr{q, 1n+d, ks, k, 1n+k}, s) == True{} : Bool}
  for +o: {Core.allIn(Core.own(q, ts, 1n+d, ks, 1n+k), Check.stepsOf(s)) == True{} : Bool}
  {Core.allIn(Core.own(q, Core.Leaf{a} <> ts, d, ks, k), Check.stepsOf(s)) == True{} : Bool}

def leaf_own(s, q, ks, a, ts, d, k, step, o):
  %Equal.sym(Nat, Nat.add(k, 1n), 1n+k, Lemma.add_one_right(k)) : {Core.allIn(Core.Bsr{q, 1n+d, ks, k, _} <> Core.own(q, ts, 1n+d, ks, _), Check.stepsOf(s)) == True{} : Bool}
  Lemma.and_true_intro(Core.member(Core.Bsr{q, 1n+d, ks, k, 1n+k}, Check.stepsOf(s)), Core.allIn(Core.own(q, ts, 1n+d, ks, 1n+k), Check.stepsOf(s)), step, o)

# After a leaf: its step, then the rest's.
def leaf_join(+grammar: +List<Core.Production>, +s: Gll.GState, +q: Nat, +ks: Nat, +a: Nat, +ts: +List<Core.Tree>, +d: Nat, +k: Nat,
  +step: {Check.stepIn(Core.Bsr{q, 1n+d, ks, k, 1n+k}, s) == True{} : Bool},
  rest: Walked(grammar, s, q, ks, ts, 1n+d, 1n+k)) -> Walked(grammar, s, q, ks, Core.Leaf{a} <> ts, d, k):
  match rest:
    case (o, (st, p)):
      +own = leaf_own(s, q, ks, a, ts, d, k, step, o)
      {(own, (st, p)) : Walked(grammar, s, q, ks, Core.Leaf{a} <> ts, d, k)}

# After a node: its step, the steps below it, then the rest's.
def node_join(+grammar: +List<Core.Production>, +s: Gll.GState, +q: Nat, +ks: Nat, +q2: Nat, +ch: +List<Core.Tree>, +ts: +List<Core.Tree>, +d: Nat, +k: Nat,
  +step: {Check.stepIn(Core.Bsr{q, 1n+d, ks, k, Nat.add(k, Core.width(Core.Node{q2, ch}))}, s) == True{} : Bool},
  +oc: {Core.allIn(Core.own(q2, ch, 0n, k, k), Check.stepsOf(s)) == True{} : Bool},
  +sc: {Core.allIn(Core.steps(ch, k), Check.stepsOf(s)) == True{} : Bool},
  rest: Walked(grammar, s, q, ks, ts, 1n+d, Nat.add(k, Core.width(Core.Node{q2, ch})))) -> Walked(grammar, s, q, ks, Core.Node{q2, ch} <> ts, d, k):
  match rest:
    case (o, (st, p)):
      +far = {Nat.add(k, Core.width(Core.Node{q2, ch})) : Nat}
      +own = Lemma.and_true_intro(Core.member(Core.Bsr{q, 1n+d, ks, k, far}, Check.stepsOf(s)), Core.allIn(Core.own(q, ts, 1n+d, ks, far), Check.stepsOf(s)), step, o)
      +below = all_in_app(Core.own(q2, ch, 0n, k, k), List.append(&2, Core.Bsr, Core.steps(ch, k), Core.steps(ts, far)), Check.stepsOf(s), oc, all_in_app(Core.steps(ch, k), Core.steps(ts, far), Check.stepsOf(s), sc, st))
      {(own, (below, p)) : Walked(grammar, s, q, ks, Core.Node{q2, ch} <> ts, d, k)}

law pop_at:
  for +grammar: +List<Core.Production>
  for +s: Gll.GState
  for +q2: Nat
  for +x: Nat
  for +ch: +List<Core.Tree>
  for +k: Nat
  for +lhs: {Core.lhsIs(grammar, q2, x) == True{} : Bool}
  for +p: {Gll.popIn(Gll.CKey{Gll.lhsOf(grammar, q2), k}, endOf(ch, k), Check.popsOf(s)) == True{} : Bool}
  {Gll.popIn(Gll.CKey{x, k}, Nat.add(k, Core.width(Core.Node{q2, ch})), Check.popsOf(s)) == True{} : Bool}

def pop_at(grammar, s, q2, x, ch, k, lhs, p):
  %lhs_of(grammar, q2, x, lhs) : {Gll.popIn(Gll.CKey{_, k}, Nat.add(k, Core.width(Core.Node{q2, ch})), Check.popsOf(s)) == True{} : Bool}
  %end_node(q2, ch, k) : {Gll.popIn(Gll.CKey{Gll.lhsOf(grammar, q2), k}, _, Check.popsOf(s)) == True{} : Bool}
  p

law need_here:
  for +grammar: +List<Core.Production>
  for +q: Nat
  for +d: Nat
  for +x: Nat
  for +need: Core.Need
  for +rest: +List<Core.Sym>
  for +k: Nat
  for +w: Nat
  for +ie: {dropFrom(d, Core.rhsOf(grammar, q)) == Core.Nonterminal{x, need} <> rest : +List<Core.Sym>}
  for +h: {Core.needOk(need, w) == True{} : Bool}
  {Gll.needHolds(Gll.needAt(grammar, q, d), k, Nat.add(k, w)) == True{} : Bool}

def need_here(grammar, q, d, x, need, rest, k, w, ie, h):
  %Equal.sym(Core.Need, Gll.needAt(grammar, q, d), need, need_at(grammar, q, d, x, need, rest, ie)) : {Gll.needHolds(_, k, Nat.add(k, w)) == True{} : Bool}
  need_holds(need, w, k, h)

# A node's children are walked: resume its caller at their end, then walk the rest.
def node_rest(+pred: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, +s: Gll.GState, +hc: {Check.closedWith(pred, grammar, input, s) == True{} : Bool},
  +q: Nat, +ks: Nat, +q2: Nat, +ch: +List<Core.Tree>, +ts: +List<Core.Tree>, +d: Nat, +k: Nat, +x: Nat, +need: Core.Need, +rest: +List<Core.Sym>,
  +ie: {dropFrom(d, Core.rhsOf(grammar, q)) == Core.Nonterminal{x, need} <> rest : +List<Core.Sym>},
  +lhs: {Core.lhsIs(grammar, q2, x) == True{} : Bool},
  +nk: {Core.needOk(need, Core.width(Core.Node{q2, ch})) == True{} : Bool},
  +rt: {Check.retIn(Gll.CKey{x, k}, Gll.Edge{q, d, ks}, Check.returnsOf(s)) == True{} : Bool},
  below: Walked(grammar, s, q2, k, ch, 0n, k),
  recTs: {Check.seenIn(Gll.Desc{q, 1n+d, ks, Nat.add(k, Core.width(Core.Node{q2, ch}))}, s) == True{} : Bool} -> Walked(grammar, s, q, ks, ts, 1n+d, Nat.add(k, Core.width(Core.Node{q2, ch}))))
  -> Walked(grammar, s, q, ks, Core.Node{q2, ch} <> ts, d, k):
  match below:
    case (oc, (sc, pc)):
      +far = {Nat.add(k, Core.width(Core.Node{q2, ch})) : Nat}
      +edge = {Gll.Edge{q, d, ks} : Gll.Edge}
      +ep = ret_ok(Check.returnsOf(s), Gll.CKey{x, k}, edge, grammar, Check.popsOf(s), s, closed_returns(pred, grammar, input, s, hc), rt)
      +eo = pop_ok(Check.popsOf(s), x, k, edge, far, grammar, s, ep, pop_at(grammar, s, q2, x, ch, k, lhs, pc))
      +nh = need_here(grammar, q, d, x, need, rest, k, Core.width(Core.Node{q2, ch}), ie, nk)
      +both = resume_parts(Gll.needHolds(Gll.needAt(grammar, q, d), k, far), q, d, ks, k, far, s, nh, eo)
      +seen = Lemma.and_true_left(Check.seenIn(Gll.Desc{q, 1n+d, ks, far}, s), Check.stepIn(Core.Bsr{q, 1n+d, ks, k, far}, s), both)
      +step = Lemma.and_true_right_side(Check.seenIn(Gll.Desc{q, 1n+d, ks, far}, s), Check.stepIn(Core.Bsr{q, 1n+d, ks, k, far}, s), both)
      node_join(grammar, s, q, ks, q2, ch, ts, d, k, step, oc, sc, recTs(seen))

law walk:
  for f: +List<Core.Tree>
  for items: +List<Core.Sym>
  for +pred: Gll.Pred
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for +hc: {Check.closedWith(pred, grammar, input, s) == True{} : Bool}
  for +q: Nat
  for +d: Nat
  for +ks: Nat
  for +k: Nat
  for +ie: {dropFrom(d, Core.rhsOf(grammar, q)) == items : +List<Core.Sym>}
  for +r: {Core.reads(f, grammar, items, input, k) == True{} : Bool}
  for +sd: {Check.seenIn(Gll.Desc{q, d, ks, k}, s) == True{} : Bool}
  for +ad: {Check.admitsAll(f, pred, input, k) == True{} : Bool}
  Walked(grammar, s, q, ks, f, d, k)

def walk(f, items, pred, grammar, input, s, hc, q, d, ks, k, ie, r, sd, ad):
  match f items:
    case Nil{} Nil{}:
      +ok = desc_end(grammar, input, s, q, d, ks, k, ie, desc_ok(Check.seenOf(s), Gll.Desc{q, d, ks, k}, grammar, input, s, closed_descs(pred, grammar, input, s, hc), sd))
      +em = {Check.emptyOk(d, q, ks, k, s) : Bool}
      +pop = {Gll.popIn(Gll.CKey{Gll.lhsOf(grammar, q), ks}, k, Check.popsOf(s)) : Bool}
      +own = empty_own(d, q, ks, k, s, Lemma.and_true_left(em, pop, ok))
      +ended = Lemma.and_true_right_side(em, pop, ok)
      {(own, ({==}, ended)) : Walked(grammar, s, q, ks, [], d, k)}
    case Nil{} Con{+y, +ys}:
      Empty.absurd(Walked(grammar, s, q, ks, [], d, k), Lemma.false_is_not_true(r))
    case Con{Core.Leaf{+a}, +ts} Nil{}:
      Empty.absurd(Walked(grammar, s, q, ks, Core.Leaf{a} <> ts, d, k), Lemma.false_is_not_true(r))
    case Con{Core.Leaf{+a}, +ts} Con{Core.Nonterminal{+x, +need}, +rest}:
      Empty.absurd(Walked(grammar, s, q, ks, Core.Leaf{a} <> ts, d, k), Lemma.false_is_not_true(r))
    case Con{Core.Leaf{+a}, +ts} Con{Core.Terminal{+t}, +rest}:
      +more = {Bool.and(Core.tokIs(Core.tokAt(input, k), a), Core.reads(ts, grammar, rest, input, 1n+k)) : Bool}
      +ea = Lemma.nat_eq_sound(a, t, Lemma.and_true_left(Nat.is_eq(a, t), more, r))
      +tk = token_here(input, k, a, t, ea, Lemma.and_true_left(Core.tokIs(Core.tokAt(input, k), a), Core.reads(ts, grammar, rest, input, 1n+k), Lemma.and_true_right_side(Nat.is_eq(a, t), more, r)))
      +rt = Lemma.and_true_right_side(Core.tokIs(Core.tokAt(input, k), a), Core.reads(ts, grammar, rest, input, 1n+k), Lemma.and_true_right_side(Nat.is_eq(a, t), more, r))
      +ok = desc_item(grammar, input, s, q, d, ks, k, Core.Terminal{t}, rest, ie, desc_ok(Check.seenOf(s), Gll.Desc{q, d, ks, k}, grammar, input, s, closed_descs(pred, grammar, input, s, hc), sd))
      +both = token_parts(Core.tokIs(Core.tokAt(input, k), t), q, d, ks, k, s, tk, ok)
      +seen = Lemma.and_true_left(Check.seenIn(Gll.Desc{q, 1n+d, ks, 1n+k}, s), Check.stepIn(Core.Bsr{q, 1n+d, ks, k, 1n+k}, s), both)
      +step = Lemma.and_true_right_side(Check.seenIn(Gll.Desc{q, 1n+d, ks, 1n+k}, s), Check.stepIn(Core.Bsr{q, 1n+d, ks, k, 1n+k}, s), both)
      leaf_join(grammar, s, q, ks, a, ts, d, k, step,
        walk(ts, rest, pred, grammar, input, s, hc, q, 1n+d, ks, 1n+k, drop_next(Core.rhsOf(grammar, q), d, Core.Terminal{t}, rest, ie), rt, seen, ad))
    case Con{Core.Node{+q2, +ch}, +ts} Nil{}:
      Empty.absurd(Walked(grammar, s, q, ks, Core.Node{q2, ch} <> ts, d, k), Lemma.false_is_not_true(r))
    case Con{Core.Node{+q2, +ch}, +ts} Con{Core.Terminal{+t}, +rest}:
      Empty.absurd(Walked(grammar, s, q, ks, Core.Node{q2, ch} <> ts, d, k), Lemma.false_is_not_true(r))
    case Con{Core.Node{+q2, +ch}, +ts} Con{Core.Nonterminal{+x, +need}, +rest}:
      +far = {Nat.add(k, Core.width(Core.Node{q2, ch})) : Nat}
      +head = {Bool.and(Core.lhsIs(grammar, q2, x), Core.needOk(need, Core.width(Core.Node{q2, ch}))) : Bool}
      +own = {Bool.and(head, Core.reads(ch, grammar, Core.rhsOf(grammar, q2), input, k)) : Bool}
      +left = Lemma.and_true_left(own, Core.reads(ts, grammar, rest, input, far), r)
      +hd = Lemma.and_true_left(head, Core.reads(ch, grammar, Core.rhsOf(grammar, q2), input, k), left)
      +lhs = Lemma.and_true_left(Core.lhsIs(grammar, q2, x), Core.needOk(need, Core.width(Core.Node{q2, ch})), hd)
      +nk = Lemma.and_true_right_side(Core.lhsIs(grammar, q2, x), Core.needOk(need, Core.width(Core.Node{q2, ch})), hd)
      +rc = Lemma.and_true_right_side(head, Core.reads(ch, grammar, Core.rhsOf(grammar, q2), input, k), left)
      +rt = Lemma.and_true_right_side(own, Core.reads(ts, grammar, rest, input, far), r)
      +ok = desc_item(grammar, input, s, q, d, ks, k, Core.Nonterminal{x, need}, rest, ie, desc_ok(Check.seenOf(s), Gll.Desc{q, d, ks, k}, grammar, input, s, closed_descs(pred, grammar, input, s, hc), sd))
      +cl = Lemma.and_true_left(Gll.keyIn(Gll.CKey{x, k}, Check.clustersOf(s)), Check.retIn(Gll.CKey{x, k}, Gll.Edge{q, d, ks}, Check.returnsOf(s)), ok)
      +re = Lemma.and_true_right_side(Gll.keyIn(Gll.CKey{x, k}, Check.clustersOf(s)), Check.retIn(Gll.CKey{x, k}, Gll.Edge{q, d, ks}, Check.returnsOf(s)), ok)
      +tok = Core.tokAt(input, k)
      +adh = {Gll.admits(pred, q2, tok) : Bool}
      +adc = {Check.admitsAll(ch, pred, input, k) : Bool}
      +adt = {Check.admitsAll(ts, pred, input, far) : Bool}
      +seed = seed_seen(grammar, q2, x, 0n, k, s, pred, tok, lhs, Lemma.and_true_left(adh, Bool.and(adc, adt), ad), cluster_seeds(Check.clustersOf(s), x, k, pred, grammar, input, s, closed_clusters(pred, grammar, input, s, hc), cl))
      +adr = Lemma.and_true_right_side(adh, Bool.and(adc, adt), ad)
      node_rest(pred, grammar, input, s, hc, q, ks, q2, ch, ts, d, k, x, need, rest, ie, lhs, nk, re,
        walk(ch, Core.rhsOf(grammar, q2), pred, grammar, input, s, hc, q2, 0n, k, k, {==}, rc, seed, Lemma.and_true_left(adc, adt, adr)),
        seen => walk(ts, rest, pred, grammar, input, s, hc, q, 1n+d, ks, far, drop_next(Core.rhsOf(grammar, q), d, Core.Nonterminal{x, need}, rest, ie), rt, seen, Lemma.and_true_right_side(adc, adt, adr)))

# ======== THE THEOREM ========

law bsr_eq_sound:
  for a: Core.Bsr
  for b: Core.Bsr
  for +e: {Core.bsrEq(a, b) == True{} : Bool}
  {a == b : Core.Bsr}

def bsr_eq_sound(a, b, e):
  match a b:
    case Core.Bsr{+q1, +d1, +i1, +k1, +j1} Core.Bsr{+q2, +d2, +i2, +k2, +j2}:
      +r1 = {Bool.and(Nat.is_eq(d1, d2), Bool.and(Nat.is_eq(i1, i2), Bool.and(Nat.is_eq(k1, k2), Nat.is_eq(j1, j2)))) : Bool}
      +r2 = {Bool.and(Nat.is_eq(i1, i2), Bool.and(Nat.is_eq(k1, k2), Nat.is_eq(j1, j2))) : Bool}
      +r3 = {Bool.and(Nat.is_eq(k1, k2), Nat.is_eq(j1, j2)) : Bool}
      +e1 = Lemma.and_true_right_side(Nat.is_eq(q1, q2), r1, e)
      +e2 = Lemma.and_true_right_side(Nat.is_eq(d1, d2), r2, e1)
      +e3 = Lemma.and_true_right_side(Nat.is_eq(i1, i2), r3, e2)
      +eq = Lemma.nat_eq_sound(q1, q2, Lemma.and_true_left(Nat.is_eq(q1, q2), r1, e))
      +ed = Lemma.nat_eq_sound(d1, d2, Lemma.and_true_left(Nat.is_eq(d1, d2), r2, e1))
      +ei = Lemma.nat_eq_sound(i1, i2, Lemma.and_true_left(Nat.is_eq(i1, i2), r3, e2))
      +ek = Lemma.nat_eq_sound(k1, k2, Lemma.and_true_left(Nat.is_eq(k1, k2), Nat.is_eq(j1, j2), e3))
      +ej = Lemma.nat_eq_sound(j1, j2, Lemma.and_true_right_side(Nat.is_eq(k1, k2), Nat.is_eq(j1, j2), e3))
      %eq : {Core.Bsr{q1, d1, i1, k1, j1} == Core.Bsr{_, d2, i2, k2, j2} : Core.Bsr}
      %ed : {Core.Bsr{q1, d1, i1, k1, j1} == Core.Bsr{q1, _, i2, k2, j2} : Core.Bsr}
      %ei : {Core.Bsr{q1, d1, i1, k1, j1} == Core.Bsr{q1, d1, _, k2, j2} : Core.Bsr}
      %ek : {Core.Bsr{q1, d1, i1, k1, j1} == Core.Bsr{q1, d1, i1, _, j2} : Core.Bsr}
      %ej : {Core.Bsr{q1, d1, i1, k1, j1} == Core.Bsr{q1, d1, i1, k1, _} : Core.Bsr}
      {==}

def member_pick(+x: Core.Bsr, +y: Core.Bsr, +rest: +List<Core.Bsr>, +set: +List<Core.Bsr>,
  cases: Either<{Core.bsrEq(x, y) == True{} : Bool}, {Core.member(x, rest) == True{} : Bool}>,
  +here: {Core.member(y, set) == True{} : Bool},
  later: {Core.member(x, rest) == True{} : Bool} -> {Core.member(x, set) == True{} : Bool})
  -> {Core.member(x, set) == True{} : Bool}:
  match cases:
    case Inl{e}:
      %Equal.sym(Core.Bsr, x, y, bsr_eq_sound(x, y, e)) : {Core.member(_, set) == True{} : Bool}
      here
    case Inr{m}:
      later(m)

law all_in_member:
  for xs: +List<Core.Bsr>
  for +set: +List<Core.Bsr>
  for +x: Core.Bsr
  for +all: {Core.allIn(xs, set) == True{} : Bool}
  for +m: {Core.member(x, xs) == True{} : Bool}
  {Core.member(x, set) == True{} : Bool}

def all_in_member(xs, set, x, all, m):
  match xs:
    case Nil{}:
      Empty.absurd({Core.member(x, set) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{+y, +rest}:
      member_pick(x, y, rest, set, Lemma.or_true_cases(Core.bsrEq(x, y), Core.member(x, rest), m),
        Lemma.and_true_left(Core.member(y, set), Core.allIn(rest, set), all),
        later => all_in_member(rest, set, x, Lemma.and_true_right_side(Core.member(y, set), Core.allIn(rest, set), all), later))

def tree_join(+grammar: +List<Core.Production>, +s: Gll.GState, +q: Nat, +ch: +List<Core.Tree>, w: Walked(grammar, s, q, 0n, ch, 0n, 0n))
  -> {Core.allIn(Core.steps([Core.Node{q, ch}], 0n), Check.stepsOf(s)) == True{} : Bool}:
  match w:
    case (o, (st, p)):
      all_in_app(Core.own(q, ch, 0n, 0n, 0n), List.append(&2, Core.Bsr, Core.steps(ch, 0n), []), Check.stepsOf(s), o, all_in_app(Core.steps(ch, 0n), [], Check.stepsOf(s), st, {==}))

law plain_admits:
  for f: +List<Core.Tree>
  for +input: +List<Nat>
  for +k: Nat
  {Check.admitsAll(f, Gll.NoPred{}, input, k) == True{} : Bool}

def plain_admits(f, input, k):
  match f:
    case Nil{}:
      {==}
    case Con{Core.Leaf{+a}, +ts}:
      plain_admits(ts, input, 1n+k)
    case Con{Core.Node{+q, +ch}, +ts}:
      +far = Nat.add(k, Core.width(Core.Node{q, ch}))
      Lemma.and_true_intro(Check.admitsAll(ch, Gll.NoPred{}, input, k), Check.admitsAll(ts, Gll.NoPred{}, input, far), plain_admits(ch, input, k), plain_admits(ts, input, far))

# Every step of a parse tree whose nodes the predictor admits is in a state closed for the
# predictor that has the start symbol's cluster at 0.
law tree_steps_with:
  for tree: Core.Tree
  for +pred: Gll.Pred
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +s: Gll.GState
  for +hc: {Check.closedWith(pred, grammar, input, s) == True{} : Bool}
  for +root: {Gll.keyIn(Gll.CKey{start, 0n}, Check.clustersOf(s)) == True{} : Bool}
  for +rr: {Core.reads([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool}
  for +ad: {Check.admitsAll([tree], pred, input, 0n) == True{} : Bool}
  {Core.allIn(Core.steps([tree], 0n), Check.stepsOf(s)) == True{} : Bool}

def tree_steps_with(tree, pred, grammar, start, input, s, hc, root, rr, ad):
  match tree:
    case Core.Leaf{+a}:
      Empty.absurd({Core.allIn(Core.steps([Core.Leaf{a}], 0n), Check.stepsOf(s)) == True{} : Bool}, Lemma.false_is_not_true(rr))
    case Core.Node{+q, +ch}:
      +w = {Core.width(Core.Node{q, ch}) : Nat}
      +head = {Bool.and(Core.lhsIs(grammar, q, start), True{}) : Bool}
      +own = {Bool.and(head, Core.reads(ch, grammar, Core.rhsOf(grammar, q), input, 0n)) : Bool}
      +left = Lemma.and_true_left(own, Core.reads([], grammar, [], input, Nat.add(0n, w)), rr)
      +lhs = Lemma.and_true_left(Core.lhsIs(grammar, q, start), True{}, Lemma.and_true_left(head, Core.reads(ch, grammar, Core.rhsOf(grammar, q), input, 0n), left))
      +rc = Lemma.and_true_right_side(head, Core.reads(ch, grammar, Core.rhsOf(grammar, q), input, 0n), left)
      +adh = {Gll.admits(pred, q, Core.tokAt(input, 0n)) : Bool}
      +adc = {Check.admitsAll(ch, pred, input, 0n) : Bool}
      +adr = Lemma.and_true_right_side(adh, Bool.and(adc, True{}), ad)
      +seed = seed_seen(grammar, q, start, 0n, 0n, s, pred, Core.tokAt(input, 0n), lhs, Lemma.and_true_left(adh, Bool.and(adc, True{}), ad), cluster_seeds(Check.clustersOf(s), start, 0n, pred, grammar, input, s, closed_clusters(pred, grammar, input, s, hc), root))
      tree_join(grammar, s, q, ch, walk(ch, Core.rhsOf(grammar, q), pred, grammar, input, s, hc, q, 0n, 0n, 0n, {==}, rc, seed, Lemma.and_true_left(adc, True{}, adr)))

# Every step of a parse tree is in a closed state that has the start symbol's cluster at 0.
law tree_steps:
  for tree: Core.Tree
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +s: Gll.GState
  for +hc: {Check.closed(grammar, input, s) == True{} : Bool}
  for +root: {Gll.keyIn(Gll.CKey{start, 0n}, Check.clustersOf(s)) == True{} : Bool}
  for +rr: {Core.reads([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool}
  {Core.allIn(Core.steps([tree], 0n), Check.stepsOf(s)) == True{} : Bool}

def tree_steps(tree, grammar, start, input, s, hc, root, rr):
  +t = tree
  tree_steps_with(t, Gll.NoPred{}, grammar, start, input, s, hc, root, rr, plain_admits([t], input, 0n))

# ======== THE CHECKED PARSER MISSES NOTHING ========

def setOr(m: Maybe<&2, +List<Core.Bsr>>, +d: +List<Core.Bsr>) -> +List<Core.Bsr>:
  match m:
    case None{}:
      d
    case Some{+x}:
      x

def isNone(m: Maybe<&2, +List<Core.Bsr>>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{x}:
      False{}

law none_not_some:
  for +set: +List<Core.Bsr>
  for +e: {None{} == Some{set} : Maybe<&2, +List<Core.Bsr>>}
  Empty

def none_not_some(set, e):
  Lemma.true_is_not_false(Equal.cong(Maybe<&2, +List<Core.Bsr>>, Bool, v => isNone(v), None{}, Some{set}, e))

def EveryFrom(+grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +s: Gll.GState, +set: +List<Core.Bsr>) -> Type:
  Core.EveryParseStep(grammar, start, input, set)

def from_parse_tree(+grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +s: Gll.GState, +set: +List<Core.Bsr>,
  +hc: {Check.closed(grammar, input, s) == True{} : Bool},
  +root: {Gll.keyIn(Gll.CKey{start, 0n}, Check.clustersOf(s)) == True{} : Bool},
  +es: {Check.stepsOf(s) == set : +List<Core.Bsr>},
  +tree: Core.Tree, +x: Core.Bsr, pt: Core.ParseTree(grammar, start, input, tree),
  +m: {Core.member(x, Core.steps([tree], 0n)) == True{} : Bool}) -> {Core.member(x, set) == True{} : Bool}:
  match pt:
    case (rr, rl):
      %es : {Core.member(x, _) == True{} : Bool}
      all_in_member(Core.steps([tree], 0n), Check.stepsOf(s), x, tree_steps(tree, grammar, start, input, s, hc, root, rr), m)

def checked_state(b: Bool, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +s: Gll.GState, +set: +List<Core.Bsr>,
  +eb: {b == Bool.and(Check.closed(grammar, input, s), Gll.keyIn(Gll.CKey{start, 0n}, Check.clustersOf(s))) : Bool},
  +e: {Check.checkPick(b, s) == Some{set} : Maybe<&2, +List<Core.Bsr>>}) -> Core.EveryParseStep(grammar, start, input, set):
  match b:
    case True{}:
      +both = Equal.sym(Bool, True{}, Bool.and(Check.closed(grammar, input, s), Gll.keyIn(Gll.CKey{start, 0n}, Check.clustersOf(s))), eb)
      +hc = Lemma.and_true_left(Check.closed(grammar, input, s), Gll.keyIn(Gll.CKey{start, 0n}, Check.clustersOf(s)), both)
      +root = Lemma.and_true_right_side(Check.closed(grammar, input, s), Gll.keyIn(Gll.CKey{start, 0n}, Check.clustersOf(s)), both)
      +es = Equal.cong(Maybe<&2, +List<Core.Bsr>>, +List<Core.Bsr>, v => setOr(v, []), Some{Check.stepsOf(s)}, Some{set}, e)
      tree => x => pt => m => from_parse_tree(grammar, start, input, s, set, hc, root, es, tree, x, pt, m)
    case False{}:
      Empty.absurd(Core.EveryParseStep(grammar, start, input, set), none_not_some(set, e))

def checked_run(r: Gll.GRun, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>,
  +e: {Check.runChecked(r, grammar, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>}) -> Core.EveryParseStep(grammar, start, input, set):
  match r:
    case Gll.GDone{+s}:
      checked_state(Bool.and(Check.closed(grammar, input, s), Gll.keyIn(Gll.CKey{start, 0n}, Check.clustersOf(s))), grammar, start, input, s, set, {==}, e)
    case Gll.OutOfFuel{+s}:
      Empty.absurd(Core.EveryParseStep(grammar, start, input, set), none_not_some(set, e))

# THE CHECKED GLL PARSER MISSES NOTHING: whenever it hands out a set of steps, every step of
# every parse tree of the input is in it.
law gll_every_parse_step:
  for fuel: Nat
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Core.Bsr>
  for +got: {Check.checkedSteps(fuel, grammar, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>}
  Core.EveryParseStep(grammar, start, input, set)

def gll_every_parse_step(fuel, grammar, start, input, set, got):
  checked_run(Gll.parse(fuel, grammar, start, input), grammar, start, input, set, got)

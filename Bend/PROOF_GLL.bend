import Base
import ./SPEC.bend as Spec
import ./LAWS.bend as Laws
import ./GLL.bend as Gll
import ./CHECK.bend as Check
import ./LEMMAS.bend as Lemma

# A CLOSED STATE HAS EVERY STEP OF EVERY PARSE TREE.
#
# The proof walks a parse tree the way `Spec.walk` lists its steps. At each item the
# closedness condition for the descriptor there says what the state must hold: a
# terminal's successor, a call's cluster and return edge, a sequence end's pop. The
# cluster's seeds start the subtree; the subtree's pop and the return edge give back
# the caller's next descriptor and step. Loops run round by round in their own cluster.

# ======== EQUAL BY ==, SO EQUAL ========

law nats_eq_sound:
  for xs: +List<Nat>
  for ys: +List<Nat>
  for e: {Gll.natsEq(xs, ys) == True{} : Bool}
  {xs == ys : +List<Nat>}

def nats_eq_sound(xs, ys, e):
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, yr}:
      Empty.absurd({[] == y <> yr : +List<Nat>}, Lemma.false_is_not_true(e))
    case Con{x, xr} Nil{}:
      Empty.absurd({x <> xr == [] : +List<Nat>}, Lemma.false_is_not_true(e))
    case Con{+x, +xr} Con{+y, +yr}:
      +both = e
      ex = Lemma.nat_eq_sound(x, y, Lemma.and_true_left(Nat.is_eq(x, y), Gll.natsEq(xr, yr), both))
      er = nats_eq_sound(xr, yr, Lemma.and_true_right_side(Nat.is_eq(x, y), Gll.natsEq(xr, yr), both))
      %ex : {x <> xr == _ <> yr : +List<Nat>}
      %er : {x <> xr == x <> _ : +List<Nat>}
      {==}

law target_eq_sound:
  for a: Gll.Target
  for b: Gll.Target
  for e: {Gll.targetEq(a, b) == True{} : Bool}
  {a == b : Gll.Target}

def target_eq_sound(a, b, e):
  match a b:
    case Gll.TNt{+x} Gll.TNt{+y}:
      Equal.cong(Nat, Gll.Target, v => Gll.TNt{v}, x, y, Lemma.nat_eq_sound(x, y, e))
    case Gll.TBr{+p, +xs} Gll.TBr{+q, +ys}:
      +both = e
      ep = Lemma.nat_eq_sound(p, q, Lemma.and_true_left(Nat.is_eq(p, q), Gll.natsEq(xs, ys), both))
      er = nats_eq_sound(xs, ys, Lemma.and_true_right_side(Nat.is_eq(p, q), Gll.natsEq(xs, ys), both))
      %ep : {Gll.TBr{p, xs} == Gll.TBr{_, ys} : Gll.Target}
      %er : {Gll.TBr{p, xs} == Gll.TBr{p, _} : Gll.Target}
      {==}
    case Gll.TNt{x} Gll.TBr{q, ys}:
      Empty.absurd({Gll.TNt{x} == Gll.TBr{q, ys} : Gll.Target}, Lemma.false_is_not_true(e))
    case Gll.TBr{p, xs} Gll.TNt{y}:
      Empty.absurd({Gll.TBr{p, xs} == Gll.TNt{y} : Gll.Target}, Lemma.false_is_not_true(e))

law key_eq_sound:
  for a: Gll.CKey
  for b: Gll.CKey
  for e: {Gll.keyEq(a, b) == True{} : Bool}
  {a == b : Gll.CKey}

def key_eq_sound(a, b, e):
  match a b:
    case Gll.CKey{+t1, +k1} Gll.CKey{+t2, +k2}:
      +both = e
      et = target_eq_sound(t1, t2, Lemma.and_true_left(Gll.targetEq(t1, t2), Nat.is_eq(k1, k2), both))
      ek = Lemma.nat_eq_sound(k1, k2, Lemma.and_true_right_side(Gll.targetEq(t1, t2), Nat.is_eq(k1, k2), both))
      %et : {Gll.CKey{t1, k1} == Gll.CKey{_, k2} : Gll.CKey}
      %ek : {Gll.CKey{t1, k1} == Gll.CKey{t1, _} : Gll.CKey}
      {==}

law edge_eq_sound:
  for a: Gll.Edge
  for b: Gll.Edge
  for e: {Gll.edgeEq(a, b) == True{} : Bool}
  {a == b : Gll.Edge}

def edge_eq_sound(a, b, e):
  match a b:
    case Gll.Edge{+p1, +r1, +d1, +k1} Gll.Edge{+p2, +r2, +d2, +k2}:
      +s0 = e
      +s1 = Lemma.and_true_right_side(Nat.is_eq(p1, p2), Bool.and(Gll.natsEq(r1, r2), Bool.and(Nat.is_eq(d1, d2), Nat.is_eq(k1, k2))), s0)
      +s2 = Lemma.and_true_right_side(Gll.natsEq(r1, r2), Bool.and(Nat.is_eq(d1, d2), Nat.is_eq(k1, k2)), s1)
      ep = Lemma.nat_eq_sound(p1, p2, Lemma.and_true_left(Nat.is_eq(p1, p2), Bool.and(Gll.natsEq(r1, r2), Bool.and(Nat.is_eq(d1, d2), Nat.is_eq(k1, k2))), s0))
      er = nats_eq_sound(r1, r2, Lemma.and_true_left(Gll.natsEq(r1, r2), Bool.and(Nat.is_eq(d1, d2), Nat.is_eq(k1, k2)), s1))
      ed = Lemma.nat_eq_sound(d1, d2, Lemma.and_true_left(Nat.is_eq(d1, d2), Nat.is_eq(k1, k2), s2))
      ek = Lemma.nat_eq_sound(k1, k2, Lemma.and_true_right_side(Nat.is_eq(d1, d2), Nat.is_eq(k1, k2), s2))
      %ep : {Gll.Edge{p1, r1, d1, k1} == Gll.Edge{_, r2, d2, k2} : Gll.Edge}
      %er : {Gll.Edge{p1, r1, d1, k1} == Gll.Edge{p1, _, d2, k2} : Gll.Edge}
      %ed : {Gll.Edge{p1, r1, d1, k1} == Gll.Edge{p1, r1, _, k2} : Gll.Edge}
      %ek : {Gll.Edge{p1, r1, d1, k1} == Gll.Edge{p1, r1, d1, _} : Gll.Edge}
      {==}

law desc_eq_sound:
  for a: Gll.Desc
  for b: Gll.Desc
  for e: {Gll.descEq(a, b) == True{} : Bool}
  {a == b : Gll.Desc}

def desc_eq_sound(a, b, e):
  match a b:
    case Gll.Desc{+p1, +r1, +d1, +k1, +i1} Gll.Desc{+p2, +r2, +d2, +k2, +i2}:
      +s0 = e
      +s1 = Lemma.and_true_right_side(Nat.is_eq(p1, p2), Bool.and(Gll.natsEq(r1, r2), Bool.and(Nat.is_eq(d1, d2), Bool.and(Nat.is_eq(k1, k2), Nat.is_eq(i1, i2)))), s0)
      +s2 = Lemma.and_true_right_side(Gll.natsEq(r1, r2), Bool.and(Nat.is_eq(d1, d2), Bool.and(Nat.is_eq(k1, k2), Nat.is_eq(i1, i2))), s1)
      +s3 = Lemma.and_true_right_side(Nat.is_eq(d1, d2), Bool.and(Nat.is_eq(k1, k2), Nat.is_eq(i1, i2)), s2)
      ep = Lemma.nat_eq_sound(p1, p2, Lemma.and_true_left(Nat.is_eq(p1, p2), Bool.and(Gll.natsEq(r1, r2), Bool.and(Nat.is_eq(d1, d2), Bool.and(Nat.is_eq(k1, k2), Nat.is_eq(i1, i2)))), s0))
      er = nats_eq_sound(r1, r2, Lemma.and_true_left(Gll.natsEq(r1, r2), Bool.and(Nat.is_eq(d1, d2), Bool.and(Nat.is_eq(k1, k2), Nat.is_eq(i1, i2))), s1))
      ed = Lemma.nat_eq_sound(d1, d2, Lemma.and_true_left(Nat.is_eq(d1, d2), Bool.and(Nat.is_eq(k1, k2), Nat.is_eq(i1, i2)), s2))
      ek = Lemma.nat_eq_sound(k1, k2, Lemma.and_true_left(Nat.is_eq(k1, k2), Nat.is_eq(i1, i2), s3))
      ei = Lemma.nat_eq_sound(i1, i2, Lemma.and_true_right_side(Nat.is_eq(k1, k2), Nat.is_eq(i1, i2), s3))
      %ep : {Gll.Desc{p1, r1, d1, k1, i1} == Gll.Desc{_, r2, d2, k2, i2} : Gll.Desc}
      %er : {Gll.Desc{p1, r1, d1, k1, i1} == Gll.Desc{p1, _, d2, k2, i2} : Gll.Desc}
      %ed : {Gll.Desc{p1, r1, d1, k1, i1} == Gll.Desc{p1, r1, _, k2, i2} : Gll.Desc}
      %ek : {Gll.Desc{p1, r1, d1, k1, i1} == Gll.Desc{p1, r1, d1, _, i2} : Gll.Desc}
      %ei : {Gll.Desc{p1, r1, d1, k1, i1} == Gll.Desc{p1, r1, d1, k1, _} : Gll.Desc}
      {==}

# ======== FROM THE CHECKS TO SINGLE FACTS ========

# ---- Every seen descriptor is ok ----

law desc_pick:
  for +d: Gll.Desc
  for +y: Gll.Desc
  for -rest: +List<Gll.Desc>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for cases: Either<{Gll.descEq(d, y) == True{} : Bool}, {Gll.descIn(d, rest) == True{} : Bool}>
  for +yOk: {Check.descOk(y, grammar, input, s) == True{} : Bool}
  for searchRest: {Gll.descIn(d, rest) == True{} : Bool} -> {Check.descOk(d, grammar, input, s) == True{} : Bool}
  {Check.descOk(d, grammar, input, s) == True{} : Bool}

def desc_pick(d, y, rest, grammar, input, s, cases, yOk, searchRest):
  match cases:
    case Inl{same}:
      Equal.trans(Bool, Check.descOk(d, grammar, input, s), Check.descOk(y, grammar, input, s), True{},
        Equal.cong(Gll.Desc, Bool, v => Check.descOk(v, grammar, input, s), d, y, desc_eq_sound(d, y, same)), yOk)
    case Inr{later}:
      searchRest(later)

law desc_ok:
  for xs: +List<Gll.Desc>
  for +d: Gll.Desc
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for all: {Check.allDescs(xs, grammar, input, s) == True{} : Bool}
  for m: {Gll.descIn(d, xs) == True{} : Bool}
  {Check.descOk(d, grammar, input, s) == True{} : Bool}

def desc_ok(xs, d, grammar, input, s, all, m):
  match xs:
    case Nil{}:
      Empty.absurd({Check.descOk(d, grammar, input, s) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{+y, +rest}:
      +both = all
      desc_pick(d, y, rest, grammar, input, s,
        Lemma.or_true_cases(Gll.descEq(d, y), Gll.descIn(d, rest), m),
        Lemma.and_true_left(Check.descOk(y, grammar, input, s), Check.allDescs(rest, grammar, input, s), both),
        later => desc_ok(rest, d, grammar, input, s, Lemma.and_true_right_side(Check.descOk(y, grammar, input, s), Check.allDescs(rest, grammar, input, s), both), later))

# ---- Every cluster has its seeds ----

law cluster_pick:
  for +key: Gll.CKey
  for +y: Gll.CKey
  for -rest: +List<Gll.CKey>
  for +grammar: +List<Spec.Production>
  for +s: Gll.GState
  for cases: Either<{Gll.keyEq(key, y) == True{} : Bool}, {Gll.keyIn(key, rest) == True{} : Bool}>
  for +yOk: {Check.allSeen(Check.seedsOf(grammar, y), s) == True{} : Bool}
  for searchRest: {Gll.keyIn(key, rest) == True{} : Bool} -> {Check.allSeen(Check.seedsOf(grammar, key), s) == True{} : Bool}
  {Check.allSeen(Check.seedsOf(grammar, key), s) == True{} : Bool}

def cluster_pick(key, y, rest, grammar, s, cases, yOk, searchRest):
  match cases:
    case Inl{same}:
      Equal.trans(Bool, Check.allSeen(Check.seedsOf(grammar, key), s), Check.allSeen(Check.seedsOf(grammar, y), s), True{},
        Equal.cong(Gll.CKey, Bool, v => Check.allSeen(Check.seedsOf(grammar, v), s), key, y, key_eq_sound(key, y, same)), yOk)
    case Inr{later}:
      searchRest(later)

law cluster_seeds:
  for cs: +List<Gll.CKey>
  for +key: Gll.CKey
  for +grammar: +List<Spec.Production>
  for +s: Gll.GState
  for all: {Check.allClusters(cs, grammar, s) == True{} : Bool}
  for m: {Gll.keyIn(key, cs) == True{} : Bool}
  {Check.allSeen(Check.seedsOf(grammar, key), s) == True{} : Bool}

def cluster_seeds(cs, key, grammar, s, all, m):
  match cs:
    case Nil{}:
      Empty.absurd({Check.allSeen(Check.seedsOf(grammar, key), s) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{+y, +rest}:
      +both = all
      cluster_pick(key, y, rest, grammar, s,
        Lemma.or_true_cases(Gll.keyEq(key, y), Gll.keyIn(key, rest), m),
        Lemma.and_true_left(Check.allSeen(Check.seedsOf(grammar, y), s), Check.allClusters(rest, grammar, s), both),
        later => cluster_seeds(rest, key, grammar, s, Lemma.and_true_right_side(Check.allSeen(Check.seedsOf(grammar, y), s), Check.allClusters(rest, grammar, s), both), later))

# ---- Every pop of a loop starts it again ----

law pop_pick:
  for +key: Gll.CKey
  for +j: Nat
  for +k2: Gll.CKey
  for +j2: Nat
  for -rest: +List<Gll.Pop>
  for +grammar: +List<Spec.Production>
  for +s: Gll.GState
  for cases: Either<{Bool.and(Gll.keyEq(key, k2), Nat.is_eq(j, j2)) == True{} : Bool}, {Gll.popIn(key, j, rest) == True{} : Bool}>
  for +yOk: {Check.allSeen(Check.againOfKey(grammar, k2, j2), s) == True{} : Bool}
  for searchRest: {Gll.popIn(key, j, rest) == True{} : Bool} -> {Check.allSeen(Check.againOfKey(grammar, key, j), s) == True{} : Bool}
  {Check.allSeen(Check.againOfKey(grammar, key, j), s) == True{} : Bool}

def pop_pick(key, j, k2, j2, rest, grammar, s, cases, yOk, searchRest):
  match cases:
    case Inl{same}:
      +both = same
      ek = key_eq_sound(key, k2, Lemma.and_true_left(Gll.keyEq(key, k2), Nat.is_eq(j, j2), both))
      ej = Lemma.nat_eq_sound(j, j2, Lemma.and_true_right_side(Gll.keyEq(key, k2), Nat.is_eq(j, j2), both))
      %Equal.sym(Gll.CKey, key, k2, ek) : {Check.allSeen(Check.againOfKey(grammar, _, j), s) == True{} : Bool}
      %Equal.sym(Nat, j, j2, ej) : {Check.allSeen(Check.againOfKey(grammar, k2, _), s) == True{} : Bool}
      yOk
    case Inr{later}:
      searchRest(later)

law pop_again:
  for ps: +List<Gll.Pop>
  for +key: Gll.CKey
  for +j: Nat
  for +grammar: +List<Spec.Production>
  for +s: Gll.GState
  for all: {Check.allPops(ps, grammar, s) == True{} : Bool}
  for m: {Gll.popIn(key, j, ps) == True{} : Bool}
  {Check.allSeen(Check.againOfKey(grammar, key, j), s) == True{} : Bool}

def pop_again(ps, key, j, grammar, s, all, m):
  match ps:
    case Nil{}:
      Empty.absurd({Check.allSeen(Check.againOfKey(grammar, key, j), s) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{Gll.Pop{+k2, +j2}, +rest}:
      +both = all
      pop_pick(key, j, k2, j2, rest, grammar, s,
        Lemma.or_true_cases(Bool.and(Gll.keyEq(key, k2), Nat.is_eq(j, j2)), Gll.popIn(key, j, rest), m),
        Lemma.and_true_left(Check.allSeen(Check.againOfKey(grammar, k2, j2), s), Check.allPops(rest, grammar, s), both),
        later => pop_again(rest, key, j, grammar, s, Lemma.and_true_right_side(Check.allSeen(Check.againOfKey(grammar, k2, j2), s), Check.allPops(rest, grammar, s), both), later))

# ---- Every return edge resumes at every pop ----

law resume_hit:
  for hit: Bool
  for +edge: Gll.Edge
  for +kc: Nat
  for +j: Nat
  for +s: Gll.GState
  for isHit: {hit == True{} : Bool}
  for r: {Check.resumeIfOk(hit, edge, kc, j, s) == True{} : Bool}
  {Check.resumeOk(edge, kc, j, s) == True{} : Bool}

def resume_hit(hit, edge, kc, j, s, isHit, r):
  match hit:
    case True{}:
      r
    case False{}:
      Empty.absurd({Check.resumeOk(edge, kc, j, s) == True{} : Bool}, Lemma.false_is_not_true(isHit))

law edge_pop_pick:
  for +key: Gll.CKey
  for +edge: Gll.Edge
  for +j: Nat
  for +k2: Gll.CKey
  for +j2: Nat
  for -rest: +List<Gll.Pop>
  for +s: Gll.GState
  for cases: Either<{Bool.and(Gll.keyEq(key, k2), Nat.is_eq(j, j2)) == True{} : Bool}, {Gll.popIn(key, j, rest) == True{} : Bool}>
  for +here: {Check.resumeIfOk(Gll.keyEq(key, k2), edge, Check.keyStart(key), j2, s) == True{} : Bool}
  for searchRest: {Gll.popIn(key, j, rest) == True{} : Bool} -> {Check.resumeOk(edge, Check.keyStart(key), j, s) == True{} : Bool}
  {Check.resumeOk(edge, Check.keyStart(key), j, s) == True{} : Bool}

def edge_pop_pick(key, edge, j, k2, j2, rest, s, cases, here, searchRest):
  match cases:
    case Inl{same}:
      +both = same
      ej = Lemma.nat_eq_sound(j, j2, Lemma.and_true_right_side(Gll.keyEq(key, k2), Nat.is_eq(j, j2), both))
      %Equal.sym(Nat, j, j2, ej) : {Check.resumeOk(edge, Check.keyStart(key), _, s) == True{} : Bool}
      resume_hit(Gll.keyEq(key, k2), edge, Check.keyStart(key), j2, s, Lemma.and_true_left(Gll.keyEq(key, k2), Nat.is_eq(j, j2), both), here)
    case Inr{later}:
      searchRest(later)

law edge_pop:
  for ps: +List<Gll.Pop>
  for +key: Gll.CKey
  for +edge: Gll.Edge
  for +j: Nat
  for +s: Gll.GState
  for all: {Check.edgePops(ps, key, edge, s) == True{} : Bool}
  for m: {Gll.popIn(key, j, ps) == True{} : Bool}
  {Check.resumeOk(edge, Check.keyStart(key), j, s) == True{} : Bool}

def edge_pop(ps, key, edge, j, s, all, m):
  match ps:
    case Nil{}:
      Empty.absurd({Check.resumeOk(edge, Check.keyStart(key), j, s) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{Gll.Pop{+k2, +j2}, +rest}:
      +both = all
      +hit = Check.resumeIfOk(Gll.keyEq(key, k2), edge, Check.keyStart(key), j2, s)
      edge_pop_pick(key, edge, j, k2, j2, rest, s,
        Lemma.or_true_cases(Bool.and(Gll.keyEq(key, k2), Nat.is_eq(j, j2)), Gll.popIn(key, j, rest), m),
        Lemma.and_true_left(hit, Check.edgePops(rest, key, edge, s), both),
        later => edge_pop(rest, key, edge, j, s, Lemma.and_true_right_side(hit, Check.edgePops(rest, key, edge, s), both), later))

law return_pick:
  for +key: Gll.CKey
  for +edge: Gll.Edge
  for +k2: Gll.CKey
  for +e2: Gll.Edge
  for -rest: +List<Gll.Ret>
  for +ps: +List<Gll.Pop>
  for +s: Gll.GState
  for cases: Either<{Bool.and(Gll.keyEq(key, k2), Gll.edgeEq(edge, e2)) == True{} : Bool}, {Gll.retIn(key, edge, rest) == True{} : Bool}>
  for +here: {Check.edgePops(ps, k2, e2, s) == True{} : Bool}
  for searchRest: {Gll.retIn(key, edge, rest) == True{} : Bool} -> {Check.edgePops(ps, key, edge, s) == True{} : Bool}
  {Check.edgePops(ps, key, edge, s) == True{} : Bool}

def return_pick(key, edge, k2, e2, rest, ps, s, cases, here, searchRest):
  match cases:
    case Inl{same}:
      +both = same
      ek = key_eq_sound(key, k2, Lemma.and_true_left(Gll.keyEq(key, k2), Gll.edgeEq(edge, e2), both))
      ee = edge_eq_sound(edge, e2, Lemma.and_true_right_side(Gll.keyEq(key, k2), Gll.edgeEq(edge, e2), both))
      %Equal.sym(Gll.CKey, key, k2, ek) : {Check.edgePops(ps, _, edge, s) == True{} : Bool}
      %Equal.sym(Gll.Edge, edge, e2, ee) : {Check.edgePops(ps, k2, _, s) == True{} : Bool}
      here
    case Inr{later}:
      searchRest(later)

law return_edge:
  for rs: +List<Gll.Ret>
  for +ps: +List<Gll.Pop>
  for +key: Gll.CKey
  for +edge: Gll.Edge
  for +s: Gll.GState
  for all: {Check.allReturns(rs, ps, s) == True{} : Bool}
  for m: {Gll.retIn(key, edge, rs) == True{} : Bool}
  {Check.edgePops(ps, key, edge, s) == True{} : Bool}

def return_edge(rs, ps, key, edge, s, all, m):
  match rs:
    case Nil{}:
      Empty.absurd({Check.edgePops(ps, key, edge, s) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{Gll.Ret{+k2, +e2}, +rest}:
      +both = all
      return_pick(key, edge, k2, e2, rest, ps, s,
        Lemma.or_true_cases(Bool.and(Gll.keyEq(key, k2), Gll.edgeEq(edge, e2)), Gll.retIn(key, edge, rest), m),
        Lemma.and_true_left(Check.edgePops(ps, k2, e2, s), Check.allReturns(rest, ps, s), both),
        later => return_edge(rest, ps, key, edge, s, Lemma.and_true_right_side(Check.edgePops(ps, k2, e2, s), Check.allReturns(rest, ps, s), both), later))

# ---- Seeds that are seen ----

law keep_head:
  for keep: Bool
  for +isKept: {keep == True{} : Bool}
  for +d: Gll.Desc
  for +ds: +List<Gll.Desc>
  for +s: Gll.GState
  for all: {Check.allSeen(Gll.keepDesc(keep, d, ds), s) == True{} : Bool}
  {Check.descSeen(d, s) == True{} : Bool}

def keep_head(keep, isKept, d, ds, s, all):
  match keep:
    case True{}:
      Lemma.and_true_left(Check.descSeen(d, s), Check.allSeen(ds, s), all)
    case False{}:
      Empty.absurd({Check.descSeen(d, s) == True{} : Bool}, Lemma.false_is_not_true(isKept))

law keep_tail:
  for keep: Bool
  for +d: Gll.Desc
  for +ds: +List<Gll.Desc>
  for +s: Gll.GState
  for all: {Check.allSeen(Gll.keepDesc(keep, d, ds), s) == True{} : Bool}
  {Check.allSeen(ds, s) == True{} : Bool}

def keep_tail(keep, d, ds, s, all):
  match keep:
    case True{}:
      Lemma.and_true_right_side(Check.descSeen(d, s), Check.allSeen(ds, s), all)
    case False{}:
      all

# A cluster of x at i has seen the start of every production of x.
law productions_seen:
  for grammar: +List<Spec.Production>
  for +x: Nat
  for +o: Nat
  for +i: Nat
  for q: Nat
  for +s: Gll.GState
  for lhsOk: {Spec.lhsIs(grammar, q, x) == True{} : Bool}
  for all: {Check.allSeen(Gll.productionsOf(grammar, x, o, i), s) == True{} : Bool}
  {Check.descSeen(Gll.Desc{Nat.add(o, q), [], 0n, i, i}, s) == True{} : Bool}

def productions_seen(grammar, x, o, i, q, s, lhsOk, all):
  match grammar q:
    case Nil{} 0n:
      Empty.absurd({Check.descSeen(Gll.Desc{Nat.add(o, 0n), [], 0n, i, i}, s) == True{} : Bool}, Lemma.false_is_not_true(lhsOk))
    case Nil{} 1n+r:
      Empty.absurd({Check.descSeen(Gll.Desc{Nat.add(o, 1n+r), [], 0n, i, i}, s) == True{} : Bool}, Lemma.false_is_not_true(lhsOk))
    case Con{Spec.Production{+lhs, +rhs}, +rest} 0n:
      %Equal.sym(Nat, Nat.add(o, 0n), o, Lemma.add_zero_right(o)) : {Check.descSeen(Gll.Desc{_, [], 0n, i, i}, s) == True{} : Bool}
      keep_head(Nat.is_eq(lhs, x), lhsOk, Gll.Desc{o, [], 0n, i, i}, Gll.productionsOf(rest, x, 1n+o, i), s, all)
    case Con{Spec.Production{+lhs, +rhs}, +rest} 1n+(+r):
      %Equal.sym(Nat, Nat.add(o, 1n+r), 1n+Nat.add(o, r), Lemma.add_succ_right(o, r)) : {Check.descSeen(Gll.Desc{_, [], 0n, i, i}, s) == True{} : Bool}
      productions_seen(rest, x, 1n+o, i, r, s, lhsOk, keep_tail(Nat.is_eq(lhs, x), Gll.Desc{o, [], 0n, i, i}, Gll.productionsOf(rest, x, 1n+o, i), s, all))

law alt_pick:
  for same: Bool
  for +m: Nat
  for +a: Nat
  for +sameEq: {Nat.is_eq(m, a) == same : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +k: Nat
  for +i: Nat
  for +s: Gll.GState
  for lt: {Nat.is_lt(a, 1n+m) == True{} : Bool}
  for all: {Check.allSeen(Gll.alternatives(1n+m, index, rpath, k, i), s) == True{} : Bool}
  for later: {Nat.is_lt(a, m) == True{} : Bool} -> {Check.allSeen(Gll.alternatives(m, index, rpath, k, i), s) == True{} : Bool} -> {Check.descSeen(Gll.Desc{index, a <> rpath, 0n, k, i}, s) == True{} : Bool}
  {Check.descSeen(Gll.Desc{index, a <> rpath, 0n, k, i}, s) == True{} : Bool}

def alt_pick(same, m, a, sameEq, index, rpath, k, i, s, lt, all, later):
  match same:
    case True{}:
      %Lemma.nat_eq_sound(m, a, sameEq) : {Check.descSeen(Gll.Desc{index, _ <> rpath, 0n, k, i}, s) == True{} : Bool}
      Lemma.and_true_left(Check.descSeen(Gll.Desc{index, m <> rpath, 0n, k, i}, s), Check.allSeen(Gll.alternatives(m, index, rpath, k, i), s), all)
    case False{}:
      later(Lemma.lt_succ_ne(a, m, lt, sameEq), Lemma.and_true_right_side(Check.descSeen(Gll.Desc{index, m <> rpath, 0n, k, i}, s), Check.allSeen(Gll.alternatives(m, index, rpath, k, i), s), all))

# A bracket's cluster has seen the start of each of its alternatives.
law alternatives_seen:
  for n: Nat
  for +index: Nat
  for +rpath: +List<Nat>
  for +k: Nat
  for +i: Nat
  for +a: Nat
  for +s: Gll.GState
  for lt: {Nat.is_lt(a, n) == True{} : Bool}
  for all: {Check.allSeen(Gll.alternatives(n, index, rpath, k, i), s) == True{} : Bool}
  {Check.descSeen(Gll.Desc{index, a <> rpath, 0n, k, i}, s) == True{} : Bool}

def alternatives_seen(n, index, rpath, k, i, a, s, lt, all):
  match n:
    case 0n:
      Empty.absurd({Check.descSeen(Gll.Desc{index, a <> rpath, 0n, k, i}, s) == True{} : Bool}, Lemma.lt_zero_false(a, lt))
    case 1n+(+m):
      alt_pick(Nat.is_eq(m, a), m, a, {==}, index, rpath, k, i, s, lt, all,
        ltM => allM => alternatives_seen(m, index, rpath, k, i, a, s, ltM, allM))

# ---- Positions in the input ----

def Spells(+forest: +List<Spec.Tree>, +input: +List<Nat>, +pos: Nat) -> Data:
  {Spec.leaves(forest) == Lemma.slice(input, pos, List.length(&2, Nat, Spec.leaves(forest))) : +List<Nat>}

law split_slice:
  for +input: +List<Nat>
  for +pos: Nat
  for +w1: +List<Nat>
  for +w2: +List<Nat>
  for sp: {List.append(&2, Nat, w1, w2) == Lemma.slice(input, pos, List.length(&2, Nat, List.append(&2, Nat, w1, w2))) : +List<Nat>}
  {Lemma.slice(input, pos, Nat.add(List.length(&2, Nat, w1), List.length(&2, Nat, w2))) == List.append(&2, Nat, w1, w2) : +List<Nat>}

def split_slice(input, pos, w1, w2, sp):
  Equal.trans(+List<Nat>, Lemma.slice(input, pos, Nat.add(List.length(&2, Nat, w1), List.length(&2, Nat, w2))), Lemma.slice(input, pos, List.length(&2, Nat, List.append(&2, Nat, w1, w2))), List.append(&2, Nat, w1, w2),
    Equal.cong(Nat, +List<Nat>, v => Lemma.slice(input, pos, v), Nat.add(List.length(&2, Nat, w1), List.length(&2, Nat, w2)), List.length(&2, Nat, List.append(&2, Nat, w1, w2)), Equal.sym(Nat, List.length(&2, Nat, List.append(&2, Nat, w1, w2)), Nat.add(List.length(&2, Nat, w1), List.length(&2, Nat, w2)), Lemma.length_append(w1, w2))),
    Equal.sym(+List<Nat>, List.append(&2, Nat, w1, w2), Lemma.slice(input, pos, List.length(&2, Nat, List.append(&2, Nat, w1, w2))), sp))

law spells_first:
  for +input: +List<Nat>
  for +pos: Nat
  for +w1: +List<Nat>
  for +w2: +List<Nat>
  for sp: {List.append(&2, Nat, w1, w2) == Lemma.slice(input, pos, List.length(&2, Nat, List.append(&2, Nat, w1, w2))) : +List<Nat>}
  {w1 == Lemma.slice(input, pos, List.length(&2, Nat, w1)) : +List<Nat>}

def spells_first(input, pos, w1, w2, sp):
  Equal.sym(+List<Nat>, Lemma.slice(input, pos, List.length(&2, Nat, w1)), w1, Lemma.slice_left(input, pos, w1, w2, split_slice(input, pos, w1, w2, sp)))

law spells_second:
  for +input: +List<Nat>
  for +pos: Nat
  for +w1: +List<Nat>
  for +w2: +List<Nat>
  for sp: {List.append(&2, Nat, w1, w2) == Lemma.slice(input, pos, List.length(&2, Nat, List.append(&2, Nat, w1, w2))) : +List<Nat>}
  {w2 == Lemma.slice(input, Nat.add(pos, List.length(&2, Nat, w1)), List.length(&2, Nat, w2)) : +List<Nat>}

def spells_second(input, pos, w1, w2, sp):
  Equal.sym(+List<Nat>, Lemma.slice(input, Nat.add(pos, List.length(&2, Nat, w1)), List.length(&2, Nat, w2)), w2, Lemma.slice_right(input, pos, w1, w2, split_slice(input, pos, w1, w2, sp)))

# The token under a leaf.
law leaf_token:
  for +input: +List<Nat>
  for +pos: Nat
  for +kind: Nat
  for +rest: +List<Nat>
  for sp: {kind <> rest == Lemma.slice(input, pos, List.length(&2, Nat, kind <> rest)) : +List<Nat>}
  {List.get(&2, Nat, input, pos) == Some{kind} : Maybe<&2, Nat>}

def leaf_token(input, pos, kind, rest, sp):
  Lemma.slice_get(input, pos, kind, Equal.sym(+List<Nat>, [kind], Lemma.slice(input, pos, 1n), spells_first(input, pos, [kind], rest, sp)))

law leaf_rest:
  for +input: +List<Nat>
  for +pos: Nat
  for +kind: Nat
  for +rest: +List<Nat>
  for sp: {kind <> rest == Lemma.slice(input, pos, List.length(&2, Nat, kind <> rest)) : +List<Nat>}
  {rest == Lemma.slice(input, 1n+pos, List.length(&2, Nat, rest)) : +List<Nat>}

def leaf_rest(input, pos, kind, rest, sp):
  %Lemma.add_one_right(pos) : {rest == Lemma.slice(input, _, List.length(&2, Nat, rest)) : +List<Nat>}
  spells_second(input, pos, [kind], rest, sp)

# Where a forest ends, split after its first part.
law end_split:
  for +pos: Nat
  for +w1: +List<Nat>
  for +w2: +List<Nat>
  {Nat.add(Nat.add(pos, List.length(&2, Nat, w1)), List.length(&2, Nat, w2)) == Nat.add(pos, List.length(&2, Nat, List.append(&2, Nat, w1, w2))) : Nat}

def end_split(pos, w1, w2):
  Equal.trans(Nat, Nat.add(Nat.add(pos, List.length(&2, Nat, w1)), List.length(&2, Nat, w2)), Nat.add(pos, Nat.add(List.length(&2, Nat, w1), List.length(&2, Nat, w2))), Nat.add(pos, List.length(&2, Nat, List.append(&2, Nat, w1, w2))),
    Lemma.add_assoc(pos, List.length(&2, Nat, w1), List.length(&2, Nat, w2)),
    Equal.cong(Nat, Nat, v => Nat.add(pos, v), Nat.add(List.length(&2, Nat, w1), List.length(&2, Nat, w2)), List.length(&2, Nat, List.append(&2, Nat, w1, w2)), Equal.sym(Nat, List.length(&2, Nat, List.append(&2, Nat, w1, w2)), Nat.add(List.length(&2, Nat, w1), List.length(&2, Nat, w2)), Lemma.length_append(w1, w2))))

law end_alone:
  for +pos: Nat
  for +w: +List<Nat>
  {Nat.add(pos, List.length(&2, Nat, w)) == Nat.add(pos, List.length(&2, Nat, List.append(&2, Nat, w, []))) : Nat}

def end_alone(pos, w):
  Equal.cong(+List<Nat>, Nat, v => Nat.add(pos, List.length(&2, Nat, v)), w, List.append(&2, Nat, w, []), Equal.sym(+List<Nat>, List.append(&2, Nat, w, []), w, Lemma.append_nil_right(w)))

# ---- Positions in the grammar ----

def dropItems(n: Nat, items: +List<Spec.Item>) -> +List<Spec.Item>:
  match n items:
    case 0n _:
      items
    case 1n+m Nil{}:
      []
    case 1n+m Con{x, rest}:
      dropItems(m, rest)

def headOr(items: +List<Spec.Item>, d: Spec.Item) -> Spec.Item:
  match items:
    case Nil{}:
      d
    case Con{x, rest}:
      x

def tailOf(items: +List<Spec.Item>) -> +List<Spec.Item>:
  match items:
    case Nil{}:
      []
    case Con{x, rest}:
      rest

def itemsEmpty(items: +List<Spec.Item>) -> Bool:
  match items:
    case Nil{}:
      True{}
    case Con{x, rest}:
      False{}

law drop_next:
  for n: Nat
  for seq: +List<Spec.Item>
  for +it: Spec.Item
  for +rest: +List<Spec.Item>
  for e: {dropItems(n, seq) == it <> rest : +List<Spec.Item>}
  {Gll.nthItem(seq, n) == Some{it} : Maybe<&2, Spec.Item>}

def drop_next(n, seq, it, rest, e):
  match n seq:
    case 0n Nil{}:
      Empty.absurd({Gll.nthItem([], 0n) == Some{it} : Maybe<&2, Spec.Item>}, Lemma.true_is_not_false(Equal.cong(+List<Spec.Item>, Bool, v => itemsEmpty(v), [], it <> rest, e)))
    case 0n Con{+x, +xs}:
      Equal.cong(Spec.Item, Maybe<&2, Spec.Item>, v => Some{v}, x, it, Equal.cong(+List<Spec.Item>, Spec.Item, v => headOr(v, x), x <> xs, it <> rest, e))
    case 1n+m Nil{}:
      Empty.absurd({Gll.nthItem([], 1n+m) == Some{it} : Maybe<&2, Spec.Item>}, Lemma.true_is_not_false(Equal.cong(+List<Spec.Item>, Bool, v => itemsEmpty(v), [], it <> rest, e)))
    case 1n+m Con{x, xs}:
      drop_next(m, xs, it, rest, e)

law drop_succ:
  for n: Nat
  for seq: +List<Spec.Item>
  for +it: Spec.Item
  for +rest: +List<Spec.Item>
  for e: {dropItems(n, seq) == it <> rest : +List<Spec.Item>}
  {dropItems(1n+n, seq) == rest : +List<Spec.Item>}

def drop_succ(n, seq, it, rest, e):
  match n seq:
    case 0n Nil{}:
      Empty.absurd({dropItems(1n, []) == rest : +List<Spec.Item>}, Lemma.true_is_not_false(Equal.cong(+List<Spec.Item>, Bool, v => itemsEmpty(v), [], it <> rest, e)))
    case 0n Con{+x, +xs}:
      Equal.cong(+List<Spec.Item>, +List<Spec.Item>, v => tailOf(v), x <> xs, it <> rest, e)
    case 1n+m Nil{}:
      Empty.absurd({dropItems(1n+1n+m, []) == rest : +List<Spec.Item>}, Lemma.true_is_not_false(Equal.cong(+List<Spec.Item>, Bool, v => itemsEmpty(v), [], it <> rest, e)))
    case 1n+m Con{x, xs}:
      drop_succ(m, xs, it, rest, e)

law drop_end:
  for n: Nat
  for seq: +List<Spec.Item>
  for e: {dropItems(n, seq) == [] : +List<Spec.Item>}
  {Gll.nthItem(seq, n) == None{} : Maybe<&2, Spec.Item>}

def drop_end(n, seq, e):
  match n seq:
    case 0n Nil{}:
      {==}
    case 0n Con{x, xs}:
      Empty.absurd({Gll.nthItem(x <> xs, 0n) == None{} : Maybe<&2, Spec.Item>}, Lemma.false_is_not_true(Equal.cong(+List<Spec.Item>, Bool, v => itemsEmpty(v), x <> xs, [], e)))
    case 1n+m Nil{}:
      {==}
    case 1n+m Con{x, xs}:
      drop_end(m, xs, e)

law lhs_of_is:
  for +grammar: +List<Spec.Production>
  for p: Nat
  for +a: Nat
  for e: {Spec.lhsIs(grammar, p, a) == True{} : Bool}
  {Gll.lhsOf(grammar, p) == a : Nat}

def lhs_of_is(grammar, p, a, e):
  match grammar p:
    case Nil{} 0n:
      Empty.absurd({0n == a : Nat}, Lemma.false_is_not_true(e))
    case Nil{} 1n+q:
      Empty.absurd({0n == a : Nat}, Lemma.false_is_not_true(e))
    case Con{Spec.Production{+lhs, rhs}, rest} 0n:
      Lemma.nat_eq_sound(lhs, a, e)
    case Con{prod, +rest} 1n+q:
      lhs_of_is(rest, q, a, e)

# ---- Slot paths: the specification's order and the engine's reversed one ----

law nat_append_assoc:
  for xs: +List<Nat>
  for +ys: +List<Nat>
  for +zs: +List<Nat>
  {List.append(&2, Nat, List.append(&2, Nat, xs, ys), zs) == List.append(&2, Nat, xs, List.append(&2, Nat, ys, zs)) : +List<Nat>}

def nat_append_assoc(xs, ys, zs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Equal.cong(+List<Nat>, +List<Nat>, v => x <> v, List.append(&2, Nat, List.append(&2, Nat, rest, ys), zs), List.append(&2, Nat, rest, List.append(&2, Nat, ys, zs)), nat_append_assoc(rest, ys, zs))

law rev_onto:
  for xs: +List<Nat>
  for +acc: +List<Nat>
  {Gll.reverseOnto(xs, acc) == List.append(&2, Nat, Gll.reverseOnto(xs, []), acc) : +List<Nat>}

def rev_onto(xs, acc):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Equal.trans(+List<Nat>, Gll.reverseOnto(rest, x <> acc), List.append(&2, Nat, Gll.reverseOnto(rest, []), x <> acc), List.append(&2, Nat, Gll.reverseOnto(rest, [x]), acc),
        rev_onto(rest, x <> acc),
        Equal.sym(+List<Nat>, List.append(&2, Nat, Gll.reverseOnto(rest, [x]), acc), List.append(&2, Nat, Gll.reverseOnto(rest, []), x <> acc),
          Equal.trans(+List<Nat>, List.append(&2, Nat, Gll.reverseOnto(rest, [x]), acc), List.append(&2, Nat, List.append(&2, Nat, Gll.reverseOnto(rest, []), [x]), acc), List.append(&2, Nat, Gll.reverseOnto(rest, []), x <> acc),
            Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, acc), Gll.reverseOnto(rest, [x]), List.append(&2, Nat, Gll.reverseOnto(rest, []), [x]), rev_onto(rest, [x])),
            nat_append_assoc(Gll.reverseOnto(rest, []), [x], acc))))

# A prefix in reading order, extended, is the reversed path read onto the extension.
law prefix_ext:
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +extra: +List<Nat>
  for pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  {List.append(&2, Nat, prefix, extra) == Gll.reverseOnto(rpath, extra) : +List<Nat>}

def prefix_ext(rpath, prefix, extra, pEq):
  Equal.trans(+List<Nat>, List.append(&2, Nat, prefix, extra), List.append(&2, Nat, Gll.reverseOnto(rpath, []), extra), Gll.reverseOnto(rpath, extra),
    Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, extra), prefix, Gll.reverseOnto(rpath, []), pEq),
    Equal.sym(+List<Nat>, Gll.reverseOnto(rpath, extra), List.append(&2, Nat, Gll.reverseOnto(rpath, []), extra), rev_onto(rpath, extra)))

# The step the specification lists is the step the engine records.
law step_in:
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +d: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for +s: Gll.GState
  for pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for m: {Check.stepIn(Gll.stepAt(index, rpath, d, i, k, j), s) == True{} : Bool}
  {Spec.bsrMember(Spec.at(index, prefix, d, i, k, j), Check.stepsOf(s)) == True{} : Bool}

def step_in(index, rpath, prefix, d, i, k, j, s, pEq, m):
  %Equal.sym(+List<Nat>, List.append(&2, Nat, prefix, [d]), Gll.reverseOnto(rpath, [d]), prefix_ext(rpath, prefix, [d], pEq)) : {Spec.bsrMember(Spec.Bsr{Spec.Slot{index, _}, i, k, j}, Check.stepsOf(s)) == True{} : Bool}
  m

# ======== THE WALK ========

def allStepsIn(+xs: +List<Spec.Bsr>, +s: Gll.GState) -> Bool:
  Spec.allIn(xs, Check.stepsOf(s))

law all_in_app:
  for xs: +List<Spec.Bsr>
  for +ys: +List<Spec.Bsr>
  for +set: +List<Spec.Bsr>
  for hx: {Spec.allIn(xs, set) == True{} : Bool}
  for +hy: {Spec.allIn(ys, set) == True{} : Bool}
  {Spec.allIn(List.append(&2, Spec.Bsr, xs, ys), set) == True{} : Bool}

def all_in_app(xs, ys, set, hx, hy):
  match xs:
    case Nil{}:
      hy
    case Con{+x, +rest}:
      +both = hx
      Lemma.and_true_intro(Spec.bsrMember(x, set), Spec.allIn(List.append(&2, Spec.Bsr, rest, ys), set),
        Lemma.and_true_left(Spec.bsrMember(x, set), Spec.allIn(rest, set), both),
        all_in_app(rest, ys, set, Lemma.and_true_right_side(Spec.bsrMember(x, set), Spec.allIn(rest, set), both), hy))

# The bracket item of a loop path: the item m of the sequence outside it.
def loopItem(+grammar: +List<Spec.Production>, +index: Nat, rpath: +List<Nat>) -> Maybe<&2, Spec.Item>:
  match rpath:
    case Con{+m, +outer}:
      Gll.nthItem(Gll.seqAt(grammar, index, outer), m)
    case Nil{}:
      None{}

# What the walk needs: in a sequence, the descriptor at the dot is seen and the forest
# fits the items from the dot on; in the rounds of a loop, every alternative of the loop
# has started at the position, and the forest is rounds of the loop's body.
def Ready(rounds: Bool, +grammar: +List<Spec.Production>, +input: +List<Nat>, +s: Gll.GState, +forest: +List<Spec.Tree>, +index: Nat, +rpath: +List<Nat>, +dot: Nat, +ctx: Nat, +pos: Nat, +items: +List<Spec.Item>, +kind: Spec.Bracket, +alts: +List<+List<Spec.Item>>) -> Type:
  match rounds:
    case False{}:
      {Check.descSeen(Gll.Desc{index, rpath, dot, ctx, pos}, s) == True{} : Bool} & {dropItems(dot, Gll.seqAt(grammar, index, rpath)) == items : +List<Spec.Item>} & {Spec.fits(forest, grammar, items) == True{} : Bool}
    case True{}:
      {Check.allSeen(Gll.alternatives(List.length(&2, +List<Spec.Item>, alts), index, rpath, ctx, pos), s) == True{} : Bool} & {loopItem(grammar, index, rpath) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>} & {Gll.isLoop(kind) == True{} : Bool} & {Spec.fits(forest, grammar, Spec.times(List.length(&2, Spec.Tree, forest), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}

# What the walk shows: its steps are in the state, and the cluster of the sequence (or
# of the loop) has ended where the forest ends.
def Walked(rounds: Bool, +grammar: +List<Spec.Production>, +s: Gll.GState, +forest: +List<Spec.Tree>, +index: Nat, +rpath: +List<Nat>, +prefix: +List<Nat>, +dot: Nat, +ctx: Nat, +pos: Nat) -> Type:
  match rounds:
    case False{}:
      {allStepsIn(Spec.walk(forest, False{}, index, prefix, dot, ctx, pos), s) == True{} : Bool} & {Check.popIn(Check.endKey(grammar, index, rpath, ctx), Nat.add(pos, List.length(&2, Nat, Spec.leaves(forest))), s) == True{} : Bool}
    case True{}:
      {allStepsIn(Spec.walk(forest, True{}, index, prefix, dot, ctx, pos), s) == True{} : Bool} & {Bool.or(List.is_empty(&2, Spec.Tree, forest), Check.popIn(Gll.CKey{Gll.TBr{index, rpath}, ctx}, Nat.add(pos, List.length(&2, Nat, Spec.leaves(forest))), s)) == True{} : Bool}

def WalkIH(+grammar: +List<Spec.Production>, +input: +List<Nat>, +s: Gll.GState, +forest: +List<Spec.Tree>) -> Type:
  @rounds: Bool -> @index: Nat -> @rpath: +List<Nat> -> @prefix: +List<Nat> -> @dot: Nat -> @ctx: Nat -> @pos: Nat -> @items: +List<Spec.Item> -> @kind: Spec.Bracket -> @alts: +List<+List<Spec.Item>> ->
    {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>} -> Spells(forest, input, pos) -> Ready(rounds, grammar, input, s, forest, index, rpath, dot, ctx, pos, items, kind, alts) -> Walked(rounds, grammar, s, forest, index, rpath, prefix, dot, ctx, pos)

# ---- The closedness conditions, one at a time ----

law seen_ok:
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for closedOk: {Check.closed(grammar, input, s) == True{} : Bool}
  for +d: Gll.Desc
  for seen: {Check.descSeen(d, s) == True{} : Bool}
  {Check.descOk(d, grammar, input, s) == True{} : Bool}

def seen_ok(grammar, input, s, closedOk, d, seen):
  desc_ok(Check.seenOf(s), d, grammar, input, s,
    Lemma.and_true_left(Check.allDescs(Check.seenOf(s), grammar, input, s), Bool.and(Check.allClusters(Check.clustersOf(s), grammar, s), Bool.and(Check.allReturns(Check.returnsOf(s), Check.popsOf(s), s), Check.allPops(Check.popsOf(s), grammar, s))), closedOk),
    seen)

law closed_rest:
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for closedOk: {Check.closed(grammar, input, s) == True{} : Bool}
  {Bool.and(Check.allClusters(Check.clustersOf(s), grammar, s), Bool.and(Check.allReturns(Check.returnsOf(s), Check.popsOf(s), s), Check.allPops(Check.popsOf(s), grammar, s))) == True{} : Bool}

def closed_rest(grammar, input, s, closedOk):
  Lemma.and_true_right_side(Check.allDescs(Check.seenOf(s), grammar, input, s), Bool.and(Check.allClusters(Check.clustersOf(s), grammar, s), Bool.and(Check.allReturns(Check.returnsOf(s), Check.popsOf(s), s), Check.allPops(Check.popsOf(s), grammar, s))), closedOk)

law cluster_ok:
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for closedOk: {Check.closed(grammar, input, s) == True{} : Bool}
  for +key: Gll.CKey
  for inC: {Check.clusterIn(key, s) == True{} : Bool}
  {Check.allSeen(Check.seedsOf(grammar, key), s) == True{} : Bool}

def cluster_ok(grammar, input, s, closedOk, key, inC):
  cluster_seeds(Check.clustersOf(s), key, grammar, s,
    Lemma.and_true_left(Check.allClusters(Check.clustersOf(s), grammar, s), Bool.and(Check.allReturns(Check.returnsOf(s), Check.popsOf(s), s), Check.allPops(Check.popsOf(s), grammar, s)), closed_rest(grammar, input, s, closedOk)),
    inC)

law closed_last:
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for closedOk: {Check.closed(grammar, input, s) == True{} : Bool}
  {Bool.and(Check.allReturns(Check.returnsOf(s), Check.popsOf(s), s), Check.allPops(Check.popsOf(s), grammar, s)) == True{} : Bool}

def closed_last(grammar, input, s, closedOk):
  Lemma.and_true_right_side(Check.allClusters(Check.clustersOf(s), grammar, s), Bool.and(Check.allReturns(Check.returnsOf(s), Check.popsOf(s), s), Check.allPops(Check.popsOf(s), grammar, s)), closed_rest(grammar, input, s, closedOk))

law resume_ok:
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for closedOk: {Check.closed(grammar, input, s) == True{} : Bool}
  for +key: Gll.CKey
  for +edge: Gll.Edge
  for +j: Nat
  for inR: {Check.returnIn(key, edge, s) == True{} : Bool}
  for inP: {Check.popIn(key, j, s) == True{} : Bool}
  {Check.resumeOk(edge, Check.keyStart(key), j, s) == True{} : Bool}

def resume_ok(grammar, input, s, closedOk, key, edge, j, inR, inP):
  edge_pop(Check.popsOf(s), key, edge, j, s,
    return_edge(Check.returnsOf(s), Check.popsOf(s), key, edge, s,
      Lemma.and_true_left(Check.allReturns(Check.returnsOf(s), Check.popsOf(s), s), Check.allPops(Check.popsOf(s), grammar, s), closed_last(grammar, input, s, closedOk)),
      inR),
    inP)

law again_ok:
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for closedOk: {Check.closed(grammar, input, s) == True{} : Bool}
  for +key: Gll.CKey
  for +j: Nat
  for inP: {Check.popIn(key, j, s) == True{} : Bool}
  {Check.allSeen(Check.againOfKey(grammar, key, j), s) == True{} : Bool}

def again_ok(grammar, input, s, closedOk, key, j, inP):
  pop_again(Check.popsOf(s), key, j, grammar, s,
    Lemma.and_true_right_side(Check.allReturns(Check.returnsOf(s), Check.popsOf(s), s), Check.allPops(Check.popsOf(s), grammar, s), closed_last(grammar, input, s, closedOk)),
    inP)

law item_ok_at:
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for +index: Nat
  for +rpath: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +item: Maybe<&2, Spec.Item>
  for itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == item : Maybe<&2, Spec.Item>}
  for ok: {Check.descOk(Gll.Desc{index, rpath, dot, ctx, pos}, grammar, input, s) == True{} : Bool}
  {Check.itemOk(item, grammar, input, index, rpath, dot, ctx, pos, s) == True{} : Bool}

def item_ok_at(grammar, input, s, index, rpath, dot, ctx, pos, item, itemEq, ok):
  Equal.trans(Bool, Check.itemOk(item, grammar, input, index, rpath, dot, ctx, pos, s), Check.itemOk(Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), grammar, input, index, rpath, dot, ctx, pos, s), True{},
    Equal.cong(Maybe<&2, Spec.Item>, Bool, v => Check.itemOk(v, grammar, input, index, rpath, dot, ctx, pos, s), item, Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), Equal.sym(Maybe<&2, Spec.Item>, Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), item, itemEq)),
    ok)

# ---- The end of a sequence ----

law nil_seq:
  for dot: Nat
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for +closedOk: {Check.closed(grammar, input, s) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +ctx: Nat
  for +pos: Nat
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +seen: {Check.descSeen(Gll.Desc{index, rpath, dot, ctx, pos}, s) == True{} : Bool}
  for +itemNone: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == None{} : Maybe<&2, Spec.Item>}
  Walked(False{}, grammar, s, [], index, rpath, prefix, dot, ctx, pos)

def nil_seq(dot, grammar, input, s, closedOk, index, rpath, prefix, ctx, pos, pEq, seen, itemNone):
  match dot:
    case 0n:
      +key = Check.endKey(grammar, index, rpath, ctx)
      +ok = item_ok_at(grammar, input, s, index, rpath, 0n, ctx, pos, None{}, itemNone, seen_ok(grammar, input, s, closedOk, Gll.Desc{index, rpath, 0n, ctx, pos}, seen))
      +eps = Gll.stepAt(index, rpath, 0n, ctx, pos, pos)
      stepP = Lemma.and_true_left(Check.stepIn(eps, s), Check.popIn(key, pos, s), ok)
      popP = Lemma.and_true_right_side(Check.stepIn(eps, s), Check.popIn(key, pos, s), ok)
      (Lemma.and_true_intro(Spec.bsrMember(Spec.at(index, prefix, 0n, ctx, pos, pos), Check.stepsOf(s)), True{}, step_in(index, rpath, prefix, 0n, ctx, pos, pos, s, pEq, stepP), {==}),
        Equal.trans(Bool, Check.popIn(key, Nat.add(pos, 0n), s), Check.popIn(key, pos, s), True{}, Equal.cong(Nat, Bool, v => Check.popIn(key, v, s), Nat.add(pos, 0n), pos, Lemma.add_zero_right(pos)), popP))
    case 1n+(+d):
      +key = Check.endKey(grammar, index, rpath, ctx)
      +ok = item_ok_at(grammar, input, s, index, rpath, 1n+d, ctx, pos, None{}, itemNone, seen_ok(grammar, input, s, closedOk, Gll.Desc{index, rpath, 1n+d, ctx, pos}, seen))
      popP = Lemma.and_true_right_side(True{}, Check.popIn(key, pos, s), ok)
      ({==}, Equal.trans(Bool, Check.popIn(key, Nat.add(pos, 0n), s), Check.popIn(key, pos, s), True{}, Equal.cong(Nat, Bool, v => Check.popIn(key, v, s), Nat.add(pos, 0n), pos, Lemma.add_zero_right(pos)), popP))

# ---- A terminal ----

law token_hit:
  for ok: Bool
  for +okEq: {ok == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +dot: Nat
  for +k: Nat
  for +i: Nat
  for +s: Gll.GState
  for r: {Check.tokenOk(ok, index, rpath, dot, k, i, s) == True{} : Bool}
  {Bool.and(Check.descSeen(Gll.Desc{index, rpath, 1n+dot, k, 1n+i}, s), Check.stepIn(Gll.stepAt(index, rpath, 1n+dot, k, i, 1n+i), s)) == True{} : Bool}

def token_hit(ok, okEq, index, rpath, dot, k, i, s, r):
  match ok:
    case True{}:
      r
    case False{}:
      Empty.absurd({Bool.and(Check.descSeen(Gll.Desc{index, rpath, 1n+dot, k, 1n+i}, s), Check.stepIn(Gll.stepAt(index, rpath, 1n+dot, k, i, 1n+i), s)) == True{} : Bool}, Lemma.false_is_not_true(okEq))

law leaf_finish:
  for +grammar: +List<Spec.Production>
  for +s: Gll.GState
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +kind: Nat
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for stepP: {Check.stepIn(Gll.stepAt(index, rpath, 1n+dot, ctx, pos, 1n+pos), s) == True{} : Bool}
  for ih: Walked(False{}, grammar, s, ts, index, rpath, prefix, 1n+dot, ctx, 1n+pos)
  Walked(False{}, grammar, s, Spec.Leaf{kind} <> ts, index, rpath, prefix, dot, ctx, pos)

def leaf_finish(grammar, s, index, rpath, prefix, dot, ctx, pos, kind, ts, pEq, stepP, ih):
  match ih:
    case (stepsTs, popTs):
      +n = List.length(&2, Nat, Spec.leaves(ts))
      +key = Check.endKey(grammar, index, rpath, ctx)
      (Lemma.and_true_intro(Spec.bsrMember(Spec.at(index, prefix, 1n+dot, ctx, pos, 1n+pos), Check.stepsOf(s)), allStepsIn(Spec.walk(ts, False{}, index, prefix, 1n+dot, ctx, 1n+pos), s), step_in(index, rpath, prefix, 1n+dot, ctx, pos, 1n+pos, s, pEq, stepP), stepsTs),
        Equal.trans(Bool, Check.popIn(key, Nat.add(pos, 1n+n), s), Check.popIn(key, 1n+Nat.add(pos, n), s), True{}, Equal.cong(Nat, Bool, v => Check.popIn(key, v, s), Nat.add(pos, 1n+n), 1n+Nat.add(pos, n), Lemma.add_succ_right(pos, n)), popTs))

law leaf_case:
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for +closedOk: {Check.closed(grammar, input, s) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +kind: Nat
  for +ts: +List<Spec.Tree>
  for +t: Nat
  for +rest: +List<Spec.Item>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: Spells(Spec.Leaf{kind} <> ts, input, pos)
  for +seen: {Check.descSeen(Gll.Desc{index, rpath, dot, ctx, pos}, s) == True{} : Bool}
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Sym{Spec.Terminal{t}}} : Maybe<&2, Spec.Item>}
  for +restEq: {dropItems(1n+dot, Gll.seqAt(grammar, index, rpath)) == rest : +List<Spec.Item>}
  for +fit: {Spec.fits(Spec.Leaf{kind} <> ts, grammar, Spec.Sym{Spec.Terminal{t}} <> rest) == True{} : Bool}
  for ihTs: WalkIH(grammar, input, s, ts)
  Walked(False{}, grammar, s, Spec.Leaf{kind} <> ts, index, rpath, prefix, dot, ctx, pos)

def leaf_case(grammar, input, s, closedOk, index, rpath, prefix, dot, ctx, pos, kind, ts, t, rest, pEq, sp, seen, itemEq, restEq, fit, ihTs):
  isKT = Lemma.and_true_left(Nat.is_eq(kind, t), Spec.fits(ts, grammar, rest), fit)
  fitTs = Lemma.and_true_right_side(Nat.is_eq(kind, t), Spec.fits(ts, grammar, rest), fit)
  ok = item_ok_at(grammar, input, s, index, rpath, dot, ctx, pos, Some{Spec.Sym{Spec.Terminal{t}}}, itemEq, seen_ok(grammar, input, s, closedOk, Gll.Desc{index, rpath, dot, ctx, pos}, seen))
  +get = List.get(&2, Nat, input, pos)
  tokEq = Equal.trans(Bool, Gll.tokenIs(get, t), Gll.tokenIs(Some{kind}, t), True{}, Equal.cong(Maybe<&2, Nat>, Bool, v => Gll.tokenIs(v, t), get, Some{kind}, leaf_token(input, pos, kind, Spec.leaves(ts), sp)), isKT)
  +hit = token_hit(Gll.tokenIs(get, t), tokEq, index, rpath, dot, ctx, pos, s, ok)
  +next = {Gll.Desc{index, rpath, 1n+dot, ctx, 1n+pos} : Gll.Desc}
  +step = Gll.stepAt(index, rpath, 1n+dot, ctx, pos, 1n+pos)
  leaf_finish(grammar, s, index, rpath, prefix, dot, ctx, pos, kind, ts, pEq, Lemma.and_true_right_side(Check.descSeen(next, s), Check.stepIn(step, s), hit),
    ihTs(False{}, index, rpath, prefix, 1n+dot, ctx, 1n+pos, rest, Spec.Group{}, [], pEq, leaf_rest(input, pos, kind, Spec.leaves(ts), sp), (Lemma.and_true_left(Check.descSeen(next, s), Check.stepIn(step, s), hit), (restEq, fitTs))))

# ---- A skipped [ ] or { } ----

law skip_finish:
  for +grammar: +List<Spec.Production>
  for +s: Gll.GState
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for stepP: {Check.stepIn(Gll.stepAt(index, rpath, 1n+dot, ctx, pos, pos), s) == True{} : Bool}
  for ih: Walked(False{}, grammar, s, ts, index, rpath, prefix, 1n+dot, ctx, pos)
  Walked(False{}, grammar, s, Spec.Skip{} <> ts, index, rpath, prefix, dot, ctx, pos)

def skip_finish(grammar, s, index, rpath, prefix, dot, ctx, pos, ts, pEq, stepP, ih):
  match ih:
    case (stepsTs, popTs):
      (Lemma.and_true_intro(Spec.bsrMember(Spec.at(index, prefix, 1n+dot, ctx, pos, pos), Check.stepsOf(s)), allStepsIn(Spec.walk(ts, False{}, index, prefix, 1n+dot, ctx, pos), s), step_in(index, rpath, prefix, 1n+dot, ctx, pos, pos, s, pEq, stepP), stepsTs), popTs)

law skip_hit:
  for skip: Bool
  for +skipEq: {skip == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +dot: Nat
  for +k: Nat
  for +i: Nat
  for +s: Gll.GState
  for r: {Check.skipOk(skip, index, rpath, dot, k, i, s) == True{} : Bool}
  {Bool.and(Check.descSeen(Gll.Desc{index, rpath, 1n+dot, k, i}, s), Check.stepIn(Gll.stepAt(index, rpath, 1n+dot, k, i, i), s)) == True{} : Bool}

def skip_hit(skip, skipEq, index, rpath, dot, k, i, s, r):
  match skip:
    case True{}:
      r
    case False{}:
      Empty.absurd({Bool.and(Check.descSeen(Gll.Desc{index, rpath, 1n+dot, k, i}, s), Check.stepIn(Gll.stepAt(index, rpath, 1n+dot, k, i, i), s)) == True{} : Bool}, Lemma.false_is_not_true(skipEq))

# The skip part of a bracket's check, for a bracket that may be skipped.
law skip_parts:
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for +closedOk: {Check.closed(grammar, input, s) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +bkind: Spec.Bracket
  for +balts: +List<+List<Spec.Item>>
  for +skippable: {Gll.isSkippable(bkind) == True{} : Bool}
  for +seen: {Check.descSeen(Gll.Desc{index, rpath, dot, ctx, pos}, s) == True{} : Bool}
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Brack{bkind, balts}} : Maybe<&2, Spec.Item>}
  {Bool.and(Check.descSeen(Gll.Desc{index, rpath, 1n+dot, ctx, pos}, s), Check.stepIn(Gll.stepAt(index, rpath, 1n+dot, ctx, pos, pos), s)) == True{} : Bool}

def skip_parts(grammar, input, s, closedOk, index, rpath, dot, ctx, pos, bkind, balts, skippable, seen, itemEq):
  +key = {Gll.CKey{Gll.TBr{index, dot <> rpath}, pos} : Gll.CKey}
  +edge = {Gll.Edge{index, rpath, dot, ctx} : Gll.Edge}
  +ok = item_ok_at(grammar, input, s, index, rpath, dot, ctx, pos, Some{Spec.Brack{bkind, balts}}, itemEq, seen_ok(grammar, input, s, closedOk, Gll.Desc{index, rpath, dot, ctx, pos}, seen))
  +skip = Check.skipOk(Gll.isSkippable(bkind), index, rpath, dot, ctx, pos, s)
  +r1 = Lemma.and_true_right_side(Check.clusterIn(key, s), Bool.and(Check.returnIn(key, edge, s), skip), ok)
  skip_hit(Gll.isSkippable(bkind), skippable, index, rpath, dot, ctx, pos, s, Lemma.and_true_right_side(Check.returnIn(key, edge, s), skip, r1))

law skip_case:
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for +closedOk: {Check.closed(grammar, input, s) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +ts: +List<Spec.Tree>
  for +balts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Item>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: Spells(Spec.Skip{} <> ts, input, pos)
  for +seen: {Check.descSeen(Gll.Desc{index, rpath, dot, ctx, pos}, s) == True{} : Bool}
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Brack{Spec.Optional{}, balts}} : Maybe<&2, Spec.Item>}
  for +restEq: {dropItems(1n+dot, Gll.seqAt(grammar, index, rpath)) == rest : +List<Spec.Item>}
  for +fitTs: {Spec.fits(ts, grammar, rest) == True{} : Bool}
  for ihTs: WalkIH(grammar, input, s, ts)
  Walked(False{}, grammar, s, Spec.Skip{} <> ts, index, rpath, prefix, dot, ctx, pos)

def skip_case(grammar, input, s, closedOk, index, rpath, prefix, dot, ctx, pos, ts, balts, rest, pEq, sp, seen, itemEq, restEq, fitTs, ihTs):
  +parts = skip_parts(grammar, input, s, closedOk, index, rpath, dot, ctx, pos, Spec.Optional{}, balts, {==}, seen, itemEq)
  +next = {Gll.Desc{index, rpath, 1n+dot, ctx, pos} : Gll.Desc}
  +step = Gll.stepAt(index, rpath, 1n+dot, ctx, pos, pos)
  skip_finish(grammar, s, index, rpath, prefix, dot, ctx, pos, ts, pEq, Lemma.and_true_right_side(Check.descSeen(next, s), Check.stepIn(step, s), parts),
    ihTs(False{}, index, rpath, prefix, 1n+dot, ctx, pos, rest, Spec.Group{}, [], pEq, sp, (Lemma.and_true_left(Check.descSeen(next, s), Check.stepIn(step, s), parts), (restEq, fitTs))))

# ---- An ε item: like a skip ----

law eps_case:
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for +closedOk: {Check.closed(grammar, input, s) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +ts: +List<Spec.Tree>
  for +rest: +List<Spec.Item>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: Spells(Spec.Skip{} <> ts, input, pos)
  for +seen: {Check.descSeen(Gll.Desc{index, rpath, dot, ctx, pos}, s) == True{} : Bool}
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Eps{}} : Maybe<&2, Spec.Item>}
  for +restEq: {dropItems(1n+dot, Gll.seqAt(grammar, index, rpath)) == rest : +List<Spec.Item>}
  for +fitTs: {Spec.fits(ts, grammar, rest) == True{} : Bool}
  for ihTs: WalkIH(grammar, input, s, ts)
  Walked(False{}, grammar, s, Spec.Skip{} <> ts, index, rpath, prefix, dot, ctx, pos)

def eps_case(grammar, input, s, closedOk, index, rpath, prefix, dot, ctx, pos, ts, rest, pEq, sp, seen, itemEq, restEq, fitTs, ihTs):
  +parts = item_ok_at(grammar, input, s, index, rpath, dot, ctx, pos, Some{Spec.Eps{}}, itemEq, seen_ok(grammar, input, s, closedOk, Gll.Desc{index, rpath, dot, ctx, pos}, seen))
  +next = {Gll.Desc{index, rpath, 1n+dot, ctx, pos} : Gll.Desc}
  +step = Gll.stepAt(index, rpath, 1n+dot, ctx, pos, pos)
  skip_finish(grammar, s, index, rpath, prefix, dot, ctx, pos, ts, pEq, Lemma.and_true_right_side(Check.descSeen(next, s), Check.stepIn(step, s), parts),
    ihTs(False{}, index, rpath, prefix, 1n+dot, ctx, pos, rest, Spec.Group{}, [], pEq, sp, (Lemma.and_true_left(Check.descSeen(next, s), Check.stepIn(step, s), parts), (restEq, fitTs))))

# A closure with no rounds: the skip, with its end written as pos + 0.
law empty_loop_finish:
  for +grammar: +List<Spec.Production>
  for +s: Gll.GState
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for stepP: {Check.stepIn(Gll.stepAt(index, rpath, 1n+dot, ctx, pos, Nat.add(pos, 0n)), s) == True{} : Bool}
  for ih: Walked(False{}, grammar, s, ts, index, rpath, prefix, 1n+dot, ctx, Nat.add(pos, 0n))
  Walked(False{}, grammar, s, Spec.Loop{[]} <> ts, index, rpath, prefix, dot, ctx, pos)

def empty_loop_finish(grammar, s, index, rpath, prefix, dot, ctx, pos, ts, pEq, stepP, ih):
  match ih:
    case (stepsTs, popTs):
      +key = Check.endKey(grammar, index, rpath, ctx)
      +n = List.length(&2, Nat, Spec.leaves(ts))
      (Lemma.and_true_intro(Spec.bsrMember(Spec.at(index, prefix, 1n+dot, ctx, pos, Nat.add(pos, 0n)), Check.stepsOf(s)), allStepsIn(Spec.walk(ts, False{}, index, prefix, 1n+dot, ctx, Nat.add(pos, 0n)), s), step_in(index, rpath, prefix, 1n+dot, ctx, pos, Nat.add(pos, 0n), s, pEq, stepP), stepsTs),
        Equal.trans(Bool, Check.popIn(key, Nat.add(pos, n), s), Check.popIn(key, Nat.add(Nat.add(pos, 0n), n), s), True{},
          Equal.cong(Nat, Bool, v => Check.popIn(key, Nat.add(v, n), s), pos, Nat.add(pos, 0n), Equal.sym(Nat, Nat.add(pos, 0n), pos, Lemma.add_zero_right(pos))), popTs))

law empty_loop_case:
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for +closedOk: {Check.closed(grammar, input, s) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +ts: +List<Spec.Tree>
  for +balts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Item>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: Spells(Spec.Loop{[]} <> ts, input, pos)
  for +seen: {Check.descSeen(Gll.Desc{index, rpath, dot, ctx, pos}, s) == True{} : Bool}
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Brack{Spec.Closure{}, balts}} : Maybe<&2, Spec.Item>}
  for +restEq: {dropItems(1n+dot, Gll.seqAt(grammar, index, rpath)) == rest : +List<Spec.Item>}
  for +fitTs: {Spec.fits(ts, grammar, rest) == True{} : Bool}
  for ihTs: WalkIH(grammar, input, s, ts)
  Walked(False{}, grammar, s, Spec.Loop{[]} <> ts, index, rpath, prefix, dot, ctx, pos)

def empty_loop_case(grammar, input, s, closedOk, index, rpath, prefix, dot, ctx, pos, ts, balts, rest, pEq, sp, seen, itemEq, restEq, fitTs, ihTs):
  +parts = skip_parts(grammar, input, s, closedOk, index, rpath, dot, ctx, pos, Spec.Closure{}, balts, {==}, seen, itemEq)
  +p0 = Nat.add(pos, 0n)
  +z = Equal.sym(Nat, p0, pos, Lemma.add_zero_right(pos))
  +next = {Gll.Desc{index, rpath, 1n+dot, ctx, pos} : Gll.Desc}
  +step = Gll.stepAt(index, rpath, 1n+dot, ctx, pos, pos)
  next0 = Equal.trans(Bool, Check.descSeen(Gll.Desc{index, rpath, 1n+dot, ctx, p0}, s), Check.descSeen(next, s), True{},
    Equal.cong(Nat, Bool, v => Check.descSeen(Gll.Desc{index, rpath, 1n+dot, ctx, v}, s), p0, pos, Lemma.add_zero_right(pos)), Lemma.and_true_left(Check.descSeen(next, s), Check.stepIn(step, s), parts))
  step0 = Equal.trans(Bool, Check.stepIn(Gll.stepAt(index, rpath, 1n+dot, ctx, pos, p0), s), Check.stepIn(step, s), True{},
    Equal.cong(Nat, Bool, v => Check.stepIn(Gll.stepAt(index, rpath, 1n+dot, ctx, pos, v), s), p0, pos, Lemma.add_zero_right(pos)), Lemma.and_true_right_side(Check.descSeen(next, s), Check.stepIn(step, s), parts))
  sp0 = Equal.trans(+List<Nat>, Spec.leaves(ts), Lemma.slice(input, pos, List.length(&2, Nat, Spec.leaves(ts))), Lemma.slice(input, p0, List.length(&2, Nat, Spec.leaves(ts))), sp,
    Equal.cong(Nat, +List<Nat>, v => Lemma.slice(input, v, List.length(&2, Nat, Spec.leaves(ts))), pos, p0, z))
  empty_loop_finish(grammar, s, index, rpath, prefix, dot, ctx, pos, ts, pEq, step0,
    ihTs(False{}, index, rpath, prefix, 1n+dot, ctx, p0, rest, Spec.Group{}, [], pEq, sp0, (next0, (restEq, fitTs))))

# ---- A call: a nonterminal, a ( ) or [ ] taken, or the rounds of a loop ----

# After the callee ended at `end`, the caller's step is in and the rest goes on from there.
law call_finish:
  for +grammar: +List<Spec.Production>
  for +s: Gll.GState
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +end: Nat
  for +inner: +List<Spec.Bsr>
  for +ts: +List<Spec.Tree>
  for +total: Nat
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for stepP: {Check.stepIn(Gll.stepAt(index, rpath, 1n+dot, ctx, pos, end), s) == True{} : Bool}
  for innerOk: {allStepsIn(inner, s) == True{} : Bool}
  for endEq: {Nat.add(end, List.length(&2, Nat, Spec.leaves(ts))) == total : Nat}
  for ih: Walked(False{}, grammar, s, ts, index, rpath, prefix, 1n+dot, ctx, end)
  {allStepsIn(Spec.at(index, prefix, 1n+dot, ctx, pos, end) <> List.append(&2, Spec.Bsr, inner, Spec.walk(ts, False{}, index, prefix, 1n+dot, ctx, end)), s) == True{} : Bool} & {Check.popIn(Check.endKey(grammar, index, rpath, ctx), total, s) == True{} : Bool}

def call_finish(grammar, s, index, rpath, prefix, dot, ctx, pos, end, inner, ts, total, pEq, stepP, innerOk, endEq, ih):
  match ih:
    case (stepsTs, popTs):
      +key = Check.endKey(grammar, index, rpath, ctx)
      +later = Spec.walk(ts, False{}, index, prefix, 1n+dot, ctx, end)
      (Lemma.and_true_intro(Spec.bsrMember(Spec.at(index, prefix, 1n+dot, ctx, pos, end), Check.stepsOf(s)), allStepsIn(List.append(&2, Spec.Bsr, inner, later), s), step_in(index, rpath, prefix, 1n+dot, ctx, pos, end, s, pEq, stepP),
          all_in_app(inner, later, Check.stepsOf(s), innerOk, stepsTs)),
        Equal.trans(Bool, Check.popIn(key, total, s), Check.popIn(key, Nat.add(end, List.length(&2, Nat, Spec.leaves(ts))), s), True{},
          Equal.cong(Nat, Bool, v => Check.popIn(key, v, s), total, Nat.add(end, List.length(&2, Nat, Spec.leaves(ts))), Equal.sym(Nat, Nat.add(end, List.length(&2, Nat, Spec.leaves(ts))), total, endEq)), popTs))

# The caller resumes after its callee: the next descriptor, and the call's step.
law resumed:
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for +closedOk: {Check.closed(grammar, input, s) == True{} : Bool}
  for +target: Gll.Target
  for +index: Nat
  for +rpath: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +end: Nat
  for inR: {Check.returnIn(Gll.CKey{target, pos}, Gll.Edge{index, rpath, dot, ctx}, s) == True{} : Bool}
  for inP: {Check.popIn(Gll.CKey{target, pos}, end, s) == True{} : Bool}
  {Bool.and(Check.descSeen(Gll.Desc{index, rpath, 1n+dot, ctx, end}, s), Check.stepIn(Gll.stepAt(index, rpath, 1n+dot, ctx, pos, end), s)) == True{} : Bool}

def resumed(grammar, input, s, closedOk, target, index, rpath, dot, ctx, pos, end, inR, inP):
  resume_ok(grammar, input, s, closedOk, Gll.CKey{target, pos}, Gll.Edge{index, rpath, dot, ctx}, end, inR, inP)

# The seeds of a bracket's cluster, once the item at the dot is known.
law alt_seeds:
  for +grammar: +List<Spec.Production>
  for +s: Gll.GState
  for +index: Nat
  for +rpath: +List<Nat>
  for +dot: Nat
  for +pos: Nat
  for +bkind: Spec.Bracket
  for +balts: +List<+List<Spec.Item>>
  for itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Brack{bkind, balts}} : Maybe<&2, Spec.Item>}
  for seeds: {Check.allSeen(Check.seedsOf(grammar, Gll.CKey{Gll.TBr{index, dot <> rpath}, pos}), s) == True{} : Bool}
  {Check.allSeen(Gll.alternatives(List.length(&2, +List<Spec.Item>, balts), index, dot <> rpath, pos, pos), s) == True{} : Bool}

def alt_seeds(grammar, s, index, rpath, dot, pos, bkind, balts, itemEq, seeds):
  +item = Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot)
  Equal.trans(Bool, Check.allSeen(Gll.alternatives(List.length(&2, +List<Spec.Item>, balts), index, dot <> rpath, pos, pos), s), Check.allSeen(Gll.alternatives(Check.altCount(item), index, dot <> rpath, pos, pos), s), True{},
    Equal.cong(Maybe<&2, Spec.Item>, Bool, v => Check.allSeen(Gll.alternatives(Check.altCount(v), index, dot <> rpath, pos, pos), s), Some{Spec.Brack{bkind, balts}}, item, Equal.sym(Maybe<&2, Spec.Item>, item, Some{Spec.Brack{bkind, balts}}, itemEq)),
    seeds)

# The sequence of alternative a of the bracket at the dot.
law alt_seq:
  for +grammar: +List<Spec.Production>
  for +index: Nat
  for +rpath: +List<Nat>
  for +dot: Nat
  for +a: Nat
  for +bkind: Spec.Bracket
  for +balts: +List<+List<Spec.Item>>
  for itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Brack{bkind, balts}} : Maybe<&2, Spec.Item>}
  {dropItems(0n, Gll.seqAt(grammar, index, a <> dot <> rpath)) == Spec.altOf(balts, a) : +List<Spec.Item>}

def alt_seq(grammar, index, rpath, dot, a, bkind, balts, itemEq):
  Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Gll.bracketAlt(v, a), Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), Some{Spec.Brack{bkind, balts}}, itemEq)

# ---- A nonterminal ----

law node_after:
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for +closedOk: {Check.closed(grammar, input, s) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +q: Nat
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +x: Nat
  for +rest: +List<Spec.Item>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: Spells(Spec.Node{q, ch} <> ts, input, pos)
  for +lhsOk: {Spec.lhsIs(grammar, q, x) == True{} : Bool}
  for +inR: {Check.returnIn(Gll.CKey{Gll.TNt{x}, pos}, Gll.Edge{index, rpath, dot, ctx}, s) == True{} : Bool}
  for +restEq: {dropItems(1n+dot, Gll.seqAt(grammar, index, rpath)) == rest : +List<Spec.Item>}
  for +fitTs: {Spec.fits(ts, grammar, rest) == True{} : Bool}
  for ihTs: WalkIH(grammar, input, s, ts)
  for inner: Walked(False{}, grammar, s, ch, q, [], [], 0n, pos, pos)
  Walked(False{}, grammar, s, Spec.Node{q, ch} <> ts, index, rpath, prefix, dot, ctx, pos)

def node_after(grammar, input, s, closedOk, index, rpath, prefix, dot, ctx, pos, q, ch, ts, x, rest, pEq, sp, lhsOk, inR, restEq, fitTs, ihTs, inner):
  match inner:
    case (stepsCh, popCh):
      +lch = Spec.leaves(ch)
      +lts = Spec.leaves(ts)
      +e1 = Nat.add(pos, List.length(&2, Nat, lch))
      popX = Equal.trans(Bool, Check.popIn(Gll.CKey{Gll.TNt{x}, pos}, e1, s), Check.popIn(Gll.CKey{Gll.TNt{Gll.lhsOf(grammar, q)}, pos}, e1, s), True{},
        Equal.cong(Nat, Bool, v => Check.popIn(Gll.CKey{Gll.TNt{v}, pos}, e1, s), x, Gll.lhsOf(grammar, q), Equal.sym(Nat, Gll.lhsOf(grammar, q), x, lhs_of_is(grammar, q, x, lhsOk))), popCh)
      +res = resumed(grammar, input, s, closedOk, Gll.TNt{x}, index, rpath, dot, ctx, pos, e1, inR, popX)
      +next = {Gll.Desc{index, rpath, 1n+dot, ctx, e1} : Gll.Desc}
      +step = Gll.stepAt(index, rpath, 1n+dot, ctx, pos, e1)
      call_finish(grammar, s, index, rpath, prefix, dot, ctx, pos, e1, Spec.walk(ch, False{}, q, [], 0n, pos, pos), ts, Nat.add(pos, List.length(&2, Nat, List.append(&2, Nat, lch, lts))), pEq,
        Lemma.and_true_right_side(Check.descSeen(next, s), Check.stepIn(step, s), res), stepsCh, end_split(pos, lch, lts),
        ihTs(False{}, index, rpath, prefix, 1n+dot, ctx, e1, rest, Spec.Group{}, [], pEq, spells_second(input, pos, lch, lts, sp), (Lemma.and_true_left(Check.descSeen(next, s), Check.stepIn(step, s), res), (restEq, fitTs))))

law node_case:
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for +closedOk: {Check.closed(grammar, input, s) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +q: Nat
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +x: Nat
  for +rest: +List<Spec.Item>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: Spells(Spec.Node{q, ch} <> ts, input, pos)
  for +seen: {Check.descSeen(Gll.Desc{index, rpath, dot, ctx, pos}, s) == True{} : Bool}
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Sym{Spec.Nonterminal{x}}} : Maybe<&2, Spec.Item>}
  for +restEq: {dropItems(1n+dot, Gll.seqAt(grammar, index, rpath)) == rest : +List<Spec.Item>}
  for +fit: {Spec.fits(Spec.Node{q, ch} <> ts, grammar, Spec.Sym{Spec.Nonterminal{x}} <> rest) == True{} : Bool}
  for ihCh: WalkIH(grammar, input, s, ch)
  for ihTs: WalkIH(grammar, input, s, ts)
  Walked(False{}, grammar, s, Spec.Node{q, ch} <> ts, index, rpath, prefix, dot, ctx, pos)

def node_case(grammar, input, s, closedOk, index, rpath, prefix, dot, ctx, pos, q, ch, ts, x, rest, pEq, sp, seen, itemEq, restEq, fit, ihCh, ihTs):
  +h = Bool.and(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)))
  +hOk = Lemma.and_true_left(h, Spec.fits(ts, grammar, rest), fit)
  +lhsOk = Lemma.and_true_left(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hOk)
  fitCh = Lemma.and_true_right_side(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hOk)
  fitTs = Lemma.and_true_right_side(h, Spec.fits(ts, grammar, rest), fit)
  +key = {Gll.CKey{Gll.TNt{x}, pos} : Gll.CKey}
  +edge = {Gll.Edge{index, rpath, dot, ctx} : Gll.Edge}
  +ok = item_ok_at(grammar, input, s, index, rpath, dot, ctx, pos, Some{Spec.Sym{Spec.Nonterminal{x}}}, itemEq, seen_ok(grammar, input, s, closedOk, Gll.Desc{index, rpath, dot, ctx, pos}, seen))
  seeds = cluster_ok(grammar, input, s, closedOk, key, Lemma.and_true_left(Check.clusterIn(key, s), Check.returnIn(key, edge, s), ok))
  start = productions_seen(grammar, x, 0n, pos, q, s, lhsOk, seeds)
  node_after(grammar, input, s, closedOk, index, rpath, prefix, dot, ctx, pos, q, ch, ts, x, rest, pEq, sp, lhsOk, Lemma.and_true_right_side(Check.clusterIn(key, s), Check.returnIn(key, edge, s), ok), restEq, fitTs, ihTs,
    ihCh(False{}, q, [], [], 0n, pos, pos, Spec.rhsOf(grammar, q), Spec.Group{}, [], {==}, spells_first(input, pos, Spec.leaves(ch), Spec.leaves(ts), sp), (start, ({==}, fitCh))))

# ---- A ( ) or [ ] that matched ----

law pick_after:
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for +closedOk: {Check.closed(grammar, input, s) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +rest: +List<Spec.Item>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: Spells(Spec.Pick{a, ch} <> ts, input, pos)
  for +inR: {Check.returnIn(Gll.CKey{Gll.TBr{index, dot <> rpath}, pos}, Gll.Edge{index, rpath, dot, ctx}, s) == True{} : Bool}
  for +restEq: {dropItems(1n+dot, Gll.seqAt(grammar, index, rpath)) == rest : +List<Spec.Item>}
  for +fitTs: {Spec.fits(ts, grammar, rest) == True{} : Bool}
  for ihTs: WalkIH(grammar, input, s, ts)
  for inner: Walked(False{}, grammar, s, ch, index, a <> dot <> rpath, List.append(&2, Nat, prefix, [dot, a]), 0n, pos, pos)
  Walked(False{}, grammar, s, Spec.Pick{a, ch} <> ts, index, rpath, prefix, dot, ctx, pos)

def pick_after(grammar, input, s, closedOk, index, rpath, prefix, dot, ctx, pos, a, ch, ts, rest, pEq, sp, inR, restEq, fitTs, ihTs, inner):
  match inner:
    case (stepsCh, popCh):
      +lch = Spec.leaves(ch)
      +lts = Spec.leaves(ts)
      +e1 = Nat.add(pos, List.length(&2, Nat, lch))
      +res = resumed(grammar, input, s, closedOk, Gll.TBr{index, dot <> rpath}, index, rpath, dot, ctx, pos, e1, inR, popCh)
      +next = {Gll.Desc{index, rpath, 1n+dot, ctx, e1} : Gll.Desc}
      +step = Gll.stepAt(index, rpath, 1n+dot, ctx, pos, e1)
      call_finish(grammar, s, index, rpath, prefix, dot, ctx, pos, e1, Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, pos, pos), ts, Nat.add(pos, List.length(&2, Nat, List.append(&2, Nat, lch, lts))), pEq,
        Lemma.and_true_right_side(Check.descSeen(next, s), Check.stepIn(step, s), res), stepsCh, end_split(pos, lch, lts),
        ihTs(False{}, index, rpath, prefix, 1n+dot, ctx, e1, rest, Spec.Group{}, [], pEq, spells_second(input, pos, lch, lts, sp), (Lemma.and_true_left(Check.descSeen(next, s), Check.stepIn(step, s), res), (restEq, fitTs))))

law pick_case:
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for +closedOk: {Check.closed(grammar, input, s) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +bkind: Spec.Bracket
  for +balts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Item>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: Spells(Spec.Pick{a, ch} <> ts, input, pos)
  for +seen: {Check.descSeen(Gll.Desc{index, rpath, dot, ctx, pos}, s) == True{} : Bool}
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Brack{bkind, balts}} : Maybe<&2, Spec.Item>}
  for +restEq: {dropItems(1n+dot, Gll.seqAt(grammar, index, rpath)) == rest : +List<Spec.Item>}
  for +isA: {Spec.isAlt(balts, a) == True{} : Bool}
  for +fitCh: {Spec.fits(ch, grammar, Spec.altOf(balts, a)) == True{} : Bool}
  for +fitTs: {Spec.fits(ts, grammar, rest) == True{} : Bool}
  for ihCh: WalkIH(grammar, input, s, ch)
  for ihTs: WalkIH(grammar, input, s, ts)
  Walked(False{}, grammar, s, Spec.Pick{a, ch} <> ts, index, rpath, prefix, dot, ctx, pos)

def pick_case(grammar, input, s, closedOk, index, rpath, prefix, dot, ctx, pos, a, ch, ts, bkind, balts, rest, pEq, sp, seen, itemEq, restEq, isA, fitCh, fitTs, ihCh, ihTs):
  +key = {Gll.CKey{Gll.TBr{index, dot <> rpath}, pos} : Gll.CKey}
  +edge = {Gll.Edge{index, rpath, dot, ctx} : Gll.Edge}
  +skip = Check.skipOk(Gll.isSkippable(bkind), index, rpath, dot, ctx, pos, s)
  +ok = item_ok_at(grammar, input, s, index, rpath, dot, ctx, pos, Some{Spec.Brack{bkind, balts}}, itemEq, seen_ok(grammar, input, s, closedOk, Gll.Desc{index, rpath, dot, ctx, pos}, seen))
  +r1 = Lemma.and_true_right_side(Check.clusterIn(key, s), Bool.and(Check.returnIn(key, edge, s), skip), ok)
  seeds = alt_seeds(grammar, s, index, rpath, dot, pos, bkind, balts, itemEq, cluster_ok(grammar, input, s, closedOk, key, Lemma.and_true_left(Check.clusterIn(key, s), Bool.and(Check.returnIn(key, edge, s), skip), ok)))
  start = alternatives_seen(List.length(&2, +List<Spec.Item>, balts), index, dot <> rpath, pos, pos, a, s, isA, seeds)
  pick_after(grammar, input, s, closedOk, index, rpath, prefix, dot, ctx, pos, a, ch, ts, rest, pEq, sp, Lemma.and_true_left(Check.returnIn(key, edge, s), skip, r1), restEq, fitTs, ihTs,
    ihCh(False{}, index, a <> dot <> rpath, List.append(&2, Nat, prefix, [dot, a]), 0n, pos, pos, Spec.altOf(balts, a), Spec.Group{}, [], prefix_ext(rpath, prefix, [dot, a], pEq), spells_first(input, pos, Spec.leaves(ch), Spec.leaves(ts), sp), (start, (alt_seq(grammar, index, rpath, dot, a, bkind, balts, itemEq), fitCh))))

# ---- A loop with rounds ----

law loop_after:
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for +closedOk: {Check.closed(grammar, input, s) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +r: Spec.Tree
  for +rr: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +rest: +List<Spec.Item>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: Spells(Spec.Loop{r <> rr} <> ts, input, pos)
  for +inR: {Check.returnIn(Gll.CKey{Gll.TBr{index, dot <> rpath}, pos}, Gll.Edge{index, rpath, dot, ctx}, s) == True{} : Bool}
  for +restEq: {dropItems(1n+dot, Gll.seqAt(grammar, index, rpath)) == rest : +List<Spec.Item>}
  for +fitTs: {Spec.fits(ts, grammar, rest) == True{} : Bool}
  for ihTs: WalkIH(grammar, input, s, ts)
  for inner: Walked(True{}, grammar, s, r <> rr, index, dot <> rpath, List.append(&2, Nat, prefix, [dot]), 0n, pos, pos)
  Walked(False{}, grammar, s, Spec.Loop{r <> rr} <> ts, index, rpath, prefix, dot, ctx, pos)

def loop_after(grammar, input, s, closedOk, index, rpath, prefix, dot, ctx, pos, r, rr, ts, rest, pEq, sp, inR, restEq, fitTs, ihTs, inner):
  match inner:
    case (stepsRs, popRs):
      +lrs = Spec.leaves(r <> rr)
      +lts = Spec.leaves(ts)
      +e1 = Nat.add(pos, List.length(&2, Nat, lrs))
      +res = resumed(grammar, input, s, closedOk, Gll.TBr{index, dot <> rpath}, index, rpath, dot, ctx, pos, e1, inR, popRs)
      +next = {Gll.Desc{index, rpath, 1n+dot, ctx, e1} : Gll.Desc}
      +step = Gll.stepAt(index, rpath, 1n+dot, ctx, pos, e1)
      call_finish(grammar, s, index, rpath, prefix, dot, ctx, pos, e1, Spec.walk(r <> rr, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, pos, pos), ts, Nat.add(pos, List.length(&2, Nat, List.append(&2, Nat, lrs, lts))), pEq,
        Lemma.and_true_right_side(Check.descSeen(next, s), Check.stepIn(step, s), res), stepsRs, end_split(pos, lrs, lts),
        ihTs(False{}, index, rpath, prefix, 1n+dot, ctx, e1, rest, Spec.Group{}, [], pEq, spells_second(input, pos, lrs, lts, sp), (Lemma.and_true_left(Check.descSeen(next, s), Check.stepIn(step, s), res), (restEq, fitTs))))

law loop_case:
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for +closedOk: {Check.closed(grammar, input, s) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +r: Spec.Tree
  for +rr: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +bkind: Spec.Bracket
  for +balts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Item>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: Spells(Spec.Loop{r <> rr} <> ts, input, pos)
  for +seen: {Check.descSeen(Gll.Desc{index, rpath, dot, ctx, pos}, s) == True{} : Bool}
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Brack{bkind, balts}} : Maybe<&2, Spec.Item>}
  for +restEq: {dropItems(1n+dot, Gll.seqAt(grammar, index, rpath)) == rest : +List<Spec.Item>}
  for +loopOk: {Gll.isLoop(bkind) == True{} : Bool}
  for +fitRs: {Spec.fits(r <> rr, grammar, Spec.times(List.length(&2, Spec.Tree, r <> rr), Spec.Brack{Spec.Group{}, balts})) == True{} : Bool}
  for +fitTs: {Spec.fits(ts, grammar, rest) == True{} : Bool}
  for ihRs: WalkIH(grammar, input, s, r <> rr)
  for ihTs: WalkIH(grammar, input, s, ts)
  Walked(False{}, grammar, s, Spec.Loop{r <> rr} <> ts, index, rpath, prefix, dot, ctx, pos)

def loop_case(grammar, input, s, closedOk, index, rpath, prefix, dot, ctx, pos, r, rr, ts, bkind, balts, rest, pEq, sp, seen, itemEq, restEq, loopOk, fitRs, fitTs, ihRs, ihTs):
  +key = {Gll.CKey{Gll.TBr{index, dot <> rpath}, pos} : Gll.CKey}
  +edge = {Gll.Edge{index, rpath, dot, ctx} : Gll.Edge}
  +skip = Check.skipOk(Gll.isSkippable(bkind), index, rpath, dot, ctx, pos, s)
  +ok = item_ok_at(grammar, input, s, index, rpath, dot, ctx, pos, Some{Spec.Brack{bkind, balts}}, itemEq, seen_ok(grammar, input, s, closedOk, Gll.Desc{index, rpath, dot, ctx, pos}, seen))
  +r1 = Lemma.and_true_right_side(Check.clusterIn(key, s), Bool.and(Check.returnIn(key, edge, s), skip), ok)
  seeds = alt_seeds(grammar, s, index, rpath, dot, pos, bkind, balts, itemEq, cluster_ok(grammar, input, s, closedOk, key, Lemma.and_true_left(Check.clusterIn(key, s), Bool.and(Check.returnIn(key, edge, s), skip), ok)))
  loop_after(grammar, input, s, closedOk, index, rpath, prefix, dot, ctx, pos, r, rr, ts, rest, pEq, sp, Lemma.and_true_left(Check.returnIn(key, edge, s), skip, r1), restEq, fitTs, ihTs,
    ihRs(True{}, index, dot <> rpath, List.append(&2, Nat, prefix, [dot]), 0n, pos, pos, [], bkind, balts, prefix_ext(rpath, prefix, [dot], pEq), spells_first(input, pos, Spec.leaves(r <> rr), Spec.leaves(ts), sp), (seeds, (itemEq, (loopOk, fitRs)))))

# ---- The rounds of a loop ----

law again_hit:
  for loop: Bool
  for +loopEq: {loop == True{} : Bool}
  for +n: Nat
  for +index: Nat
  for +rpath: +List<Nat>
  for +k: Nat
  for +i: Nat
  for +s: Gll.GState
  for r: {Check.allSeen(Gll.againPick(loop, n, index, rpath, k, i), s) == True{} : Bool}
  {Check.allSeen(Gll.alternatives(n, index, rpath, k, i), s) == True{} : Bool}

def again_hit(loop, loopEq, n, index, rpath, k, i, s, r):
  match loop:
    case True{}:
      r
    case False{}:
      Empty.absurd({Check.allSeen(Gll.alternatives(n, index, rpath, k, i), s) == True{} : Bool}, Lemma.false_is_not_true(loopEq))

# After a round ends at j, the loop starts every alternative again from j.
law round_again:
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for +closedOk: {Check.closed(grammar, input, s) == True{} : Bool}
  for +index: Nat
  for +m: Nat
  for +outer: +List<Nat>
  for +ctx: Nat
  for +j: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, outer), m) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +loopOk: {Gll.isLoop(kind) == True{} : Bool}
  for inP: {Check.popIn(Gll.CKey{Gll.TBr{index, m <> outer}, ctx}, j, s) == True{} : Bool}
  {Check.allSeen(Gll.alternatives(List.length(&2, +List<Spec.Item>, alts), index, m <> outer, ctx, j), s) == True{} : Bool}

def round_again(grammar, input, s, closedOk, index, m, outer, ctx, j, kind, alts, itemEq, loopOk, inP):
  +item = Gll.nthItem(Gll.seqAt(grammar, index, outer), m)
  again = again_ok(grammar, input, s, closedOk, Gll.CKey{Gll.TBr{index, m <> outer}, ctx}, j, inP)
  againK = Equal.trans(Bool, Check.allSeen(Gll.againOf(Some{Spec.Brack{kind, alts}}, index, m <> outer, ctx, j), s), Check.allSeen(Gll.againOf(item, index, m <> outer, ctx, j), s), True{},
    Equal.cong(Maybe<&2, Spec.Item>, Bool, v => Check.allSeen(Gll.againOf(v, index, m <> outer, ctx, j), s), Some{Spec.Brack{kind, alts}}, item, Equal.sym(Maybe<&2, Spec.Item>, item, Some{Spec.Brack{kind, alts}}, itemEq)),
    again)
  again_hit(Gll.isLoop(kind), loopOk, List.length(&2, +List<Spec.Item>, alts), index, m <> outer, ctx, j, s, againK)

law round_rest:
  for +grammar: +List<Spec.Production>
  for +s: Gll.GState
  for +index: Nat
  for +m: Nat
  for +outer: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +r2: Spec.Tree
  for +rest2: +List<Spec.Tree>
  for stepsCh: {allStepsIn(Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [a]), 0n, ctx, pos), s) == True{} : Bool}
  for later: Walked(True{}, grammar, s, r2 <> rest2, index, m <> outer, prefix, 0n, ctx, Nat.add(pos, List.length(&2, Nat, Spec.leaves(ch))))
  Walked(True{}, grammar, s, Spec.Pick{a, ch} <> r2 <> rest2, index, m <> outer, prefix, dot, ctx, pos)

def round_rest(grammar, s, index, m, outer, prefix, dot, ctx, pos, a, ch, r2, rest2, stepsCh, later):
  match later:
    case (stepsRest, popRest):
      +lch = Spec.leaves(ch)
      +lrest = Spec.leaves(r2 <> rest2)
      +e1 = Nat.add(pos, List.length(&2, Nat, lch))
      +key = {Gll.CKey{Gll.TBr{index, m <> outer}, ctx} : Gll.CKey}
      (all_in_app(Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [a]), 0n, ctx, pos), Spec.walk(r2 <> rest2, True{}, index, prefix, 0n, ctx, e1), Check.stepsOf(s), stepsCh, stepsRest),
        Equal.trans(Bool, Check.popIn(key, Nat.add(pos, List.length(&2, Nat, List.append(&2, Nat, lch, lrest))), s), Check.popIn(key, Nat.add(e1, List.length(&2, Nat, lrest)), s), True{},
          Equal.cong(Nat, Bool, v => Check.popIn(key, v, s), Nat.add(pos, List.length(&2, Nat, List.append(&2, Nat, lch, lrest))), Nat.add(e1, List.length(&2, Nat, lrest)), Equal.sym(Nat, Nat.add(e1, List.length(&2, Nat, lrest)), Nat.add(pos, List.length(&2, Nat, List.append(&2, Nat, lch, lrest))), end_split(pos, lch, lrest))),
          popRest))

law round_after:
  for rest: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for +closedOk: {Check.closed(grammar, input, s) == True{} : Bool}
  for +index: Nat
  for +m: Nat
  for +outer: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +pEq: {prefix == Gll.reverseOnto(m <> outer, []) : +List<Nat>}
  for +sp: Spells(Spec.Pick{a, ch} <> rest, input, pos)
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, outer), m) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +loopOk: {Gll.isLoop(kind) == True{} : Bool}
  for +fitRest: {Spec.fits(rest, grammar, Spec.times(List.length(&2, Spec.Tree, rest), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for ihRest: WalkIH(grammar, input, s, rest)
  for inner: Walked(False{}, grammar, s, ch, index, a <> m <> outer, List.append(&2, Nat, prefix, [a]), 0n, ctx, pos)
  Walked(True{}, grammar, s, Spec.Pick{a, ch} <> rest, index, m <> outer, prefix, dot, ctx, pos)

def round_after(rest, grammar, input, s, closedOk, index, m, outer, prefix, dot, ctx, pos, a, ch, kind, alts, pEq, sp, itemEq, loopOk, fitRest, ihRest, inner):
  match rest:
    case Nil{}:
      match inner:
        case (stepsCh, popCh):
          +lch = Spec.leaves(ch)
          +key = {Gll.CKey{Gll.TBr{index, m <> outer}, ctx} : Gll.CKey}
          (all_in_app(Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [a]), 0n, ctx, pos), [], Check.stepsOf(s), stepsCh, {==}),
            Equal.trans(Bool, Check.popIn(key, Nat.add(pos, List.length(&2, Nat, List.append(&2, Nat, lch, []))), s), Check.popIn(key, Nat.add(pos, List.length(&2, Nat, lch)), s), True{},
              Equal.cong(Nat, Bool, v => Check.popIn(key, v, s), Nat.add(pos, List.length(&2, Nat, List.append(&2, Nat, lch, []))), Nat.add(pos, List.length(&2, Nat, lch)), Equal.sym(Nat, Nat.add(pos, List.length(&2, Nat, lch)), Nat.add(pos, List.length(&2, Nat, List.append(&2, Nat, lch, []))), end_alone(pos, lch))),
              popCh))
    case Con{+r2, +rest2}:
      match inner:
        case (stepsCh, popCh):
          +lch = Spec.leaves(ch)
          +lrest = Spec.leaves(r2 <> rest2)
          +e1 = Nat.add(pos, List.length(&2, Nat, lch))
          +key = {Gll.CKey{Gll.TBr{index, m <> outer}, ctx} : Gll.CKey}
          starts = round_again(grammar, input, s, closedOk, index, m, outer, ctx, e1, kind, alts, itemEq, loopOk, popCh)
          round_rest(grammar, s, index, m, outer, prefix, dot, ctx, pos, a, ch, r2, rest2, stepsCh,
            ihRest(True{}, index, m <> outer, prefix, 0n, ctx, e1, [], kind, alts, pEq, spells_second(input, pos, lch, lrest, sp), (starts, (itemEq, (loopOk, fitRest)))))

def isNone(x: Maybe<&2, Spec.Item>) -> Bool:
  match x:
    case None{}:
      True{}
    case Some{v}:
      False{}

law round_case:
  for rpath: +List<Nat>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for +closedOk: {Check.closed(grammar, input, s) == True{} : Bool}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +rest: +List<Spec.Tree>
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: Spells(Spec.Pick{a, ch} <> rest, input, pos)
  for +starts: {Check.allSeen(Gll.alternatives(List.length(&2, +List<Spec.Item>, alts), index, rpath, ctx, pos), s) == True{} : Bool}
  for +itemEq: {loopItem(grammar, index, rpath) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +loopOk: {Gll.isLoop(kind) == True{} : Bool}
  for +isA: {Spec.isAlt(alts, a) == True{} : Bool}
  for +fitCh: {Spec.fits(ch, grammar, Spec.altOf(alts, a)) == True{} : Bool}
  for +fitRest: {Spec.fits(rest, grammar, Spec.times(List.length(&2, Spec.Tree, rest), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for ihCh: WalkIH(grammar, input, s, ch)
  for ihRest: WalkIH(grammar, input, s, rest)
  Walked(True{}, grammar, s, Spec.Pick{a, ch} <> rest, index, rpath, prefix, dot, ctx, pos)

def round_case(rpath, grammar, input, s, closedOk, index, prefix, dot, ctx, pos, a, ch, rest, kind, alts, pEq, sp, starts, itemEq, loopOk, isA, fitCh, fitRest, ihCh, ihRest):
  match rpath:
    case Nil{}:
      Empty.absurd(Walked(True{}, grammar, s, Spec.Pick{a, ch} <> rest, index, [], prefix, dot, ctx, pos), Lemma.true_is_not_false(Equal.cong(Maybe<&2, Spec.Item>, Bool, v => isNone(v), None{}, Some{Spec.Brack{kind, alts}}, itemEq)))
    case Con{+m, +outer}:
      start = alternatives_seen(List.length(&2, +List<Spec.Item>, alts), index, m <> outer, ctx, pos, a, s, isA, starts)
      remCh = Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Gll.bracketAlt(v, a), Gll.nthItem(Gll.seqAt(grammar, index, outer), m), Some{Spec.Brack{kind, alts}}, itemEq)
      round_after(rest, grammar, input, s, closedOk, index, m, outer, prefix, dot, ctx, pos, a, ch, kind, alts, pEq, sp, itemEq, loopOk, fitRest, ihRest,
        ihCh(False{}, index, a <> m <> outer, List.append(&2, Nat, prefix, [a]), 0n, ctx, pos, Spec.altOf(alts, a), Spec.Group{}, [], prefix_ext(m <> outer, prefix, [a], pEq), spells_first(input, pos, Spec.leaves(ch), Spec.leaves(rest), sp), (start, (remCh, fitCh))))

law leaf_disp:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for +closedOk: {Check.closed(grammar, input, s) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +k0: Nat
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: Spells(Spec.Leaf{k0} <> ts, input, pos)
  for ready: Ready(False{}, grammar, input, s, Spec.Leaf{k0} <> ts, index, rpath, dot, ctx, pos, items, kind, alts)
  for ihTs: WalkIH(grammar, input, s, ts)
  Walked(False{}, grammar, s, Spec.Leaf{k0} <> ts, index, rpath, prefix, dot, ctx, pos)

def leaf_disp(items, grammar, input, s, closedOk, index, rpath, prefix, dot, ctx, pos, kind, alts, k0, ts, pEq, sp, ready, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (seen, (rem, fit)):
          Empty.absurd(Walked(False{}, grammar, s, Spec.Leaf{k0} <> ts, index, rpath, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit))
    case Con{Spec.Sym{Spec.Terminal{+t}}, +rest}:
      match ready:
        case (seen0, (rem0, fit0)):
          +seen = {seen0 : {Check.descSeen(Gll.Desc{index, rpath, dot, ctx, pos}, s) == True{} : Bool}}
          +rem = {rem0 : {dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Sym{Spec.Terminal{t}} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Leaf{k0} <> ts, grammar, Spec.Sym{Spec.Terminal{t}} <> rest) == True{} : Bool}}
          +itemEq = drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Sym{Spec.Terminal{t}}, rest, rem)
          +restEq = drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Sym{Spec.Terminal{t}}, rest, rem)
          leaf_case(grammar, input, s, closedOk, index, rpath, prefix, dot, ctx, pos, k0, ts, t, rest, pEq, sp, seen, itemEq, restEq, fit, ihTs)
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (seen0, (rem0, fit0)):
          Empty.absurd(Walked(False{}, grammar, s, Spec.Leaf{k0} <> ts, index, rpath, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (seen0, (rem0, fit0)):
          Empty.absurd(Walked(False{}, grammar, s, Spec.Leaf{k0} <> ts, index, rpath, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (seen0, (rem0, fit0)):
          Empty.absurd(Walked(False{}, grammar, s, Spec.Leaf{k0} <> ts, index, rpath, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (seen0, (rem0, fit0)):
          Empty.absurd(Walked(False{}, grammar, s, Spec.Leaf{k0} <> ts, index, rpath, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (seen0, (rem0, fit0)):
          Empty.absurd(Walked(False{}, grammar, s, Spec.Leaf{k0} <> ts, index, rpath, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (seen0, (rem0, fit0)):
          Empty.absurd(Walked(False{}, grammar, s, Spec.Leaf{k0} <> ts, index, rpath, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))

law node_disp:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for +closedOk: {Check.closed(grammar, input, s) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +q: Nat
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: Spells(Spec.Node{q, ch} <> ts, input, pos)
  for ready: Ready(False{}, grammar, input, s, Spec.Node{q, ch} <> ts, index, rpath, dot, ctx, pos, items, kind, alts)
  for ihCh: WalkIH(grammar, input, s, ch)
  for ihTs: WalkIH(grammar, input, s, ts)
  Walked(False{}, grammar, s, Spec.Node{q, ch} <> ts, index, rpath, prefix, dot, ctx, pos)

def node_disp(items, grammar, input, s, closedOk, index, rpath, prefix, dot, ctx, pos, kind, alts, q, ch, ts, pEq, sp, ready, ihCh, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (seen, (rem, fit)):
          Empty.absurd(Walked(False{}, grammar, s, Spec.Node{q, ch} <> ts, index, rpath, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit))
    case Con{Spec.Sym{Spec.Terminal{+t}}, +rest}:
      match ready:
        case (seen0, (rem0, fit0)):
          Empty.absurd(Walked(False{}, grammar, s, Spec.Node{q, ch} <> ts, index, rpath, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (seen0, (rem0, fit0)):
          +seen = {seen0 : {Check.descSeen(Gll.Desc{index, rpath, dot, ctx, pos}, s) == True{} : Bool}}
          +rem = {rem0 : {dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Sym{Spec.Nonterminal{x}} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Node{q, ch} <> ts, grammar, Spec.Sym{Spec.Nonterminal{x}} <> rest) == True{} : Bool}}
          +itemEq = drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Sym{Spec.Nonterminal{x}}, rest, rem)
          +restEq = drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Sym{Spec.Nonterminal{x}}, rest, rem)
          node_case(grammar, input, s, closedOk, index, rpath, prefix, dot, ctx, pos, q, ch, ts, x, rest, pEq, sp, seen, itemEq, restEq, fit, ihCh, ihTs)
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (seen0, (rem0, fit0)):
          Empty.absurd(Walked(False{}, grammar, s, Spec.Node{q, ch} <> ts, index, rpath, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (seen0, (rem0, fit0)):
          Empty.absurd(Walked(False{}, grammar, s, Spec.Node{q, ch} <> ts, index, rpath, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (seen0, (rem0, fit0)):
          Empty.absurd(Walked(False{}, grammar, s, Spec.Node{q, ch} <> ts, index, rpath, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (seen0, (rem0, fit0)):
          Empty.absurd(Walked(False{}, grammar, s, Spec.Node{q, ch} <> ts, index, rpath, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (seen0, (rem0, fit0)):
          Empty.absurd(Walked(False{}, grammar, s, Spec.Node{q, ch} <> ts, index, rpath, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))

law pick_disp:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for +closedOk: {Check.closed(grammar, input, s) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: Spells(Spec.Pick{a, ch} <> ts, input, pos)
  for ready: Ready(False{}, grammar, input, s, Spec.Pick{a, ch} <> ts, index, rpath, dot, ctx, pos, items, kind, alts)
  for ihCh: WalkIH(grammar, input, s, ch)
  for ihTs: WalkIH(grammar, input, s, ts)
  Walked(False{}, grammar, s, Spec.Pick{a, ch} <> ts, index, rpath, prefix, dot, ctx, pos)

def pick_disp(items, grammar, input, s, closedOk, index, rpath, prefix, dot, ctx, pos, kind, alts, a, ch, ts, pEq, sp, ready, ihCh, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (seen, (rem, fit)):
          Empty.absurd(Walked(False{}, grammar, s, Spec.Pick{a, ch} <> ts, index, rpath, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit))
    case Con{Spec.Sym{Spec.Terminal{+t}}, +rest}:
      match ready:
        case (seen0, (rem0, fit0)):
          Empty.absurd(Walked(False{}, grammar, s, Spec.Pick{a, ch} <> ts, index, rpath, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (seen0, (rem0, fit0)):
          Empty.absurd(Walked(False{}, grammar, s, Spec.Pick{a, ch} <> ts, index, rpath, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (seen0, (rem0, fit0)):
          +seen = {seen0 : {Check.descSeen(Gll.Desc{index, rpath, dot, ctx, pos}, s) == True{} : Bool}}
          +rem = {rem0 : {dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Group{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Spec.Brack{Spec.Group{}, balts} <> rest) == True{} : Bool}}
          +itemEq = drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Group{}, balts}, rest, rem)
          +restEq = drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Group{}, balts}, rest, rem)
          +hOk = Lemma.and_true_left(Bool.and(Spec.isAlt(balts, a), Spec.fits(ch, grammar, Spec.altOf(balts, a))), Spec.fits(ts, grammar, rest), fit)
          pick_case(grammar, input, s, closedOk, index, rpath, prefix, dot, ctx, pos, a, ch, ts, Spec.Group{}, balts, rest, pEq, sp, seen, itemEq, restEq,
            Lemma.and_true_left(Spec.isAlt(balts, a), Spec.fits(ch, grammar, Spec.altOf(balts, a)), hOk),
            Lemma.and_true_right_side(Spec.isAlt(balts, a), Spec.fits(ch, grammar, Spec.altOf(balts, a)), hOk),
            Lemma.and_true_right_side(Bool.and(Spec.isAlt(balts, a), Spec.fits(ch, grammar, Spec.altOf(balts, a))), Spec.fits(ts, grammar, rest), fit), ihCh, ihTs)
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (seen0, (rem0, fit0)):
          +seen = {seen0 : {Check.descSeen(Gll.Desc{index, rpath, dot, ctx, pos}, s) == True{} : Bool}}
          +rem = {rem0 : {dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Optional{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Spec.Brack{Spec.Optional{}, balts} <> rest) == True{} : Bool}}
          +itemEq = drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Optional{}, balts}, rest, rem)
          +restEq = drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Optional{}, balts}, rest, rem)
          +okR = Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}])
          +hOk = Lemma.and_true_left(Bool.and(Bool.and(okR, Spec.isAlt(balts, a)), Spec.fits(ch, grammar, Spec.altOf(balts, a))), Spec.fits(ts, grammar, rest), fit)
          +altOk = Lemma.and_true_left(Bool.and(okR, Spec.isAlt(balts, a)), Spec.fits(ch, grammar, Spec.altOf(balts, a)), hOk)
          pick_case(grammar, input, s, closedOk, index, rpath, prefix, dot, ctx, pos, a, ch, ts, Spec.Optional{}, balts, rest, pEq, sp, seen, itemEq, restEq,
            Lemma.and_true_right_side(okR, Spec.isAlt(balts, a), altOk),
            Lemma.and_true_right_side(Bool.and(okR, Spec.isAlt(balts, a)), Spec.fits(ch, grammar, Spec.altOf(balts, a)), hOk),
            Lemma.and_true_right_side(Bool.and(Bool.and(okR, Spec.isAlt(balts, a)), Spec.fits(ch, grammar, Spec.altOf(balts, a))), Spec.fits(ts, grammar, rest), fit), ihCh, ihTs)
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (seen0, (rem0, fit0)):
          Empty.absurd(Walked(False{}, grammar, s, Spec.Pick{a, ch} <> ts, index, rpath, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (seen0, (rem0, fit0)):
          Empty.absurd(Walked(False{}, grammar, s, Spec.Pick{a, ch} <> ts, index, rpath, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (seen0, (rem0, fit0)):
          Empty.absurd(Walked(False{}, grammar, s, Spec.Pick{a, ch} <> ts, index, rpath, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))

law skip_disp:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for +closedOk: {Check.closed(grammar, input, s) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: Spells(Spec.Skip{} <> ts, input, pos)
  for ready: Ready(False{}, grammar, input, s, Spec.Skip{} <> ts, index, rpath, dot, ctx, pos, items, kind, alts)
  for ihTs: WalkIH(grammar, input, s, ts)
  Walked(False{}, grammar, s, Spec.Skip{} <> ts, index, rpath, prefix, dot, ctx, pos)

def skip_disp(items, grammar, input, s, closedOk, index, rpath, prefix, dot, ctx, pos, kind, alts, ts, pEq, sp, ready, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (seen, (rem, fit)):
          Empty.absurd(Walked(False{}, grammar, s, Spec.Skip{} <> ts, index, rpath, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit))
    case Con{Spec.Sym{Spec.Terminal{+t}}, +rest}:
      match ready:
        case (seen0, (rem0, fit0)):
          Empty.absurd(Walked(False{}, grammar, s, Spec.Skip{} <> ts, index, rpath, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (seen0, (rem0, fit0)):
          Empty.absurd(Walked(False{}, grammar, s, Spec.Skip{} <> ts, index, rpath, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (seen0, (rem0, fit0)):
          Empty.absurd(Walked(False{}, grammar, s, Spec.Skip{} <> ts, index, rpath, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (seen0, (rem0, fit0)):
          +seen = {seen0 : {Check.descSeen(Gll.Desc{index, rpath, dot, ctx, pos}, s) == True{} : Bool}}
          +rem = {rem0 : {dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Optional{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Skip{} <> ts, grammar, Spec.Brack{Spec.Optional{}, balts} <> rest) == True{} : Bool}}
          +itemEq = drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Optional{}, balts}, rest, rem)
          +restEq = drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Optional{}, balts}, rest, rem)
          skip_case(grammar, input, s, closedOk, index, rpath, prefix, dot, ctx, pos, ts, balts, rest, pEq, sp, seen, itemEq, restEq, fit, ihTs)
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (seen0, (rem0, fit0)):
          Empty.absurd(Walked(False{}, grammar, s, Spec.Skip{} <> ts, index, rpath, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (seen0, (rem0, fit0)):
          Empty.absurd(Walked(False{}, grammar, s, Spec.Skip{} <> ts, index, rpath, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (seen0, (rem0, fit0)):
          +seen = {seen0 : {Check.descSeen(Gll.Desc{index, rpath, dot, ctx, pos}, s) == True{} : Bool}}
          +rem = {rem0 : {dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Eps{} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Skip{} <> ts, grammar, Spec.Eps{} <> rest) == True{} : Bool}}
          +itemEq = drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Eps{}, rest, rem)
          +restEq = drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Eps{}, rest, rem)
          eps_case(grammar, input, s, closedOk, index, rpath, prefix, dot, ctx, pos, ts, rest, pEq, sp, seen, itemEq, restEq, fit, ihTs)

law loop0_disp:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for +closedOk: {Check.closed(grammar, input, s) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: Spells(Spec.Loop{[]} <> ts, input, pos)
  for ready: Ready(False{}, grammar, input, s, Spec.Loop{[]} <> ts, index, rpath, dot, ctx, pos, items, kind, alts)
  for ihTs: WalkIH(grammar, input, s, ts)
  Walked(False{}, grammar, s, Spec.Loop{[]} <> ts, index, rpath, prefix, dot, ctx, pos)

def loop0_disp(items, grammar, input, s, closedOk, index, rpath, prefix, dot, ctx, pos, kind, alts, ts, pEq, sp, ready, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (seen, (rem, fit)):
          Empty.absurd(Walked(False{}, grammar, s, Spec.Loop{[]} <> ts, index, rpath, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit))
    case Con{Spec.Sym{Spec.Terminal{+t}}, +rest}:
      match ready:
        case (seen0, (rem0, fit0)):
          Empty.absurd(Walked(False{}, grammar, s, Spec.Loop{[]} <> ts, index, rpath, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (seen0, (rem0, fit0)):
          Empty.absurd(Walked(False{}, grammar, s, Spec.Loop{[]} <> ts, index, rpath, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (seen0, (rem0, fit0)):
          Empty.absurd(Walked(False{}, grammar, s, Spec.Loop{[]} <> ts, index, rpath, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (seen0, (rem0, fit0)):
          Empty.absurd(Walked(False{}, grammar, s, Spec.Loop{[]} <> ts, index, rpath, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (seen0, (rem0, fit0)):
          +seen = {seen0 : {Check.descSeen(Gll.Desc{index, rpath, dot, ctx, pos}, s) == True{} : Bool}}
          +rem = {rem0 : {dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Closure{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Loop{[]} <> ts, grammar, Spec.Brack{Spec.Closure{}, balts} <> rest) == True{} : Bool}}
          +itemEq = drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Closure{}, balts}, rest, rem)
          +restEq = drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Closure{}, balts}, rest, rem)
          empty_loop_case(grammar, input, s, closedOk, index, rpath, prefix, dot, ctx, pos, ts, balts, rest, pEq, sp, seen, itemEq, restEq, fit, ihTs)
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (seen0, (rem0, fit0)):
          Empty.absurd(Walked(False{}, grammar, s, Spec.Loop{[]} <> ts, index, rpath, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (seen0, (rem0, fit0)):
          Empty.absurd(Walked(False{}, grammar, s, Spec.Loop{[]} <> ts, index, rpath, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))

law loop_disp:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for +closedOk: {Check.closed(grammar, input, s) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +r: Spec.Tree
  for +rr: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: Spells(Spec.Loop{r <> rr} <> ts, input, pos)
  for ready: Ready(False{}, grammar, input, s, Spec.Loop{r <> rr} <> ts, index, rpath, dot, ctx, pos, items, kind, alts)
  for ihRs: WalkIH(grammar, input, s, r <> rr)
  for ihTs: WalkIH(grammar, input, s, ts)
  Walked(False{}, grammar, s, Spec.Loop{r <> rr} <> ts, index, rpath, prefix, dot, ctx, pos)

def loop_disp(items, grammar, input, s, closedOk, index, rpath, prefix, dot, ctx, pos, kind, alts, r, rr, ts, pEq, sp, ready, ihRs, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (seen, (rem, fit)):
          Empty.absurd(Walked(False{}, grammar, s, Spec.Loop{r <> rr} <> ts, index, rpath, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit))
    case Con{Spec.Sym{Spec.Terminal{+t}}, +rest}:
      match ready:
        case (seen0, (rem0, fit0)):
          Empty.absurd(Walked(False{}, grammar, s, Spec.Loop{r <> rr} <> ts, index, rpath, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (seen0, (rem0, fit0)):
          Empty.absurd(Walked(False{}, grammar, s, Spec.Loop{r <> rr} <> ts, index, rpath, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (seen0, (rem0, fit0)):
          Empty.absurd(Walked(False{}, grammar, s, Spec.Loop{r <> rr} <> ts, index, rpath, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (seen0, (rem0, fit0)):
          Empty.absurd(Walked(False{}, grammar, s, Spec.Loop{r <> rr} <> ts, index, rpath, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (seen0, (rem0, fit0)):
          +seen = {seen0 : {Check.descSeen(Gll.Desc{index, rpath, dot, ctx, pos}, s) == True{} : Bool}}
          +rem = {rem0 : {dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Closure{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Loop{r <> rr} <> ts, grammar, Spec.Brack{Spec.Closure{}, balts} <> rest) == True{} : Bool}}
          +itemEq = drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Closure{}, balts}, rest, rem)
          +restEq = drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Closure{}, balts}, rest, rem)
          +okR = Spec.roundsOk(Spec.Closure{}, r <> rr)
          +both = Lemma.and_true_left(Bool.and(okR, Spec.fits(r <> rr, grammar, Spec.times(List.length(&2, Spec.Tree, r <> rr), Spec.Brack{Spec.Group{}, balts}))), Spec.fits(ts, grammar, rest), fit)
          loop_case(grammar, input, s, closedOk, index, rpath, prefix, dot, ctx, pos, r, rr, ts, Spec.Closure{}, balts, rest, pEq, sp, seen, itemEq, restEq, {==},
            Lemma.and_true_right_side(okR, Spec.fits(r <> rr, grammar, Spec.times(List.length(&2, Spec.Tree, r <> rr), Spec.Brack{Spec.Group{}, balts})), both),
            Lemma.and_true_right_side(Bool.and(okR, Spec.fits(r <> rr, grammar, Spec.times(List.length(&2, Spec.Tree, r <> rr), Spec.Brack{Spec.Group{}, balts}))), Spec.fits(ts, grammar, rest), fit), ihRs, ihTs)
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (seen0, (rem0, fit0)):
          +seen = {seen0 : {Check.descSeen(Gll.Desc{index, rpath, dot, ctx, pos}, s) == True{} : Bool}}
          +rem = {rem0 : {dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Positive{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Loop{r <> rr} <> ts, grammar, Spec.Brack{Spec.Positive{}, balts} <> rest) == True{} : Bool}}
          +itemEq = drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Positive{}, balts}, rest, rem)
          +restEq = drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Positive{}, balts}, rest, rem)
          +okR = Spec.roundsOk(Spec.Positive{}, r <> rr)
          +both = Lemma.and_true_left(Bool.and(okR, Spec.fits(r <> rr, grammar, Spec.times(List.length(&2, Spec.Tree, r <> rr), Spec.Brack{Spec.Group{}, balts}))), Spec.fits(ts, grammar, rest), fit)
          loop_case(grammar, input, s, closedOk, index, rpath, prefix, dot, ctx, pos, r, rr, ts, Spec.Positive{}, balts, rest, pEq, sp, seen, itemEq, restEq, {==},
            Lemma.and_true_right_side(okR, Spec.fits(r <> rr, grammar, Spec.times(List.length(&2, Spec.Tree, r <> rr), Spec.Brack{Spec.Group{}, balts})), both),
            Lemma.and_true_right_side(Bool.and(okR, Spec.fits(r <> rr, grammar, Spec.times(List.length(&2, Spec.Tree, r <> rr), Spec.Brack{Spec.Group{}, balts}))), Spec.fits(ts, grammar, rest), fit), ihRs, ihTs)
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (seen0, (rem0, fit0)):
          Empty.absurd(Walked(False{}, grammar, s, Spec.Loop{r <> rr} <> ts, index, rpath, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))

law round_disp:
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for +closedOk: {Check.closed(grammar, input, s) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: Spells(Spec.Pick{a, ch} <> rest, input, pos)
  for ready: Ready(True{}, grammar, input, s, Spec.Pick{a, ch} <> rest, index, rpath, dot, ctx, pos, [], kind, alts)
  for ihCh: WalkIH(grammar, input, s, ch)
  for ihRest: WalkIH(grammar, input, s, rest)
  Walked(True{}, grammar, s, Spec.Pick{a, ch} <> rest, index, rpath, prefix, dot, ctx, pos)

def round_disp(a, ch, grammar, input, s, closedOk, index, rpath, prefix, dot, ctx, pos, kind, alts, rest, pEq, sp, ready, ihCh, ihRest):
  match ready:
    case (starts0, (itemEq0, (loopOk0, fit0))):
      +starts = {starts0 : {Check.allSeen(Gll.alternatives(List.length(&2, +List<Spec.Item>, alts), index, rpath, ctx, pos), s) == True{} : Bool}}
      +itemEq = {itemEq0 : {loopItem(grammar, index, rpath) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}}
      +loopOk = {loopOk0 : {Gll.isLoop(kind) == True{} : Bool}}
      +fit = {fit0 : {Spec.fits(Spec.Pick{a, ch} <> rest, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Pick{a, ch} <> rest), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}}
      +h = Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)))
      +R = Spec.fits(rest, grammar, Spec.times(List.length(&2, Spec.Tree, rest), Spec.Brack{Spec.Group{}, alts}))
      +hOk = Lemma.and_true_left(h, R, fit)
      round_case(rpath, grammar, input, s, closedOk, index, prefix, dot, ctx, pos, a, ch, rest, kind, alts, pEq, sp, starts, itemEq, loopOk,
        Lemma.and_true_left(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hOk),
        Lemma.and_true_right_side(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hOk),
        Lemma.and_true_right_side(h, R, fit), ihCh, ihRest)

law seq_nil:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for +closedOk: {Check.closed(grammar, input, s) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for ready: Ready(False{}, grammar, input, s, [], index, rpath, dot, ctx, pos, items, kind, alts)
  Walked(False{}, grammar, s, [], index, rpath, prefix, dot, ctx, pos)

def seq_nil(items, grammar, input, s, closedOk, index, rpath, prefix, dot, ctx, pos, kind, alts, pEq, ready):
  match items:
    case Nil{}:
      match ready:
        case (seen, (rem, fit)):
          nil_seq(dot, grammar, input, s, closedOk, index, rpath, prefix, ctx, pos, pEq, seen, drop_end(dot, Gll.seqAt(grammar, index, rpath), rem))
    case Con{it, rest}:
      match ready:
        case (seen, (rem, fit)):
          Empty.absurd(Walked(False{}, grammar, s, [], index, rpath, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit))

# Every step of a forest walked from a seen descriptor (or from a loop's starts) is in a
# closed state, and the sequence (or the loop) ends where the forest ends.
law walk_closed:
  for forest: +List<Spec.Tree>
  for rounds: Bool
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for +closedOk: {Check.closed(grammar, input, s) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +items: +List<Spec.Item>
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: Spells(forest, input, pos)
  for ready: Ready(rounds, grammar, input, s, forest, index, rpath, dot, ctx, pos, items, kind, alts)
  Walked(rounds, grammar, s, forest, index, rpath, prefix, dot, ctx, pos)

def walk_closed(forest, rounds, grammar, input, s, closedOk, index, rpath, prefix, dot, ctx, pos, items, kind, alts, pEq, sp, ready):
  match forest rounds:
    case Nil{} False{}:
      seq_nil(items, grammar, input, s, closedOk, index, rpath, prefix, dot, ctx, pos, kind, alts, pEq, ready)
    case Nil{} True{}:
      ({==}, {==})
    case Con{Spec.Leaf{+k0}, +ts} False{}:
      leaf_disp(items, grammar, input, s, closedOk, index, rpath, prefix, dot, ctx, pos, kind, alts, k0, ts, pEq, sp, ready, (ri => ix => rx => px => dx => cx => qx => its => kx => ax => pe => spx => rd => walk_closed(ts, ri, grammar, input, s, closedOk, ix, rx, px, dx, cx, qx, its, kx, ax, pe, spx, rd)))
    case Con{Spec.Node{+q, +ch}, +ts} False{}:
      node_disp(items, grammar, input, s, closedOk, index, rpath, prefix, dot, ctx, pos, kind, alts, q, ch, ts, pEq, sp, ready, (ri => ix => rx => px => dx => cx => qx => its => kx => ax => pe => spx => rd => walk_closed(ch, ri, grammar, input, s, closedOk, ix, rx, px, dx, cx, qx, its, kx, ax, pe, spx, rd)), (ri => ix => rx => px => dx => cx => qx => its => kx => ax => pe => spx => rd => walk_closed(ts, ri, grammar, input, s, closedOk, ix, rx, px, dx, cx, qx, its, kx, ax, pe, spx, rd)))
    case Con{Spec.Pick{+a, +ch}, +ts} False{}:
      pick_disp(items, grammar, input, s, closedOk, index, rpath, prefix, dot, ctx, pos, kind, alts, a, ch, ts, pEq, sp, ready, (ri => ix => rx => px => dx => cx => qx => its => kx => ax => pe => spx => rd => walk_closed(ch, ri, grammar, input, s, closedOk, ix, rx, px, dx, cx, qx, its, kx, ax, pe, spx, rd)), (ri => ix => rx => px => dx => cx => qx => its => kx => ax => pe => spx => rd => walk_closed(ts, ri, grammar, input, s, closedOk, ix, rx, px, dx, cx, qx, its, kx, ax, pe, spx, rd)))
    case Con{Spec.Skip{}, +ts} False{}:
      skip_disp(items, grammar, input, s, closedOk, index, rpath, prefix, dot, ctx, pos, kind, alts, ts, pEq, sp, ready, (ri => ix => rx => px => dx => cx => qx => its => kx => ax => pe => spx => rd => walk_closed(ts, ri, grammar, input, s, closedOk, ix, rx, px, dx, cx, qx, its, kx, ax, pe, spx, rd)))
    case Con{Spec.Loop{Nil{}}, +ts} False{}:
      loop0_disp(items, grammar, input, s, closedOk, index, rpath, prefix, dot, ctx, pos, kind, alts, ts, pEq, sp, ready, (ri => ix => rx => px => dx => cx => qx => its => kx => ax => pe => spx => rd => walk_closed(ts, ri, grammar, input, s, closedOk, ix, rx, px, dx, cx, qx, its, kx, ax, pe, spx, rd)))
    case Con{Spec.Loop{Con{+r, +rr}}, +ts} False{}:
      loop_disp(items, grammar, input, s, closedOk, index, rpath, prefix, dot, ctx, pos, kind, alts, r, rr, ts, pEq, sp, ready, (ri => ix => rx => px => dx => cx => qx => its => kx => ax => pe => spx => rd => walk_closed(r <> rr, ri, grammar, input, s, closedOk, ix, rx, px, dx, cx, qx, its, kx, ax, pe, spx, rd)), (ri => ix => rx => px => dx => cx => qx => its => kx => ax => pe => spx => rd => walk_closed(ts, ri, grammar, input, s, closedOk, ix, rx, px, dx, cx, qx, its, kx, ax, pe, spx, rd)))
    case Con{Spec.Pick{+a, +ch}, +rest} True{}:
      round_disp(a, ch, grammar, input, s, closedOk, index, rpath, prefix, dot, ctx, pos, kind, alts, rest, pEq, sp, ready, (ri => ix => rx => px => dx => cx => qx => its => kx => ax => pe => spx => rd => walk_closed(ch, ri, grammar, input, s, closedOk, ix, rx, px, dx, cx, qx, its, kx, ax, pe, spx, rd)), (ri => ix => rx => px => dx => cx => qx => its => kx => ax => pe => spx => rd => walk_closed(rest, ri, grammar, input, s, closedOk, ix, rx, px, dx, cx, qx, its, kx, ax, pe, spx, rd)))
    case Con{Spec.Leaf{k0}, rest} True{}:
      match ready:
        case (st, (ie, (lo, fit))):
          Empty.absurd(Walked(True{}, grammar, s, Spec.Leaf{k0} <> rest, index, rpath, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit))
    case Con{Spec.Node{q, ch}, rest} True{}:
      match ready:
        case (st, (ie, (lo, fit))):
          Empty.absurd(Walked(True{}, grammar, s, Spec.Node{q, ch} <> rest, index, rpath, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit))
    case Con{Spec.Skip{}, rest} True{}:
      match ready:
        case (st, (ie, (lo, fit))):
          Empty.absurd(Walked(True{}, grammar, s, Spec.Skip{} <> rest, index, rpath, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit))
    case Con{Spec.Loop{rs}, rest} True{}:
      match ready:
        case (st, (ie, (lo, fit))):
          Empty.absurd(Walked(True{}, grammar, s, Spec.Loop{rs} <> rest, index, rpath, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit))

# ======== THE THEOREM ========

# The leaves of the root's children are the input, read from position 0.
law root_spells:
  for +input: +List<Nat>
  for +q: Nat
  for +ch: +List<Spec.Tree>
  for spelled: {Spec.leaves([Spec.Node{q, ch}]) == input : +List<Nat>}
  Spells(ch, input, 0n)

def root_spells(input, q, ch, spelled):
  +lch = Spec.leaves(ch)
  +same = Equal.trans(+List<Nat>, lch, List.append(&2, Nat, lch, []), input, Equal.sym(+List<Nat>, List.append(&2, Nat, lch, []), lch, Lemma.append_nil_right(lch)), spelled)
  Equal.trans(+List<Nat>, lch, input, Lemma.takeN(List.length(&2, Nat, lch), input), same,
    Equal.trans(+List<Nat>, input, Lemma.takeN(List.length(&2, Nat, input), input), Lemma.takeN(List.length(&2, Nat, lch), input),
      Equal.sym(+List<Nat>, Lemma.takeN(List.length(&2, Nat, input), input), input, Lemma.take_length(input)),
      Equal.cong(+List<Nat>, +List<Nat>, v => Lemma.takeN(List.length(&2, Nat, v), input), input, lch, Equal.sym(+List<Nat>, lch, input, same))))

law root_done:
  for +grammar: +List<Spec.Production>
  for +s: Gll.GState
  for +q: Nat
  for +ch: +List<Spec.Tree>
  for w: Walked(False{}, grammar, s, ch, q, [], [], 0n, 0n, 0n)
  {Spec.allIn(Spec.steps(Spec.Node{q, ch}, 0n), Check.stepsOf(s)) == True{} : Bool}

def root_done(grammar, s, q, ch, w):
  match w:
    case (steps, pop):
      steps

# A closed state with the start symbol's cluster at 0 holds every step of every parse tree.
law closed_complete:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +s: Gll.GState
  for +closedOk: {Check.closed(grammar, input, s) == True{} : Bool}
  for +rootIn: {Check.clusterIn(Gll.CKey{Gll.TNt{start}, 0n}, s) == True{} : Bool}
  for tree: Spec.Tree
  for fitting: {Spec.fits([tree], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for spelled: {Spec.leaves([tree]) == input : +List<Nat>}
  {Spec.allIn(Spec.steps(tree, 0n), Check.stepsOf(s)) == True{} : Bool}

def closed_complete(grammar, start, input, s, closedOk, rootIn, tree, fitting, spelled):
  match tree:
    case Spec.Leaf{k}:
      Empty.absurd({Spec.allIn(Spec.steps(Spec.Leaf{k}, 0n), Check.stepsOf(s)) == True{} : Bool}, Lemma.false_is_not_true(fitting))
    case Spec.Node{+q, +ch}:
      +both = fitting
      +h = Bool.and(Spec.lhsIs(grammar, q, start), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)))
      +hOk = Lemma.and_true_left(h, True{}, both)
      lhsOk = Lemma.and_true_left(Spec.lhsIs(grammar, q, start), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hOk)
      fitCh = Lemma.and_true_right_side(Spec.lhsIs(grammar, q, start), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hOk)
      seeds = cluster_ok(grammar, input, s, closedOk, Gll.CKey{Gll.TNt{start}, 0n}, rootIn)
      startSeen = productions_seen(grammar, start, 0n, 0n, q, s, lhsOk, seeds)
      root_done(grammar, s, q, ch,
        walk_closed(ch, False{}, grammar, input, s, closedOk, q, [], [], 0n, 0n, 0n, Spec.rhsOf(grammar, q), Spec.Group{}, [], {==}, root_spells(input, q, ch, spelled), (startSeen, ({==}, fitCh))))
    case Spec.Pick{a, ch}:
      Empty.absurd({Spec.allIn(Spec.steps(Spec.Pick{a, ch}, 0n), Check.stepsOf(s)) == True{} : Bool}, Lemma.false_is_not_true(fitting))
    case Spec.Skip{}:
      Empty.absurd({Spec.allIn(Spec.steps(Spec.Skip{}, 0n), Check.stepsOf(s)) == True{} : Bool}, Lemma.false_is_not_true(fitting))
    case Spec.Loop{rs}:
      Empty.absurd({Spec.allIn(Spec.steps(Spec.Loop{rs}, 0n), Check.stepsOf(s)) == True{} : Bool}, Lemma.false_is_not_true(fitting))
# ======== THE CHECKED PARSER MISSES NOTHING ========

law path_eq_sound:
  for xs: +List<Nat>
  for ys: +List<Nat>
  for e: {Spec.pathEq(xs, ys) == True{} : Bool}
  {xs == ys : +List<Nat>}

def path_eq_sound(xs, ys, e):
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, yr}:
      Empty.absurd({[] == y <> yr : +List<Nat>}, Lemma.false_is_not_true(e))
    case Con{x, xr} Nil{}:
      Empty.absurd({x <> xr == [] : +List<Nat>}, Lemma.false_is_not_true(e))
    case Con{+x, +xr} Con{+y, +yr}:
      +both = e
      ex = Lemma.nat_eq_sound(x, y, Lemma.and_true_left(Nat.is_eq(x, y), Spec.pathEq(xr, yr), both))
      er = path_eq_sound(xr, yr, Lemma.and_true_right_side(Nat.is_eq(x, y), Spec.pathEq(xr, yr), both))
      %ex : {x <> xr == _ <> yr : +List<Nat>}
      %er : {x <> xr == x <> _ : +List<Nat>}
      {==}

law ebnf_bsr_eq_sound:
  for +p: Nat
  for +path: +List<Nat>
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for +p2: Nat
  for +path2: +List<Nat>
  for +i2: Nat
  for +k2: Nat
  for +j2: Nat
  for same: {Bool.and(Nat.is_eq(p, p2), Bool.and(Spec.pathEq(path, path2), Bool.and(Nat.is_eq(i, i2), Bool.and(Nat.is_eq(k, k2), Nat.is_eq(j, j2))))) == True{} : Bool}
  {Spec.Bsr{Spec.Slot{p, path}, i, k, j} == Spec.Bsr{Spec.Slot{p2, path2}, i2, k2, j2} : Spec.Bsr}

def ebnf_bsr_eq_sound(p, path, i, k, j, p2, path2, i2, k2, j2, same):
  +s0 = same
  +s1 = Lemma.and_true_right_side(Nat.is_eq(p, p2), Bool.and(Spec.pathEq(path, path2), Bool.and(Nat.is_eq(i, i2), Bool.and(Nat.is_eq(k, k2), Nat.is_eq(j, j2)))), s0)
  +s2 = Lemma.and_true_right_side(Spec.pathEq(path, path2), Bool.and(Nat.is_eq(i, i2), Bool.and(Nat.is_eq(k, k2), Nat.is_eq(j, j2))), s1)
  +s3 = Lemma.and_true_right_side(Nat.is_eq(i, i2), Bool.and(Nat.is_eq(k, k2), Nat.is_eq(j, j2)), s2)
  ep = Lemma.nat_eq_sound(p, p2, Lemma.and_true_left(Nat.is_eq(p, p2), Bool.and(Spec.pathEq(path, path2), Bool.and(Nat.is_eq(i, i2), Bool.and(Nat.is_eq(k, k2), Nat.is_eq(j, j2)))), s0))
  epath = path_eq_sound(path, path2, Lemma.and_true_left(Spec.pathEq(path, path2), Bool.and(Nat.is_eq(i, i2), Bool.and(Nat.is_eq(k, k2), Nat.is_eq(j, j2))), s1))
  ei = Lemma.nat_eq_sound(i, i2, Lemma.and_true_left(Nat.is_eq(i, i2), Bool.and(Nat.is_eq(k, k2), Nat.is_eq(j, j2)), s2))
  ek = Lemma.nat_eq_sound(k, k2, Lemma.and_true_left(Nat.is_eq(k, k2), Nat.is_eq(j, j2), s3))
  ej = Lemma.nat_eq_sound(j, j2, Lemma.and_true_right_side(Nat.is_eq(k, k2), Nat.is_eq(j, j2), s3))
  %ep : {Spec.Bsr{Spec.Slot{p, path}, i, k, j} == Spec.Bsr{Spec.Slot{_, path2}, i2, k2, j2} : Spec.Bsr}
  %epath : {Spec.Bsr{Spec.Slot{p, path}, i, k, j} == Spec.Bsr{Spec.Slot{p, _}, i2, k2, j2} : Spec.Bsr}
  %ei : {Spec.Bsr{Spec.Slot{p, path}, i, k, j} == Spec.Bsr{Spec.Slot{p, path}, _, k2, j2} : Spec.Bsr}
  %ek : {Spec.Bsr{Spec.Slot{p, path}, i, k, j} == Spec.Bsr{Spec.Slot{p, path}, i, _, j2} : Spec.Bsr}
  %ej : {Spec.Bsr{Spec.Slot{p, path}, i, k, j} == Spec.Bsr{Spec.Slot{p, path}, i, k, _} : Spec.Bsr}
  {==}

law member_pick:
  for +element: Spec.Bsr
  for +x: Spec.Bsr
  for -rest: +List<Spec.Bsr>
  for +set: +List<Spec.Bsr>
  for cases: Either<{element == x : Spec.Bsr}, {Spec.bsrMember(element, rest) == True{} : Bool}>
  for +inX: {Spec.bsrMember(x, set) == True{} : Bool}
  for searchRest: {Spec.bsrMember(element, rest) == True{} : Bool} -> {Spec.bsrMember(element, set) == True{} : Bool}
  {Spec.bsrMember(element, set) == True{} : Bool}

def member_pick(element, x, rest, set, cases, inX, searchRest):
  match cases:
    case Inl{same}:
      Equal.trans(Bool, Spec.bsrMember(element, set), Spec.bsrMember(x, set), True{}, Equal.cong(Spec.Bsr, Bool, v => Spec.bsrMember(v, set), element, x, same), inX)
    case Inr{later}:
      searchRest(later)

law ebnf_cases_pick:
  for +p: Nat
  for +path: +List<Nat>
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for +p2: Nat
  for +path2: +List<Nat>
  for +i2: Nat
  for +k2: Nat
  for +j2: Nat
  for -rest: +List<Spec.Bsr>
  for cases: Either<{Bool.and(Nat.is_eq(p, p2), Bool.and(Spec.pathEq(path, path2), Bool.and(Nat.is_eq(i, i2), Bool.and(Nat.is_eq(k, k2), Nat.is_eq(j, j2))))) == True{} : Bool}, {Spec.bsrMember(Spec.Bsr{Spec.Slot{p, path}, i, k, j}, rest) == True{} : Bool}>
  Either<{Spec.Bsr{Spec.Slot{p, path}, i, k, j} == Spec.Bsr{Spec.Slot{p2, path2}, i2, k2, j2} : Spec.Bsr}, {Spec.bsrMember(Spec.Bsr{Spec.Slot{p, path}, i, k, j}, rest) == True{} : Bool}>

def ebnf_cases_pick(p, path, i, k, j, p2, path2, i2, k2, j2, rest, cases):
  match cases:
    case Inl{same}:
      Inl{ebnf_bsr_eq_sound(p, path, i, k, j, p2, path2, i2, k2, j2, same)}
    case Inr{later}:
      Inr{later}

law ebnf_member_cases:
  for element: Spec.Bsr
  for x: Spec.Bsr
  for -rest: +List<Spec.Bsr>
  for m: {Spec.bsrMember(element, x <> rest) == True{} : Bool}
  Either<{element == x : Spec.Bsr}, {Spec.bsrMember(element, rest) == True{} : Bool}>

def ebnf_member_cases(element, x, rest, m):
  match element x:
    case Spec.Bsr{Spec.Slot{+p, +path}, +i, +k, +j} Spec.Bsr{Spec.Slot{+p2, +path2}, +i2, +k2, +j2}:
      ebnf_cases_pick(p, path, i, k, j, p2, path2, i2, k2, j2, rest,
        Lemma.or_true_cases(Bool.and(Nat.is_eq(p, p2), Bool.and(Spec.pathEq(path, path2), Bool.and(Nat.is_eq(i, i2), Bool.and(Nat.is_eq(k, k2), Nat.is_eq(j, j2))))), Spec.bsrMember(Spec.Bsr{Spec.Slot{p, path}, i, k, j}, rest), m))

law ebnf_not_in_empty:
  for element: Spec.Bsr
  for m: {Spec.bsrMember(element, []) == True{} : Bool}
  Empty

def ebnf_not_in_empty(element, m):
  match element:
    case Spec.Bsr{Spec.Slot{p, path}, i, k, j}:
      Lemma.false_is_not_true(m)

# An element of xs is in every set that holds all of xs.
law ebnf_all_in_member:
  for xs: +List<Spec.Bsr>
  for +set: +List<Spec.Bsr>
  for +element: Spec.Bsr
  for all: {Spec.allIn(xs, set) == True{} : Bool}
  for m: {Spec.bsrMember(element, xs) == True{} : Bool}
  {Spec.bsrMember(element, set) == True{} : Bool}

def ebnf_all_in_member(xs, set, element, all, m):
  match xs:
    case Nil{}:
      Empty.absurd({Spec.bsrMember(element, set) == True{} : Bool}, ebnf_not_in_empty(element, m))
    case Con{+x, +rest}:
      +both = all
      member_pick(element, x, rest, set, ebnf_member_cases(element, x, rest, m),
        Lemma.and_true_left(Spec.bsrMember(x, set), Spec.allIn(rest, set), both),
        later => ebnf_all_in_member(rest, set, element, Lemma.and_true_right_side(Spec.bsrMember(x, set), Spec.allIn(rest, set), both), later))

def stepsOr(m: Maybe<&2, +List<Spec.Bsr>>) -> +List<Spec.Bsr>:
  match m:
    case None{}:
      []
    case Some{xs}:
      xs

def isNothing(m: Maybe<&2, +List<Spec.Bsr>>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{xs}:
      False{}

law check_pick:
  for ok: Bool
  for +s: Gll.GState
  for +set: +List<Spec.Bsr>
  for got: {Check.checkPick(ok, s) == Some{set} : Maybe<&2, +List<Spec.Bsr>>}
  {ok == True{} : Bool} & {Check.stepsOf(s) == set : +List<Spec.Bsr>}

def check_pick(ok, s, set, got):
  match ok:
    case True{}:
      ({==}, Equal.cong(Maybe<&2, +List<Spec.Bsr>>, +List<Spec.Bsr>, v => stepsOr(v), Some{Check.stepsOf(s)}, Some{set}, got))
    case False{}:
      Empty.absurd({False{} == True{} : Bool} & {Check.stepsOf(s) == set : +List<Spec.Bsr>}, Lemma.true_is_not_false(Equal.cong(Maybe<&2, +List<Spec.Bsr>>, Bool, v => isNothing(v), None{}, Some{set}, got)))

law state_done:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +s: Gll.GState
  for +set: +List<Spec.Bsr>
  for facts: {Bool.and(Check.closed(grammar, input, s), Check.clusterIn(Gll.CKey{Gll.TNt{start}, 0n}, s)) == True{} : Bool} & {Check.stepsOf(s) == set : +List<Spec.Bsr>}
  Spec.EveryParseStep(grammar, start, input, set)

def state_done(grammar, start, input, s, set, facts):
  match facts:
    case (ok0, same0):
      +ok = {ok0 : {Bool.and(Check.closed(grammar, input, s), Check.clusterIn(Gll.CKey{Gll.TNt{start}, 0n}, s)) == True{} : Bool}}
      +same = {same0 : {Check.stepsOf(s) == set : +List<Spec.Bsr>}}
      +closedOk = Lemma.and_true_left(Check.closed(grammar, input, s), Check.clusterIn(Gll.CKey{Gll.TNt{start}, 0n}, s), ok)
      +rootIn = Lemma.and_true_right_side(Check.closed(grammar, input, s), Check.clusterIn(Gll.CKey{Gll.TNt{start}, 0n}, s), ok)
      +tree => +element => fitting => spelled => inTree =>
        inS = ebnf_all_in_member(Spec.steps(tree, 0n), Check.stepsOf(s), element, closed_complete(grammar, start, input, s, closedOk, rootIn, tree, fitting, spelled), inTree)
        Equal.trans(Bool, Spec.bsrMember(element, set), Spec.bsrMember(element, Check.stepsOf(s)), True{},
          Equal.cong(+List<Spec.Bsr>, Bool, v => Spec.bsrMember(element, v), set, Check.stepsOf(s), Equal.sym(+List<Spec.Bsr>, Check.stepsOf(s), set, same)), inS)

law state_complete:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +s: Gll.GState
  for +set: +List<Spec.Bsr>
  for got: {Check.checkPick(Bool.and(Check.closed(grammar, input, s), Check.clusterIn(Gll.CKey{Gll.TNt{start}, 0n}, s)), s) == Some{set} : Maybe<&2, +List<Spec.Bsr>>}
  Spec.EveryParseStep(grammar, start, input, set)

def state_complete(grammar, start, input, s, set, got):
  state_done(grammar, start, input, s, set, check_pick(Bool.and(Check.closed(grammar, input, s), Check.clusterIn(Gll.CKey{Gll.TNt{start}, 0n}, s)), s, set, got))
law run_complete:
  for r: Gll.GRun
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for got: {Check.runChecked(r, grammar, start, input) == Some{set} : Maybe<&2, +List<Spec.Bsr>>}
  Spec.EveryParseStep(grammar, start, input, set)

def run_complete(r, grammar, start, input, set, got):
  match r:
    case Gll.GDone{+s}:
      state_complete(grammar, start, input, s, set, got)
    case Gll.OutOfFuel{s}:
      Empty.absurd(Spec.EveryParseStep(grammar, start, input, set), Lemma.true_is_not_false(Equal.cong(Maybe<&2, +List<Spec.Bsr>>, Bool, v => isNothing(v), None{}, Some{set}, got)))

# The law gll_every_parse_step.
def Laws.gll_every_parse_step(fuel, grammar, start, input, set, got):
  run_complete(Gll.parse(fuel, grammar, start, input), grammar, start, input, set, got)

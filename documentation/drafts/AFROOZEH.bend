import Base
import ./SPEC.bend as Spec
import ./GLL.bend as Gll
import ./LEMMAS.bend as Lemma

# AFROOZEH: THE CHECK FOR DUPLICATE RETURN EDGES IS REDUNDANT.
#
# Afroozeh and Izmaylova (Faster, Practical GLL Parsing, 2015, section 4) observe that
# there is at most one call to `create` with the same arguments, so a GSS node's edges
# need no check for duplicates: a call is made only while a descriptor is processed, its
# arguments are fixed by that descriptor, and no descriptor is processed twice. Here that
# argument is made formal for GLL.bend: an engine whose `call` never looks for an existing
# return edge (`callPickFree`) computes exactly the same run as GLL.bend's.
#
# The invariant, between steps: the descriptors still to do are seen, without duplicates;
# and every return edge was added while its origin, the descriptor with the edge's slot
# and the call's position, was processed, so the origin is seen and no longer to do.

# ---- The engine without the check ----

def callPickFree(known: Bool, +pr: Gll.Pred, +grammar: +List<Spec.Production>, +input: +List<Nat>, +key: Gll.CKey, +kc: Nat, +edge: Gll.Edge, +seeds: +List<Gll.Desc>, s: Gll.GState) -> Gll.GState:
  match known s:
    case False{} Gll.GState{seen, todo, cs, rs, ps, ys}:
      Gll.withDescsP(pr, grammar, input, seeds, Gll.GState{seen, todo, key <> cs, Gll.Ret{key, edge} <> rs, ps, ys})
    case True{} Gll.GState{seen, todo, cs, rs, +ps, ys}:
      Gll.resumePops(ps, pr, grammar, input, key, edge, kc, Gll.GState{seen, todo, cs, Gll.Ret{key, edge} <> rs, ps, ys})

def callFree(+pr: Gll.Pred, +grammar: +List<Spec.Production>, +input: +List<Nat>, +target: Gll.Target, +i: Nat, +edge: Gll.Edge, +seeds: +List<Gll.Desc>, s: Gll.GState) -> Gll.GState:
  match s:
    case Gll.GState{seen, todo, +cs, rs, ps, ys}:
      +key = {Gll.CKey{target, i} : Gll.CKey}
      callPickFree(Gll.keyIn(key, cs), pr, grammar, input, key, i, edge, seeds, Gll.GState{seen, todo, cs, rs, ps, ys})

def stepItemFree(item: Maybe<&2, Spec.Item>, +pr: Gll.Pred, +grammar: +List<Spec.Production>, +input: +List<Nat>, +index: Nat, +rpath: +List<Nat>, +dot: Nat, +k: Nat, +i: Nat, s: Gll.GState) -> Gll.GState:
  match item:
    case Some{Spec.Sym{Spec.Terminal{+t}}}:
      Gll.matchToken(Gll.tokenIs(List.get(&2, Nat, input, i), t), pr, grammar, input, index, rpath, dot, k, i, s)
    case Some{Spec.Sym{Spec.Nonterminal{+x}}}:
      callFree(pr, grammar, input, Gll.TNt{x}, i, Gll.Edge{index, rpath, dot, k}, Gll.productionsOf(grammar, x, 0n, i), s)
    case Some{Spec.Brack{+kind, +alts}}:
      Gll.skipIf(Gll.isSkippable(kind), pr, grammar, input, index, rpath, dot, k, i,
        callFree(pr, grammar, input, Gll.TBr{index, dot <> rpath}, i, Gll.Edge{index, rpath, dot, k}, Gll.alternatives(List.length(&2, +List<Spec.Item>, alts), index, dot <> rpath, i, i), s))
    case Some{Spec.Eps{}}:
      Gll.skipIf(True{}, pr, grammar, input, index, rpath, dot, k, i, s)
    case None{}:
      Gll.finish(pr, grammar, input, index, rpath, k, i, Gll.emptyIf(dot, index, rpath, k, i, s))

def stepFree(d: Gll.Desc, +pr: Gll.Pred, +grammar: +List<Spec.Production>, +input: +List<Nat>, s: Gll.GState) -> Gll.GState:
  match d:
    case Gll.Desc{+index, +rpath, +dot, +k, +i}:
      stepItemFree(Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), pr, grammar, input, index, rpath, dot, k, i, s)

def runFree(fuel: Nat, +pr: Gll.Pred, +grammar: +List<Spec.Production>, +input: +List<Nat>, s: Gll.GState) -> Gll.GRun:
  match fuel s:
    case 0n _:
      Gll.OutOfFuel{s}
    case 1n+f Gll.GState{seen, Nil{}, cs, rs, ps, ys}:
      Gll.GDone{Gll.GState{seen, [], cs, rs, ps, ys}}
    case 1n+f Gll.GState{seen, Con{d, rest}, cs, rs, ps, ys}:
      runFree(f, pr, grammar, input, stepFree(d, pr, grammar, input, Gll.GState{seen, rest, cs, rs, ps, ys}))

def parseWithFree(fuel: Nat, +pr: Gll.Pred, +grammar: +List<Spec.Production>, +start: Nat, +input: +List<Nat>) -> Gll.GRun:
  runFree(fuel, pr, grammar, input, Gll.withDescsP(pr, grammar, input, Gll.productionsOf(grammar, start, 0n, 0n), Gll.GState{[], [], [Gll.CKey{Gll.TNt{start}, 0n}], [], [], []}))

# ---- The invariant ----

# The descriptor whose processing adds this return edge: the edge's slot, at the call's position.
def origin(r: Gll.Ret) -> Gll.Desc:
  match r:
    case Gll.Ret{Gll.CKey{t, +i}, Gll.Edge{+index, +rpath, +dot, +k}}:
      Gll.Desc{index, rpath, dot, k, i}

def subB(xs: +List<Gll.Desc>, +ys: +List<Gll.Desc>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, rest}:
      Bool.and(Gll.descIn(x, ys), subB(rest, ys))

def NoDup(xs: +List<Gll.Desc>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{+x, +rest}:
      {Gll.descIn(x, rest) == False{} : Bool} & NoDup(rest)

def retsB(rs: +List<Gll.Ret>, +seen: +List<Gll.Desc>, +todo: +List<Gll.Desc>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Con{+r, rest}:
      Bool.and(Bool.and(Gll.descIn(origin(r), seen), Bool.not(Gll.descIn(origin(r), todo))), retsB(rest, seen, todo))

def Inv(s: Gll.GState) -> Type:
  match s:
    case Gll.GState{+seen, +todo, cs, +rs, ps, ys}:
      {subB(todo, seen) == True{} : Bool} & NoDup(todo) & {retsB(rs, seen, todo) == True{} : Bool}

# ---- Equality of keys and edges (from PROOF_GLL.bend) ----

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

# ---- Small facts about Bool and membership ----

law bool_cases:
  for b: Bool
  Either<{b == True{} : Bool}, {b == False{} : Bool}>

def bool_cases(b):
  match b:
    case True{}:
      Inl{{==}}
    case False{}:
      Inr{{==}}

law both_false:
  for a: Bool
  for -b: Bool
  for ea: {a == False{} : Bool}
  for eb: {b == False{} : Bool}
  {Bool.or(a, b) == False{} : Bool}

def both_false(a, b, ea, eb):
  match a:
    case False{}:
      eb
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, Lemma.true_is_not_false(ea))

law or_false_r:
  for a: Bool
  for -b: Bool
  for e: {Bool.or(a, b) == False{} : Bool}
  {b == False{} : Bool}

def or_false_r(a, b, e):
  match a:
    case False{}:
      e
    case True{}:
      Empty.absurd({b == False{} : Bool}, Lemma.true_is_not_false(e))

law both_ways:
  for -x: Bool
  for t: {x == True{} : Bool}
  for f: {x == False{} : Bool}
  Empty

def both_ways(x, t, f):
  Lemma.true_is_not_false(Equal.trans(Bool, True{}, x, False{}, Equal.sym(Bool, x, True{}, t), f))

law nats_eq_refl:
  for +xs: +List<Nat>
  {Gll.natsEq(xs, xs) == True{} : Bool}

def nats_eq_refl(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Lemma.and_true_intro(Nat.is_eq(x, x), Gll.natsEq(rest, rest), Lemma.nat_eq_refl(x), nats_eq_refl(rest))

law desc_eq_refl:
  for +d: Gll.Desc
  {Gll.descEq(d, d) == True{} : Bool}

def desc_eq_refl(d):
  match d:
    case Gll.Desc{+p, +r, +dt, +k, +i}:
      Lemma.and_true_intro(Nat.is_eq(p, p), Bool.and(Gll.natsEq(r, r), Bool.and(Nat.is_eq(dt, dt), Bool.and(Nat.is_eq(k, k), Nat.is_eq(i, i)))), Lemma.nat_eq_refl(p),
        Lemma.and_true_intro(Gll.natsEq(r, r), Bool.and(Nat.is_eq(dt, dt), Bool.and(Nat.is_eq(k, k), Nat.is_eq(i, i))), nats_eq_refl(r),
          Lemma.and_true_intro(Nat.is_eq(dt, dt), Bool.and(Nat.is_eq(k, k), Nat.is_eq(i, i)), Lemma.nat_eq_refl(dt),
            Lemma.and_true_intro(Nat.is_eq(k, k), Nat.is_eq(i, i), Lemma.nat_eq_refl(k), Lemma.nat_eq_refl(i)))))

law in_head:
  for +d: Gll.Desc
  for +rest: +List<Gll.Desc>
  {Gll.descIn(d, d <> rest) == True{} : Bool}

def in_head(d, rest):
  Lemma.or_true_left_intro(Gll.descEq(d, d), Gll.descIn(d, rest), desc_eq_refl(d))

law in_cons:
  for +x: Gll.Desc
  for +y: Gll.Desc
  for +ys: +List<Gll.Desc>
  for e: {Gll.descIn(x, ys) == True{} : Bool}
  {Gll.descIn(x, y <> ys) == True{} : Bool}

def in_cons(x, y, ys, e):
  Lemma.or_true_right_intro(Gll.descEq(x, y), Gll.descIn(x, ys), e)

law not_in_cons:
  for +x: Gll.Desc
  for +y: Gll.Desc
  for +ys: +List<Gll.Desc>
  for ne: {Gll.descEq(x, y) == False{} : Bool}
  for e: {Gll.descIn(x, ys) == False{} : Bool}
  {Gll.descIn(x, y <> ys) == False{} : Bool}

def not_in_cons(x, y, ys, ne, e):
  both_false(Gll.descEq(x, y), Gll.descIn(x, ys), ne, e)

law not_in_tail:
  for +x: Gll.Desc
  for +y: Gll.Desc
  for +ys: +List<Gll.Desc>
  for e: {Gll.descIn(x, y <> ys) == False{} : Bool}
  {Gll.descIn(x, ys) == False{} : Bool}

def not_in_tail(x, y, ys, e):
  or_false_r(Gll.descEq(x, y), Gll.descIn(x, ys), e)

# A member of xs is a member of every superset ys.
def sub_pick(+x: Gll.Desc, +y: Gll.Desc, +rest: +List<Gll.Desc>, +ys: +List<Gll.Desc>,
             cases: Either<{Gll.descEq(x, y) == True{} : Bool}, {Gll.descIn(x, rest) == True{} : Bool}>,
             hy: {Gll.descIn(y, ys) == True{} : Bool}, later: {Gll.descIn(x, rest) == True{} : Bool} -> {Gll.descIn(x, ys) == True{} : Bool}) -> {Gll.descIn(x, ys) == True{} : Bool}:
  match cases:
    case Inl{same}:
      +eq = desc_eq_sound(x, y, same)
      %Equal.sym(Gll.Desc, x, y, eq) : {Gll.descIn(_, ys) == True{} : Bool}
      hy
    case Inr{there}:
      later(there)

law sub_in:
  for xs: +List<Gll.Desc>
  for +ys: +List<Gll.Desc>
  for +x: Gll.Desc
  for h: {subB(xs, ys) == True{} : Bool}
  for e: {Gll.descIn(x, xs) == True{} : Bool}
  {Gll.descIn(x, ys) == True{} : Bool}

def sub_in(xs, ys, x, h, e):
  match xs:
    case Nil{}:
      Empty.absurd({Gll.descIn(x, ys) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{+y, +rest}:
      +hh = h
      sub_pick(x, y, rest, ys, Lemma.or_true_cases(Gll.descEq(x, y), Gll.descIn(x, rest), e),
        Lemma.and_true_left(Gll.descIn(y, ys), subB(rest, ys), hh),
        there => sub_in(rest, ys, x, Lemma.and_true_right_side(Gll.descIn(y, ys), subB(rest, ys), hh), there))

def out_pick(+x: Gll.Desc, +xs: +List<Gll.Desc>, +ys: +List<Gll.Desc>, cases: Either<{Gll.descIn(x, xs) == True{} : Bool}, {Gll.descIn(x, xs) == False{} : Bool}>,
             h: {subB(xs, ys) == True{} : Bool}, out: {Gll.descIn(x, ys) == False{} : Bool}) -> {Gll.descIn(x, xs) == False{} : Bool}:
  match cases:
    case Inl{t}:
      Empty.absurd({Gll.descIn(x, xs) == False{} : Bool}, both_ways(Gll.descIn(x, ys), sub_in(xs, ys, x, h, t), out))
    case Inr{f}:
      f

# What is not in ys is not in any subset of ys.
law sub_out:
  for +xs: +List<Gll.Desc>
  for +ys: +List<Gll.Desc>
  for +x: Gll.Desc
  for h: {subB(xs, ys) == True{} : Bool}
  for out: {Gll.descIn(x, ys) == False{} : Bool}
  {Gll.descIn(x, xs) == False{} : Bool}

def sub_out(xs, ys, x, h, out):
  out_pick(x, xs, ys, bool_cases(Gll.descIn(x, xs)), h, out)

law sub_cons:
  for xs: +List<Gll.Desc>
  for +ys: +List<Gll.Desc>
  for +y: Gll.Desc
  for h: {subB(xs, ys) == True{} : Bool}
  {subB(xs, y <> ys) == True{} : Bool}

def sub_cons(xs, ys, y, h):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +hh = h
      Lemma.and_true_intro(Gll.descIn(x, y <> ys), subB(rest, y <> ys),
        in_cons(x, y, ys, Lemma.and_true_left(Gll.descIn(x, ys), subB(rest, ys), hh)),
        sub_cons(rest, ys, y, Lemma.and_true_right_side(Gll.descIn(x, ys), subB(rest, ys), hh)))

law dInOf:
  for -o: Gll.Desc
  for -d: Gll.Desc
  for +seen: +List<Gll.Desc>
  for eq: {o == d : Gll.Desc}
  for e: {Gll.descIn(o, seen) == True{} : Bool}
  {Gll.descIn(d, seen) == True{} : Bool}

def dInOf(o, d, seen, eq, e):
  %eq : {Gll.descIn(_, seen) == True{} : Bool}
  e

def neq_pick(+o: Gll.Desc, +d: Gll.Desc, +seen: +List<Gll.Desc>, cases: Either<{Gll.descEq(o, d) == True{} : Bool}, {Gll.descEq(o, d) == False{} : Bool}>,
             oIn: {Gll.descIn(o, seen) == True{} : Bool}, dOut: {Gll.descIn(d, seen) == False{} : Bool}) -> {Gll.descEq(o, d) == False{} : Bool}:
  match cases:
    case Inl{t}:
      +eq = desc_eq_sound(o, d, t)
      +dIn = {oIn : {Gll.descIn(o, seen) == True{} : Bool}}
      Empty.absurd({Gll.descEq(o, d) == False{} : Bool}, both_ways(Gll.descIn(d, seen), dInOf(o, d, seen, eq, dIn), dOut))
    case Inr{f}:
      f

# A seen descriptor differs from one not yet seen.
law neq_of_absent:
  for +o: Gll.Desc
  for +d: Gll.Desc
  for +seen: +List<Gll.Desc>
  for oIn: {Gll.descIn(o, seen) == True{} : Bool}
  for dOut: {Gll.descIn(d, seen) == False{} : Bool}
  {Gll.descEq(o, d) == False{} : Bool}

def neq_of_absent(o, d, seen, oIn, dOut):
  neq_pick(o, d, seen, bool_cases(Gll.descEq(o, d)), oIn, dOut)

law not_true:
  for b: Bool
  for e: {Bool.not(b) == True{} : Bool}
  {b == False{} : Bool}

def not_true(b, e):
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, Lemma.true_is_not_false(Equal.sym(Bool, False{}, True{}, e)))
    case False{}:
      {==}

law not_intro:
  for b: Bool
  for e: {b == False{} : Bool}
  {Bool.not(b) == True{} : Bool}

def not_intro(b, e):
  match b:
    case True{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.true_is_not_false(e))
    case False{}:
      {==}

# Adding a descriptor not yet seen keeps every return edge's origin seen and not to do.
law rets_grow:
  for rs: +List<Gll.Ret>
  for +seen: +List<Gll.Desc>
  for +todo: +List<Gll.Desc>
  for +d: Gll.Desc
  for dOut: {Gll.descIn(d, seen) == False{} : Bool}
  for h: {retsB(rs, seen, todo) == True{} : Bool}
  {retsB(rs, d <> seen, d <> todo) == True{} : Bool}

def rets_grow(rs, seen, todo, d, dOut, h):
  match rs:
    case Nil{}:
      {==}
    case Con{+r, +rest}:
      +hh = h
      +o = origin(r)
      +head = Lemma.and_true_left(Bool.and(Gll.descIn(o, seen), Bool.not(Gll.descIn(o, todo))), retsB(rest, seen, todo), hh)
      +oIn = Lemma.and_true_left(Gll.descIn(o, seen), Bool.not(Gll.descIn(o, todo)), head)
      +oOut = not_true(Gll.descIn(o, todo), Lemma.and_true_right_side(Gll.descIn(o, seen), Bool.not(Gll.descIn(o, todo)), head))
      +out = dOut
      Lemma.and_true_intro(Bool.and(Gll.descIn(o, d <> seen), Bool.not(Gll.descIn(o, d <> todo))), retsB(rest, d <> seen, d <> todo),
        Lemma.and_true_intro(Gll.descIn(o, d <> seen), Bool.not(Gll.descIn(o, d <> todo)),
          in_cons(o, d, seen, oIn),
          not_intro(Gll.descIn(o, d <> todo), not_in_cons(o, d, todo, neq_of_absent(o, d, seen, oIn, out), oOut))),
        rets_grow(rest, seen, todo, d, out, Lemma.and_true_right_side(Bool.and(Gll.descIn(o, seen), Bool.not(Gll.descIn(o, todo))), retsB(rest, seen, todo), hh)))

# Taking the head off the descriptors to do keeps every origin not to do.
law rets_tail:
  for rs: +List<Gll.Ret>
  for +seen: +List<Gll.Desc>
  for +d: Gll.Desc
  for +rest: +List<Gll.Desc>
  for h: {retsB(rs, seen, d <> rest) == True{} : Bool}
  {retsB(rs, seen, rest) == True{} : Bool}

def rets_tail(rs, seen, d, rest, h):
  match rs:
    case Nil{}:
      {==}
    case Con{+r, +more}:
      +hh = h
      +o = origin(r)
      +head = Lemma.and_true_left(Bool.and(Gll.descIn(o, seen), Bool.not(Gll.descIn(o, d <> rest))), retsB(more, seen, d <> rest), hh)
      Lemma.and_true_intro(Bool.and(Gll.descIn(o, seen), Bool.not(Gll.descIn(o, rest))), retsB(more, seen, rest),
        Lemma.and_true_intro(Gll.descIn(o, seen), Bool.not(Gll.descIn(o, rest)),
          Lemma.and_true_left(Gll.descIn(o, seen), Bool.not(Gll.descIn(o, d <> rest)), head),
          not_intro(Gll.descIn(o, rest), not_in_tail(o, d, rest, not_true(Gll.descIn(o, d <> rest), Lemma.and_true_right_side(Gll.descIn(o, seen), Bool.not(Gll.descIn(o, d <> rest)), head))))),
        rets_tail(more, seen, d, rest, Lemma.and_true_right_side(Bool.and(Gll.descIn(o, seen), Bool.not(Gll.descIn(o, d <> rest))), retsB(more, seen, d <> rest), hh)))

# ---- Every operation of the engine keeps the invariant ----

def desc_pick_inv(known: Bool, +d: Gll.Desc, +seen: +List<Gll.Desc>, +todo: +List<Gll.Desc>, +cs: +List<Gll.CKey>, +rs: +List<Gll.Ret>, +ps: +List<Gll.Pop>, +ys: +List<Spec.Bsr>,
                  eqk: {Gll.descIn(d, seen) == known : Bool}, h: Inv(Gll.GState{seen, todo, cs, rs, ps, ys})) -> Inv(Gll.descPick(known, d, Gll.GState{seen, todo, cs, rs, ps, ys})):
  match known:
    case True{}:
      h
    case False{}:
      match h:
        case (hSub, (hNoDup, hRets)):
          +sub = hSub
          +out = eqk
          (Lemma.and_true_intro(Gll.descIn(d, d <> seen), subB(todo, d <> seen), in_head(d, seen), sub_cons(todo, seen, d, sub)),
           ((sub_out(todo, seen, d, sub, out), hNoDup), rets_grow(rs, seen, todo, d, out, hRets)))

law with_desc_inv:
  for +d: Gll.Desc
  for +s: Gll.GState
  for h: Inv(s)
  Inv(Gll.withDesc(d, s))

def with_desc_inv(d, s, h):
  match s:
    case Gll.GState{+seen, +todo, +cs, +rs, +ps, +ys}:
      desc_pick_inv(Gll.descIn(d, seen), d, seen, todo, cs, rs, ps, ys, {==}, h)

def yield_pick_inv(known: Bool, +y: Spec.Bsr, +seen: +List<Gll.Desc>, +todo: +List<Gll.Desc>, +cs: +List<Gll.CKey>, +rs: +List<Gll.Ret>, +ps: +List<Gll.Pop>, +ys: +List<Spec.Bsr>,
                   h: Inv(Gll.GState{seen, todo, cs, rs, ps, ys})) -> Inv(Gll.yieldPick(known, y, Gll.GState{seen, todo, cs, rs, ps, ys})):
  match known:
    case True{}:
      h
    case False{}:
      h

law with_yield_inv:
  for +y: Spec.Bsr
  for +s: Gll.GState
  for h: Inv(s)
  Inv(Gll.withYield(y, s))

def with_yield_inv(y, s, h):
  match s:
    case Gll.GState{+seen, +todo, +cs, +rs, +ps, +ys}:
      yield_pick_inv(Spec.bsrMember(y, ys), y, seen, todo, cs, rs, ps, ys, h)

law admit_pick_inv:
  for ok: Bool
  for +d: Gll.Desc
  for +s: Gll.GState
  for h: Inv(s)
  Inv(Gll.admitPick(ok, d, s))

def admit_pick_inv(ok, d, s, h):
  match ok:
    case True{}:
      with_desc_inv(d, s, h)
    case False{}:
      h

law with_descs_p_inv:
  for +pr: Gll.Pred
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for ds: +List<Gll.Desc>
  for +s: Gll.GState
  for h: Inv(s)
  Inv(Gll.withDescsP(pr, grammar, input, ds, s))

def with_descs_p_inv(pr, grammar, input, ds, s, h):
  match ds:
    case Nil{}:
      h
    case Con{+d, +rest}:
      with_descs_p_inv(pr, grammar, input, rest, Gll.withDescP(pr, grammar, input, d, s), admit_pick_inv(Gll.admits(pr, grammar, input, d), d, s, h))

law pair_pick_inv:
  for ok: Bool
  for +d: Gll.Desc
  for +y: Spec.Bsr
  for +s: Gll.GState
  for h: Inv(s)
  Inv(Gll.pairPick(ok, d, y, s))

def pair_pick_inv(ok, d, y, s, h):
  match ok:
    case True{}:
      with_yield_inv(y, Gll.withDesc(d, s), with_desc_inv(d, s, h))
    case False{}:
      h

law resume_if_inv:
  for hit: Bool
  for +pr: Gll.Pred
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +edge: Gll.Edge
  for +kc: Nat
  for +j: Nat
  for +s: Gll.GState
  for h: Inv(s)
  Inv(Gll.resumeIf(hit, pr, grammar, input, edge, kc, j, s))

def resume_if_inv(hit, pr, grammar, input, edge, kc, j, s, h):
  match hit edge:
    case True{} Gll.Edge{+index, +rpath, +dot, +k}:
      +d = {Gll.Desc{index, rpath, 1n+dot, k, j} : Gll.Desc}
      pair_pick_inv(Gll.admits(pr, grammar, input, d), d, Gll.stepAt(index, rpath, 1n+dot, k, kc, j), s, h)
    case False{} _:
      h

law resume_all_inv:
  for rets: +List<Gll.Ret>
  for +pr: Gll.Pred
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +key: Gll.CKey
  for +kc: Nat
  for +j: Nat
  for +s: Gll.GState
  for h: Inv(s)
  Inv(Gll.resumeAll(rets, pr, grammar, input, key, kc, j, s))

def resume_all_inv(rets, pr, grammar, input, key, kc, j, s, h):
  match rets:
    case Nil{}:
      h
    case Con{Gll.Ret{+k2, +e2}, +rest}:
      resume_all_inv(rest, pr, grammar, input, key, kc, j, Gll.resumeIf(Gll.keyEq(key, k2), pr, grammar, input, e2, kc, j, s),
        resume_if_inv(Gll.keyEq(key, k2), pr, grammar, input, e2, kc, j, s, h))

law resume_pops_inv:
  for pops: +List<Gll.Pop>
  for +pr: Gll.Pred
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +key: Gll.CKey
  for +edge: Gll.Edge
  for +kc: Nat
  for +s: Gll.GState
  for h: Inv(s)
  Inv(Gll.resumePops(pops, pr, grammar, input, key, edge, kc, s))

def resume_pops_inv(pops, pr, grammar, input, key, edge, kc, s, h):
  match pops:
    case Nil{}:
      h
    case Con{Gll.Pop{+k2, +j}, +rest}:
      resume_pops_inv(rest, pr, grammar, input, key, edge, kc, Gll.resumeIf(Gll.keyEq(key, k2), pr, grammar, input, edge, kc, j, s),
        resume_if_inv(Gll.keyEq(key, k2), pr, grammar, input, edge, kc, j, s, h))

def leave_pick_inv(known: Bool, +pr: Gll.Pred, +grammar: +List<Spec.Production>, +input: +List<Nat>, +key: Gll.CKey, +kc: Nat, +j: Nat, +again: +List<Gll.Desc>,
                   +seen: +List<Gll.Desc>, +todo: +List<Gll.Desc>, +cs: +List<Gll.CKey>, +rs: +List<Gll.Ret>, +ps: +List<Gll.Pop>, +ys: +List<Spec.Bsr>,
                   h: Inv(Gll.GState{seen, todo, cs, rs, ps, ys})) -> Inv(Gll.leavePick(known, pr, grammar, input, key, kc, j, again, Gll.GState{seen, todo, cs, rs, ps, ys})):
  match known:
    case True{}:
      h
    case False{}:
      +s2 = {Gll.GState{seen, todo, cs, rs, Gll.Pop{key, j} <> ps, ys} : Gll.GState}
      with_descs_p_inv(pr, grammar, input, again, Gll.resumeAll(rs, pr, grammar, input, key, kc, j, s2), resume_all_inv(rs, pr, grammar, input, key, kc, j, s2, h))

law leave_inv:
  for +pr: Gll.Pred
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +key: Gll.CKey
  for +kc: Nat
  for +j: Nat
  for +again: +List<Gll.Desc>
  for +s: Gll.GState
  for h: Inv(s)
  Inv(Gll.leave(pr, grammar, input, key, kc, j, again, s))

def leave_inv(pr, grammar, input, key, kc, j, again, s, h):
  match s:
    case Gll.GState{+seen, +todo, +cs, +rs, +ps, +ys}:
      leave_pick_inv(Gll.popIn(key, j, ps), pr, grammar, input, key, kc, j, again, seen, todo, cs, rs, ps, ys, h)

law match_token_inv:
  for ok: Bool
  for +pr: Gll.Pred
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +index: Nat
  for +rpath: +List<Nat>
  for +dot: Nat
  for +k: Nat
  for +i: Nat
  for +s: Gll.GState
  for h: Inv(s)
  Inv(Gll.matchToken(ok, pr, grammar, input, index, rpath, dot, k, i, s))

def match_token_inv(ok, pr, grammar, input, index, rpath, dot, k, i, s, h):
  match ok:
    case True{}:
      +d = {Gll.Desc{index, rpath, 1n+dot, k, 1n+i} : Gll.Desc}
      pair_pick_inv(Gll.admits(pr, grammar, input, d), d, Gll.stepAt(index, rpath, 1n+dot, k, i, 1n+i), s, h)
    case False{}:
      h

law skip_if_inv:
  for skip: Bool
  for +pr: Gll.Pred
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +index: Nat
  for +rpath: +List<Nat>
  for +dot: Nat
  for +k: Nat
  for +i: Nat
  for +s: Gll.GState
  for h: Inv(s)
  Inv(Gll.skipIf(skip, pr, grammar, input, index, rpath, dot, k, i, s))

def skip_if_inv(skip, pr, grammar, input, index, rpath, dot, k, i, s, h):
  match skip:
    case True{}:
      +d = {Gll.Desc{index, rpath, 1n+dot, k, i} : Gll.Desc}
      pair_pick_inv(Gll.admits(pr, grammar, input, d), d, Gll.stepAt(index, rpath, 1n+dot, k, i, i), s, h)
    case False{}:
      h

law empty_if_inv:
  for dot: Nat
  for +index: Nat
  for +rpath: +List<Nat>
  for +k: Nat
  for +i: Nat
  for +s: Gll.GState
  for h: Inv(s)
  Inv(Gll.emptyIf(dot, index, rpath, k, i, s))

def empty_if_inv(dot, index, rpath, k, i, s, h):
  match dot:
    case 0n:
      with_yield_inv(Gll.stepAt(index, rpath, 0n, k, i, i), s, h)
    case 1n+d:
      h

law finish_inv:
  for +pr: Gll.Pred
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +index: Nat
  for rpath: +List<Nat>
  for +k: Nat
  for +i: Nat
  for +s: Gll.GState
  for h: Inv(s)
  Inv(Gll.finish(pr, grammar, input, index, rpath, k, i, s))

def finish_inv(pr, grammar, input, index, rpath, k, i, s, h):
  match rpath:
    case Con{a, Con{+m, +outer}}:
      leave_inv(pr, grammar, input, Gll.CKey{Gll.TBr{index, m <> outer}, k}, k, i, Gll.againOf(Gll.nthItem(Gll.seqAt(grammar, index, outer), m), index, m <> outer, k, i), s, h)
    case Con{a, Nil{}}:
      leave_inv(pr, grammar, input, Gll.CKey{Gll.TNt{Gll.lhsOf(grammar, index)}, k}, k, i, [], s, h)
    case Nil{}:
      leave_inv(pr, grammar, input, Gll.CKey{Gll.TNt{Gll.lhsOf(grammar, index)}, k}, k, i, [], s, h)

# A call adds the return edge whose origin is the descriptor being processed: seen, no longer to do.
def call_pick_inv(known: Bool, known2: Bool, +pr: Gll.Pred, +grammar: +List<Spec.Production>, +input: +List<Nat>, +key: Gll.CKey, +kc: Nat, +edge: Gll.Edge, +seeds: +List<Gll.Desc>,
                  +seen: +List<Gll.Desc>, +todo: +List<Gll.Desc>, +cs: +List<Gll.CKey>, +rs: +List<Gll.Ret>, +ps: +List<Gll.Pop>, +ys: +List<Spec.Bsr>,
                  h: Inv(Gll.GState{seen, todo, cs, rs, ps, ys}),
                  oIn: {Gll.descIn(origin(Gll.Ret{key, edge}), seen) == True{} : Bool}, oOut: {Gll.descIn(origin(Gll.Ret{key, edge}), todo) == False{} : Bool})
                  -> Inv(Gll.callPick(known, known2, pr, grammar, input, key, kc, edge, seeds, Gll.GState{seen, todo, cs, rs, ps, ys})):
  match known known2:
    case False{} _:
      match h:
        case (hSub, (hNoDup, hRets)):
          +s2 = {Gll.GState{seen, todo, key <> cs, Gll.Ret{key, edge} <> rs, ps, ys} : Gll.GState}
          with_descs_p_inv(pr, grammar, input, seeds, s2, (hSub, (hNoDup, Lemma.and_true_intro(Bool.and(Gll.descIn(origin(Gll.Ret{key, edge}), seen), Bool.not(Gll.descIn(origin(Gll.Ret{key, edge}), todo))), retsB(rs, seen, todo),
            Lemma.and_true_intro(Gll.descIn(origin(Gll.Ret{key, edge}), seen), Bool.not(Gll.descIn(origin(Gll.Ret{key, edge}), todo)), oIn, not_intro(Gll.descIn(origin(Gll.Ret{key, edge}), todo), oOut)), hRets))))
    case True{} True{}:
      h
    case True{} False{}:
      match h:
        case (hSub, (hNoDup, hRets)):
          +s2 = {Gll.GState{seen, todo, cs, Gll.Ret{key, edge} <> rs, ps, ys} : Gll.GState}
          resume_pops_inv(ps, pr, grammar, input, key, edge, kc, s2, (hSub, (hNoDup, Lemma.and_true_intro(Bool.and(Gll.descIn(origin(Gll.Ret{key, edge}), seen), Bool.not(Gll.descIn(origin(Gll.Ret{key, edge}), todo))), retsB(rs, seen, todo),
            Lemma.and_true_intro(Gll.descIn(origin(Gll.Ret{key, edge}), seen), Bool.not(Gll.descIn(origin(Gll.Ret{key, edge}), todo)), oIn, not_intro(Gll.descIn(origin(Gll.Ret{key, edge}), todo), oOut)), hRets))))

def call_inv(+pr: Gll.Pred, +grammar: +List<Spec.Production>, +input: +List<Nat>, +target: Gll.Target, +i: Nat, +edge: Gll.Edge, +seeds: +List<Gll.Desc>,
             +seen: +List<Gll.Desc>, +todo: +List<Gll.Desc>, +cs: +List<Gll.CKey>, +rs: +List<Gll.Ret>, +ps: +List<Gll.Pop>, +ys: +List<Spec.Bsr>,
             h: Inv(Gll.GState{seen, todo, cs, rs, ps, ys}),
             oIn: {Gll.descIn(origin(Gll.Ret{Gll.CKey{target, i}, edge}), seen) == True{} : Bool}, oOut: {Gll.descIn(origin(Gll.Ret{Gll.CKey{target, i}, edge}), todo) == False{} : Bool})
             -> Inv(Gll.call(pr, grammar, input, target, i, edge, seeds, Gll.GState{seen, todo, cs, rs, ps, ys})):
  +key = {Gll.CKey{target, i} : Gll.CKey}
  call_pick_inv(Gll.keyIn(key, cs), Gll.retIn(key, edge, rs), pr, grammar, input, key, i, edge, seeds, seen, todo, cs, rs, ps, ys, h, oIn, oOut)

# One step keeps the invariant, when the descriptor it processes is seen and no longer to do.
def step_item_inv(item: Maybe<&2, Spec.Item>, +pr: Gll.Pred, +grammar: +List<Spec.Production>, +input: +List<Nat>, +index: Nat, +rpath: +List<Nat>, +dot: Nat, +k: Nat, +i: Nat,
                  +seen: +List<Gll.Desc>, +todo: +List<Gll.Desc>, +cs: +List<Gll.CKey>, +rs: +List<Gll.Ret>, +ps: +List<Gll.Pop>, +ys: +List<Spec.Bsr>,
                  h: Inv(Gll.GState{seen, todo, cs, rs, ps, ys}),
                  dIn: {Gll.descIn(Gll.Desc{index, rpath, dot, k, i}, seen) == True{} : Bool}, dOut: {Gll.descIn(Gll.Desc{index, rpath, dot, k, i}, todo) == False{} : Bool})
                  -> Inv(Gll.stepItem(item, pr, grammar, input, index, rpath, dot, k, i, Gll.GState{seen, todo, cs, rs, ps, ys})):
  match item:
    case Some{Spec.Sym{Spec.Terminal{+t}}}:
      +s = {Gll.GState{seen, todo, cs, rs, ps, ys} : Gll.GState}
      match_token_inv(Gll.tokenIs(List.get(&2, Nat, input, i), t), pr, grammar, input, index, rpath, dot, k, i, s, h)
    case Some{Spec.Sym{Spec.Nonterminal{+x}}}:
      call_inv(pr, grammar, input, Gll.TNt{x}, i, Gll.Edge{index, rpath, dot, k}, Gll.productionsOf(grammar, x, 0n, i), seen, todo, cs, rs, ps, ys, h, dIn, dOut)
    case Some{Spec.Brack{+kind, +alts}}:
      +s = {Gll.GState{seen, todo, cs, rs, ps, ys} : Gll.GState}
      +seeds = Gll.alternatives(List.length(&2, +List<Spec.Item>, alts), index, dot <> rpath, i, i)
      +target = {Gll.TBr{index, dot <> rpath} : Gll.Target}
      +edge = {Gll.Edge{index, rpath, dot, k} : Gll.Edge}
      skip_if_inv(Gll.isSkippable(kind), pr, grammar, input, index, rpath, dot, k, i, Gll.call(pr, grammar, input, target, i, edge, seeds, s),
        call_inv(pr, grammar, input, target, i, edge, seeds, seen, todo, cs, rs, ps, ys, h, dIn, dOut))
    case Some{Spec.Eps{}}:
      skip_if_inv(True{}, pr, grammar, input, index, rpath, dot, k, i, Gll.GState{seen, todo, cs, rs, ps, ys}, h)
    case None{}:
      +s = {Gll.GState{seen, todo, cs, rs, ps, ys} : Gll.GState}
      finish_inv(pr, grammar, input, index, rpath, k, i, Gll.emptyIf(dot, index, rpath, k, i, s), empty_if_inv(dot, index, rpath, k, i, s, h))

def step_at_inv(+index: Nat, +rpath: +List<Nat>, +dot: Nat, +k: Nat, +i: Nat, +pr: Gll.Pred, +grammar: +List<Spec.Production>, +input: +List<Nat>,
                +seen: +List<Gll.Desc>, +rest: +List<Gll.Desc>, +cs: +List<Gll.CKey>, +rs: +List<Gll.Ret>, +ps: +List<Gll.Pop>, +ys: +List<Spec.Bsr>,
                h: Inv(Gll.GState{seen, Gll.Desc{index, rpath, dot, k, i} <> rest, cs, rs, ps, ys}))
                -> Inv(Gll.step(Gll.Desc{index, rpath, dot, k, i}, pr, grammar, input, Gll.GState{seen, rest, cs, rs, ps, ys})):
  match h:
    case (hSub, ((dNotRest, ndRest), hRets)):
      +dd = {Gll.Desc{index, rpath, dot, k, i} : Gll.Desc}
      +sub = hSub
      step_item_inv(Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), pr, grammar, input, index, rpath, dot, k, i, seen, rest, cs, rs, ps, ys,
        (Lemma.and_true_right_side(Gll.descIn(dd, seen), subB(rest, seen), sub), (ndRest, rets_tail(rs, seen, dd, rest, hRets))),
        Lemma.and_true_left(Gll.descIn(dd, seen), subB(rest, seen), sub), dNotRest)

# The run's step: the head d of the descriptors to do is taken off and processed.
law step_inv:
  for d: Gll.Desc
  for +pr: Gll.Pred
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +seen: +List<Gll.Desc>
  for +rest: +List<Gll.Desc>
  for +cs: +List<Gll.CKey>
  for +rs: +List<Gll.Ret>
  for +ps: +List<Gll.Pop>
  for +ys: +List<Spec.Bsr>
  for h: Inv(Gll.GState{seen, d <> rest, cs, rs, ps, ys})
  Inv(Gll.step(d, pr, grammar, input, Gll.GState{seen, rest, cs, rs, ps, ys}))

def step_inv(d, pr, grammar, input, seen, rest, cs, rs, ps, ys, h):
  match d:
    case Gll.Desc{+index, +rpath, +dot, +k, +i}:
      step_at_inv(index, rpath, dot, k, i, pr, grammar, input, seen, rest, cs, rs, ps, ys, h)

# ---- Afroozeh's argument: the check never finds an edge ----

# An existing edge equal to the one d is about to add would have d as its origin.
law origin_is:
  for +target: Gll.Target
  for +i: Nat
  for +index: Nat
  for +rpath: +List<Nat>
  for +dot: Nat
  for +k: Nat
  for -k2: Gll.CKey
  for -e2: Gll.Edge
  for +rest: +List<Gll.Desc>
  for ek: {Gll.CKey{target, i} == k2 : Gll.CKey}
  for ee: {Gll.Edge{index, rpath, dot, k} == e2 : Gll.Edge}
  {Gll.descIn(origin(Gll.Ret{k2, e2}), Gll.Desc{index, rpath, dot, k, i} <> rest) == True{} : Bool}

def origin_is(target, i, index, rpath, dot, k, k2, e2, rest, ek, ee):
  %ek : {Gll.descIn(origin(Gll.Ret{_, e2}), Gll.Desc{index, rpath, dot, k, i} <> rest) == True{} : Bool}
  %ee : {Gll.descIn(origin(Gll.Ret{Gll.CKey{target, i}, _}), Gll.Desc{index, rpath, dot, k, i} <> rest) == True{} : Bool}
  in_head(Gll.Desc{index, rpath, dot, k, i}, rest)

law and_false_by:
  for a: Bool
  for b: Bool
  for f: {a == True{} : Bool} -> {b == True{} : Bool} -> Empty
  {Bool.and(a, b) == False{} : Bool}

def and_false_by(a, b, f):
  match a b:
    case False{} _:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      Empty.absurd({True{} == False{} : Bool}, f({==}, {==}))

# While d is processed (it was the head of the descriptors to do), no return edge matches its call.
law no_edge:
  for +target: Gll.Target
  for +i: Nat
  for +index: Nat
  for +rpath: +List<Nat>
  for +dot: Nat
  for +k: Nat
  for rs: +List<Gll.Ret>
  for +seen: +List<Gll.Desc>
  for +rest: +List<Gll.Desc>
  for h: {retsB(rs, seen, Gll.Desc{index, rpath, dot, k, i} <> rest) == True{} : Bool}
  {Gll.retIn(Gll.CKey{target, i}, Gll.Edge{index, rpath, dot, k}, rs) == False{} : Bool}

def no_edge(target, i, index, rpath, dot, k, rs, seen, rest, h):
  match rs:
    case Nil{}:
      {==}
    case Con{Gll.Ret{+k2, +e2}, +more}:
      +hh = h
      +dd = {Gll.Desc{index, rpath, dot, k, i} : Gll.Desc}
      +o = origin(Gll.Ret{k2, e2})
      +head = Lemma.and_true_left(Bool.and(Gll.descIn(o, seen), Bool.not(Gll.descIn(o, dd <> rest))), retsB(more, seen, dd <> rest), hh)
      +oOut = not_true(Gll.descIn(o, dd <> rest), Lemma.and_true_right_side(Gll.descIn(o, seen), Bool.not(Gll.descIn(o, dd <> rest)), head))
      +key = {Gll.CKey{target, i} : Gll.CKey}
      +edge = {Gll.Edge{index, rpath, dot, k} : Gll.Edge}
      both_false(Bool.and(Gll.keyEq(key, k2), Gll.edgeEq(edge, e2)), Gll.retIn(key, edge, more),
        and_false_by(Gll.keyEq(key, k2), Gll.edgeEq(edge, e2),
          ka => eb => both_ways(Gll.descIn(o, dd <> rest), origin_is(target, i, index, rpath, dot, k, k2, e2, rest, key_eq_sound(key, k2, ka), edge_eq_sound(edge, e2, eb)), oOut)),
        no_edge(target, i, index, rpath, dot, k, more, seen, rest, Lemma.and_true_right_side(Bool.and(Gll.descIn(o, seen), Bool.not(Gll.descIn(o, dd <> rest))), retsB(more, seen, dd <> rest), hh)))

# ---- So the engine without the check runs the same ----

def call_pick_same(known: Bool, +pr: Gll.Pred, +grammar: +List<Spec.Production>, +input: +List<Nat>, +key: Gll.CKey, +kc: Nat, +edge: Gll.Edge, +seeds: +List<Gll.Desc>,
                   +seen: +List<Gll.Desc>, +todo: +List<Gll.Desc>, +cs: +List<Gll.CKey>, +rs: +List<Gll.Ret>, +ps: +List<Gll.Pop>, +ys: +List<Spec.Bsr>)
                   -> {Gll.callPick(known, False{}, pr, grammar, input, key, kc, edge, seeds, Gll.GState{seen, todo, cs, rs, ps, ys}) == callPickFree(known, pr, grammar, input, key, kc, edge, seeds, Gll.GState{seen, todo, cs, rs, ps, ys}) : Gll.GState}:
  match known:
    case False{}:
      {==}
    case True{}:
      {==}

def call_same(+pr: Gll.Pred, +grammar: +List<Spec.Production>, +input: +List<Nat>, +target: Gll.Target, +i: Nat, +edge: Gll.Edge, +seeds: +List<Gll.Desc>,
              +seen: +List<Gll.Desc>, +todo: +List<Gll.Desc>, +cs: +List<Gll.CKey>, +rs: +List<Gll.Ret>, +ps: +List<Gll.Pop>, +ys: +List<Spec.Bsr>,
              nr: {Gll.retIn(Gll.CKey{target, i}, edge, rs) == False{} : Bool})
              -> {Gll.call(pr, grammar, input, target, i, edge, seeds, Gll.GState{seen, todo, cs, rs, ps, ys}) == callFree(pr, grammar, input, target, i, edge, seeds, Gll.GState{seen, todo, cs, rs, ps, ys}) : Gll.GState}:
  +key = {Gll.CKey{target, i} : Gll.CKey}
  %Equal.sym(Bool, Gll.retIn(key, edge, rs), False{}, nr) : {Gll.callPick(Gll.keyIn(key, cs), _, pr, grammar, input, key, i, edge, seeds, Gll.GState{seen, todo, cs, rs, ps, ys}) == callPickFree(Gll.keyIn(key, cs), pr, grammar, input, key, i, edge, seeds, Gll.GState{seen, todo, cs, rs, ps, ys}) : Gll.GState}
  call_pick_same(Gll.keyIn(key, cs), pr, grammar, input, key, i, edge, seeds, seen, todo, cs, rs, ps, ys)

def step_item_same(item: Maybe<&2, Spec.Item>, +pr: Gll.Pred, +grammar: +List<Spec.Production>, +input: +List<Nat>, +index: Nat, +rpath: +List<Nat>, +dot: Nat, +k: Nat, +i: Nat,
                   +seen: +List<Gll.Desc>, +rest: +List<Gll.Desc>, +cs: +List<Gll.CKey>, +rs: +List<Gll.Ret>, +ps: +List<Gll.Pop>, +ys: +List<Spec.Bsr>,
                   hR: {retsB(rs, seen, Gll.Desc{index, rpath, dot, k, i} <> rest) == True{} : Bool})
                   -> {Gll.stepItem(item, pr, grammar, input, index, rpath, dot, k, i, Gll.GState{seen, rest, cs, rs, ps, ys}) == stepItemFree(item, pr, grammar, input, index, rpath, dot, k, i, Gll.GState{seen, rest, cs, rs, ps, ys}) : Gll.GState}:
  match item:
    case Some{Spec.Sym{Spec.Terminal{+t}}}:
      {==}
    case Some{Spec.Sym{Spec.Nonterminal{+x}}}:
      call_same(pr, grammar, input, Gll.TNt{x}, i, Gll.Edge{index, rpath, dot, k}, Gll.productionsOf(grammar, x, 0n, i), seen, rest, cs, rs, ps, ys,
        no_edge(Gll.TNt{x}, i, index, rpath, dot, k, rs, seen, rest, hR))
    case Some{Spec.Brack{+kind, +alts}}:
      +s = {Gll.GState{seen, rest, cs, rs, ps, ys} : Gll.GState}
      +seeds = Gll.alternatives(List.length(&2, +List<Spec.Item>, alts), index, dot <> rpath, i, i)
      +target = {Gll.TBr{index, dot <> rpath} : Gll.Target}
      +edge = {Gll.Edge{index, rpath, dot, k} : Gll.Edge}
      %call_same(pr, grammar, input, target, i, edge, seeds, seen, rest, cs, rs, ps, ys, no_edge(target, i, index, rpath, dot, k, rs, seen, rest, hR)) : {Gll.skipIf(Gll.isSkippable(kind), pr, grammar, input, index, rpath, dot, k, i, Gll.call(pr, grammar, input, target, i, edge, seeds, s)) == Gll.skipIf(Gll.isSkippable(kind), pr, grammar, input, index, rpath, dot, k, i, _) : Gll.GState}
      {==}
    case Some{Spec.Eps{}}:
      {==}
    case None{}:
      {==}

# Both facts about one step from one copy of the invariant: the two steps agree, and the
# invariant holds after it. (The invariant is a proof, used once; its parts are Bools.)
def step_both(+index: Nat, +rpath: +List<Nat>, +dot: Nat, +k: Nat, +i: Nat, +pr: Gll.Pred, +grammar: +List<Spec.Production>, +input: +List<Nat>,
              +seen: +List<Gll.Desc>, +rest: +List<Gll.Desc>, +cs: +List<Gll.CKey>, +rs: +List<Gll.Ret>, +ps: +List<Gll.Pop>, +ys: +List<Spec.Bsr>,
              h: Inv(Gll.GState{seen, Gll.Desc{index, rpath, dot, k, i} <> rest, cs, rs, ps, ys}))
              -> {Gll.step(Gll.Desc{index, rpath, dot, k, i}, pr, grammar, input, Gll.GState{seen, rest, cs, rs, ps, ys}) == stepFree(Gll.Desc{index, rpath, dot, k, i}, pr, grammar, input, Gll.GState{seen, rest, cs, rs, ps, ys}) : Gll.GState}
                 & Inv(Gll.step(Gll.Desc{index, rpath, dot, k, i}, pr, grammar, input, Gll.GState{seen, rest, cs, rs, ps, ys})):
  match h:
    case (hSub, ((dNotRest, ndRest), hRets)):
      +dd = {Gll.Desc{index, rpath, dot, k, i} : Gll.Desc}
      +rets = {hRets : {retsB(rs, seen, dd <> rest) == True{} : Bool}}
      +sub = {hSub : {Bool.and(Gll.descIn(dd, seen), subB(rest, seen)) == True{} : Bool}}
      (step_item_same(Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), pr, grammar, input, index, rpath, dot, k, i, seen, rest, cs, rs, ps, ys, rets),
       step_item_inv(Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), pr, grammar, input, index, rpath, dot, k, i, seen, rest, cs, rs, ps, ys,
         (Lemma.and_true_right_side(Gll.descIn(dd, seen), subB(rest, seen), sub), (ndRest, rets_tail(rs, seen, dd, rest, rets))),
         Lemma.and_true_left(Gll.descIn(dd, seen), subB(rest, seen), sub), dNotRest))

def run_go(+f: Nat, +pr: Gll.Pred, +grammar: +List<Spec.Production>, +input: +List<Nat>, +s1: Gll.GState, +s2: Gll.GState,
           both: {s1 == s2 : Gll.GState} & Inv(s1),
           rec: Inv(s1) -> {runFree(f, pr, grammar, input, s1) == Gll.run(f, pr, grammar, input, s1) : Gll.GRun}) -> {runFree(f, pr, grammar, input, s2) == Gll.run(f, pr, grammar, input, s1) : Gll.GRun}:
  match both:
    case (eq, h):
      %eq : {runFree(f, pr, grammar, input, _) == Gll.run(f, pr, grammar, input, s1) : Gll.GRun}
      rec(h)

law run_same:
  for fuel: Nat
  for +pr: Gll.Pred
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for h: Inv(s)
  {runFree(fuel, pr, grammar, input, s) == Gll.run(fuel, pr, grammar, input, s) : Gll.GRun}

def run_same(fuel, pr, grammar, input, s, h):
  match fuel s:
    case 0n _:
      {==}
    case 1n+(+f) Gll.GState{+seen, Nil{}, +cs, +rs, +ps, +ys}:
      {==}
    case 1n+(+f) Gll.GState{+seen, Con{Gll.Desc{+index, +rpath, +dot, +k, +i}, +rest}, +cs, +rs, +ps, +ys}:
      +s1 = {Gll.GState{seen, rest, cs, rs, ps, ys} : Gll.GState}
      +d = {Gll.Desc{index, rpath, dot, k, i} : Gll.Desc}
      +next = Gll.step(d, pr, grammar, input, s1)
      run_go(f, pr, grammar, input, next, stepFree(d, pr, grammar, input, s1),
        step_both(index, rpath, dot, k, i, pr, grammar, input, seen, rest, cs, rs, ps, ys, h),
        h1 => run_same(f, pr, grammar, input, next, h1))

# ---- The theorem ----

# AFROOZEH. The parser that never looks for an existing return edge runs exactly as GLL.bend:
# the same descriptors, clusters, return edges, pops and steps, with or without prediction.
# So a cluster's return edges can be kept in a list (an array) that is only appended to.
law afroozeh_return_edges:
  for fuel: Nat
  for +pr: Gll.Pred
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  {parseWithFree(fuel, pr, grammar, start, input) == Gll.parseWith(fuel, pr, grammar, start, input) : Gll.GRun}

def afroozeh_return_edges(fuel, pr, grammar, start, input):
  +s0 = {Gll.GState{[], [], [Gll.CKey{Gll.TNt{start}, 0n}], [], [], []} : Gll.GState}
  run_same(fuel, pr, grammar, input, Gll.withDescsP(pr, grammar, input, Gll.productionsOf(grammar, start, 0n, 0n), s0),
    with_descs_p_inv(pr, grammar, input, Gll.productionsOf(grammar, start, 0n, 0n), s0, ({==}, (Unit{}, {==}))))

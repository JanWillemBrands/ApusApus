import Base
import ./LEMMAS.bend as Lemma
import ./CORE.bend as Core
import ./GLL.bend as Gll
import ./GUARD.bend as Guard
import ./RIVAL.bend as R
import ./PREFER.bend as P
import ./RUN.bend as Run
import ./PROOF_GLL.bend as G
import ./PROOF_COUNT.bend as C
import ./PROOF_RUN.bend as RN
import ./PROOF_WITNESS.bend as WC
import ./PROOF_WSOUND.bend as WS
import ./PROOF_DECIDE.bend as D
import ./PROOF_SPELL.bend as S
import ./PROOF_RIVAL_GROW.bend as RG

# THE RIVAL'S CERTIFICATE IS SOUND (RIVAL.bend, PREFER.bend): every grown segment's forest
# reads its prefix of items from its start to its end, and every step of it in its node is
# answered Yes by phase 1. So the forest of a segment that completes m is a certificate that
# passes `certWith`, and phase 2's rival verdict is decided whenever phase 1 decides.

# ======== ALL YES ========

law ay_left:
  for a: +List<Core.Bsr>
  for +b: +List<Core.Bsr>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +input: +List<Nat>
  for +h: {P.allYes(List.append(&2, Core.Bsr, a, b), fuel, grammar, gmarks, input) == True{} : Bool}
  {P.allYes(a, fuel, grammar, gmarks, input) == True{} : Bool}

def ay_left(a, b, fuel, grammar, gmarks, input, h):
  match a:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Lemma.and_true_intro(Guard.isYes(Guard.stepTri(fuel, grammar, gmarks, input, x)), P.allYes(rest, fuel, grammar, gmarks, input), Lemma.and_true_left(Guard.isYes(Guard.stepTri(fuel, grammar, gmarks, input, x)), P.allYes(List.append(&2, Core.Bsr, rest, b), fuel, grammar, gmarks, input), h),
        ay_left(rest, b, fuel, grammar, gmarks, input, Lemma.and_true_right_side(Guard.isYes(Guard.stepTri(fuel, grammar, gmarks, input, x)), P.allYes(List.append(&2, Core.Bsr, rest, b), fuel, grammar, gmarks, input), h)))

law ay_right:
  for a: +List<Core.Bsr>
  for +b: +List<Core.Bsr>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +input: +List<Nat>
  for +h: {P.allYes(List.append(&2, Core.Bsr, a, b), fuel, grammar, gmarks, input) == True{} : Bool}
  {P.allYes(b, fuel, grammar, gmarks, input) == True{} : Bool}

def ay_right(a, b, fuel, grammar, gmarks, input, h):
  match a:
    case Nil{}:
      h
    case Con{+x, +rest}:
      ay_right(rest, b, fuel, grammar, gmarks, input, Lemma.and_true_right_side(Guard.isYes(Guard.stepTri(fuel, grammar, gmarks, input, x)), P.allYes(List.append(&2, Core.Bsr, rest, b), fuel, grammar, gmarks, input), h))

law ay_app:
  for a: +List<Core.Bsr>
  for +b: +List<Core.Bsr>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +input: +List<Nat>
  for +ha: {P.allYes(a, fuel, grammar, gmarks, input) == True{} : Bool}
  for +hb: {P.allYes(b, fuel, grammar, gmarks, input) == True{} : Bool}
  {P.allYes(List.append(&2, Core.Bsr, a, b), fuel, grammar, gmarks, input) == True{} : Bool}

def ay_app(a, b, fuel, grammar, gmarks, input, ha, hb):
  match a:
    case Nil{}:
      hb
    case Con{+x, +rest}:
      Lemma.and_true_intro(Guard.isYes(Guard.stepTri(fuel, grammar, gmarks, input, x)), P.allYes(List.append(&2, Core.Bsr, rest, b), fuel, grammar, gmarks, input), Lemma.and_true_left(Guard.isYes(Guard.stepTri(fuel, grammar, gmarks, input, x)), P.allYes(rest, fuel, grammar, gmarks, input), ha),
        ay_app(rest, b, fuel, grammar, gmarks, input, Lemma.and_true_right_side(Guard.isYes(Guard.stepTri(fuel, grammar, gmarks, input, x)), P.allYes(rest, fuel, grammar, gmarks, input), ha), hb))

def yes_succ(+q: Nat, +d: Nat, +n: Nat, +ks: Nat, +k: Nat, +j: Nat, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>,
  +h: {Guard.isYes(Guard.stepTri(fuel, grammar, gmarks, input, Core.Bsr{q, 1n+Nat.add(d, 1n+n), ks, k, j})) == True{} : Bool})
  -> {Guard.isYes(Guard.stepTri(fuel, grammar, gmarks, input, Core.Bsr{q, 1n+Nat.add(1n+d, n), ks, k, j})) == True{} : Bool}:
  %Lemma.add_succ_right(d, n) : {Guard.isYes(Guard.stepTri(fuel, grammar, gmarks, input, Core.Bsr{q, 1n+_, ks, k, j})) == True{} : Bool}
  h

def yes_zero(+q: Nat, +d: Nat, +ks: Nat, +k: Nat, +j: Nat, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>,
  +h: {Guard.isYes(Guard.stepTri(fuel, grammar, gmarks, input, Core.Bsr{q, 1n+Nat.add(d, 0n), ks, k, j})) == True{} : Bool})
  -> {Guard.isYes(Guard.stepTri(fuel, grammar, gmarks, input, Core.Bsr{q, 1n+d, ks, k, j})) == True{} : Bool}:
  %Lemma.add_zero_right(d) : {Guard.isYes(Guard.stepTri(fuel, grammar, gmarks, input, Core.Bsr{q, 1n+_, ks, k, j})) == True{} : Bool}
  h

# A node's own steps with a child added at the end: the old ones and the new child's.
law ay_own_snoc:
  for +q: Nat
  for f: +List<Core.Tree>
  for +t: Core.Tree
  for +d: Nat
  for +ks: Nat
  for +k: Nat
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +input: +List<Nat>
  for +h1: {P.allYes(WC.ownNE(q, f, d, ks, k), fuel, grammar, gmarks, input) == True{} : Bool}
  for +h2: {Guard.isYes(Guard.stepTri(fuel, grammar, gmarks, input, Core.Bsr{q, 1n+Nat.add(d, List.length(&2, Core.Tree, f)), ks, WS.endW(f, k), Nat.add(WS.endW(f, k), Core.width(t))})) == True{} : Bool}
  {P.allYes(WC.ownNE(q, List.append(&2, Core.Tree, f, [t]), d, ks, k), fuel, grammar, gmarks, input) == True{} : Bool}

def ay_own_snoc(q, f, t, d, ks, k, fuel, grammar, gmarks, input, h1, h2):
  match f:
    case Nil{}:
      Lemma.and_true_intro(Guard.isYes(Guard.stepTri(fuel, grammar, gmarks, input, Core.Bsr{q, 1n+d, ks, k, Nat.add(k, Core.width(t))})), True{}, yes_zero(q, d, ks, k, Nat.add(k, Core.width(t)), fuel, grammar, gmarks, input, h2), {==})
    case Con{+s, +rest}:
      +far = Nat.add(k, Core.width(s))
      +b = {Core.Bsr{q, 1n+d, ks, k, far} : Core.Bsr}
      Lemma.and_true_intro(Guard.isYes(Guard.stepTri(fuel, grammar, gmarks, input, b)), P.allYes(WC.ownNE(q, List.append(&2, Core.Tree, rest, [t]), 1n+d, ks, far), fuel, grammar, gmarks, input),
        Lemma.and_true_left(Guard.isYes(Guard.stepTri(fuel, grammar, gmarks, input, b)), P.allYes(WC.ownNE(q, rest, 1n+d, ks, far), fuel, grammar, gmarks, input), h1),
        ay_own_snoc(q, rest, t, 1n+d, ks, far, fuel, grammar, gmarks, input, Lemma.and_true_right_side(Guard.isYes(Guard.stepTri(fuel, grammar, gmarks, input, b)), P.allYes(WC.ownNE(q, rest, 1n+d, ks, far), fuel, grammar, gmarks, input), h1),
          yes_succ(q, d, List.length(&2, Core.Tree, rest), ks, WS.endW(rest, far), Nat.add(WS.endW(rest, far), Core.width(t)), fuel, grammar, gmarks, input, h2)))

# A forest's steps with a tree added at the end: the old ones and the new tree's.
law ay_steps_snoc:
  for f: +List<Core.Tree>
  for +t: Core.Tree
  for +k: Nat
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +input: +List<Nat>
  for +h1: {P.allYes(Core.steps(f, k), fuel, grammar, gmarks, input) == True{} : Bool}
  for +h2: {P.allYes(Core.steps([t], G.endOf(f, k)), fuel, grammar, gmarks, input) == True{} : Bool}
  {P.allYes(Core.steps(List.append(&2, Core.Tree, f, [t]), k), fuel, grammar, gmarks, input) == True{} : Bool}

def ay_steps_snoc(f, t, k, fuel, grammar, gmarks, input, h1, h2):
  match f:
    case Nil{}:
      h2
    case Con{Core.Leaf{+a}, +ts}:
      ay_steps_snoc(ts, t, 1n+k, fuel, grammar, gmarks, input, h1, h2)
    case Con{Core.Node{+q, +ch}, +ts}:
      +o = Core.own(q, ch, 0n, k, k)
      +w = Nat.add(k, Core.width(Core.Node{q, ch}))
      +rest = List.append(&2, Core.Bsr, Core.steps(ch, k), Core.steps(ts, w))
      +hr = ay_right(o, rest, fuel, grammar, gmarks, input, h1)
      ay_app(o, List.append(&2, Core.Bsr, Core.steps(ch, k), Core.steps(List.append(&2, Core.Tree, ts, [t]), w)), fuel, grammar, gmarks, input, ay_left(o, rest, fuel, grammar, gmarks, input, h1),
        ay_app(Core.steps(ch, k), Core.steps(List.append(&2, Core.Tree, ts, [t]), w), fuel, grammar, gmarks, input, ay_left(Core.steps(ch, k), Core.steps(ts, w), fuel, grammar, gmarks, input, hr),
          ay_steps_snoc(ts, t, w, fuel, grammar, gmarks, input, ay_right(Core.steps(ch, k), Core.steps(ts, w), fuel, grammar, gmarks, input, hr), h2)))

# ======== WHAT A SOUND SEGMENT IS ========

# Segment (q, ks, d, e) with forest f: f reads the first d items of q from ks to e, and
# every step of f in q's node is answered Yes.
def segOk(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, s: R.Seg) -> Bool:
  match s:
    case R.Seg{+q, +ks, +d, +e, +f}:
      Bool.and(Core.reads(f, grammar, WS.takeN(d, Core.rhsOf(grammar, q)), input, ks),
        Bool.and(Nat.is_eq(G.endOf(f, ks), e),
          Bool.and(Nat.is_eq(List.length(&2, Core.Tree, f), d), P.allYes(List.append(&2, Core.Bsr, WC.ownNE(q, f, 0n, ks, ks), Core.steps(f, ks)), fuel, grammar, gmarks, input))))

def segsOk(segs: +List<R.Seg>, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>) -> Bool:
  match segs:
    case Nil{}:
      True{}
    case Con{+s, rest}:
      Bool.and(segOk(fuel, grammar, gmarks, input, s), segsOk(rest, fuel, grammar, gmarks, input))

def symOf(m: Maybe<&2, Core.Sym>, +dflt: Core.Sym) -> Core.Sym:
  match m:
    case Some{+y}:
      y
    case None{}:
      dflt

# The item after d: the rest of the right side from d starts with it.
law nth_to_drop:
  for items: +List<Core.Sym>
  for d: Nat
  for +y: Core.Sym
  for +h: {Gll.nthSym(items, d) == Some{y} : Maybe<&2, Core.Sym>}
  {G.dropFrom(d, items) == y <> G.dropFrom(1n+d, items) : +List<Core.Sym>}

def nth_to_drop(items, d, y, h):
  match items d:
    case Nil{} +d0:
      Empty.absurd({G.dropFrom(d0, []) == y <> G.dropFrom(1n+d0, []) : +List<Core.Sym>}, Lemma.false_is_not_true(Equal.cong(Maybe<&2, Core.Sym>, Bool, v => RN.isSome(v), None{}, Some{y}, h)))
    case Con{+x, +xs} 0n:
      %Equal.cong(Maybe<&2, Core.Sym>, Core.Sym, v => symOf(v, x), Some{x}, Some{y}, h) : {x <> xs == _ <> xs : +List<Core.Sym>}
      {==}
    case Con{+x, +xs} 1n+(+m):
      nth_to_drop(xs, m, y, h)

law len_snoc:
  for f: +List<Core.Tree>
  for +t: Core.Tree
  {List.length(&2, Core.Tree, List.append(&2, Core.Tree, f, [t])) == 1n+List.length(&2, Core.Tree, f) : Nat}

def len_snoc(f, t):
  match f:
    case Nil{}:
      {==}
    case Con{+s, +rest}:
      %len_snoc(rest, t) : {1n+List.length(&2, Core.Tree, List.append(&2, Core.Tree, rest, [t])) == 1n+_ : Nat}
      {==}

def eq_is(+a: Nat, +b: Nat, +e: {a == b : Nat}) -> {Nat.is_eq(a, b) == True{} : Bool}:
  %e : {Nat.is_eq(a, _) == True{} : Bool}
  Lemma.nat_eq_refl(a)

def yes_at(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +q: Nat, +ks: Nat, +a: Nat, +b: Nat, +c: Nat, +a2: Nat, +b2: Nat, +c2: Nat, +ea: {a == a2 : Nat}, +eb: {b == b2 : Nat}, +ec: {c == c2 : Nat},
  +h: {Guard.isYes(Guard.stepTri(fuel, grammar, gmarks, input, Core.Bsr{q, a2, ks, b2, c2})) == True{} : Bool}) -> {Guard.isYes(Guard.stepTri(fuel, grammar, gmarks, input, Core.Bsr{q, a, ks, b, c})) == True{} : Bool}:
  %Equal.sym(Nat, a, a2, ea) : {Guard.isYes(Guard.stepTri(fuel, grammar, gmarks, input, Core.Bsr{q, _, ks, b, c})) == True{} : Bool}
  %Equal.sym(Nat, b, b2, eb) : {Guard.isYes(Guard.stepTri(fuel, grammar, gmarks, input, Core.Bsr{q, a2, ks, _, c})) == True{} : Bool}
  %Equal.sym(Nat, c, c2, ec) : {Guard.isYes(Guard.stepTri(fuel, grammar, gmarks, input, Core.Bsr{q, a2, ks, b2, _})) == True{} : Bool}
  h

def reads_at(+t: Core.Tree, +y: Core.Sym, +grammar: +List<Core.Production>, +input: +List<Nat>, +a: Nat, +b: Nat, +e: {a == b : Nat},
  +h: {Core.reads([t], grammar, [y], input, b) == True{} : Bool}) -> {Core.reads([t], grammar, [y], input, a) == True{} : Bool}:
  %Equal.sym(Nat, a, b, e) : {Core.reads([t], grammar, [y], input, _) == True{} : Bool}
  h

def ay_at(+t: Core.Tree, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +a: Nat, +b: Nat, +e: {a == b : Nat},
  +h: {P.allYes(Core.steps([t], b), fuel, grammar, gmarks, input) == True{} : Bool}) -> {P.allYes(Core.steps([t], a), fuel, grammar, gmarks, input) == True{} : Bool}:
  %Equal.sym(Nat, a, b, e) : {P.allYes(Core.steps([t], _), fuel, grammar, gmarks, input) == True{} : Bool}
  h

def reads_take(+f: +List<Core.Tree>, +grammar: +List<Core.Production>, +input: +List<Nat>, +ks: Nat, +d: Nat, +items: +List<Core.Sym>, +y: Core.Sym,
  +ie: {G.dropFrom(d, items) == y <> G.dropFrom(1n+d, items) : +List<Core.Sym>},
  +h: {Core.reads(f, grammar, List.append(&2, Core.Sym, WS.takeN(d, items), [y]), input, ks) == True{} : Bool})
  -> {Core.reads(f, grammar, WS.takeN(1n+d, items), input, ks) == True{} : Bool}:
  %Equal.sym(+List<Core.Sym>, WS.takeN(1n+d, items), List.append(&2, Core.Sym, WS.takeN(d, items), [y]), WS.take_snoc(d, items, y, G.dropFrom(1n+d, items), ie)) : {Core.reads(f, grammar, _, input, ks) == True{} : Bool}
  h

def end_to(+f: +List<Core.Tree>, +t: Core.Tree, +ks: Nat, +k: Nat, +e2: Nat, +ek: {G.endOf(f, ks) == k : Nat}, +et: {G.endOf([t], k) == e2 : Nat})
  -> {G.endOf(List.append(&2, Core.Tree, f, [t]), ks) == e2 : Nat}:
  %Equal.sym(Nat, G.endOf(List.append(&2, Core.Tree, f, [t]), ks), G.endOf([t], G.endOf(f, ks)), WS.end_snoc(f, t, ks)) : {_ == e2 : Nat}
  %Equal.sym(Nat, G.endOf(f, ks), k, ek) : {G.endOf([t], _) == e2 : Nat}
  et

def len_to(+f: +List<Core.Tree>, +t: Core.Tree, +d: Nat, +ed: {List.length(&2, Core.Tree, f) == d : Nat})
  -> {List.length(&2, Core.Tree, List.append(&2, Core.Tree, f, [t])) == 1n+d : Nat}:
  Equal.trans(Nat, List.length(&2, Core.Tree, List.append(&2, Core.Tree, f, [t])), 1n+List.length(&2, Core.Tree, f), 1n+d, len_snoc(f, t),
    Equal.cong(Nat, Nat, v => 1n+v, List.length(&2, Core.Tree, f), d, ed))

# A sound prefix with one more tree for the next item: a sound prefix one item longer.
def snoc_ok(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +f: +List<Core.Tree>, +t: Core.Tree, +y: Core.Sym, +e2: Nat,
  +ei: {Gll.nthSym(Core.rhsOf(grammar, q), d) == Some{y} : Maybe<&2, Core.Sym>},
  +hp: {segOk(fuel, grammar, gmarks, input, R.Seg{q, ks, d, k, f}) == True{} : Bool},
  +hr: {Core.reads([t], grammar, [y], input, k) == True{} : Bool},
  +hy: {P.allYes(Core.steps([t], k), fuel, grammar, gmarks, input) == True{} : Bool},
  +he: {G.endOf([t], k) == e2 : Nat},
  +hw: {Nat.add(k, Core.width(t)) == e2 : Nat},
  +hs: {Guard.isYes(Guard.stepTri(fuel, grammar, gmarks, input, Core.Bsr{q, 1n+d, ks, k, e2})) == True{} : Bool})
  -> {segOk(fuel, grammar, gmarks, input, R.Seg{q, ks, 1n+d, e2, List.append(&2, Core.Tree, f, [t])}) == True{} : Bool}:
  +RD = {Core.reads(f, grammar, WS.takeN(d, Core.rhsOf(grammar, q)), input, ks) : Bool}
  +EN = {Nat.is_eq(G.endOf(f, ks), k) : Bool}
  +LN = {Nat.is_eq(List.length(&2, Core.Tree, f), d) : Bool}
  +AY = {P.allYes(List.append(&2, Core.Bsr, WC.ownNE(q, f, 0n, ks, ks), Core.steps(f, ks)), fuel, grammar, gmarks, input) : Bool}
  +r1 = Lemma.and_true_left(RD, Bool.and(EN, Bool.and(LN, AY)), hp)
  +r2 = Lemma.and_true_right_side(RD, Bool.and(EN, Bool.and(LN, AY)), hp)
  +ek = Lemma.nat_eq_sound(G.endOf(f, ks), k, Lemma.and_true_left(EN, Bool.and(LN, AY), r2))
  +r3 = Lemma.and_true_right_side(EN, Bool.and(LN, AY), r2)
  +ed = Lemma.nat_eq_sound(List.length(&2, Core.Tree, f), d, Lemma.and_true_left(LN, AY, r3))
  +ay = Lemma.and_true_right_side(LN, AY, r3)
  +f2 = List.append(&2, Core.Tree, f, [t])
  +ie = nth_to_drop(Core.rhsOf(grammar, q), d, y, ei)
  +rd = reads_take(f2, grammar, input, ks, d, Core.rhsOf(grammar, q), y, ie,
    WS.reads_snoc(f, WS.takeN(d, Core.rhsOf(grammar, q)), grammar, input, ks, t, y, r1, reads_at(t, y, grammar, input, G.endOf(f, ks), k, ek, hr)))
  +ew = Equal.trans(Nat, WS.endW(f, ks), G.endOf(f, ks), k, WS.end_w(f, ks), ek)
  +own = WC.ownNE(q, f, 0n, ks, ks)
  +ns = yes_at(fuel, grammar, gmarks, input, q, ks, 1n+List.length(&2, Core.Tree, f), WS.endW(f, ks), Nat.add(WS.endW(f, ks), Core.width(t)), 1n+d, k, e2,
    Equal.cong(Nat, Nat, v => 1n+v, List.length(&2, Core.Tree, f), d, ed), ew,
    Equal.trans(Nat, Nat.add(WS.endW(f, ks), Core.width(t)), Nat.add(k, Core.width(t)), e2, Equal.cong(Nat, Nat, v => Nat.add(v, Core.width(t)), WS.endW(f, ks), k, ew), hw), hs)
  +ay2 = ay_app(WC.ownNE(q, f2, 0n, ks, ks), Core.steps(f2, ks), fuel, grammar, gmarks, input,
    ay_own_snoc(q, f, t, 0n, ks, ks, fuel, grammar, gmarks, input, ay_left(own, Core.steps(f, ks), fuel, grammar, gmarks, input, ay), ns),
    ay_steps_snoc(f, t, ks, fuel, grammar, gmarks, input, ay_right(own, Core.steps(f, ks), fuel, grammar, gmarks, input, ay), ay_at(t, fuel, grammar, gmarks, input, G.endOf(f, ks), k, ek, hy)))
  Lemma.and_true_intro(Core.reads(f2, grammar, WS.takeN(1n+d, Core.rhsOf(grammar, q)), input, ks), Bool.and(Nat.is_eq(G.endOf(f2, ks), e2), Bool.and(Nat.is_eq(List.length(&2, Core.Tree, f2), 1n+d), P.allYes(List.append(&2, Core.Bsr, WC.ownNE(q, f2, 0n, ks, ks), Core.steps(f2, ks)), fuel, grammar, gmarks, input))), rd,
    Lemma.and_true_intro(Nat.is_eq(G.endOf(f2, ks), e2), Bool.and(Nat.is_eq(List.length(&2, Core.Tree, f2), 1n+d), P.allYes(List.append(&2, Core.Bsr, WC.ownNE(q, f2, 0n, ks, ks), Core.steps(f2, ks)), fuel, grammar, gmarks, input)),
      eq_is(G.endOf(f2, ks), e2, end_to(f, t, ks, k, e2, ek, he)),
      Lemma.and_true_intro(Nat.is_eq(List.length(&2, Core.Tree, f2), 1n+d), P.allYes(List.append(&2, Core.Bsr, WC.ownNE(q, f2, 0n, ks, ks), Core.steps(f2, ks)), fuel, grammar, gmarks, input),
        eq_is(List.length(&2, Core.Tree, f2), 1n+d, len_to(f, t, d, ed)), ay2)))

# A seed: nothing read yet.
def seed_ok(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +base: Nat, +k: Nat) -> {segOk(fuel, grammar, gmarks, input, R.Seg{base, k, 0n, k, []}) == True{} : Bool}:
  Lemma.and_true_intro(True{}, Bool.and(Nat.is_eq(k, k), Bool.and(True{}, True{})), {==},
    Lemma.and_true_intro(Nat.is_eq(k, k), Bool.and(True{}, True{}), Lemma.nat_eq_refl(k), {==}))

# A token read after a sound prefix.
def leaf_ok(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +f: +List<Core.Tree>, +t: Nat,
  +ei: {Gll.nthSym(Core.rhsOf(grammar, q), d) == Some{Core.Terminal{t}} : Maybe<&2, Core.Sym>},
  +hp: {segOk(fuel, grammar, gmarks, input, R.Seg{q, ks, d, k, f}) == True{} : Bool},
  +ht: {Core.tokIs(Core.tokAt(input, k), t) == True{} : Bool},
  +hs: {Guard.isYes(Guard.stepTri(fuel, grammar, gmarks, input, Core.Bsr{q, 1n+d, ks, k, 1n+k})) == True{} : Bool})
  -> {segOk(fuel, grammar, gmarks, input, R.Seg{q, ks, 1n+d, 1n+k, List.append(&2, Core.Tree, f, [Core.Leaf{t}])}) == True{} : Bool}:
  snoc_ok(fuel, grammar, gmarks, input, q, ks, d, k, f, Core.Leaf{t}, Core.Terminal{t}, 1n+k, ei, hp,
    Lemma.and_true_intro(Nat.is_eq(t, t), Bool.and(Core.tokIs(Core.tokAt(input, k), t), True{}), Lemma.nat_eq_refl(t), Lemma.and_true_intro(Core.tokIs(Core.tokAt(input, k), t), True{}, ht, {==})),
    {==}, {==}, Lemma.add_one_right(k), hs)

# ======== A COMPLETED NODE ========

def end_yes_nil(rhs: +List<Core.Sym>, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +p: Nat, +k: Nat, +e: Nat, +hr: {Core.reads([], grammar, rhs, input, k) == True{} : Bool},
  +hend: {Guard.isYes(R.endTri(rhs, fuel, grammar, gmarks, input, p, k, e)) == True{} : Bool}, +ec: {k == e : Nat})
  -> {Guard.isYes(Guard.stepTri(fuel, grammar, gmarks, input, Core.Bsr{p, 0n, k, k, k})) == True{} : Bool}:
  match rhs:
    case Nil{}:
      yes_at(fuel, grammar, gmarks, input, p, k, 0n, k, k, 0n, k, e, {==}, {==}, ec, hend)
    case Con{+s, +rest}:
      Empty.absurd({Guard.isYes(Guard.stepTri(fuel, grammar, gmarks, input, Core.Bsr{p, 0n, k, k, k})) == True{} : Bool}, Lemma.false_is_not_true(hr))

def child_yes(fp: +List<Core.Tree>, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +p: Nat, +k: Nat, +e: Nat, +rd: {Core.reads(fp, grammar, Core.rhsOf(grammar, p), input, k) == True{} : Bool},
  +ec: {G.endOf(fp, k) == e : Nat}, +hend: {Guard.isYes(R.endTri(Core.rhsOf(grammar, p), fuel, grammar, gmarks, input, p, k, e)) == True{} : Bool},
  +ay: {P.allYes(List.append(&2, Core.Bsr, WC.ownNE(p, fp, 0n, k, k), Core.steps(fp, k)), fuel, grammar, gmarks, input) == True{} : Bool})
  -> {P.allYes(Core.steps([Core.Node{p, fp}], k), fuel, grammar, gmarks, input) == True{} : Bool}:
  match fp:
    case Nil{}:
      Lemma.and_true_intro(Guard.isYes(Guard.stepTri(fuel, grammar, gmarks, input, Core.Bsr{p, 0n, k, k, k})), True{}, end_yes_nil(Core.rhsOf(grammar, p), fuel, grammar, gmarks, input, p, k, e, rd, hend, ec), {==})
    case Con{+t1, +r1}:
      +own = WC.ownNE(p, t1 <> r1, 0n, k, k)
      +st = Core.steps(t1 <> r1, k)
      %Equal.sym(+List<Core.Bsr>, Core.own(p, t1 <> r1, 0n, k, k), own, WC.own_first(p, t1, r1, 0n, k, k)) : {P.allYes(List.append(&2, Core.Bsr, _, List.append(&2, Core.Bsr, st, Core.steps([], Nat.add(k, Core.width(Core.Node{p, t1 <> r1}))))), fuel, grammar, gmarks, input) == True{} : Bool}
      ay_app(own, List.append(&2, Core.Bsr, st, []), fuel, grammar, gmarks, input, ay_left(own, st, fuel, grammar, gmarks, input, ay), ay_app(st, [], fuel, grammar, gmarks, input, ay_right(own, st, fuel, grammar, gmarks, input, ay), {==}))

# A sound completed segment of p after a sound prefix: the prefix reads the node of p.
def node_ok(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +f: +List<Core.Tree>, +p: Nat, +x: Nat, +need: Core.Need, +e: Nat, +fp: +List<Core.Tree>,
  +ei: {Gll.nthSym(Core.rhsOf(grammar, q), d) == Some{Core.Nonterminal{x, need}} : Maybe<&2, Core.Sym>},
  +hp: {segOk(fuel, grammar, gmarks, input, R.Seg{q, ks, d, k, f}) == True{} : Bool},
  +hc: {segOk(fuel, grammar, gmarks, input, R.Seg{p, k, List.length(&2, Core.Sym, Core.rhsOf(grammar, p)), e, fp}) == True{} : Bool},
  +hl: {Core.lhsIs(grammar, p, x) == True{} : Bool},
  +hn: {Gll.needHolds(need, k, e) == True{} : Bool},
  +hend: {Guard.isYes(R.endTri(Core.rhsOf(grammar, p), fuel, grammar, gmarks, input, p, k, e)) == True{} : Bool},
  +hs: {Guard.isYes(Guard.stepTri(fuel, grammar, gmarks, input, Core.Bsr{q, 1n+d, ks, k, e})) == True{} : Bool})
  -> {segOk(fuel, grammar, gmarks, input, R.Seg{q, ks, 1n+d, e, List.append(&2, Core.Tree, f, [Core.Node{p, fp}])}) == True{} : Bool}:
  +RD = {Core.reads(fp, grammar, WS.takeN(List.length(&2, Core.Sym, Core.rhsOf(grammar, p)), Core.rhsOf(grammar, p)), input, k) : Bool}
  +EN = {Nat.is_eq(G.endOf(fp, k), e) : Bool}
  +LN = {Nat.is_eq(List.length(&2, Core.Tree, fp), List.length(&2, Core.Sym, Core.rhsOf(grammar, p))) : Bool}
  +AY = {P.allYes(List.append(&2, Core.Bsr, WC.ownNE(p, fp, 0n, k, k), Core.steps(fp, k)), fuel, grammar, gmarks, input) : Bool}
  +r2 = Lemma.and_true_right_side(RD, Bool.and(EN, Bool.and(LN, AY)), hc)
  +rd = WS.reads_all(grammar, input, fp, Core.rhsOf(grammar, p), k, Lemma.and_true_left(RD, Bool.and(EN, Bool.and(LN, AY)), hc))
  +ec = Lemma.nat_eq_sound(G.endOf(fp, k), e, Lemma.and_true_left(EN, Bool.and(LN, AY), r2))
  +ay = Lemma.and_true_right_side(LN, AY, Lemma.and_true_right_side(EN, Bool.and(LN, AY), r2))
  +w = Core.width(Core.Node{p, fp})
  +hw = Equal.trans(Nat, Nat.add(k, w), G.endOf(fp, k), e, Equal.sym(Nat, G.endOf(fp, k), Nat.add(k, w), G.end_node(p, fp, k)), ec)
  +nk = WS.need_ok(need, k, w, WS.need_to(need, k, e, Nat.add(k, w), hw, hn))
  +head = {Bool.and(Core.lhsIs(grammar, p, x), Core.needOk(need, w)) : Bool}
  +own = {Bool.and(head, Core.reads(fp, grammar, Core.rhsOf(grammar, p), input, k)) : Bool}
  +hr = Lemma.and_true_intro(own, True{}, Lemma.and_true_intro(head, Core.reads(fp, grammar, Core.rhsOf(grammar, p), input, k), Lemma.and_true_intro(Core.lhsIs(grammar, p, x), Core.needOk(need, w), hl, nk), rd), {==})
  snoc_ok(fuel, grammar, gmarks, input, q, ks, d, k, f, Core.Node{p, fp}, Core.Nonterminal{x, need}, e, ei, hp, hr, child_yes(fp, fuel, grammar, gmarks, input, p, k, e, rd, ec, hend, ay), hw, hw, hs)

# ======== THE PRODUCTIONS FROM base ON ========

def dropP(n: Nat, prods: +List<Core.Production>) -> +List<Core.Production>:
  match n prods:
    case 0n _:
      prods
    case 1n+m Nil{}:
      []
    case 1n+m Con{p, rest}:
      dropP(m, rest)

def headLhs(ps: +List<Core.Production>) -> Nat:
  match ps:
    case Nil{}:
      0n
    case Con{Core.Production{+l, r}, rest}:
      l

def isNilP(ps: +List<Core.Production>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Con{p, rest}:
      False{}

law lhs_from_drop:
  for grammar: +List<Core.Production>
  for base: Nat
  for +lhs: Nat
  for +rhs: +List<Core.Sym>
  for +rest: +List<Core.Production>
  for +x: Nat
  for +e: {dropP(base, grammar) == Core.Production{lhs, rhs} <> rest : +List<Core.Production>}
  for +h: {Nat.is_eq(lhs, x) == True{} : Bool}
  {Core.lhsIs(grammar, base, x) == True{} : Bool}

def lhs_from_drop(grammar, base, lhs, rhs, rest, x, e, h):
  match grammar base:
    case Nil{} 0n:
      Empty.absurd({Core.lhsIs([], 0n, x) == True{} : Bool}, Lemma.true_is_not_false(Equal.cong(+List<Core.Production>, Bool, v => isNilP(v), [], Core.Production{lhs, rhs} <> rest, e)))
    case Con{Core.Production{+l2, +r2}, +rest0} 0n:
      %Equal.sym(Nat, l2, lhs, Equal.cong(+List<Core.Production>, Nat, v => headLhs(v), Core.Production{l2, r2} <> rest0, Core.Production{lhs, rhs} <> rest, e)) : {Nat.is_eq(_, x) == True{} : Bool}
      h
    case Nil{} 1n+(+m):
      Empty.absurd({Core.lhsIs([], 1n+m, x) == True{} : Bool}, Lemma.true_is_not_false(Equal.cong(+List<Core.Production>, Bool, v => isNilP(v), [], Core.Production{lhs, rhs} <> rest, e)))
    case Con{+p0, +rest0} 1n+(+m):
      lhs_from_drop(rest0, m, lhs, rhs, rest, x, e, h)

def tailP(ps: +List<Core.Production>) -> +List<Core.Production>:
  match ps:
    case Nil{}:
      []
    case Con{p, rest}:
      rest

law drop_step:
  for grammar: +List<Core.Production>
  for base: Nat
  for +p0: Core.Production
  for +rest: +List<Core.Production>
  for +e: {dropP(base, grammar) == p0 <> rest : +List<Core.Production>}
  {dropP(1n+base, grammar) == rest : +List<Core.Production>}

def drop_step(grammar, base, p0, rest, e):
  match grammar base:
    case Nil{} 0n:
      Empty.absurd({dropP(1n, []) == rest : +List<Core.Production>}, Lemma.true_is_not_false(Equal.cong(+List<Core.Production>, Bool, v => isNilP(v), [], p0 <> rest, e)))
    case Nil{} 1n+(+m):
      Empty.absurd({dropP(2n+m, []) == rest : +List<Core.Production>}, Lemma.true_is_not_false(Equal.cong(+List<Core.Production>, Bool, v => isNilP(v), [], p0 <> rest, e)))
    case Con{+g1, +gs} 0n:
      Equal.cong(+List<Core.Production>, +List<Core.Production>, v => tailP(v), g1 <> gs, p0 <> rest, e)
    case Con{+g1, +gs} 1n+(+m):
      drop_step(gs, m, p0, rest, e)

# ======== EVERY GROWN SEGMENT IS SOUND ========

law so_app:
  for a: +List<R.Seg>
  for +b: +List<R.Seg>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +input: +List<Nat>
  for +ha: {segsOk(a, fuel, grammar, gmarks, input) == True{} : Bool}
  for +hb: {segsOk(b, fuel, grammar, gmarks, input) == True{} : Bool}
  {segsOk(List.append(&2, R.Seg, a, b), fuel, grammar, gmarks, input) == True{} : Bool}

def so_app(a, b, fuel, grammar, gmarks, input, ha, hb):
  match a:
    case Nil{}:
      hb
    case Con{+s, +rest}:
      Lemma.and_true_intro(segOk(fuel, grammar, gmarks, input, s), segsOk(List.append(&2, R.Seg, rest, b), fuel, grammar, gmarks, input), Lemma.and_true_left(segOk(fuel, grammar, gmarks, input, s), segsOk(rest, fuel, grammar, gmarks, input), ha),
        so_app(rest, b, fuel, grammar, gmarks, input, Lemma.and_true_right_side(segOk(fuel, grammar, gmarks, input, s), segsOk(rest, fuel, grammar, gmarks, input), ha), hb))

def seg_if_ok(b: Bool, +s: R.Seg, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, f: {b == True{} : Bool} -> {segOk(fuel, grammar, gmarks, input, s) == True{} : Bool}) -> {segsOk(R.segIf(b, s), fuel, grammar, gmarks, input) == True{} : Bool}:
  match b:
    case True{}:
      Lemma.and_true_intro(segOk(fuel, grammar, gmarks, input, s), True{}, f({==}), {==})
    case False{}:
      {==}

def seg_to(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +p2: Nat, +k2: Nat, +d2: Nat, +e: Nat, +fp: +List<Core.Tree>, +p: Nat, +k: Nat, +d: Nat,
  +e1: {p2 == p : Nat}, +e2: {k2 == k : Nat}, +e3: {d2 == d : Nat}, +h: {segOk(fuel, grammar, gmarks, input, R.Seg{p2, k2, d2, e, fp}) == True{} : Bool})
  -> {segOk(fuel, grammar, gmarks, input, R.Seg{p, k, d, e, fp}) == True{} : Bool}:
  %e1 : {segOk(fuel, grammar, gmarks, input, R.Seg{_, k, d, e, fp}) == True{} : Bool}
  %e2 : {segOk(fuel, grammar, gmarks, input, R.Seg{p2, _, d, e, fp}) == True{} : Bool}
  %e3 : {segOk(fuel, grammar, gmarks, input, R.Seg{p2, k2, _, e, fp}) == True{} : Bool}
  h

def hit_ok(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +need: Core.Need, +p: Nat, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +f: +List<Core.Tree>, +x: Nat, +p2: Nat, +k2: Nat, +d2: Nat, +e: Nat, +fp: +List<Core.Tree>,
  +hh: {segOk(fuel, grammar, gmarks, input, R.Seg{p2, k2, d2, e, fp}) == True{} : Bool}, +hp: {segOk(fuel, grammar, gmarks, input, R.Seg{q, ks, d, k, f}) == True{} : Bool},
  +ei: {Gll.nthSym(Core.rhsOf(grammar, q), d) == Some{Core.Nonterminal{x, need}} : Maybe<&2, Core.Sym>}, +hl: {Core.lhsIs(grammar, p, x) == True{} : Bool},
  +hit: {Bool.and(Bool.and(Nat.is_eq(p2, p), Bool.and(Nat.is_eq(k2, k), Nat.is_eq(d2, List.length(&2, Core.Sym, Core.rhsOf(grammar, p))))), Bool.and(R.isYes(R.endTri(Core.rhsOf(grammar, p), fuel, grammar, gmarks, input, p, k, e)), Bool.and(Gll.needHolds(need, k, e), R.isYes(R.tri(fuel, grammar, gmarks, input, Core.Bsr{q, 1n+d, ks, k, e}))))) == True{} : Bool})
  -> {segOk(fuel, grammar, gmarks, input, R.Seg{q, ks, 1n+d, e, List.append(&2, Core.Tree, f, [Core.Node{p, fp}])}) == True{} : Bool}:
  +M = {Bool.and(Nat.is_eq(p2, p), Bool.and(Nat.is_eq(k2, k), Nat.is_eq(d2, List.length(&2, Core.Sym, Core.rhsOf(grammar, p))))) : Bool}
  +Y1 = {R.isYes(R.endTri(Core.rhsOf(grammar, p), fuel, grammar, gmarks, input, p, k, e)) : Bool}
  +NH = {Gll.needHolds(need, k, e) : Bool}
  +Y2 = {R.isYes(R.tri(fuel, grammar, gmarks, input, Core.Bsr{q, 1n+d, ks, k, e})) : Bool}
  +m = Lemma.and_true_left(M, Bool.and(Y1, Bool.and(NH, Y2)), hit)
  +r = Lemma.and_true_right_side(M, Bool.and(Y1, Bool.and(NH, Y2)), hit)
  +r2 = Lemma.and_true_right_side(Y1, Bool.and(NH, Y2), r)
  +m2 = Lemma.and_true_right_side(Nat.is_eq(p2, p), Bool.and(Nat.is_eq(k2, k), Nat.is_eq(d2, List.length(&2, Core.Sym, Core.rhsOf(grammar, p)))), m)
  +hc = seg_to(fuel, grammar, gmarks, input, p2, k2, d2, e, fp, p, k, List.length(&2, Core.Sym, Core.rhsOf(grammar, p)),
    Lemma.nat_eq_sound(p2, p, Lemma.and_true_left(Nat.is_eq(p2, p), Bool.and(Nat.is_eq(k2, k), Nat.is_eq(d2, List.length(&2, Core.Sym, Core.rhsOf(grammar, p)))), m)),
    Lemma.nat_eq_sound(k2, k, Lemma.and_true_left(Nat.is_eq(k2, k), Nat.is_eq(d2, List.length(&2, Core.Sym, Core.rhsOf(grammar, p))), m2)),
    Lemma.nat_eq_sound(d2, List.length(&2, Core.Sym, Core.rhsOf(grammar, p)), Lemma.and_true_right_side(Nat.is_eq(k2, k), Nat.is_eq(d2, List.length(&2, Core.Sym, Core.rhsOf(grammar, p))), m2)), hh)
  node_ok(fuel, grammar, gmarks, input, q, ks, d, k, f, p, x, need, e, fp, ei, hp, hc, hl, Lemma.and_true_left(NH, Y2, r2), Lemma.and_true_left(Y1, Bool.and(NH, Y2), r), Lemma.and_true_right_side(NH, Y2, r2))

law cw_ok:
  for ss: +List<R.Seg>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +input: +List<Nat>
  for +need: Core.Need
  for +p: Nat
  for +q: Nat
  for +ks: Nat
  for +d: Nat
  for +k: Nat
  for +f: +List<Core.Tree>
  for +x: Nat
  for +hss: {segsOk(ss, fuel, grammar, gmarks, input) == True{} : Bool}
  for +hp: {segOk(fuel, grammar, gmarks, input, R.Seg{q, ks, d, k, f}) == True{} : Bool}
  for +ei: {Gll.nthSym(Core.rhsOf(grammar, q), d) == Some{Core.Nonterminal{x, need}} : Maybe<&2, Core.Sym>}
  for +hl: {Core.lhsIs(grammar, p, x) == True{} : Bool}
  {segsOk(R.completeWith(ss, fuel, grammar, gmarks, input, need, p, q, ks, d, k, f), fuel, grammar, gmarks, input) == True{} : Bool}

def cw_ok(ss, fuel, grammar, gmarks, input, need, p, q, ks, d, k, f, x, hss, hp, ei, hl):
  match ss:
    case Nil{}:
      {==}
    case Con{R.Seg{+p2, +k2, +d2, +e, +fp}, +rest}:
      +hh = Lemma.and_true_left(segOk(fuel, grammar, gmarks, input, R.Seg{p2, k2, d2, e, fp}), segsOk(rest, fuel, grammar, gmarks, input), hss)
      +hit = Bool.and(Bool.and(Nat.is_eq(p2, p), Bool.and(Nat.is_eq(k2, k), Nat.is_eq(d2, List.length(&2, Core.Sym, Core.rhsOf(grammar, p))))),
        Bool.and(R.isYes(R.endTri(Core.rhsOf(grammar, p), fuel, grammar, gmarks, input, p, k, e)), Bool.and(Gll.needHolds(need, k, e), R.isYes(R.tri(fuel, grammar, gmarks, input, Core.Bsr{q, 1n+d, ks, k, e})))))
      +ns = {R.Seg{q, ks, 1n+d, e, List.append(&2, Core.Tree, f, [Core.Node{p, fp}])} : R.Seg}
      so_app(R.segIf(hit, ns), R.completeWith(rest, fuel, grammar, gmarks, input, need, p, q, ks, d, k, f), fuel, grammar, gmarks, input,
        seg_if_ok(hit, ns, fuel, grammar, gmarks, input, h => hit_ok(fuel, grammar, gmarks, input, need, p, q, ks, d, k, f, x, p2, k2, d2, e, fp, hh, hp, ei, hl, h)),
        cw_ok(rest, fuel, grammar, gmarks, input, need, p, q, ks, d, k, f, x, Lemma.and_true_right_side(segOk(fuel, grammar, gmarks, input, R.Seg{p2, k2, d2, e, fp}), segsOk(rest, fuel, grammar, gmarks, input), hss), hp, ei, hl))

def pp_ok(b: Bool, +segs: +List<R.Seg>, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +need: Core.Need, +base: Nat, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +f: +List<Core.Tree>, +x: Nat,
  +lhs: Nat, +rhs: +List<Core.Sym>, +rest: +List<Core.Production>, +eb: {Nat.is_eq(lhs, x) == b : Bool},
  +hsuf: {dropP(base, grammar) == Core.Production{lhs, rhs} <> rest : +List<Core.Production>},
  +hs: {segsOk(segs, fuel, grammar, gmarks, input) == True{} : Bool}, +hp: {segOk(fuel, grammar, gmarks, input, R.Seg{q, ks, d, k, f}) == True{} : Bool},
  +ei: {Gll.nthSym(Core.rhsOf(grammar, q), d) == Some{Core.Nonterminal{x, need}} : Maybe<&2, Core.Sym>})
  -> {segsOk(R.prodPick(b, segs, fuel, grammar, gmarks, input, need, base, q, ks, d, k, f), fuel, grammar, gmarks, input) == True{} : Bool}:
  match b:
    case True{}:
      cw_ok(segs, fuel, grammar, gmarks, input, need, base, q, ks, d, k, f, x, hs, hp, ei, lhs_from_drop(grammar, base, lhs, rhs, rest, x, hsuf, eb))
    case False{}:
      {==}

law gp_ok:
  for g: +List<Core.Production>
  for +base: Nat
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +input: +List<Nat>
  for +segs: +List<R.Seg>
  for +x: Nat
  for +need: Core.Need
  for +q: Nat
  for +ks: Nat
  for +d: Nat
  for +k: Nat
  for +f: +List<Core.Tree>
  for +hsuf: {dropP(base, grammar) == g : +List<Core.Production>}
  for +hs: {segsOk(segs, fuel, grammar, gmarks, input) == True{} : Bool}
  for +hp: {segOk(fuel, grammar, gmarks, input, R.Seg{q, ks, d, k, f}) == True{} : Bool}
  for +ei: {Gll.nthSym(Core.rhsOf(grammar, q), d) == Some{Core.Nonterminal{x, need}} : Maybe<&2, Core.Sym>}
  {segsOk(R.growProds(g, base, fuel, grammar, gmarks, input, segs, x, need, q, ks, d, k, f), fuel, grammar, gmarks, input) == True{} : Bool}

def gp_ok(g, base, fuel, grammar, gmarks, input, segs, x, need, q, ks, d, k, f, hsuf, hs, hp, ei):
  match g:
    case Nil{}:
      {==}
    case Con{Core.Production{+lhs, +rhs}, +rest}:
      +a2 = R.prodPick(Nat.is_eq(lhs, x), segs, fuel, grammar, gmarks, input, need, base, q, ks, d, k, f)
      +a3 = R.growProds(rest, 1n+base, fuel, grammar, gmarks, input, segs, x, need, q, ks, d, k, f)
      so_app(R.segIf(Nat.is_eq(lhs, x), R.Seg{base, k, 0n, k, []}), List.append(&2, R.Seg, a2, a3), fuel, grammar, gmarks, input,
        seg_if_ok(Nat.is_eq(lhs, x), R.Seg{base, k, 0n, k, []}, fuel, grammar, gmarks, input, h => seed_ok(fuel, grammar, gmarks, input, base, k)),
        so_app(a2, a3, fuel, grammar, gmarks, input, pp_ok(Nat.is_eq(lhs, x), segs, fuel, grammar, gmarks, input, need, base, q, ks, d, k, f, x, lhs, rhs, rest, {==}, hsuf, hs, hp, ei),
          gp_ok(rest, 1n+base, fuel, grammar, gmarks, input, segs, x, need, q, ks, d, k, f, drop_step(grammar, base, Core.Production{lhs, rhs}, rest, hsuf), hs, hp, ei)))

def tok_seg_ok(b: Bool, +x: Bool, +y: Bool, +s: R.Seg, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +eb: {Bool.and(x, y) == b : Bool},
  f: {x == True{} : Bool} -> {y == True{} : Bool} -> {segOk(fuel, grammar, gmarks, input, s) == True{} : Bool}) -> {segsOk(R.segIf(b, s), fuel, grammar, gmarks, input) == True{} : Bool}:
  match b:
    case True{}:
      Lemma.and_true_intro(segOk(fuel, grammar, gmarks, input, s), True{}, f(Lemma.and_true_left(x, y, eb), Lemma.and_true_right_side(x, y, eb)), {==})
    case False{}:
      {==}

def gi_sym(sym: Core.Sym, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +segs: +List<R.Seg>, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +f: +List<Core.Tree>,
  +ei: {Gll.nthSym(Core.rhsOf(grammar, q), d) == Some{sym} : Maybe<&2, Core.Sym>},
  +hs: {segsOk(segs, fuel, grammar, gmarks, input) == True{} : Bool}, +hp: {segOk(fuel, grammar, gmarks, input, R.Seg{q, ks, d, k, f}) == True{} : Bool})
  -> {segsOk(R.growItem(Some{sym}, fuel, grammar, gmarks, input, segs, q, ks, d, k, f), fuel, grammar, gmarks, input) == True{} : Bool}:
  match sym:
    case Core.Terminal{+t}:
      tok_seg_ok(Bool.and(Core.tokIs(Core.tokAt(input, k), t), R.isYes(R.tri(fuel, grammar, gmarks, input, Core.Bsr{q, 1n+d, ks, k, 1n+k}))), Core.tokIs(Core.tokAt(input, k), t), R.isYes(R.tri(fuel, grammar, gmarks, input, Core.Bsr{q, 1n+d, ks, k, 1n+k})),
        R.Seg{q, ks, 1n+d, 1n+k, List.append(&2, Core.Tree, f, [Core.Leaf{t}])}, fuel, grammar, gmarks, input, {==},
        ht => hy => leaf_ok(fuel, grammar, gmarks, input, q, ks, d, k, f, t, ei, hp, ht, hy))
    case Core.Nonterminal{+x, +need}:
      gp_ok(grammar, 0n, fuel, grammar, gmarks, input, segs, x, need, q, ks, d, k, f, {==}, hs, hp, ei)

def gi_ok(item: Maybe<&2, Core.Sym>, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +segs: +List<R.Seg>, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +f: +List<Core.Tree>,
  +ei: {Gll.nthSym(Core.rhsOf(grammar, q), d) == item : Maybe<&2, Core.Sym>},
  +hs: {segsOk(segs, fuel, grammar, gmarks, input) == True{} : Bool}, +hp: {segOk(fuel, grammar, gmarks, input, R.Seg{q, ks, d, k, f}) == True{} : Bool})
  -> {segsOk(R.growItem(item, fuel, grammar, gmarks, input, segs, q, ks, d, k, f), fuel, grammar, gmarks, input) == True{} : Bool}:
  match item:
    case Some{+sym}:
      gi_sym(sym, fuel, grammar, gmarks, input, segs, q, ks, d, k, f, ei, hs, hp)
    case None{}:
      {==}

law ga_ok:
  for ss: +List<R.Seg>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +input: +List<Nat>
  for +segs: +List<R.Seg>
  for +hss: {segsOk(ss, fuel, grammar, gmarks, input) == True{} : Bool}
  for +hs: {segsOk(segs, fuel, grammar, gmarks, input) == True{} : Bool}
  {segsOk(R.growAll(ss, fuel, grammar, gmarks, input, segs), fuel, grammar, gmarks, input) == True{} : Bool}

def ga_ok(ss, fuel, grammar, gmarks, input, segs, hss, hs):
  match ss:
    case Nil{}:
      {==}
    case Con{R.Seg{+q, +ks, +d, +k, +f}, +rest}:
      so_app(R.growItem(Gll.nthSym(Core.rhsOf(grammar, q), d), fuel, grammar, gmarks, input, segs, q, ks, d, k, f), R.growAll(rest, fuel, grammar, gmarks, input, segs), fuel, grammar, gmarks, input,
        gi_ok(Gll.nthSym(Core.rhsOf(grammar, q), d), fuel, grammar, gmarks, input, segs, q, ks, d, k, f, {==}, hs, Lemma.and_true_left(segOk(fuel, grammar, gmarks, input, R.Seg{q, ks, d, k, f}), segsOk(rest, fuel, grammar, gmarks, input), hss)),
        ga_ok(rest, fuel, grammar, gmarks, input, segs, Lemma.and_true_right_side(segOk(fuel, grammar, gmarks, input, R.Seg{q, ks, d, k, f}), segsOk(rest, fuel, grammar, gmarks, input), hss), hs))

def pick_ok(have: Bool, +s: R.Seg, +segs: +List<R.Seg>, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +h1: {segOk(fuel, grammar, gmarks, input, s) == True{} : Bool}, +hs: {segsOk(segs, fuel, grammar, gmarks, input) == True{} : Bool})
  -> {segsOk(R.addPick(have, s, segs), fuel, grammar, gmarks, input) == True{} : Bool}:
  match have:
    case True{}:
      hs
    case False{}:
      so_app(segs, [s], fuel, grammar, gmarks, input, hs, Lemma.and_true_intro(segOk(fuel, grammar, gmarks, input, s), True{}, h1, {==}))

law an_ok:
  for new: +List<R.Seg>
  for +segs: +List<R.Seg>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +input: +List<Nat>
  for +hn: {segsOk(new, fuel, grammar, gmarks, input) == True{} : Bool}
  for +hs: {segsOk(segs, fuel, grammar, gmarks, input) == True{} : Bool}
  {segsOk(R.addNew(new, segs), fuel, grammar, gmarks, input) == True{} : Bool}

def an_ok(new, segs, fuel, grammar, gmarks, input, hn, hs):
  match new:
    case Nil{}:
      hs
    case Con{R.Seg{+q, +ks, +d, +e, +f}, +rest}:
      an_ok(rest, R.addPick(R.hasSeg(q, ks, d, e, segs), R.Seg{q, ks, d, e, f}, segs), fuel, grammar, gmarks, input, Lemma.and_true_right_side(segOk(fuel, grammar, gmarks, input, R.Seg{q, ks, d, e, f}), segsOk(rest, fuel, grammar, gmarks, input), hn),
        pick_ok(R.hasSeg(q, ks, d, e, segs), R.Seg{q, ks, d, e, f}, segs, fuel, grammar, gmarks, input, Lemma.and_true_left(segOk(fuel, grammar, gmarks, input, R.Seg{q, ks, d, e, f}), segsOk(rest, fuel, grammar, gmarks, input), hn), hs))

law until_ok:
  for n: Nat
  for done: Bool
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +input: +List<Nat>
  for +segs: +List<R.Seg>
  for +hs: {segsOk(segs, fuel, grammar, gmarks, input) == True{} : Bool}
  {segsOk(R.growUntil(n, done, fuel, grammar, gmarks, input, segs), fuel, grammar, gmarks, input) == True{} : Bool}

def until_ok(n, done, fuel, grammar, gmarks, input, segs, hs):
  match n:
    case 0n:
      hs
    case 1n+(+p):
      match done:
        case True{}:
          hs
        case False{}:
          until_ok(p, R.closedAll(R.addNew(R.growAll(segs, fuel, grammar, gmarks, input, segs), segs), fuel, grammar, gmarks, input, R.addNew(R.growAll(segs, fuel, grammar, gmarks, input, segs), segs)), fuel, grammar, gmarks, input, R.addNew(R.growAll(segs, fuel, grammar, gmarks, input, segs), segs), an_ok(R.growAll(segs, fuel, grammar, gmarks, input, segs), segs, fuel, grammar, gmarks, input, ga_ok(segs, fuel, grammar, gmarks, input, segs, hs, hs), hs))

# Growth keeps every segment sound.
law grow_ok:
  for n: Nat
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +input: +List<Nat>
  for +segs: +List<R.Seg>
  for +hs: {segsOk(segs, fuel, grammar, gmarks, input) == True{} : Bool}
  {segsOk(R.grow(n, fuel, grammar, gmarks, input, segs), fuel, grammar, gmarks, input) == True{} : Bool}

def grow_ok(n, fuel, grammar, gmarks, input, segs, hs):
  until_ok(n, R.closedAll(segs, fuel, grammar, gmarks, input, segs), fuel, grammar, gmarks, input, segs, hs)

# ======== THE FIRST FOREST OF A KEY ========

def seg_to4(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +q2: Nat, +ks2: Nat, +d2: Nat, +e2: Nat, +fo: +List<Core.Tree>, +q: Nat, +ks: Nat, +d: Nat, +e: Nat,
  +e1: {q2 == q : Nat}, +ek: {ks2 == ks : Nat}, +ed: {d2 == d : Nat}, +ee: {e2 == e : Nat}, +h: {segOk(fuel, grammar, gmarks, input, R.Seg{q2, ks2, d2, e2, fo}) == True{} : Bool})
  -> {segOk(fuel, grammar, gmarks, input, R.Seg{q, ks, d, e, fo}) == True{} : Bool}:
  %e1 : {segOk(fuel, grammar, gmarks, input, R.Seg{_, ks, d, e, fo}) == True{} : Bool}
  %ek : {segOk(fuel, grammar, gmarks, input, R.Seg{q2, _, d, e, fo}) == True{} : Bool}
  %ed : {segOk(fuel, grammar, gmarks, input, R.Seg{q2, ks2, _, e, fo}) == True{} : Bool}
  %ee : {segOk(fuel, grammar, gmarks, input, R.Seg{q2, ks2, d2, _, fo}) == True{} : Bool}
  h

def key_seg(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +q: Nat, +ks: Nat, +d: Nat, +e: Nat, +q2: Nat, +ks2: Nat, +d2: Nat, +e2: Nat, +fo: +List<Core.Tree>,
  +hk: {R.keyIs(q, ks, d, e, R.Seg{q2, ks2, d2, e2, fo}) == True{} : Bool}, +h: {segOk(fuel, grammar, gmarks, input, R.Seg{q2, ks2, d2, e2, fo}) == True{} : Bool})
  -> {segOk(fuel, grammar, gmarks, input, R.Seg{q, ks, d, e, fo}) == True{} : Bool}:
  +r1 = Lemma.and_true_right_side(Nat.is_eq(q2, q), Bool.and(Nat.is_eq(ks2, ks), Bool.and(Nat.is_eq(d2, d), Nat.is_eq(e2, e))), hk)
  +r2 = Lemma.and_true_right_side(Nat.is_eq(ks2, ks), Bool.and(Nat.is_eq(d2, d), Nat.is_eq(e2, e)), r1)
  seg_to4(fuel, grammar, gmarks, input, q2, ks2, d2, e2, fo, q, ks, d, e,
    Lemma.nat_eq_sound(q2, q, Lemma.and_true_left(Nat.is_eq(q2, q), Bool.and(Nat.is_eq(ks2, ks), Bool.and(Nat.is_eq(d2, d), Nat.is_eq(e2, e))), hk)),
    Lemma.nat_eq_sound(ks2, ks, Lemma.and_true_left(Nat.is_eq(ks2, ks), Bool.and(Nat.is_eq(d2, d), Nat.is_eq(e2, e)), r1)),
    Lemma.nat_eq_sound(d2, d, Lemma.and_true_left(Nat.is_eq(d2, d), Nat.is_eq(e2, e), r2)),
    Lemma.nat_eq_sound(e2, e, Lemma.and_true_right_side(Nat.is_eq(d2, d), Nat.is_eq(e2, e), r2)), h)

def fa_pick(b: Bool, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +q: Nat, +ks: Nat, +d: Nat, +e: Nat, +q2: Nat, +ks2: Nat, +d2: Nat, +e2: Nat, +fo: +List<Core.Tree>, +rest: +List<R.Seg>,
  +eb: {R.keyIs(q, ks, d, e, R.Seg{q2, ks2, d2, e2, fo}) == b : Bool},
  +hh: {Bool.or(b, R.hasSeg(q, ks, d, e, rest)) == True{} : Bool},
  +h1: {segOk(fuel, grammar, gmarks, input, R.Seg{q2, ks2, d2, e2, fo}) == True{} : Bool},
  later: {R.hasSeg(q, ks, d, e, rest) == True{} : Bool} -> {segOk(fuel, grammar, gmarks, input, R.Seg{q, ks, d, e, R.forestAt(q, ks, d, e, rest)}) == True{} : Bool})
  -> {segOk(fuel, grammar, gmarks, input, R.Seg{q, ks, d, e, R.forestPick(b, fo, R.forestAt(q, ks, d, e, rest))}) == True{} : Bool}:
  match b:
    case True{}:
      key_seg(fuel, grammar, gmarks, input, q, ks, d, e, q2, ks2, d2, e2, fo, eb, h1)
    case False{}:
      later(hh)

# The forest handed out for a key is the forest of a sound segment with that key.
law forest_at_ok:
  for segs: +List<R.Seg>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +input: +List<Nat>
  for +q: Nat
  for +ks: Nat
  for +d: Nat
  for +e: Nat
  for +hs: {segsOk(segs, fuel, grammar, gmarks, input) == True{} : Bool}
  for +hh: {R.hasSeg(q, ks, d, e, segs) == True{} : Bool}
  {segOk(fuel, grammar, gmarks, input, R.Seg{q, ks, d, e, R.forestAt(q, ks, d, e, segs)}) == True{} : Bool}

def forest_at_ok(segs, fuel, grammar, gmarks, input, q, ks, d, e, hs, hh):
  match segs:
    case Nil{}:
      Empty.absurd({segOk(fuel, grammar, gmarks, input, R.Seg{q, ks, d, e, []}) == True{} : Bool}, Lemma.false_is_not_true(hh))
    case Con{R.Seg{+q2, +ks2, +d2, +e2, +fo}, +rest}:
      fa_pick(R.keyIs(q, ks, d, e, R.Seg{q2, ks2, d2, e2, fo}), fuel, grammar, gmarks, input, q, ks, d, e, q2, ks2, d2, e2, fo, rest, {==}, hh,
        Lemma.and_true_left(segOk(fuel, grammar, gmarks, input, R.Seg{q2, ks2, d2, e2, fo}), segsOk(rest, fuel, grammar, gmarks, input), hs),
        h2 => forest_at_ok(rest, fuel, grammar, gmarks, input, q, ks, d, e, Lemma.and_true_right_side(segOk(fuel, grammar, gmarks, input, R.Seg{q2, ks2, d2, e2, fo}), segsOk(rest, fuel, grammar, gmarks, input), hs), h2))

# ======== THE TOKENS ON THE SLICE ========

def spells_nil(w: +List<Nat>, +p: Nat, +h: {S.spells(w, [], 1n+p) == True{} : Bool}) -> {S.spells(w, [], 0n) == True{} : Bool}:
  match w:
    case Nil{}:
      {==}
    case Con{+c, +rest}:
      Empty.absurd({S.spells(c <> rest, [], 0n) == True{} : Bool}, Lemma.false_is_not_true(h))

law spells_drop:
  for +w: +List<Nat>
  for input: +List<Nat>
  for i: Nat
  for +h: {S.spells(w, input, i) == True{} : Bool}
  {S.spells(w, Lemma.dropN(i, input), 0n) == True{} : Bool}

def spells_drop(w, input, i, h):
  match input i:
    case +xs 0n:
      h
    case Nil{} 1n+(+p):
      spells_nil(w, p, h)
    case Con{+x, +xs} 1n+(+p):
      spells_drop(w, xs, p, S.spells_shift(w, x, xs, p, h))

law spells_take:
  for w: +List<Nat>
  for l: Nat
  for xs: +List<Nat>
  for +h: {S.spells(w, xs, 0n) == True{} : Bool}
  for +hl: {Nat.is_le(List.length(&2, Nat, w), l) == True{} : Bool}
  {S.spells(w, Lemma.takeN(l, xs), 0n) == True{} : Bool}

def spells_take(w, l, xs, h, hl):
  match w l xs:
    case Nil{} +l0 +xs0:
      {==}
    case Con{+c, +wr} 0n +xs0:
      Empty.absurd({S.spells(c <> wr, Lemma.takeN(0n, xs0), 0n) == True{} : Bool}, Lemma.false_is_not_true(hl))
    case Con{+c, +wr} 1n+(+lp) Nil{}:
      Empty.absurd({S.spells(c <> wr, Lemma.takeN(1n+lp, []), 0n) == True{} : Bool}, Lemma.false_is_not_true(h))
    case Con{+c, +wr} 1n+(+lp) Con{+x, +xr}:
      Lemma.and_true_intro(Core.tokIs(Some{x}, c), S.spells(wr, x <> Lemma.takeN(lp, xr), 1n), Lemma.and_true_left(Core.tokIs(Some{x}, c), S.spells(wr, x <> xr, 1n), h),
        D.spells_unshift(wr, x, Lemma.takeN(lp, xr), 0n, spells_take(wr, lp, xr, S.spells_shift(wr, x, xr, 0n, Lemma.and_true_right_side(Core.tokIs(Some{x}, c), S.spells(wr, x <> xr, 1n), h)), hl)))

law take_le:
  for l: Nat
  for xs: +List<Nat>
  {Nat.is_le(List.length(&2, Nat, Lemma.takeN(l, xs)), l) == True{} : Bool}

def take_le(l, xs):
  match l xs:
    case 0n +xs0:
      {==}
    case 1n+(+p) Nil{}:
      Lemma.zero_le(1n+p)
    case 1n+(+p) Con{+x, +xr}:
      take_le(p, xr)

law drop_len:
  for input: +List<Nat>
  for i: Nat
  for +h: {Nat.is_le(i, List.length(&2, Nat, input)) == True{} : Bool}
  {Nat.add(i, List.length(&2, Nat, Lemma.dropN(i, input))) == List.length(&2, Nat, input) : Nat}

def drop_len(input, i, h):
  match input i:
    case +xs 0n:
      {==}
    case Nil{} 1n+(+p):
      Empty.absurd({Nat.add(1n+p, List.length(&2, Nat, Lemma.dropN(1n+p, []))) == 0n : Nat}, Lemma.false_is_not_true(h))
    case Con{+x, +xs} 1n+(+p):
      Equal.cong(Nat, Nat, v => 1n+v, Nat.add(p, List.length(&2, Nat, Lemma.dropN(p, xs))), List.length(&2, Nat, xs), drop_len(xs, p, h))

law add_le_l:
  for a: Nat
  for +b: Nat
  for +c: Nat
  for +h: {Nat.is_le(b, c) == True{} : Bool}
  {Nat.is_le(Nat.add(a, b), Nat.add(a, c)) == True{} : Bool}

def add_le_l(a, b, c, h):
  match a:
    case 0n:
      h
    case 1n+(+p):
      add_le_l(p, b, c, h)

# The end of the slice from i lies within the input.
def end_bound(+input: +List<Nat>, +i: Nat, +l: Nat, +h: {Nat.is_le(i, List.length(&2, Nat, input)) == True{} : Bool})
  -> {Nat.is_le(Nat.add(i, List.length(&2, Nat, Lemma.slice(input, i, l))), List.length(&2, Nat, input)) == True{} : Bool}:
  +dr = Lemma.dropN(i, input)
  %drop_len(input, i, h) : {Nat.is_le(Nat.add(i, List.length(&2, Nat, Lemma.slice(input, i, l))), _) == True{} : Bool}
  add_le_l(i, List.length(&2, Nat, Lemma.takeN(l, dr)), List.length(&2, Nat, dr), Lemma.length_take_le(l, dr))

# ======== THE CERTIFICATE ========

def le_by(+a: Nat, +b: Nat, +c: Nat, +e: {a == b : Nat}, +h: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  %Equal.sym(Nat, a, b, e) : {Nat.is_le(_, c) == True{} : Bool}
  h

def forest_ok(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +m: Nat, +i: Nat, +j: Nat, +e: Nat, +ch: +List<Core.Tree>,
  +rd: {Core.reads(ch, grammar, Core.rhsOf(grammar, m), input, i) == True{} : Bool},
  +ec: {G.endOf(ch, i) == e : Nat}, +he: {e == Nat.add(i, List.length(&2, Nat, Lemma.slice(input, i, Nat.sub(j, i)))) : Nat})
  -> {Guard.forestOk(grammar, m, Lemma.slice(input, i, Nat.sub(j, i)), ch) == True{} : Bool}:
  +lv = List.length(&2, Nat, Core.leaves(ch))
  +lw = List.length(&2, Nat, Lemma.slice(input, i, Nat.sub(j, i)))
  +el = Lemma.add_cancel_left(i, lv, lw, Equal.trans(Nat, Nat.add(i, lv), G.endOf(ch, i), Nat.add(i, lw), Equal.sym(Nat, G.endOf(ch, i), Nat.add(i, lv), G.end_eq(ch, i)), Equal.trans(Nat, G.endOf(ch, i), e, Nat.add(i, lw), ec, he)))
  +sp = spells_take(Core.leaves(ch), Nat.sub(j, i), Lemma.dropN(i, input), spells_drop(Core.leaves(ch), input, i, S.reads_spells(ch, Core.rhsOf(grammar, m), grammar, input, i, rd)),
    le_by(lv, lw, Nat.sub(j, i), el, take_le(Nat.sub(j, i), Lemma.dropN(i, input))))
  Lemma.and_true_intro(Core.reads(ch, grammar, Core.rhsOf(grammar, m), Lemma.slice(input, i, Nat.sub(j, i)), 0n), Nat.is_eq(lv, lw),
    D.fits_reads(ch, Core.rhsOf(grammar, m), grammar, Lemma.slice(input, i, Nat.sub(j, i)), 0n, D.reads_fits(ch, Core.rhsOf(grammar, m), grammar, input, i, rd), sp), eq_is(lv, lw, el))

# A sound segment that completes m over i .. e passes the certificate check.
def cert_ok(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +m: Nat, +i: Nat, +j: Nat, +e: Nat, +ch: +List<Core.Tree>,
  +hc: {segOk(fuel, grammar, gmarks, input, R.Seg{m, i, List.length(&2, Core.Sym, Core.rhsOf(grammar, m)), e, ch}) == True{} : Bool}, +he: {e == Nat.add(i, List.length(&2, Nat, Lemma.slice(input, i, Nat.sub(j, i)))) : Nat},
  +hend: {Guard.isYes(R.endTri(Core.rhsOf(grammar, m), fuel, grammar, gmarks, input, m, i, e)) == True{} : Bool})
  -> {P.certWith(ch, fuel, grammar, gmarks, input, m, i, j) == True{} : Bool}:
  +RD = {Core.reads(ch, grammar, WS.takeN(List.length(&2, Core.Sym, Core.rhsOf(grammar, m)), Core.rhsOf(grammar, m)), input, i) : Bool}
  +EN = {Nat.is_eq(G.endOf(ch, i), e) : Bool}
  +LN = {Nat.is_eq(List.length(&2, Core.Tree, ch), List.length(&2, Core.Sym, Core.rhsOf(grammar, m))) : Bool}
  +AY = {P.allYes(List.append(&2, Core.Bsr, WC.ownNE(m, ch, 0n, i, i), Core.steps(ch, i)), fuel, grammar, gmarks, input) : Bool}
  +r2 = Lemma.and_true_right_side(RD, Bool.and(EN, Bool.and(LN, AY)), hc)
  +rd = WS.reads_all(grammar, input, ch, Core.rhsOf(grammar, m), i, Lemma.and_true_left(RD, Bool.and(EN, Bool.and(LN, AY)), hc))
  +ec = Lemma.nat_eq_sound(G.endOf(ch, i), e, Lemma.and_true_left(EN, Bool.and(LN, AY), r2))
  +ay = Lemma.and_true_right_side(LN, AY, Lemma.and_true_right_side(EN, Bool.and(LN, AY), r2))
  Lemma.and_true_intro(Guard.forestOk(grammar, m, Lemma.slice(input, i, Nat.sub(j, i)), ch), P.allYes(Core.steps([Core.Node{m, ch}], i), fuel, grammar, gmarks, input),
    forest_ok(fuel, grammar, gmarks, input, m, i, j, e, ch, rd, ec, he), child_yes(ch, fuel, grammar, gmarks, input, m, i, e, rd, ec, hend, ay))

# ======== PHASE 2'S RIVAL VERDICT IS DECIDED ========

def cert_dec(b: Bool, +h: {b == True{} : Bool}) -> {RG.decidedTri(P.certTri(b)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(h))

def closed_dec(b: Bool, +h: {b == True{} : Bool}) -> {RG.decidedTri(P.closedTri(b)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(h))

def found_dec(found: Bool, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +m: Nat, +i: Nat, +j: Nat, +e: Nat, +segs: +List<R.Seg>,
  +ef: {R.hasSeg(m, i, List.length(&2, Core.Sym, Core.rhsOf(grammar, m)), e, segs) == found : Bool}, +hs: {segsOk(segs, fuel, grammar, gmarks, input) == True{} : Bool}, +he: {e == Nat.add(i, List.length(&2, Nat, Lemma.slice(input, i, Nat.sub(j, i)))) : Nat},
  +hend: {Guard.isYes(R.endTri(Core.rhsOf(grammar, m), fuel, grammar, gmarks, input, m, i, e)) == True{} : Bool},
  +hcl: {Bool.and(R.closedAll(segs, fuel, grammar, gmarks, input, segs), R.hasSeg(m, i, 0n, i, segs)) == True{} : Bool})
  -> {RG.decidedTri(P.foundTri(found, fuel, grammar, gmarks, input, m, i, j, e, segs)) == True{} : Bool}:
  match found:
    case True{}:
      cert_dec(P.certWith(R.forestAt(m, i, List.length(&2, Core.Sym, Core.rhsOf(grammar, m)), e, segs), fuel, grammar, gmarks, input, m, i, j),
        cert_ok(fuel, grammar, gmarks, input, m, i, j, e, R.forestAt(m, i, List.length(&2, Core.Sym, Core.rhsOf(grammar, m)), e, segs), forest_at_ok(segs, fuel, grammar, gmarks, input, m, i, List.length(&2, Core.Sym, Core.rhsOf(grammar, m)), e, hs, ef), he, hend))
    case False{}:
      closed_dec(Bool.and(R.closedAll(segs, fuel, grammar, gmarks, input, segs), R.hasSeg(m, i, 0n, i, segs)), hcl)

def yes_of(+t: Guard.Tri, +e: {t == Guard.Yes{} : Guard.Tri}) -> {Guard.isYes(t) == True{} : Bool}:
  %Equal.sym(Guard.Tri, t, Guard.Yes{}, e) : {Guard.isYes(_) == True{} : Bool}
  {==}

def root_dec(t: Guard.Tri, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +m: Nat, +i: Nat, +j: Nat, +e: Nat, +segs: +List<R.Seg>,
  +et: {R.endTri(Core.rhsOf(grammar, m), fuel, grammar, gmarks, input, m, i, e) == t : Guard.Tri},
  +hd: {RG.decidedTri(t) == True{} : Bool}, +hs: {segsOk(segs, fuel, grammar, gmarks, input) == True{} : Bool}, +he: {e == Nat.add(i, List.length(&2, Nat, Lemma.slice(input, i, Nat.sub(j, i)))) : Nat},
  +hcl: {Bool.and(R.closedAll(segs, fuel, grammar, gmarks, input, segs), R.hasSeg(m, i, 0n, i, segs)) == True{} : Bool})
  -> {RG.decidedTri(P.rootTri(t, R.hasSeg(m, i, List.length(&2, Core.Sym, Core.rhsOf(grammar, m)), e, segs), fuel, grammar, gmarks, input, m, i, j, e, segs)) == True{} : Bool}:
  match t:
    case Guard.Yes{}:
      found_dec(R.hasSeg(m, i, List.length(&2, Core.Sym, Core.rhsOf(grammar, m)), e, segs), fuel, grammar, gmarks, input, m, i, j, e, segs, {==}, hs, he, yes_of(R.endTri(Core.rhsOf(grammar, m), fuel, grammar, gmarks, input, m, i, e), et), hcl)
    case Guard.No{}:
      {==}
    case Guard.Unknown{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(hd))

# THE RIVAL VERDICT IS DECIDED: for a production m within the grammar and a start i within
# the input, when phase 1 decides every step within bounds, with fuel 1 + the size of the
# descriptor universe, phase 2's rival search answers Yes or No, never Unknown.
law rival_decided:
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +input: +List<Nat>
  for +m: Nat
  for +i: Nat
  for +j: Nat
  for +hm: {Nat.is_le(1n+m, List.length(&2, Core.Production, grammar)) == True{} : Bool}
  for +hi: {Nat.is_le(i, List.length(&2, Nat, input)) == True{} : Bool}
  for +hdec: {RG.decided(fuel, grammar, gmarks, input) == True{} : Bool}
  for +hf: {Nat.is_le(1n+List.length(&2, Gll.Desc, Run.univ(grammar, input)), fuel) == True{} : Bool}
  {RG.decidedTri(P.rivalTri(fuel, grammar, gmarks, input, m, i, j)) == True{} : Bool}

def rival_decided(fuel, grammar, gmarks, input, m, i, j, hm, hi, hdec, hf):
  +e = Nat.add(i, List.length(&2, Nat, Lemma.slice(input, i, Nat.sub(j, i))))
  +t = R.endTri(Core.rhsOf(grammar, m), fuel, grammar, gmarks, input, m, i, e)
  root_dec(t, fuel, grammar, gmarks, input, m, i, j, e, R.segsFrom(fuel, grammar, gmarks, input, m, i), {==},
    RG.end_decided(Core.rhsOf(grammar, m), fuel, grammar, gmarks, input, m, i, e, hdec, hm, hi, end_bound(input, i, Nat.sub(j, i), hi)),
    grow_ok(fuel, fuel, grammar, gmarks, input, [R.Seg{m, i, 0n, i, []}], Lemma.and_true_intro(segOk(fuel, grammar, gmarks, input, R.Seg{m, i, 0n, i, []}), True{}, seed_ok(fuel, grammar, gmarks, input, m, i), {==})),
    {==}, RG.rival_closed(fuel, grammar, gmarks, input, m, i, hm, hi, hdec, hf))

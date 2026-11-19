import Base
import ../LEMMAS.bend as Lemma
import ./CORE.bend as Core
import ./GLL.bend as Gll
import ./GUARD.bend as Guard
import ./RIVAL.bend as R
import ./RUN.bend as Run
import ./PROOF_GLL.bend as G
import ./PROOF_COUNT.bend as C
import ./PROOF_RUN.bend as RN

# THE RIVAL CLOSURE ANSWERS (RIVAL.bend): when phase 1 decides every step within bounds
# (`decided`: no step's verdict is Unknown), the segments grown from m at i end closed with
# fuel 1 + the size of the descriptor universe: a round either adds a segment with a new key
# (counted as a descriptor, RUN.bend) or changes nothing, and then the set is closed.

# ======== PHASE 1 DECIDES EVERY STEP ========

def decidedTri(t: Guard.Tri) -> Bool:
  match t:
    case Guard.Yes{}:
      True{}
    case Guard.No{}:
      True{}
    case Guard.Unknown{}:
      False{}

def bsrAt(dd: Gll.Desc, +k: Nat) -> Core.Bsr:
  match dd:
    case Gll.Desc{+q, +d, +i, +j}:
      Core.Bsr{q, d, i, k, j}

# Every step of descriptor (q, d, i, j) with a middle position up to m.
def ksOf(+dd: Gll.Desc, m: Nat) -> +List<Core.Bsr>:
  match m:
    case 0n:
      [bsrAt(dd, 0n)]
    case 1n+(+p):
      bsrAt(dd, 1n+p) <> ksOf(dd, p)

def stepsOver(ds: +List<Gll.Desc>, +n: Nat) -> +List<Core.Bsr>:
  match ds:
    case Nil{}:
      []
    case Con{+dd, rest}:
      List.append(&2, Core.Bsr, ksOf(dd, n), stepsOver(rest, n))

def allDecided(ys: +List<Core.Bsr>, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{+y, rest}:
      Bool.and(decidedTri(Guard.stepTri(fuel, grammar, gmarks, input, y)), allDecided(rest, fuel, grammar, gmarks, input))

# Phase 1 decides every step within bounds.
def decided(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>) -> Bool:
  allDecided(stepsOver(Run.univ(grammar, input), List.length(&2, Nat, input)), fuel, grammar, gmarks, input)

law ad_left:
  for a: +List<Core.Bsr>
  for +b: +List<Core.Bsr>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +input: +List<Nat>
  for +h: {allDecided(List.append(&2, Core.Bsr, a, b), fuel, grammar, gmarks, input) == True{} : Bool}
  {allDecided(a, fuel, grammar, gmarks, input) == True{} : Bool}

def ad_left(a, b, fuel, grammar, gmarks, input, h):
  match a:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      Lemma.and_true_intro(decidedTri(Guard.stepTri(fuel, grammar, gmarks, input, y)), allDecided(rest, fuel, grammar, gmarks, input), Lemma.and_true_left(decidedTri(Guard.stepTri(fuel, grammar, gmarks, input, y)), allDecided(List.append(&2, Core.Bsr, rest, b), fuel, grammar, gmarks, input), h),
        ad_left(rest, b, fuel, grammar, gmarks, input, Lemma.and_true_right_side(decidedTri(Guard.stepTri(fuel, grammar, gmarks, input, y)), allDecided(List.append(&2, Core.Bsr, rest, b), fuel, grammar, gmarks, input), h)))

law ad_right:
  for a: +List<Core.Bsr>
  for +b: +List<Core.Bsr>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +input: +List<Nat>
  for +h: {allDecided(List.append(&2, Core.Bsr, a, b), fuel, grammar, gmarks, input) == True{} : Bool}
  {allDecided(b, fuel, grammar, gmarks, input) == True{} : Bool}

def ad_right(a, b, fuel, grammar, gmarks, input, h):
  match a:
    case Nil{}:
      h
    case Con{+y, +rest}:
      ad_right(rest, b, fuel, grammar, gmarks, input, Lemma.and_true_right_side(decidedTri(Guard.stepTri(fuel, grammar, gmarks, input, y)), allDecided(List.append(&2, Core.Bsr, rest, b), fuel, grammar, gmarks, input), h))

def ks_pick(b: Bool, +dd: Gll.Desc, +k: Nat, +p: Nat, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +eb: {Nat.is_eq(k, 1n+p) == b : Bool}, +hk: {Nat.is_le(k, 1n+p) == True{} : Bool},
  +h: {allDecided(ksOf(dd, 1n+p), fuel, grammar, gmarks, input) == True{} : Bool},
  later: {Nat.is_le(k, p) == True{} : Bool} -> {allDecided(ksOf(dd, p), fuel, grammar, gmarks, input) == True{} : Bool} -> {decidedTri(Guard.stepTri(fuel, grammar, gmarks, input, bsrAt(dd, k))) == True{} : Bool})
  -> {decidedTri(Guard.stepTri(fuel, grammar, gmarks, input, bsrAt(dd, k))) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Nat, k, 1n+p, Lemma.nat_eq_sound(k, 1n+p, eb)) : {decidedTri(Guard.stepTri(fuel, grammar, gmarks, input, bsrAt(dd, _))) == True{} : Bool}
      Lemma.and_true_left(decidedTri(Guard.stepTri(fuel, grammar, gmarks, input, bsrAt(dd, 1n+p))), allDecided(ksOf(dd, p), fuel, grammar, gmarks, input), h)
    case False{}:
      later(C.le_pred_ne(k, p, hk, eb), Lemma.and_true_right_side(decidedTri(Guard.stepTri(fuel, grammar, gmarks, input, bsrAt(dd, 1n+p))), allDecided(ksOf(dd, p), fuel, grammar, gmarks, input), h))

law ks_at:
  for m: Nat
  for +dd: Gll.Desc
  for +k: Nat
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +input: +List<Nat>
  for +h: {allDecided(ksOf(dd, m), fuel, grammar, gmarks, input) == True{} : Bool}
  for +hk: {Nat.is_le(k, m) == True{} : Bool}
  {decidedTri(Guard.stepTri(fuel, grammar, gmarks, input, bsrAt(dd, k))) == True{} : Bool}

def ks_at(m, dd, k, fuel, grammar, gmarks, input, h, hk):
  match m:
    case 0n:
      %Equal.sym(Nat, k, 0n, C.le_zero_eq(k, hk)) : {decidedTri(Guard.stepTri(fuel, grammar, gmarks, input, bsrAt(dd, _))) == True{} : Bool}
      Lemma.and_true_left(decidedTri(Guard.stepTri(fuel, grammar, gmarks, input, bsrAt(dd, 0n))), True{}, h)
    case 1n+(+p):
      ks_pick(Nat.is_eq(k, 1n+p), dd, k, p, fuel, grammar, gmarks, input, {==}, hk, h, h2 => h3 => ks_at(p, dd, k, fuel, grammar, gmarks, input, h3, h2))

def over_pick(+dd: Gll.Desc, +d2: Gll.Desc, +rest: +List<Gll.Desc>, +n: Nat, +k: Nat, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +hk: {Nat.is_le(k, n) == True{} : Bool},
  +h: {allDecided(List.append(&2, Core.Bsr, ksOf(d2, n), stepsOver(rest, n)), fuel, grammar, gmarks, input) == True{} : Bool},
  cases: Either<{Gll.descEq(dd, d2) == True{} : Bool}, {Gll.descIn(dd, rest) == True{} : Bool}>,
  later: {Gll.descIn(dd, rest) == True{} : Bool} -> {allDecided(stepsOver(rest, n), fuel, grammar, gmarks, input) == True{} : Bool} -> {decidedTri(Guard.stepTri(fuel, grammar, gmarks, input, bsrAt(dd, k))) == True{} : Bool})
  -> {decidedTri(Guard.stepTri(fuel, grammar, gmarks, input, bsrAt(dd, k))) == True{} : Bool}:
  match cases:
    case Inl{e}:
      %Equal.sym(Gll.Desc, dd, d2, G.desc_eq_sound(dd, d2, e)) : {decidedTri(Guard.stepTri(fuel, grammar, gmarks, input, bsrAt(_, k))) == True{} : Bool}
      ks_at(n, d2, k, fuel, grammar, gmarks, input, ad_left(ksOf(d2, n), stepsOver(rest, n), fuel, grammar, gmarks, input, h), hk)
    case Inr{m}:
      later(m, ad_right(ksOf(d2, n), stepsOver(rest, n), fuel, grammar, gmarks, input, h))

law over_at:
  for ds: +List<Gll.Desc>
  for +n: Nat
  for +dd: Gll.Desc
  for +k: Nat
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +input: +List<Nat>
  for +h: {allDecided(stepsOver(ds, n), fuel, grammar, gmarks, input) == True{} : Bool}
  for +m: {Gll.descIn(dd, ds) == True{} : Bool}
  for +hk: {Nat.is_le(k, n) == True{} : Bool}
  {decidedTri(Guard.stepTri(fuel, grammar, gmarks, input, bsrAt(dd, k))) == True{} : Bool}

def over_at(ds, n, dd, k, fuel, grammar, gmarks, input, h, m, hk):
  match ds:
    case Nil{}:
      Empty.absurd({decidedTri(Guard.stepTri(fuel, grammar, gmarks, input, bsrAt(dd, k))) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{+d2, +rest}:
      over_pick(dd, d2, rest, n, k, fuel, grammar, gmarks, input, hk, h, Lemma.or_true_cases(Gll.descEq(dd, d2), Gll.descIn(dd, rest), m),
        m2 => h2 => over_at(rest, n, dd, k, fuel, grammar, gmarks, input, h2, m2, hk))

# A step within bounds is decided.
law decided_at:
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +input: +List<Nat>
  for +q: Nat
  for +d: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for +hd: {decided(fuel, grammar, gmarks, input) == True{} : Bool}
  for +hb: {Run.stepBound(Core.Bsr{q, d, i, k, j}, grammar, input) == True{} : Bool}
  {decidedTri(Guard.stepTri(fuel, grammar, gmarks, input, Core.Bsr{q, d, i, k, j})) == True{} : Bool}

def decided_at(fuel, grammar, gmarks, input, q, d, i, k, j, hd, hb):
  over_at(Run.univ(grammar, input), List.length(&2, Nat, input), Gll.Desc{q, d, i, j}, k, fuel, grammar, gmarks, input, hd,
    C.bound_mem(Gll.Desc{q, d, i, j}, grammar, input, Lemma.and_true_left(Run.descBound(Gll.Desc{q, d, i, j}, grammar, input), Nat.is_le(k, List.length(&2, Nat, input)), hb)),
    Lemma.and_true_right_side(Run.descBound(Gll.Desc{q, d, i, j}, grammar, input), Nat.is_le(k, List.length(&2, Nat, input)), hb))

# What a decided verdict asks of the set holds when Yes leads there.
def clause_by(t: Guard.Tri, +c: Bool, +hd: {decidedTri(t) == True{} : Bool}, yes: {Guard.isYes(t) == True{} : Bool} -> {c == True{} : Bool})
  -> {R.clause(t, c) == True{} : Bool}:
  match t:
    case Guard.Yes{}:
      yes({==})
    case Guard.No{}:
      {==}
    case Guard.Unknown{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(hd))

# ======== SEGMENTS, COUNTED ========

def segBound(s: R.Seg, +grammar: +List<Core.Production>, +input: +List<Nat>) -> Bool:
  match s:
    case R.Seg{+q, +ks, +d, +e, f}:
      Run.descBound(Gll.Desc{q, d, ks, e}, grammar, input)

def segsBounded(segs: +List<R.Seg>, +grammar: +List<Core.Production>, +input: +List<Nat>) -> Bool:
  match segs:
    case Nil{}:
      True{}
    case Con{+s, rest}:
      Bool.and(segBound(s, grammar, input), segsBounded(rest, grammar, input))

# A segment's key as a descriptor: (q, ks, d, e) as Desc{q, d, ks, e}.
def segDescs(segs: +List<R.Seg>) -> +List<Gll.Desc>:
  match segs:
    case Nil{}:
      []
    case Con{R.Seg{+q, +ks, +d, +e, f}, rest}:
      Gll.Desc{q, d, ks, e} <> segDescs(rest)

def rMeas(+grammar: +List<Core.Production>, +input: +List<Nat>, +segs: +List<R.Seg>) -> Nat:
  Run.countNot(Run.univ(grammar, input), segDescs(segs))

def allHave(ss: +List<R.Seg>, +segs: +List<R.Seg>) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case Con{R.Seg{+q, +ks, +d, +e, f}, rest}:
      Bool.and(R.hasSeg(q, ks, d, e, segs), allHave(rest, segs))

def dQ(dd: Gll.Desc) -> Nat:
  match dd:
    case Gll.Desc{+q, +d, +k, +i}:
      q

def dD(dd: Gll.Desc) -> Nat:
  match dd:
    case Gll.Desc{+q, +d, +k, +i}:
      d

def dK(dd: Gll.Desc) -> Nat:
  match dd:
    case Gll.Desc{+q, +d, +k, +i}:
      k

def dI(dd: Gll.Desc) -> Nat:
  match dd:
    case Gll.Desc{+q, +d, +k, +i}:
      i

def key_refl(+q: Nat, +ks: Nat, +d: Nat, +e: Nat, +f: +List<Core.Tree>) -> {R.keyIs(q, ks, d, e, R.Seg{q, ks, d, e, f}) == True{} : Bool}:
  Lemma.and_true_intro(Nat.is_eq(q, q), Bool.and(Nat.is_eq(ks, ks), Bool.and(Nat.is_eq(d, d), Nat.is_eq(e, e))), Lemma.nat_eq_refl(q),
    Lemma.and_true_intro(Nat.is_eq(ks, ks), Bool.and(Nat.is_eq(d, d), Nat.is_eq(e, e)), Lemma.nat_eq_refl(ks),
      Lemma.and_true_intro(Nat.is_eq(d, d), Nat.is_eq(e, e), Lemma.nat_eq_refl(d), Lemma.nat_eq_refl(e))))

def key_at(+q: Nat, +ks: Nat, +d: Nat, +e: Nat, +q2: Nat, +ks2: Nat, +d2: Nat, +e2: Nat, +f: +List<Core.Tree>,
  +ed: {Gll.Desc{q, d, ks, e} == Gll.Desc{q2, d2, ks2, e2} : Gll.Desc}) -> {R.keyIs(q, ks, d, e, R.Seg{q2, ks2, d2, e2, f}) == True{} : Bool}:
  %Equal.cong(Gll.Desc, Nat, v => dQ(v), Gll.Desc{q, d, ks, e}, Gll.Desc{q2, d2, ks2, e2}, ed) : {R.keyIs(q, ks, d, e, R.Seg{_, ks2, d2, e2, f}) == True{} : Bool}
  %Equal.cong(Gll.Desc, Nat, v => dD(v), Gll.Desc{q, d, ks, e}, Gll.Desc{q2, d2, ks2, e2}, ed) : {R.keyIs(q, ks, d, e, R.Seg{q, ks2, _, e2, f}) == True{} : Bool}
  %Equal.cong(Gll.Desc, Nat, v => dK(v), Gll.Desc{q, d, ks, e}, Gll.Desc{q2, d2, ks2, e2}, ed) : {R.keyIs(q, ks, d, e, R.Seg{q, _, d, e2, f}) == True{} : Bool}
  %Equal.cong(Gll.Desc, Nat, v => dI(v), Gll.Desc{q, d, ks, e}, Gll.Desc{q2, d2, ks2, e2}, ed) : {R.keyIs(q, ks, d, e, R.Seg{q, ks, d, _, f}) == True{} : Bool}
  key_refl(q, ks, d, e, f)

def sd_pick(+q: Nat, +ks: Nat, +d: Nat, +e: Nat, +q2: Nat, +ks2: Nat, +d2: Nat, +e2: Nat, +f: +List<Core.Tree>, +rest: +List<R.Seg>,
  cases: Either<{Gll.descEq(Gll.Desc{q, d, ks, e}, Gll.Desc{q2, d2, ks2, e2}) == True{} : Bool}, {Gll.descIn(Gll.Desc{q, d, ks, e}, segDescs(rest)) == True{} : Bool}>,
  later: {Gll.descIn(Gll.Desc{q, d, ks, e}, segDescs(rest)) == True{} : Bool} -> {R.hasSeg(q, ks, d, e, rest) == True{} : Bool})
  -> {R.hasSeg(q, ks, d, e, R.Seg{q2, ks2, d2, e2, f} <> rest) == True{} : Bool}:
  match cases:
    case Inl{h}:
      Lemma.or_true_left_intro(R.keyIs(q, ks, d, e, R.Seg{q2, ks2, d2, e2, f}), R.hasSeg(q, ks, d, e, rest),
        key_at(q, ks, d, e, q2, ks2, d2, e2, f, G.desc_eq_sound(Gll.Desc{q, d, ks, e}, Gll.Desc{q2, d2, ks2, e2}, h)))
    case Inr{m}:
      Lemma.or_true_right_intro(R.keyIs(q, ks, d, e, R.Seg{q2, ks2, d2, e2, f}), R.hasSeg(q, ks, d, e, rest), later(m))

# A key counted is a segment of the set.
law sd_back:
  for segs: +List<R.Seg>
  for +q: Nat
  for +ks: Nat
  for +d: Nat
  for +e: Nat
  for +h: {Gll.descIn(Gll.Desc{q, d, ks, e}, segDescs(segs)) == True{} : Bool}
  {R.hasSeg(q, ks, d, e, segs) == True{} : Bool}

def sd_back(segs, q, ks, d, e, h):
  match segs:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(h))
    case Con{R.Seg{+q2, +ks2, +d2, +e2, +f}, +rest}:
      sd_pick(q, ks, d, e, q2, ks2, d2, e2, f, rest, Lemma.or_true_cases(Gll.descEq(Gll.Desc{q, d, ks, e}, Gll.Desc{q2, d2, ks2, e2}), Gll.descIn(Gll.Desc{q, d, ks, e}, segDescs(rest)), h),
        m => sd_back(rest, q, ks, d, e, m))

def sd_out(b: Bool, +q: Nat, +ks: Nat, +d: Nat, +e: Nat, +segs: +List<R.Seg>, +eb: {Gll.descIn(Gll.Desc{q, d, ks, e}, segDescs(segs)) == b : Bool},
  +out: {R.hasSeg(q, ks, d, e, segs) == False{} : Bool}) -> {Gll.descIn(Gll.Desc{q, d, ks, e}, segDescs(segs)) == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({Gll.descIn(Gll.Desc{q, d, ks, e}, segDescs(segs)) == False{} : Bool}, Lemma.true_is_not_false(Equal.trans(Bool, True{}, R.hasSeg(q, ks, d, e, segs), False{}, Equal.sym(Bool, R.hasSeg(q, ks, d, e, segs), True{}, sd_back(segs, q, ks, d, e, eb)), out)))
    case False{}:
      eb

law seg_descs_app:
  for a: +List<R.Seg>
  for +b: +List<R.Seg>
  {segDescs(List.append(&2, R.Seg, a, b)) == List.append(&2, Gll.Desc, segDescs(a), segDescs(b)) : +List<Gll.Desc>}

def seg_descs_app(a, b):
  match a:
    case Nil{}:
      {==}
    case Con{R.Seg{+q, +ks, +d, +e, +f}, +rest}:
      %seg_descs_app(rest, b) : {Gll.Desc{q, d, ks, e} <> segDescs(List.append(&2, R.Seg, rest, b)) == Gll.Desc{q, d, ks, e} <> _ : +List<Gll.Desc>}
      {==}

law sub_app:
  for xs: +List<Gll.Desc>
  for +ys: +List<Gll.Desc>
  for +c: +List<Gll.Desc>
  for +h: {Run.subDescs(xs, ys) == True{} : Bool}
  {Run.subDescs(xs, List.append(&2, Gll.Desc, ys, c)) == True{} : Bool}

def sub_app(xs, ys, c, h):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Lemma.and_true_intro(Gll.descIn(x, List.append(&2, Gll.Desc, ys, c)), Run.subDescs(rest, List.append(&2, Gll.Desc, ys, c)),
        C.desc_in_app_left(ys, c, x, Lemma.and_true_left(Gll.descIn(x, ys), Run.subDescs(rest, ys), h)),
        sub_app(rest, ys, c, Lemma.and_true_right_side(Gll.descIn(x, ys), Run.subDescs(rest, ys), h)))

# A new segment within bounds, added at the end: one fewer unseen key.
def r_drop(+grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +ks: Nat, +d: Nat, +e: Nat, +f: +List<Core.Tree>, +segs: +List<R.Seg>,
  +hb: {Run.descBound(Gll.Desc{q, d, ks, e}, grammar, input) == True{} : Bool}, +out: {R.hasSeg(q, ks, d, e, segs) == False{} : Bool})
  -> {Nat.is_le(1n+rMeas(grammar, input, List.append(&2, R.Seg, segs, [R.Seg{q, ks, d, e, f}])), rMeas(grammar, input, segs)) == True{} : Bool}:
  +U = Run.univ(grammar, input)
  +D = {Gll.Desc{q, d, ks, e} : Gll.Desc}
  %Equal.sym(+List<Gll.Desc>, segDescs(List.append(&2, R.Seg, segs, [R.Seg{q, ks, d, e, f}])), List.append(&2, Gll.Desc, segDescs(segs), [D]), seg_descs_app(segs, [R.Seg{q, ks, d, e, f}])) : {Nat.is_le(1n+Run.countNot(U, _), rMeas(grammar, input, segs)) == True{} : Bool}
  Lemma.le_trans(1n+Run.countNot(U, List.append(&2, Gll.Desc, segDescs(segs), [D])), 1n+Run.countNot(U, D <> segDescs(segs)), Run.countNot(U, segDescs(segs)),
    C.count_mono(U, D <> segDescs(segs), List.append(&2, Gll.Desc, segDescs(segs), [D]),
      Lemma.and_true_intro(Gll.descIn(D, List.append(&2, Gll.Desc, segDescs(segs), [D])), Run.subDescs(segDescs(segs), List.append(&2, Gll.Desc, segDescs(segs), [D])),
        C.desc_in_app_right(segDescs(segs), [D], D, C.desc_head(q, d, ks, e, [])),
        sub_app(segDescs(segs), segDescs(segs), [D], C.desc_refl(segDescs(segs))))),
    C.count_drop(U, segDescs(segs), D, C.bound_mem(D, grammar, input, hb), sd_out(Gll.descIn(D, segDescs(segs)), q, ks, d, e, segs, {==}, out)))

# ======== ADDING NEW SEGMENTS ========

law hs_app_left:
  for a: +List<R.Seg>
  for +b: +List<R.Seg>
  for +q: Nat
  for +ks: Nat
  for +d: Nat
  for +e: Nat
  for +h: {R.hasSeg(q, ks, d, e, a) == True{} : Bool}
  {R.hasSeg(q, ks, d, e, List.append(&2, R.Seg, a, b)) == True{} : Bool}

def hs_app_pick(+s: R.Seg, +rest: +List<R.Seg>, +b: +List<R.Seg>, +q: Nat, +ks: Nat, +d: Nat, +e: Nat,
  cases: Either<{R.keyIs(q, ks, d, e, s) == True{} : Bool}, {R.hasSeg(q, ks, d, e, rest) == True{} : Bool}>,
  later: {R.hasSeg(q, ks, d, e, rest) == True{} : Bool} -> {R.hasSeg(q, ks, d, e, List.append(&2, R.Seg, rest, b)) == True{} : Bool})
  -> {R.hasSeg(q, ks, d, e, s <> List.append(&2, R.Seg, rest, b)) == True{} : Bool}:
  match cases:
    case Inl{h}:
      Lemma.or_true_left_intro(R.keyIs(q, ks, d, e, s), R.hasSeg(q, ks, d, e, List.append(&2, R.Seg, rest, b)), h)
    case Inr{m}:
      Lemma.or_true_right_intro(R.keyIs(q, ks, d, e, s), R.hasSeg(q, ks, d, e, List.append(&2, R.Seg, rest, b)), later(m))

def hs_app_left(a, b, q, ks, d, e, h):
  match a:
    case Nil{}:
      Empty.absurd({R.hasSeg(q, ks, d, e, b) == True{} : Bool}, Lemma.false_is_not_true(h))
    case Con{+s, +rest}:
      hs_app_pick(s, rest, b, q, ks, d, e, Lemma.or_true_cases(R.keyIs(q, ks, d, e, s), R.hasSeg(q, ks, d, e, rest), h), m => hs_app_left(rest, b, q, ks, d, e, m))

law sb_app:
  for a: +List<R.Seg>
  for +b: +List<R.Seg>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +ha: {segsBounded(a, grammar, input) == True{} : Bool}
  for +hb: {segsBounded(b, grammar, input) == True{} : Bool}
  {segsBounded(List.append(&2, R.Seg, a, b), grammar, input) == True{} : Bool}

def sb_app(a, b, grammar, input, ha, hb):
  match a:
    case Nil{}:
      hb
    case Con{+s, +rest}:
      Lemma.and_true_intro(segBound(s, grammar, input), segsBounded(List.append(&2, R.Seg, rest, b), grammar, input), Lemma.and_true_left(segBound(s, grammar, input), segsBounded(rest, grammar, input), ha),
        sb_app(rest, b, grammar, input, Lemma.and_true_right_side(segBound(s, grammar, input), segsBounded(rest, grammar, input), ha), hb))

def pick_bounded(have: Bool, +s: R.Seg, +segs: +List<R.Seg>, +grammar: +List<Core.Production>, +input: +List<Nat>, +hs: {segBound(s, grammar, input) == True{} : Bool}, +h: {segsBounded(segs, grammar, input) == True{} : Bool})
  -> {segsBounded(R.addPick(have, s, segs), grammar, input) == True{} : Bool}:
  match have:
    case True{}:
      h
    case False{}:
      sb_app(segs, [s], grammar, input, h, Lemma.and_true_intro(segBound(s, grammar, input), True{}, hs, {==}))

# Adding keeps the segments within bounds.
law an_bounded:
  for new: +List<R.Seg>
  for +segs: +List<R.Seg>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +hn: {segsBounded(new, grammar, input) == True{} : Bool}
  for +hs: {segsBounded(segs, grammar, input) == True{} : Bool}
  {segsBounded(R.addNew(new, segs), grammar, input) == True{} : Bool}

def an_bounded(new, segs, grammar, input, hn, hs):
  match new:
    case Nil{}:
      hs
    case Con{R.Seg{+q, +ks, +d, +e, +f}, +rest}:
      an_bounded(rest, R.addPick(R.hasSeg(q, ks, d, e, segs), R.Seg{q, ks, d, e, f}, segs), grammar, input,
        Lemma.and_true_right_side(segBound(R.Seg{q, ks, d, e, f}, grammar, input), segsBounded(rest, grammar, input), hn),
        pick_bounded(R.hasSeg(q, ks, d, e, segs), R.Seg{q, ks, d, e, f}, segs, grammar, input,
          Lemma.and_true_left(segBound(R.Seg{q, ks, d, e, f}, grammar, input), segsBounded(rest, grammar, input), hn), hs))

def pick_keep(have: Bool, +s: R.Seg, +segs: +List<R.Seg>, +q: Nat, +ks: Nat, +d: Nat, +e: Nat, +h: {R.hasSeg(q, ks, d, e, segs) == True{} : Bool})
  -> {R.hasSeg(q, ks, d, e, R.addPick(have, s, segs)) == True{} : Bool}:
  match have:
    case True{}:
      h
    case False{}:
      hs_app_left(segs, [s], q, ks, d, e, h)

# Adding keeps every segment.
law an_keep:
  for new: +List<R.Seg>
  for +segs: +List<R.Seg>
  for +q: Nat
  for +ks: Nat
  for +d: Nat
  for +e: Nat
  for +h: {R.hasSeg(q, ks, d, e, segs) == True{} : Bool}
  {R.hasSeg(q, ks, d, e, R.addNew(new, segs)) == True{} : Bool}

def an_keep(new, segs, q, ks, d, e, h):
  match new:
    case Nil{}:
      h
    case Con{R.Seg{+q2, +ks2, +d2, +e2, +f}, +rest}:
      an_keep(rest, R.addPick(R.hasSeg(q2, ks2, d2, e2, segs), R.Seg{q2, ks2, d2, e2, f}, segs), q, ks, d, e,
        pick_keep(R.hasSeg(q2, ks2, d2, e2, segs), R.Seg{q2, ks2, d2, e2, f}, segs, q, ks, d, e, h))

def ASame(+new: +List<R.Seg>, +segs: +List<R.Seg>) -> Type:
  {R.addNew(new, segs) == segs : +List<R.Seg>} & {allHave(new, segs) == True{} : Bool}

def ARes(+grammar: +List<Core.Production>, +input: +List<Nat>, +new: +List<R.Seg>, +segs: +List<R.Seg>) -> Type:
  Either<ASame(new, segs), {Nat.is_le(1n+rMeas(grammar, input, R.addNew(new, segs)), rMeas(grammar, input, segs)) == True{} : Bool}>

def AResB(+b: Bool, +grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +ks: Nat, +d: Nat, +e: Nat, +f: +List<Core.Tree>, +rest: +List<R.Seg>, +segs: +List<R.Seg>) -> Type:
  Either<({R.addNew(rest, R.addPick(b, R.Seg{q, ks, d, e, f}, segs)) == segs : +List<R.Seg>} & {Bool.and(R.hasSeg(q, ks, d, e, segs), allHave(rest, segs)) == True{} : Bool}),
    {Nat.is_le(1n+rMeas(grammar, input, R.addNew(rest, R.addPick(b, R.Seg{q, ks, d, e, f}, segs))), rMeas(grammar, input, segs)) == True{} : Bool}>

def rmeas_eq(+grammar: +List<Core.Production>, +input: +List<Nat>, +a: +List<R.Seg>, +b: +List<R.Seg>, +eq: {a == b : +List<R.Seg>}) -> {Nat.is_le(rMeas(grammar, input, a), rMeas(grammar, input, b)) == True{} : Bool}:
  %eq : {Nat.is_le(rMeas(grammar, input, a), rMeas(grammar, input, _)) == True{} : Bool}
  Lemma.le_refl(rMeas(grammar, input, a))

def rmeas_to(+grammar: +List<Core.Production>, +input: +List<Nat>, +a: +List<R.Seg>, +b: +List<R.Seg>, +x: Nat, +eq: {a == b : +List<R.Seg>},
  +h: {Nat.is_le(1n+x, rMeas(grammar, input, a)) == True{} : Bool}) -> {Nat.is_le(1n+x, rMeas(grammar, input, b)) == True{} : Bool}:
  %eq : {Nat.is_le(1n+x, rMeas(grammar, input, _)) == True{} : Bool}
  h

def asame_le(+grammar: +List<Core.Production>, +input: +List<Nat>, +new: +List<R.Seg>, +segs: +List<R.Seg>, p: ASame(new, segs)) -> {Nat.is_le(rMeas(grammar, input, R.addNew(new, segs)), rMeas(grammar, input, segs)) == True{} : Bool}:
  match p:
    case (+eq, +have):
      rmeas_eq(grammar, input, R.addNew(new, segs), segs, eq)

def ares_le(+grammar: +List<Core.Production>, +input: +List<Nat>, +new: +List<R.Seg>, +segs: +List<R.Seg>, r: ARes(grammar, input, new, segs)) -> {Nat.is_le(rMeas(grammar, input, R.addNew(new, segs)), rMeas(grammar, input, segs)) == True{} : Bool}:
  match r:
    case Inl{p}:
      asame_le(grammar, input, new, segs, p)
    case Inr{m}:
      Lemma.le_of_succ_le(rMeas(grammar, input, R.addNew(new, segs)), rMeas(grammar, input, segs), m)

def ab_have2(+grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +ks: Nat, +d: Nat, +e: Nat, +f: +List<Core.Tree>, +rest: +List<R.Seg>, +segs: +List<R.Seg>, +eb: {R.hasSeg(q, ks, d, e, segs) == True{} : Bool}, p: ASame(rest, segs))
  -> AResB(True{}, grammar, input, q, ks, d, e, f, rest, segs):
  match p:
    case (+eq, +have):
      Inl{(eq, Lemma.and_true_intro(R.hasSeg(q, ks, d, e, segs), allHave(rest, segs), eb, have))}

def ab_have(+grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +ks: Nat, +d: Nat, +e: Nat, +f: +List<Core.Tree>, +rest: +List<R.Seg>, +segs: +List<R.Seg>, +eb: {R.hasSeg(q, ks, d, e, segs) == True{} : Bool}, r: ARes(grammar, input, rest, segs))
  -> AResB(True{}, grammar, input, q, ks, d, e, f, rest, segs):
  match r:
    case Inl{p}:
      ab_have2(grammar, input, q, ks, d, e, f, rest, segs, eb, p)
    case Inr{m}:
      Inr{m}

def ares_b(b: Bool, +grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +ks: Nat, +d: Nat, +e: Nat, +f: +List<Core.Tree>, +rest: +List<R.Seg>, +segs: +List<R.Seg>, +eb: {R.hasSeg(q, ks, d, e, segs) == b : Bool},
  +hb: {Run.descBound(Gll.Desc{q, d, ks, e}, grammar, input) == True{} : Bool},
  later: @a: +List<R.Seg> -> ARes(grammar, input, rest, a)) -> AResB(b, grammar, input, q, ks, d, e, f, rest, segs):
  match b:
    case True{}:
      ab_have(grammar, input, q, ks, d, e, f, rest, segs, eb, later(segs))
    case False{}:
      +s2 = List.append(&2, R.Seg, segs, [R.Seg{q, ks, d, e, f}])
      Inr{Lemma.le_trans(1n+rMeas(grammar, input, R.addNew(rest, s2)), 1n+rMeas(grammar, input, s2), rMeas(grammar, input, segs),
        ares_le(grammar, input, rest, s2, later(s2)), r_drop(grammar, input, q, ks, d, e, f, segs, hb, eb))}

# Adding segments within bounds: all keys were there and nothing changed, or the count drops.
law ares:
  for new: +List<R.Seg>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +segs: +List<R.Seg>
  for +hn: {segsBounded(new, grammar, input) == True{} : Bool}
  ARes(grammar, input, new, segs)

def ares(new, grammar, input, segs, hn):
  match new:
    case Nil{}:
      Inl{({==}, {==})}
    case Con{R.Seg{+q, +ks, +d, +e, +f}, +rest}:
      ares_b(R.hasSeg(q, ks, d, e, segs), grammar, input, q, ks, d, e, f, rest, segs, {==},
        Lemma.and_true_left(segBound(R.Seg{q, ks, d, e, f}, grammar, input), segsBounded(rest, grammar, input), hn),
        a => ares(rest, grammar, input, a, Lemma.and_true_right_side(segBound(R.Seg{q, ks, d, e, f}, grammar, input), segsBounded(rest, grammar, input), hn)))

# ======== GROWTH STAYS WITHIN BOUNDS ========

def db_intro(+q: Nat, +d: Nat, +ks: Nat, +e: Nat, +grammar: +List<Core.Production>, +input: +List<Nat>,
  +hq: {Nat.is_le(1n+q, List.length(&2, Core.Production, grammar)) == True{} : Bool}, +hd: {Nat.is_le(d, List.length(&2, Core.Sym, Core.rhsOf(grammar, q))) == True{} : Bool},
  +hks: {Nat.is_le(ks, List.length(&2, Nat, input)) == True{} : Bool}, +he: {Nat.is_le(e, List.length(&2, Nat, input)) == True{} : Bool})
  -> {Run.descBound(Gll.Desc{q, d, ks, e}, grammar, input) == True{} : Bool}:
  Lemma.and_true_intro(Nat.is_le(1n+q, List.length(&2, Core.Production, grammar)), Bool.and(Nat.is_le(d, List.length(&2, Core.Sym, Core.rhsOf(grammar, q))), Bool.and(Nat.is_le(ks, List.length(&2, Nat, input)), Nat.is_le(e, List.length(&2, Nat, input)))), hq,
    Lemma.and_true_intro(Nat.is_le(d, List.length(&2, Core.Sym, Core.rhsOf(grammar, q))), Bool.and(Nat.is_le(ks, List.length(&2, Nat, input)), Nat.is_le(e, List.length(&2, Nat, input))), hd,
      Lemma.and_true_intro(Nat.is_le(ks, List.length(&2, Nat, input)), Nat.is_le(e, List.length(&2, Nat, input)), hks, he)))

def db_q(+q: Nat, +d: Nat, +ks: Nat, +e: Nat, +grammar: +List<Core.Production>, +input: +List<Nat>, +h: {Run.descBound(Gll.Desc{q, d, ks, e}, grammar, input) == True{} : Bool})
  -> {Nat.is_le(1n+q, List.length(&2, Core.Production, grammar)) == True{} : Bool}:
  Lemma.and_true_left(Nat.is_le(1n+q, List.length(&2, Core.Production, grammar)), Bool.and(Nat.is_le(d, List.length(&2, Core.Sym, Core.rhsOf(grammar, q))), Bool.and(Nat.is_le(ks, List.length(&2, Nat, input)), Nat.is_le(e, List.length(&2, Nat, input)))), h)

def db_rest(+q: Nat, +d: Nat, +ks: Nat, +e: Nat, +grammar: +List<Core.Production>, +input: +List<Nat>, +h: {Run.descBound(Gll.Desc{q, d, ks, e}, grammar, input) == True{} : Bool})
  -> {Bool.and(Nat.is_le(ks, List.length(&2, Nat, input)), Nat.is_le(e, List.length(&2, Nat, input))) == True{} : Bool}:
  Lemma.and_true_right_side(Nat.is_le(d, List.length(&2, Core.Sym, Core.rhsOf(grammar, q))), Bool.and(Nat.is_le(ks, List.length(&2, Nat, input)), Nat.is_le(e, List.length(&2, Nat, input))),
    Lemma.and_true_right_side(Nat.is_le(1n+q, List.length(&2, Core.Production, grammar)), Bool.and(Nat.is_le(d, List.length(&2, Core.Sym, Core.rhsOf(grammar, q))), Bool.and(Nat.is_le(ks, List.length(&2, Nat, input)), Nat.is_le(e, List.length(&2, Nat, input)))), h))

def db_ks(+q: Nat, +d: Nat, +ks: Nat, +e: Nat, +grammar: +List<Core.Production>, +input: +List<Nat>, +h: {Run.descBound(Gll.Desc{q, d, ks, e}, grammar, input) == True{} : Bool})
  -> {Nat.is_le(ks, List.length(&2, Nat, input)) == True{} : Bool}:
  Lemma.and_true_left(Nat.is_le(ks, List.length(&2, Nat, input)), Nat.is_le(e, List.length(&2, Nat, input)), db_rest(q, d, ks, e, grammar, input, h))

def db_e(+q: Nat, +d: Nat, +ks: Nat, +e: Nat, +grammar: +List<Core.Production>, +input: +List<Nat>, +h: {Run.descBound(Gll.Desc{q, d, ks, e}, grammar, input) == True{} : Bool})
  -> {Nat.is_le(e, List.length(&2, Nat, input)) == True{} : Bool}:
  Lemma.and_true_right_side(Nat.is_le(ks, List.length(&2, Nat, input)), Nat.is_le(e, List.length(&2, Nat, input)), db_rest(q, d, ks, e, grammar, input, h))

def seg_if_any(b: Bool, +s: R.Seg, +grammar: +List<Core.Production>, +input: +List<Nat>, +hs: {segBound(s, grammar, input) == True{} : Bool})
  -> {segsBounded(R.segIf(b, s), grammar, input) == True{} : Bool}:
  match b:
    case True{}:
      Lemma.and_true_intro(segBound(s, grammar, input), True{}, hs, {==})
    case False{}:
      {==}

def seg_if_tok(b: Bool, +x: Bool, +y: Bool, +s: R.Seg, +grammar: +List<Core.Production>, +input: +List<Nat>, +eb: {Bool.and(x, y) == b : Bool},
  f: {x == True{} : Bool} -> {segBound(s, grammar, input) == True{} : Bool})
  -> {segsBounded(R.segIf(b, s), grammar, input) == True{} : Bool}:
  match b:
    case True{}:
      Lemma.and_true_intro(segBound(s, grammar, input), True{}, f(Lemma.and_true_left(x, y, eb)), {==})
    case False{}:
      {==}

# Completing at every segment of ss stays within bounds.
law cw_bounded:
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
  for +hss: {segsBounded(ss, grammar, input) == True{} : Bool}
  for +hq: {Nat.is_le(1n+q, List.length(&2, Core.Production, grammar)) == True{} : Bool}
  for +hd: {Nat.is_le(1n+d, List.length(&2, Core.Sym, Core.rhsOf(grammar, q))) == True{} : Bool}
  for +hks: {Nat.is_le(ks, List.length(&2, Nat, input)) == True{} : Bool}
  {segsBounded(R.completeWith(ss, fuel, grammar, gmarks, input, need, p, q, ks, d, k, f), grammar, input) == True{} : Bool}

def cw_bounded(ss, fuel, grammar, gmarks, input, need, p, q, ks, d, k, f, hss, hq, hd, hks):
  match ss:
    case Nil{}:
      {==}
    case Con{R.Seg{+p2, +k2, +d2, +e, +fp}, +rest}:
      +hh = Lemma.and_true_left(segBound(R.Seg{p2, k2, d2, e, fp}, grammar, input), segsBounded(rest, grammar, input), hss)
      +hit = Bool.and(Bool.and(Nat.is_eq(p2, p), Bool.and(Nat.is_eq(k2, k), Nat.is_eq(d2, List.length(&2, Core.Sym, Core.rhsOf(grammar, p))))),
        Bool.and(R.isYes(R.endTri(Core.rhsOf(grammar, p), fuel, grammar, gmarks, input, p, k, e)),
          Bool.and(Gll.needHolds(need, k, e), R.isYes(R.tri(fuel, grammar, gmarks, input, Core.Bsr{q, 1n+d, ks, k, e})))))
      sb_app(R.segIf(hit, R.Seg{q, ks, 1n+d, e, List.append(&2, Core.Tree, f, [Core.Node{p, fp}])}), R.completeWith(rest, fuel, grammar, gmarks, input, need, p, q, ks, d, k, f), grammar, input,
        seg_if_any(hit, R.Seg{q, ks, 1n+d, e, List.append(&2, Core.Tree, f, [Core.Node{p, fp}])}, grammar, input,
          db_intro(q, 1n+d, ks, e, grammar, input, hq, hd, hks, db_e(p2, d2, k2, e, grammar, input, hh))),
        cw_bounded(rest, fuel, grammar, gmarks, input, need, p, q, ks, d, k, f, Lemma.and_true_right_side(segBound(R.Seg{p2, k2, d2, e, fp}, grammar, input), segsBounded(rest, grammar, input), hss), hq, hd, hks))

def prod_pick_bounded(b: Bool, +segs: +List<R.Seg>, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +need: Core.Need, +p: Nat, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +f: +List<Core.Tree>,
  +hs: {segsBounded(segs, grammar, input) == True{} : Bool}, +hq: {Nat.is_le(1n+q, List.length(&2, Core.Production, grammar)) == True{} : Bool},
  +hd: {Nat.is_le(1n+d, List.length(&2, Core.Sym, Core.rhsOf(grammar, q))) == True{} : Bool}, +hks: {Nat.is_le(ks, List.length(&2, Nat, input)) == True{} : Bool})
  -> {segsBounded(R.prodPick(b, segs, fuel, grammar, gmarks, input, need, p, q, ks, d, k, f), grammar, input) == True{} : Bool}:
  match b:
    case True{}:
      cw_bounded(segs, fuel, grammar, gmarks, input, need, p, q, ks, d, k, f, hs, hq, hd, hks)
    case False{}:
      {==}

def base_shift(+a: Nat, +b: Nat, +c: Nat, +h: {Nat.is_le(1n+Nat.add(a, b), c) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, 1n+b), c) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(a, 1n+b), 1n+Nat.add(a, b), Lemma.add_succ_right(a, b)) : {Nat.is_le(_, c) == True{} : Bool}
  h

# Growing at a nonterminal stays within bounds; g is the grammar from production base on.
law gp_bounded:
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
  for +hg: {Nat.is_le(Nat.add(List.length(&2, Core.Production, g), base), List.length(&2, Core.Production, grammar)) == True{} : Bool}
  for +hs: {segsBounded(segs, grammar, input) == True{} : Bool}
  for +hq: {Nat.is_le(1n+q, List.length(&2, Core.Production, grammar)) == True{} : Bool}
  for +hd: {Nat.is_le(1n+d, List.length(&2, Core.Sym, Core.rhsOf(grammar, q))) == True{} : Bool}
  for +hks: {Nat.is_le(ks, List.length(&2, Nat, input)) == True{} : Bool}
  for +hk: {Nat.is_le(k, List.length(&2, Nat, input)) == True{} : Bool}
  {segsBounded(R.growProds(g, base, fuel, grammar, gmarks, input, segs, x, need, q, ks, d, k, f), grammar, input) == True{} : Bool}

def gp_bounded(g, base, fuel, grammar, gmarks, input, segs, x, need, q, ks, d, k, f, hg, hs, hq, hd, hks, hk):
  match g:
    case Nil{}:
      {==}
    case Con{Core.Production{+lhs, +rhs}, +rest}:
      +hb = Lemma.le_trans(1n+base, 1n+Nat.add(List.length(&2, Core.Production, rest), base), List.length(&2, Core.Production, grammar), Lemma.le_add_left(List.length(&2, Core.Production, rest), base), hg)
      sb_app(R.segIf(Nat.is_eq(lhs, x), R.Seg{base, k, 0n, k, []}),
        List.append(&2, R.Seg, R.prodPick(Nat.is_eq(lhs, x), segs, fuel, grammar, gmarks, input, need, base, q, ks, d, k, f), R.growProds(rest, 1n+base, fuel, grammar, gmarks, input, segs, x, need, q, ks, d, k, f)), grammar, input,
        seg_if_any(Nat.is_eq(lhs, x), R.Seg{base, k, 0n, k, []}, grammar, input,
          db_intro(base, 0n, k, k, grammar, input, hb, Lemma.zero_le(List.length(&2, Core.Sym, Core.rhsOf(grammar, base))), hk, hk)),
        sb_app(R.prodPick(Nat.is_eq(lhs, x), segs, fuel, grammar, gmarks, input, need, base, q, ks, d, k, f), R.growProds(rest, 1n+base, fuel, grammar, gmarks, input, segs, x, need, q, ks, d, k, f), grammar, input,
          prod_pick_bounded(Nat.is_eq(lhs, x), segs, fuel, grammar, gmarks, input, need, base, q, ks, d, k, f, hs, hq, hd, hks),
          gp_bounded(rest, 1n+base, fuel, grammar, gmarks, input, segs, x, need, q, ks, d, k, f, base_shift(List.length(&2, Core.Production, rest), base, List.length(&2, Core.Production, grammar), hg), hs, hq, hd, hks, hk)))

def add_len_zero(+grammar: +List<Core.Production>) -> {Nat.is_le(Nat.add(List.length(&2, Core.Production, grammar), 0n), List.length(&2, Core.Production, grammar)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(List.length(&2, Core.Production, grammar), 0n), List.length(&2, Core.Production, grammar), Lemma.add_zero_right(List.length(&2, Core.Production, grammar))) : {Nat.is_le(_, List.length(&2, Core.Production, grammar)) == True{} : Bool}
  Lemma.le_refl(List.length(&2, Core.Production, grammar))

def gi_sym(sym: Core.Sym, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +segs: +List<R.Seg>, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +f: +List<Core.Tree>,
  +ei: {Gll.nthSym(Core.rhsOf(grammar, q), d) == Some{sym} : Maybe<&2, Core.Sym>},
  +hq: {Nat.is_le(1n+q, List.length(&2, Core.Production, grammar)) == True{} : Bool}, +hks: {Nat.is_le(ks, List.length(&2, Nat, input)) == True{} : Bool}, +hk: {Nat.is_le(k, List.length(&2, Nat, input)) == True{} : Bool},
  +hs: {segsBounded(segs, grammar, input) == True{} : Bool})
  -> {segsBounded(R.growItem(Some{sym}, fuel, grammar, gmarks, input, segs, q, ks, d, k, f), grammar, input) == True{} : Bool}:
  match sym:
    case Core.Terminal{+t}:
      seg_if_tok(Bool.and(Core.tokIs(Core.tokAt(input, k), t), R.isYes(R.tri(fuel, grammar, gmarks, input, Core.Bsr{q, 1n+d, ks, k, 1n+k}))), Core.tokIs(Core.tokAt(input, k), t), R.isYes(R.tri(fuel, grammar, gmarks, input, Core.Bsr{q, 1n+d, ks, k, 1n+k})),
        R.Seg{q, ks, 1n+d, 1n+k, List.append(&2, Core.Tree, f, [Core.Leaf{t}])}, grammar, input, {==},
        ht => db_intro(q, 1n+d, ks, 1n+k, grammar, input, hq, RN.nth_lt(Core.rhsOf(grammar, q), d, Core.Terminal{t}, ei), hks, RN.tok_lt(input, k, t, ht)))
    case Core.Nonterminal{+x, +need}:
      gp_bounded(grammar, 0n, fuel, grammar, gmarks, input, segs, x, need, q, ks, d, k, f, add_len_zero(grammar), hs, hq, RN.nth_lt(Core.rhsOf(grammar, q), d, Core.Nonterminal{x, need}, ei), hks, hk)

def gi_bounded(item: Maybe<&2, Core.Sym>, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +segs: +List<R.Seg>, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +f: +List<Core.Tree>,
  +ei: {Gll.nthSym(Core.rhsOf(grammar, q), d) == item : Maybe<&2, Core.Sym>},
  +hq: {Nat.is_le(1n+q, List.length(&2, Core.Production, grammar)) == True{} : Bool}, +hks: {Nat.is_le(ks, List.length(&2, Nat, input)) == True{} : Bool}, +hk: {Nat.is_le(k, List.length(&2, Nat, input)) == True{} : Bool},
  +hs: {segsBounded(segs, grammar, input) == True{} : Bool})
  -> {segsBounded(R.growItem(item, fuel, grammar, gmarks, input, segs, q, ks, d, k, f), grammar, input) == True{} : Bool}:
  match item:
    case Some{+sym}:
      gi_sym(sym, fuel, grammar, gmarks, input, segs, q, ks, d, k, f, ei, hq, hks, hk, hs)
    case None{}:
      {==}

# One round of growth stays within bounds.
law ga_bounded:
  for ss: +List<R.Seg>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +input: +List<Nat>
  for +segs: +List<R.Seg>
  for +hss: {segsBounded(ss, grammar, input) == True{} : Bool}
  for +hs: {segsBounded(segs, grammar, input) == True{} : Bool}
  {segsBounded(R.growAll(ss, fuel, grammar, gmarks, input, segs), grammar, input) == True{} : Bool}

def ga_bounded(ss, fuel, grammar, gmarks, input, segs, hss, hs):
  match ss:
    case Nil{}:
      {==}
    case Con{R.Seg{+q, +ks, +d, +k, +f}, +rest}:
      +hh = Lemma.and_true_left(segBound(R.Seg{q, ks, d, k, f}, grammar, input), segsBounded(rest, grammar, input), hss)
      sb_app(R.growItem(Gll.nthSym(Core.rhsOf(grammar, q), d), fuel, grammar, gmarks, input, segs, q, ks, d, k, f), R.growAll(rest, fuel, grammar, gmarks, input, segs), grammar, input,
        gi_bounded(Gll.nthSym(Core.rhsOf(grammar, q), d), fuel, grammar, gmarks, input, segs, q, ks, d, k, f, {==}, db_q(q, d, ks, k, grammar, input, hh), db_ks(q, d, ks, k, grammar, input, hh), db_e(q, d, ks, k, grammar, input, hh), hs),
        ga_bounded(rest, fuel, grammar, gmarks, input, segs, Lemma.and_true_right_side(segBound(R.Seg{q, ks, d, k, f}, grammar, input), segsBounded(rest, grammar, input), hss), hs))

# ======== A ROUND THAT ADDS NOTHING: THE SET IS CLOSED ========

law ah_left:
  for a: +List<R.Seg>
  for +b: +List<R.Seg>
  for +segs: +List<R.Seg>
  for +h: {allHave(List.append(&2, R.Seg, a, b), segs) == True{} : Bool}
  {allHave(a, segs) == True{} : Bool}

def ah_left(a, b, segs, h):
  match a:
    case Nil{}:
      {==}
    case Con{R.Seg{+q, +ks, +d, +e, +f}, +rest}:
      Lemma.and_true_intro(R.hasSeg(q, ks, d, e, segs), allHave(rest, segs), Lemma.and_true_left(R.hasSeg(q, ks, d, e, segs), allHave(List.append(&2, R.Seg, rest, b), segs), h),
        ah_left(rest, b, segs, Lemma.and_true_right_side(R.hasSeg(q, ks, d, e, segs), allHave(List.append(&2, R.Seg, rest, b), segs), h)))

law ah_right:
  for a: +List<R.Seg>
  for +b: +List<R.Seg>
  for +segs: +List<R.Seg>
  for +h: {allHave(List.append(&2, R.Seg, a, b), segs) == True{} : Bool}
  {allHave(b, segs) == True{} : Bool}

def ah_right(a, b, segs, h):
  match a:
    case Nil{}:
      h
    case Con{R.Seg{+q, +ks, +d, +e, +f}, +rest}:
      ah_right(rest, b, segs, Lemma.and_true_right_side(R.hasSeg(q, ks, d, e, segs), allHave(List.append(&2, R.Seg, rest, b), segs), h))

def seg_has(b: Bool, +q: Nat, +ks: Nat, +d: Nat, +e: Nat, +f: +List<Core.Tree>, +segs: +List<R.Seg>, +eb: {b == True{} : Bool},
  +h: {allHave(R.segIf(b, R.Seg{q, ks, d, e, f}), segs) == True{} : Bool}) -> {R.hasSeg(q, ks, d, e, segs) == True{} : Bool}:
  match b:
    case True{}:
      Lemma.and_true_left(R.hasSeg(q, ks, d, e, segs), True{}, h)
    case False{}:
      Empty.absurd({R.hasSeg(q, ks, d, e, segs) == True{} : Bool}, Lemma.false_is_not_true(eb))

def when_by(b: Bool, +c: Bool, f: {b == True{} : Bool} -> {c == True{} : Bool}) -> {R.whenB(b, c) == True{} : Bool}:
  match b:
    case True{}:
      f({==})
    case False{}:
      {==}

def end_decided(rhs: +List<Core.Sym>, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +p: Nat, +k: Nat, +e: Nat, +hdec: {decided(fuel, grammar, gmarks, input) == True{} : Bool},
  +hp: {Nat.is_le(1n+p, List.length(&2, Core.Production, grammar)) == True{} : Bool}, +hk: {Nat.is_le(k, List.length(&2, Nat, input)) == True{} : Bool}, +he: {Nat.is_le(e, List.length(&2, Nat, input)) == True{} : Bool})
  -> {decidedTri(R.endTri(rhs, fuel, grammar, gmarks, input, p, k, e)) == True{} : Bool}:
  match rhs:
    case Nil{}:
      decided_at(fuel, grammar, gmarks, input, p, 0n, k, k, e, hdec,
        Lemma.and_true_intro(Run.descBound(Gll.Desc{p, 0n, k, e}, grammar, input), Nat.is_le(k, List.length(&2, Nat, input)), db_intro(p, 0n, k, e, grammar, input, hp, Lemma.zero_le(List.length(&2, Core.Sym, Core.rhsOf(grammar, p))), hk, he), hk))
    case Con{+s, +rest}:
      {==}

def comp_in3(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +segs: +List<R.Seg>, +need: Core.Need, +p: Nat, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +f: +List<Core.Tree>, +p2: Nat, +k2: Nat, +d2: Nat, +e: Nat, +fp: +List<Core.Tree>,
  +hm: {Bool.and(Nat.is_eq(p2, p), Bool.and(Nat.is_eq(k2, k), Nat.is_eq(d2, List.length(&2, Core.Sym, Core.rhsOf(grammar, p))))) == True{} : Bool}, +y1: {R.isYes(R.endTri(Core.rhsOf(grammar, p), fuel, grammar, gmarks, input, p, k, e)) == True{} : Bool}, +yn: {Gll.needHolds(need, k, e) == True{} : Bool},
  +y2: {R.isYes(R.tri(fuel, grammar, gmarks, input, Core.Bsr{q, 1n+d, ks, k, e})) == True{} : Bool},
  +h: {allHave(R.segIf(Bool.and(Bool.and(Nat.is_eq(p2, p), Bool.and(Nat.is_eq(k2, k), Nat.is_eq(d2, List.length(&2, Core.Sym, Core.rhsOf(grammar, p))))), Bool.and(R.isYes(R.endTri(Core.rhsOf(grammar, p), fuel, grammar, gmarks, input, p, k, e)), Bool.and(Gll.needHolds(need, k, e), R.isYes(R.tri(fuel, grammar, gmarks, input, Core.Bsr{q, 1n+d, ks, k, e}))))), R.Seg{q, ks, 1n+d, e, List.append(&2, Core.Tree, f, [Core.Node{p, fp}])}), segs) == True{} : Bool})
  -> {R.hasSeg(q, ks, 1n+d, e, segs) == True{} : Bool}:
  seg_has(Bool.and(Bool.and(Nat.is_eq(p2, p), Bool.and(Nat.is_eq(k2, k), Nat.is_eq(d2, List.length(&2, Core.Sym, Core.rhsOf(grammar, p))))), Bool.and(R.isYes(R.endTri(Core.rhsOf(grammar, p), fuel, grammar, gmarks, input, p, k, e)), Bool.and(Gll.needHolds(need, k, e), R.isYes(R.tri(fuel, grammar, gmarks, input, Core.Bsr{q, 1n+d, ks, k, e}))))), q, ks, 1n+d, e, List.append(&2, Core.Tree, f, [Core.Node{p, fp}]), segs,
    Lemma.and_true_intro(Bool.and(Nat.is_eq(p2, p), Bool.and(Nat.is_eq(k2, k), Nat.is_eq(d2, List.length(&2, Core.Sym, Core.rhsOf(grammar, p))))), Bool.and(R.isYes(R.endTri(Core.rhsOf(grammar, p), fuel, grammar, gmarks, input, p, k, e)), Bool.and(Gll.needHolds(need, k, e), R.isYes(R.tri(fuel, grammar, gmarks, input, Core.Bsr{q, 1n+d, ks, k, e})))), hm,
      Lemma.and_true_intro(R.isYes(R.endTri(Core.rhsOf(grammar, p), fuel, grammar, gmarks, input, p, k, e)), Bool.and(Gll.needHolds(need, k, e), R.isYes(R.tri(fuel, grammar, gmarks, input, Core.Bsr{q, 1n+d, ks, k, e}))), y1,
        Lemma.and_true_intro(Gll.needHolds(need, k, e), R.isYes(R.tri(fuel, grammar, gmarks, input, Core.Bsr{q, 1n+d, ks, k, e})), yn, y2))), h)

def comp_in2(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +segs: +List<R.Seg>, +need: Core.Need, +p: Nat, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +f: +List<Core.Tree>, +p2: Nat, +k2: Nat, +d2: Nat, +e: Nat, +fp: +List<Core.Tree>,
  +hm: {Bool.and(Nat.is_eq(p2, p), Bool.and(Nat.is_eq(k2, k), Nat.is_eq(d2, List.length(&2, Core.Sym, Core.rhsOf(grammar, p))))) == True{} : Bool}, +y1: {R.isYes(R.endTri(Core.rhsOf(grammar, p), fuel, grammar, gmarks, input, p, k, e)) == True{} : Bool}, +yn: {Gll.needHolds(need, k, e) == True{} : Bool},
  +h: {allHave(R.segIf(Bool.and(Bool.and(Nat.is_eq(p2, p), Bool.and(Nat.is_eq(k2, k), Nat.is_eq(d2, List.length(&2, Core.Sym, Core.rhsOf(grammar, p))))), Bool.and(R.isYes(R.endTri(Core.rhsOf(grammar, p), fuel, grammar, gmarks, input, p, k, e)), Bool.and(Gll.needHolds(need, k, e), R.isYes(R.tri(fuel, grammar, gmarks, input, Core.Bsr{q, 1n+d, ks, k, e}))))), R.Seg{q, ks, 1n+d, e, List.append(&2, Core.Tree, f, [Core.Node{p, fp}])}), segs) == True{} : Bool},
  +hdec: {decided(fuel, grammar, gmarks, input) == True{} : Bool}, +hq: {Nat.is_le(1n+q, List.length(&2, Core.Production, grammar)) == True{} : Bool},
  +hd: {Nat.is_le(1n+d, List.length(&2, Core.Sym, Core.rhsOf(grammar, q))) == True{} : Bool}, +hks: {Nat.is_le(ks, List.length(&2, Nat, input)) == True{} : Bool},
  +hk: {Nat.is_le(k, List.length(&2, Nat, input)) == True{} : Bool}, +he: {Nat.is_le(e, List.length(&2, Nat, input)) == True{} : Bool})
  -> {R.clause(R.tri(fuel, grammar, gmarks, input, Core.Bsr{q, 1n+d, ks, k, e}), R.hasSeg(q, ks, 1n+d, e, segs)) == True{} : Bool}:
  clause_by(R.tri(fuel, grammar, gmarks, input, Core.Bsr{q, 1n+d, ks, k, e}), R.hasSeg(q, ks, 1n+d, e, segs),
    decided_at(fuel, grammar, gmarks, input, q, 1n+d, ks, k, e, hdec, Lemma.and_true_intro(Run.descBound(Gll.Desc{q, 1n+d, ks, e}, grammar, input), Nat.is_le(k, List.length(&2, Nat, input)), db_intro(q, 1n+d, ks, e, grammar, input, hq, hd, hks, he), hk)),
    y2 => comp_in3(fuel, grammar, gmarks, input, segs, need, p, q, ks, d, k, f, p2, k2, d2, e, fp, hm, y1, yn, y2, h))

def comp_in1(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +segs: +List<R.Seg>, +need: Core.Need, +p: Nat, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +f: +List<Core.Tree>, +p2: Nat, +k2: Nat, +d2: Nat, +e: Nat, +fp: +List<Core.Tree>,
  +hm: {Bool.and(Nat.is_eq(p2, p), Bool.and(Nat.is_eq(k2, k), Nat.is_eq(d2, List.length(&2, Core.Sym, Core.rhsOf(grammar, p))))) == True{} : Bool}, +y1: {R.isYes(R.endTri(Core.rhsOf(grammar, p), fuel, grammar, gmarks, input, p, k, e)) == True{} : Bool},
  +h: {allHave(R.segIf(Bool.and(Bool.and(Nat.is_eq(p2, p), Bool.and(Nat.is_eq(k2, k), Nat.is_eq(d2, List.length(&2, Core.Sym, Core.rhsOf(grammar, p))))), Bool.and(R.isYes(R.endTri(Core.rhsOf(grammar, p), fuel, grammar, gmarks, input, p, k, e)), Bool.and(Gll.needHolds(need, k, e), R.isYes(R.tri(fuel, grammar, gmarks, input, Core.Bsr{q, 1n+d, ks, k, e}))))), R.Seg{q, ks, 1n+d, e, List.append(&2, Core.Tree, f, [Core.Node{p, fp}])}), segs) == True{} : Bool},
  +hdec: {decided(fuel, grammar, gmarks, input) == True{} : Bool}, +hq: {Nat.is_le(1n+q, List.length(&2, Core.Production, grammar)) == True{} : Bool},
  +hd: {Nat.is_le(1n+d, List.length(&2, Core.Sym, Core.rhsOf(grammar, q))) == True{} : Bool}, +hks: {Nat.is_le(ks, List.length(&2, Nat, input)) == True{} : Bool},
  +hk: {Nat.is_le(k, List.length(&2, Nat, input)) == True{} : Bool}, +he: {Nat.is_le(e, List.length(&2, Nat, input)) == True{} : Bool})
  -> {R.whenB(Gll.needHolds(need, k, e), R.clause(R.tri(fuel, grammar, gmarks, input, Core.Bsr{q, 1n+d, ks, k, e}), R.hasSeg(q, ks, 1n+d, e, segs))) == True{} : Bool}:
  when_by(Gll.needHolds(need, k, e), R.clause(R.tri(fuel, grammar, gmarks, input, Core.Bsr{q, 1n+d, ks, k, e}), R.hasSeg(q, ks, 1n+d, e, segs)),
    yn => comp_in2(fuel, grammar, gmarks, input, segs, need, p, q, ks, d, k, f, p2, k2, d2, e, fp, hm, y1, yn, h, hdec, hq, hd, hks, hk, he))

def comp_in(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +segs: +List<R.Seg>, +need: Core.Need, +p: Nat, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +f: +List<Core.Tree>, +p2: Nat, +k2: Nat, +d2: Nat, +e: Nat, +fp: +List<Core.Tree>,
  +hm: {Bool.and(Nat.is_eq(p2, p), Bool.and(Nat.is_eq(k2, k), Nat.is_eq(d2, List.length(&2, Core.Sym, Core.rhsOf(grammar, p))))) == True{} : Bool},
  +h: {allHave(R.segIf(Bool.and(Bool.and(Nat.is_eq(p2, p), Bool.and(Nat.is_eq(k2, k), Nat.is_eq(d2, List.length(&2, Core.Sym, Core.rhsOf(grammar, p))))), Bool.and(R.isYes(R.endTri(Core.rhsOf(grammar, p), fuel, grammar, gmarks, input, p, k, e)), Bool.and(Gll.needHolds(need, k, e), R.isYes(R.tri(fuel, grammar, gmarks, input, Core.Bsr{q, 1n+d, ks, k, e}))))), R.Seg{q, ks, 1n+d, e, List.append(&2, Core.Tree, f, [Core.Node{p, fp}])}), segs) == True{} : Bool},
  +hdec: {decided(fuel, grammar, gmarks, input) == True{} : Bool}, +hp: {Nat.is_le(1n+p, List.length(&2, Core.Production, grammar)) == True{} : Bool}, +hq: {Nat.is_le(1n+q, List.length(&2, Core.Production, grammar)) == True{} : Bool},
  +hd: {Nat.is_le(1n+d, List.length(&2, Core.Sym, Core.rhsOf(grammar, q))) == True{} : Bool}, +hks: {Nat.is_le(ks, List.length(&2, Nat, input)) == True{} : Bool},
  +hk: {Nat.is_le(k, List.length(&2, Nat, input)) == True{} : Bool}, +he: {Nat.is_le(e, List.length(&2, Nat, input)) == True{} : Bool})
  -> {R.compOk(fuel, grammar, gmarks, input, segs, need, p, q, ks, d, k, e) == True{} : Bool}:
  clause_by(R.endTri(Core.rhsOf(grammar, p), fuel, grammar, gmarks, input, p, k, e), R.whenB(Gll.needHolds(need, k, e), R.clause(R.tri(fuel, grammar, gmarks, input, Core.Bsr{q, 1n+d, ks, k, e}), R.hasSeg(q, ks, 1n+d, e, segs))),
    end_decided(Core.rhsOf(grammar, p), fuel, grammar, gmarks, input, p, k, e, hdec, hp, hk, he),
    y1 => comp_in1(fuel, grammar, gmarks, input, segs, need, p, q, ks, d, k, f, p2, k2, d2, e, fp, hm, y1, h, hdec, hq, hd, hks, hk, he))

# Completions all present: every completed segment of p lets the prefix go on.
law comps_ok:
  for ss: +List<R.Seg>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +input: +List<Nat>
  for +segs: +List<R.Seg>
  for +need: Core.Need
  for +p: Nat
  for +q: Nat
  for +ks: Nat
  for +d: Nat
  for +k: Nat
  for +f: +List<Core.Tree>
  for +h: {allHave(R.completeWith(ss, fuel, grammar, gmarks, input, need, p, q, ks, d, k, f), segs) == True{} : Bool}
  for +hss: {segsBounded(ss, grammar, input) == True{} : Bool}
  for +hdec: {decided(fuel, grammar, gmarks, input) == True{} : Bool}
  for +hp: {Nat.is_le(1n+p, List.length(&2, Core.Production, grammar)) == True{} : Bool}
  for +hq: {Nat.is_le(1n+q, List.length(&2, Core.Production, grammar)) == True{} : Bool}
  for +hd: {Nat.is_le(1n+d, List.length(&2, Core.Sym, Core.rhsOf(grammar, q))) == True{} : Bool}
  for +hks: {Nat.is_le(ks, List.length(&2, Nat, input)) == True{} : Bool}
  for +hk: {Nat.is_le(k, List.length(&2, Nat, input)) == True{} : Bool}
  {R.compsOk(ss, fuel, grammar, gmarks, input, segs, need, p, q, ks, d, k) == True{} : Bool}

def comps_ok(ss, fuel, grammar, gmarks, input, segs, need, p, q, ks, d, k, f, h, hss, hdec, hp, hq, hd, hks, hk):
  match ss:
    case Nil{}:
      {==}
    case Con{R.Seg{+p2, +k2, +d2, +e, +fp}, +rest}:
      +hh = Lemma.and_true_left(segBound(R.Seg{p2, k2, d2, e, fp}, grammar, input), segsBounded(rest, grammar, input), hss)
      +hrest = Lemma.and_true_right_side(segBound(R.Seg{p2, k2, d2, e, fp}, grammar, input), segsBounded(rest, grammar, input), hss)
      +s1 = R.segIf(Bool.and(Bool.and(Nat.is_eq(p2, p), Bool.and(Nat.is_eq(k2, k), Nat.is_eq(d2, List.length(&2, Core.Sym, Core.rhsOf(grammar, p))))), Bool.and(R.isYes(R.endTri(Core.rhsOf(grammar, p), fuel, grammar, gmarks, input, p, k, e)), Bool.and(Gll.needHolds(need, k, e), R.isYes(R.tri(fuel, grammar, gmarks, input, Core.Bsr{q, 1n+d, ks, k, e}))))), R.Seg{q, ks, 1n+d, e, List.append(&2, Core.Tree, f, [Core.Node{p, fp}])})
      +s2 = R.completeWith(rest, fuel, grammar, gmarks, input, need, p, q, ks, d, k, f)
      Lemma.and_true_intro(R.whenB(Bool.and(Nat.is_eq(p2, p), Bool.and(Nat.is_eq(k2, k), Nat.is_eq(d2, List.length(&2, Core.Sym, Core.rhsOf(grammar, p))))), R.compOk(fuel, grammar, gmarks, input, segs, need, p, q, ks, d, k, e)), R.compsOk(rest, fuel, grammar, gmarks, input, segs, need, p, q, ks, d, k),
        when_by(Bool.and(Nat.is_eq(p2, p), Bool.and(Nat.is_eq(k2, k), Nat.is_eq(d2, List.length(&2, Core.Sym, Core.rhsOf(grammar, p))))), R.compOk(fuel, grammar, gmarks, input, segs, need, p, q, ks, d, k, e),
          hm => comp_in(fuel, grammar, gmarks, input, segs, need, p, q, ks, d, k, f, p2, k2, d2, e, fp, hm, ah_left(s1, s2, segs, h), hdec, hp, hq, hd, hks, hk, db_e(p2, d2, k2, e, grammar, input, hh))),
        comps_ok(rest, fuel, grammar, gmarks, input, segs, need, p, q, ks, d, k, f, ah_right(s1, s2, segs, h), hrest, hdec, hp, hq, hd, hks, hk))

def pp_when(b: Bool, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +segs: +List<R.Seg>, +need: Core.Need, +base: Nat, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +f: +List<Core.Tree>,
  +h1: {allHave(R.segIf(b, R.Seg{base, k, 0n, k, []}), segs) == True{} : Bool},
  +h2: {allHave(R.prodPick(b, segs, fuel, grammar, gmarks, input, need, base, q, ks, d, k, f), segs) == True{} : Bool},
  +hs: {segsBounded(segs, grammar, input) == True{} : Bool}, +hdec: {decided(fuel, grammar, gmarks, input) == True{} : Bool}, +hp: {Nat.is_le(1n+base, List.length(&2, Core.Production, grammar)) == True{} : Bool},
  +hq: {Nat.is_le(1n+q, List.length(&2, Core.Production, grammar)) == True{} : Bool}, +hd: {Nat.is_le(1n+d, List.length(&2, Core.Sym, Core.rhsOf(grammar, q))) == True{} : Bool},
  +hks: {Nat.is_le(ks, List.length(&2, Nat, input)) == True{} : Bool}, +hk: {Nat.is_le(k, List.length(&2, Nat, input)) == True{} : Bool})
  -> {R.whenB(b, Bool.and(R.hasSeg(base, k, 0n, k, segs), R.compsOk(segs, fuel, grammar, gmarks, input, segs, need, base, q, ks, d, k))) == True{} : Bool}:
  match b:
    case True{}:
      Lemma.and_true_intro(R.hasSeg(base, k, 0n, k, segs), R.compsOk(segs, fuel, grammar, gmarks, input, segs, need, base, q, ks, d, k),
        seg_has(True{}, base, k, 0n, k, [], segs, {==}, h1), comps_ok(segs, fuel, grammar, gmarks, input, segs, need, base, q, ks, d, k, f, h2, hs, hdec, hp, hq, hd, hks, hk))
    case False{}:
      {==}

# Growth at a nonterminal all present: every production of x is started and completed on.
law prods_ok:
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
  for +h: {allHave(R.growProds(g, base, fuel, grammar, gmarks, input, segs, x, need, q, ks, d, k, f), segs) == True{} : Bool}
  for +hg: {Nat.is_le(Nat.add(List.length(&2, Core.Production, g), base), List.length(&2, Core.Production, grammar)) == True{} : Bool}
  for +hs: {segsBounded(segs, grammar, input) == True{} : Bool}
  for +hdec: {decided(fuel, grammar, gmarks, input) == True{} : Bool}
  for +hq: {Nat.is_le(1n+q, List.length(&2, Core.Production, grammar)) == True{} : Bool}
  for +hd: {Nat.is_le(1n+d, List.length(&2, Core.Sym, Core.rhsOf(grammar, q))) == True{} : Bool}
  for +hks: {Nat.is_le(ks, List.length(&2, Nat, input)) == True{} : Bool}
  for +hk: {Nat.is_le(k, List.length(&2, Nat, input)) == True{} : Bool}
  {R.prodsOk(g, base, fuel, grammar, gmarks, input, segs, x, need, q, ks, d, k) == True{} : Bool}

def prods_ok(g, base, fuel, grammar, gmarks, input, segs, x, need, q, ks, d, k, f, h, hg, hs, hdec, hq, hd, hks, hk):
  match g:
    case Nil{}:
      {==}
    case Con{Core.Production{+lhs, +rhs}, +rest}:
      +hb = Lemma.le_trans(1n+base, 1n+Nat.add(List.length(&2, Core.Production, rest), base), List.length(&2, Core.Production, grammar), Lemma.le_add_left(List.length(&2, Core.Production, rest), base), hg)
      +a1 = R.segIf(Nat.is_eq(lhs, x), R.Seg{base, k, 0n, k, []})
      +a2 = R.prodPick(Nat.is_eq(lhs, x), segs, fuel, grammar, gmarks, input, need, base, q, ks, d, k, f)
      +a3 = R.growProds(rest, 1n+base, fuel, grammar, gmarks, input, segs, x, need, q, ks, d, k, f)
      +h23 = ah_right(a1, List.append(&2, R.Seg, a2, a3), segs, h)
      Lemma.and_true_intro(R.whenB(Nat.is_eq(lhs, x), Bool.and(R.hasSeg(base, k, 0n, k, segs), R.compsOk(segs, fuel, grammar, gmarks, input, segs, need, base, q, ks, d, k))), R.prodsOk(rest, 1n+base, fuel, grammar, gmarks, input, segs, x, need, q, ks, d, k),
        pp_when(Nat.is_eq(lhs, x), fuel, grammar, gmarks, input, segs, need, base, q, ks, d, k, f, ah_left(a1, List.append(&2, R.Seg, a2, a3), segs, h), ah_left(a2, a3, segs, h23), hs, hdec, hb, hq, hd, hks, hk),
        prods_ok(rest, 1n+base, fuel, grammar, gmarks, input, segs, x, need, q, ks, d, k, f, ah_right(a2, a3, segs, h23), base_shift(List.length(&2, Core.Production, rest), base, List.length(&2, Core.Production, grammar), hg), hs, hdec, hq, hd, hks, hk))

def ext_tok(+t: Nat, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +segs: +List<R.Seg>, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +f: +List<Core.Tree>,
  +ei: {Gll.nthSym(Core.rhsOf(grammar, q), d) == Some{Core.Terminal{t}} : Maybe<&2, Core.Sym>},
  +hq: {Nat.is_le(1n+q, List.length(&2, Core.Production, grammar)) == True{} : Bool}, +hks: {Nat.is_le(ks, List.length(&2, Nat, input)) == True{} : Bool}, +hk: {Nat.is_le(k, List.length(&2, Nat, input)) == True{} : Bool},
  +hdec: {decided(fuel, grammar, gmarks, input) == True{} : Bool}, +ht: {Core.tokIs(Core.tokAt(input, k), t) == True{} : Bool},
  +h: {allHave(R.growItem(Some{Core.Terminal{t}}, fuel, grammar, gmarks, input, segs, q, ks, d, k, f), segs) == True{} : Bool})
  -> {R.clause(R.tri(fuel, grammar, gmarks, input, Core.Bsr{q, 1n+d, ks, k, 1n+k}), R.hasSeg(q, ks, 1n+d, 1n+k, segs)) == True{} : Bool}:
  clause_by(R.tri(fuel, grammar, gmarks, input, Core.Bsr{q, 1n+d, ks, k, 1n+k}), R.hasSeg(q, ks, 1n+d, 1n+k, segs),
    decided_at(fuel, grammar, gmarks, input, q, 1n+d, ks, k, 1n+k, hdec, Lemma.and_true_intro(Run.descBound(Gll.Desc{q, 1n+d, ks, 1n+k}, grammar, input), Nat.is_le(k, List.length(&2, Nat, input)),
      db_intro(q, 1n+d, ks, 1n+k, grammar, input, hq, RN.nth_lt(Core.rhsOf(grammar, q), d, Core.Terminal{t}, ei), hks, RN.tok_lt(input, k, t, ht)), hk)),
    hy => seg_has(Bool.and(Core.tokIs(Core.tokAt(input, k), t), R.isYes(R.tri(fuel, grammar, gmarks, input, Core.Bsr{q, 1n+d, ks, k, 1n+k}))), q, ks, 1n+d, 1n+k, List.append(&2, Core.Tree, f, [Core.Leaf{t}]), segs,
      Lemma.and_true_intro(Core.tokIs(Core.tokAt(input, k), t), R.isYes(R.tri(fuel, grammar, gmarks, input, Core.Bsr{q, 1n+d, ks, k, 1n+k})), ht, hy), h))

def ext_sym(sym: Core.Sym, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +segs: +List<R.Seg>, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +f: +List<Core.Tree>,
  +ei: {Gll.nthSym(Core.rhsOf(grammar, q), d) == Some{sym} : Maybe<&2, Core.Sym>},
  +hq: {Nat.is_le(1n+q, List.length(&2, Core.Production, grammar)) == True{} : Bool}, +hks: {Nat.is_le(ks, List.length(&2, Nat, input)) == True{} : Bool}, +hk: {Nat.is_le(k, List.length(&2, Nat, input)) == True{} : Bool},
  +hs: {segsBounded(segs, grammar, input) == True{} : Bool}, +hdec: {decided(fuel, grammar, gmarks, input) == True{} : Bool},
  +h: {allHave(R.growItem(Some{sym}, fuel, grammar, gmarks, input, segs, q, ks, d, k, f), segs) == True{} : Bool})
  -> {R.extOk(Some{sym}, fuel, grammar, gmarks, input, segs, q, ks, d, k) == True{} : Bool}:
  match sym:
    case Core.Terminal{+t}:
      when_by(Core.tokIs(Core.tokAt(input, k), t), R.clause(R.tri(fuel, grammar, gmarks, input, Core.Bsr{q, 1n+d, ks, k, 1n+k}), R.hasSeg(q, ks, 1n+d, 1n+k, segs)),
        ht => ext_tok(t, fuel, grammar, gmarks, input, segs, q, ks, d, k, f, ei, hq, hks, hk, hdec, ht, h))
    case Core.Nonterminal{+x, +need}:
      prods_ok(grammar, 0n, fuel, grammar, gmarks, input, segs, x, need, q, ks, d, k, f, h, add_len_zero(grammar), hs, hdec, hq, RN.nth_lt(Core.rhsOf(grammar, q), d, Core.Nonterminal{x, need}, ei), hks, hk)

def ext_ok(item: Maybe<&2, Core.Sym>, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +segs: +List<R.Seg>, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +f: +List<Core.Tree>,
  +ei: {Gll.nthSym(Core.rhsOf(grammar, q), d) == item : Maybe<&2, Core.Sym>},
  +hq: {Nat.is_le(1n+q, List.length(&2, Core.Production, grammar)) == True{} : Bool}, +hks: {Nat.is_le(ks, List.length(&2, Nat, input)) == True{} : Bool}, +hk: {Nat.is_le(k, List.length(&2, Nat, input)) == True{} : Bool},
  +hs: {segsBounded(segs, grammar, input) == True{} : Bool}, +hdec: {decided(fuel, grammar, gmarks, input) == True{} : Bool},
  +h: {allHave(R.growItem(item, fuel, grammar, gmarks, input, segs, q, ks, d, k, f), segs) == True{} : Bool})
  -> {R.extOk(item, fuel, grammar, gmarks, input, segs, q, ks, d, k) == True{} : Bool}:
  match item:
    case Some{+sym}:
      ext_sym(sym, fuel, grammar, gmarks, input, segs, q, ks, d, k, f, ei, hq, hks, hk, hs, hdec, h)
    case None{}:
      {==}

# A round whose segments are all present: the set is closed.
law closed_from:
  for ss: +List<R.Seg>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +input: +List<Nat>
  for +segs: +List<R.Seg>
  for +hss: {segsBounded(ss, grammar, input) == True{} : Bool}
  for +hs: {segsBounded(segs, grammar, input) == True{} : Bool}
  for +hdec: {decided(fuel, grammar, gmarks, input) == True{} : Bool}
  for +h: {allHave(R.growAll(ss, fuel, grammar, gmarks, input, segs), segs) == True{} : Bool}
  {R.closedAll(ss, fuel, grammar, gmarks, input, segs) == True{} : Bool}

def closed_from(ss, fuel, grammar, gmarks, input, segs, hss, hs, hdec, h):
  match ss:
    case Nil{}:
      {==}
    case Con{R.Seg{+q, +ks, +d, +k, +f}, +rest}:
      +hh = Lemma.and_true_left(segBound(R.Seg{q, ks, d, k, f}, grammar, input), segsBounded(rest, grammar, input), hss)
      +a1 = R.growItem(Gll.nthSym(Core.rhsOf(grammar, q), d), fuel, grammar, gmarks, input, segs, q, ks, d, k, f)
      +a2 = R.growAll(rest, fuel, grammar, gmarks, input, segs)
      Lemma.and_true_intro(R.extOk(Gll.nthSym(Core.rhsOf(grammar, q), d), fuel, grammar, gmarks, input, segs, q, ks, d, k), R.closedAll(rest, fuel, grammar, gmarks, input, segs),
        ext_ok(Gll.nthSym(Core.rhsOf(grammar, q), d), fuel, grammar, gmarks, input, segs, q, ks, d, k, f, {==}, db_q(q, d, ks, k, grammar, input, hh), db_ks(q, d, ks, k, grammar, input, hh), db_e(q, d, ks, k, grammar, input, hh), hs, hdec, ah_left(a1, a2, segs, h)),
        closed_from(rest, fuel, grammar, gmarks, input, segs, Lemma.and_true_right_side(segBound(R.Seg{q, ks, d, k, f}, grammar, input), segsBounded(rest, grammar, input), hss), hs, hdec, ah_right(a1, a2, segs, h)))

# ======== THE GROWTH ENDS CLOSED ========

def GSame(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +segs: +List<R.Seg>) -> Type:
  {R.addNew(R.growAll(segs, fuel, grammar, gmarks, input, segs), segs) == segs : +List<R.Seg>} & {R.closedAll(segs, fuel, grammar, gmarks, input, segs) == True{} : Bool}

def GRes(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +segs: +List<R.Seg>) -> Type:
  Either<GSame(fuel, grammar, gmarks, input, segs), {Nat.is_le(1n+rMeas(grammar, input, R.addNew(R.growAll(segs, fuel, grammar, gmarks, input, segs), segs)), rMeas(grammar, input, segs)) == True{} : Bool}>

def g_same(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +segs: +List<R.Seg>, +hs: {segsBounded(segs, grammar, input) == True{} : Bool}, +hdec: {decided(fuel, grammar, gmarks, input) == True{} : Bool},
  p: ASame(R.growAll(segs, fuel, grammar, gmarks, input, segs), segs)) -> GRes(fuel, grammar, gmarks, input, segs):
  match p:
    case (+eq, +have):
      Inl{(eq, closed_from(segs, fuel, grammar, gmarks, input, segs, hs, hs, hdec, have))}

# One round on segments within bounds, with phase 1 deciding: nothing changes and the set
# is closed, or the count drops.
def g_round(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +segs: +List<R.Seg>, +hs: {segsBounded(segs, grammar, input) == True{} : Bool}, +hdec: {decided(fuel, grammar, gmarks, input) == True{} : Bool},
  r: ARes(grammar, input, R.growAll(segs, fuel, grammar, gmarks, input, segs), segs)) -> GRes(fuel, grammar, gmarks, input, segs):
  match r:
    case Inl{p}:
      g_same(fuel, grammar, gmarks, input, segs, hs, hdec, p)
    case Inr{m}:
      Inr{m}

law grow_stays:
  for n: Nat
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +input: +List<Nat>
  for +segs: +List<R.Seg>
  for +eq: {R.addNew(R.growAll(segs, fuel, grammar, gmarks, input, segs), segs) == segs : +List<R.Seg>}
  {R.grow(n, fuel, grammar, gmarks, input, segs) == segs : +List<R.Seg>}

def grow_stays(n, fuel, grammar, gmarks, input, segs, eq):
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      %Equal.sym(+List<R.Seg>, R.addNew(R.growAll(segs, fuel, grammar, gmarks, input, segs), segs), segs, eq) : {R.grow(p, fuel, grammar, gmarks, input, _) == segs : +List<R.Seg>}
      grow_stays(p, fuel, grammar, gmarks, input, segs, eq)

law grow_keep:
  for n: Nat
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +input: +List<Nat>
  for +segs: +List<R.Seg>
  for +q: Nat
  for +ks: Nat
  for +d: Nat
  for +e: Nat
  for +h: {R.hasSeg(q, ks, d, e, segs) == True{} : Bool}
  {R.hasSeg(q, ks, d, e, R.grow(n, fuel, grammar, gmarks, input, segs)) == True{} : Bool}

def grow_keep(n, fuel, grammar, gmarks, input, segs, q, ks, d, e, h):
  match n:
    case 0n:
      h
    case 1n+(+p):
      grow_keep(p, fuel, grammar, gmarks, input, R.addNew(R.growAll(segs, fuel, grammar, gmarks, input, segs), segs), q, ks, d, e, an_keep(R.growAll(segs, fuel, grammar, gmarks, input, segs), segs, q, ks, d, e, h))

def gfix_same2(+f: Nat, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +segs: +List<R.Seg>, +eq: {R.addNew(R.growAll(segs, fuel, grammar, gmarks, input, segs), segs) == segs : +List<R.Seg>}, +cl: {R.closedAll(segs, fuel, grammar, gmarks, input, segs) == True{} : Bool})
  -> {R.closedAll(R.grow(f, fuel, grammar, gmarks, input, R.addNew(R.growAll(segs, fuel, grammar, gmarks, input, segs), segs)), fuel, grammar, gmarks, input, R.grow(f, fuel, grammar, gmarks, input, R.addNew(R.growAll(segs, fuel, grammar, gmarks, input, segs), segs))) == True{} : Bool}:
  %Equal.sym(+List<R.Seg>, R.addNew(R.growAll(segs, fuel, grammar, gmarks, input, segs), segs), segs, eq) : {R.closedAll(R.grow(f, fuel, grammar, gmarks, input, _), fuel, grammar, gmarks, input, R.grow(f, fuel, grammar, gmarks, input, _)) == True{} : Bool}
  %Equal.sym(+List<R.Seg>, R.grow(f, fuel, grammar, gmarks, input, segs), segs, grow_stays(f, fuel, grammar, gmarks, input, segs, eq)) : {R.closedAll(_, fuel, grammar, gmarks, input, _) == True{} : Bool}
  cl

def gfix_same(+f: Nat, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +segs: +List<R.Seg>, p: GSame(fuel, grammar, gmarks, input, segs))
  -> {R.closedAll(R.grow(f, fuel, grammar, gmarks, input, R.addNew(R.growAll(segs, fuel, grammar, gmarks, input, segs), segs)), fuel, grammar, gmarks, input, R.grow(f, fuel, grammar, gmarks, input, R.addNew(R.growAll(segs, fuel, grammar, gmarks, input, segs), segs))) == True{} : Bool}:
  match p:
    case (+eq, +cl):
      gfix_same2(f, fuel, grammar, gmarks, input, segs, eq, cl)

def gfix_step(+f: Nat, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +segs: +List<R.Seg>, r: GRes(fuel, grammar, gmarks, input, segs), +hf: {Nat.is_le(rMeas(grammar, input, segs), f) == True{} : Bool},
  later: {Nat.is_le(1n+rMeas(grammar, input, R.addNew(R.growAll(segs, fuel, grammar, gmarks, input, segs), segs)), f) == True{} : Bool} -> {R.closedAll(R.grow(f, fuel, grammar, gmarks, input, R.addNew(R.growAll(segs, fuel, grammar, gmarks, input, segs), segs)), fuel, grammar, gmarks, input, R.grow(f, fuel, grammar, gmarks, input, R.addNew(R.growAll(segs, fuel, grammar, gmarks, input, segs), segs))) == True{} : Bool})
  -> {R.closedAll(R.grow(f, fuel, grammar, gmarks, input, R.addNew(R.growAll(segs, fuel, grammar, gmarks, input, segs), segs)), fuel, grammar, gmarks, input, R.grow(f, fuel, grammar, gmarks, input, R.addNew(R.growAll(segs, fuel, grammar, gmarks, input, segs), segs))) == True{} : Bool}:
  match r:
    case Inl{p}:
      gfix_same(f, fuel, grammar, gmarks, input, segs, p)
    case Inr{m}:
      later(Lemma.le_trans(1n+rMeas(grammar, input, R.addNew(R.growAll(segs, fuel, grammar, gmarks, input, segs), segs)), rMeas(grammar, input, segs), f, m, hf))

# With more rounds than unseen keys, the segments end closed.
law rival_fix:
  for n: Nat
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +input: +List<Nat>
  for +segs: +List<R.Seg>
  for +hs: {segsBounded(segs, grammar, input) == True{} : Bool}
  for +hdec: {decided(fuel, grammar, gmarks, input) == True{} : Bool}
  for +hf: {Nat.is_le(1n+rMeas(grammar, input, segs), n) == True{} : Bool}
  {R.closedAll(R.grow(n, fuel, grammar, gmarks, input, segs), fuel, grammar, gmarks, input, R.grow(n, fuel, grammar, gmarks, input, segs)) == True{} : Bool}

def rival_fix(n, fuel, grammar, gmarks, input, segs, hs, hdec, hf):
  match n:
    case 0n:
      Empty.absurd({R.closedAll(segs, fuel, grammar, gmarks, input, segs) == True{} : Bool}, Lemma.false_is_not_true(hf))
    case 1n+(+f):
      gfix_step(f, fuel, grammar, gmarks, input, segs, g_round(fuel, grammar, gmarks, input, segs, hs, hdec, ares(R.growAll(segs, fuel, grammar, gmarks, input, segs), grammar, input, segs, ga_bounded(segs, fuel, grammar, gmarks, input, segs, hs, hs))), hf,
        h2 => rival_fix(f, fuel, grammar, gmarks, input, R.addNew(R.growAll(segs, fuel, grammar, gmarks, input, segs), segs), an_bounded(R.growAll(segs, fuel, grammar, gmarks, input, segs), segs, grammar, input, ga_bounded(segs, fuel, grammar, gmarks, input, segs, hs, hs), hs), hdec, h2))

def len_to2(+fuel: Nat, +us: +List<Gll.Desc>, +hf: {Nat.is_le(1n+List.length(&2, Gll.Desc, us), fuel) == True{} : Bool})
  -> {Nat.is_le(1n+Run.countNot(us, []), fuel) == True{} : Bool}:
  %Equal.sym(Nat, Run.countNot(us, []), List.length(&2, Gll.Desc, us), C.count_empty(us)) : {Nat.is_le(1n+_, fuel) == True{} : Bool}
  hf

def seed_meas(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +m: Nat, +i: Nat, +hf: {Nat.is_le(1n+List.length(&2, Gll.Desc, Run.univ(grammar, input)), fuel) == True{} : Bool})
  -> {Nat.is_le(1n+rMeas(grammar, input, [R.Seg{m, i, 0n, i, []}]), fuel) == True{} : Bool}:
  Lemma.le_trans(1n+rMeas(grammar, input, [R.Seg{m, i, 0n, i, []}]), 1n+Run.countNot(Run.univ(grammar, input), []), fuel,
    C.count_mono(Run.univ(grammar, input), [], segDescs([R.Seg{m, i, 0n, i, []}]), {==}), len_to2(fuel, Run.univ(grammar, input), hf))

# THE RIVAL CLOSURE ANSWERS: for a production m and a position i within bounds, when
# phase 1 decides every step within bounds, with fuel 1 + the size of the descriptor
# universe, the segments grown from m at i are closed and have m's start: the check
# `rivalTri` asks for when no segment completes m.
law rival_closed:
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +input: +List<Nat>
  for +m: Nat
  for +i: Nat
  for +hm: {Nat.is_le(1n+m, List.length(&2, Core.Production, grammar)) == True{} : Bool}
  for +hi: {Nat.is_le(i, List.length(&2, Nat, input)) == True{} : Bool}
  for +hdec: {decided(fuel, grammar, gmarks, input) == True{} : Bool}
  for +hf: {Nat.is_le(1n+List.length(&2, Gll.Desc, Run.univ(grammar, input)), fuel) == True{} : Bool}
  {Bool.and(R.closedAll(R.segsFrom(fuel, grammar, gmarks, input, m, i), fuel, grammar, gmarks, input, R.segsFrom(fuel, grammar, gmarks, input, m, i)), R.hasSeg(m, i, 0n, i, R.segsFrom(fuel, grammar, gmarks, input, m, i))) == True{} : Bool}

def rival_closed(fuel, grammar, gmarks, input, m, i, hm, hi, hdec, hf):
  +seed = {[R.Seg{m, i, 0n, i, []}] : +List<R.Seg>}
  Lemma.and_true_intro(R.closedAll(R.segsFrom(fuel, grammar, gmarks, input, m, i), fuel, grammar, gmarks, input, R.segsFrom(fuel, grammar, gmarks, input, m, i)), R.hasSeg(m, i, 0n, i, R.segsFrom(fuel, grammar, gmarks, input, m, i)),
    rival_fix(fuel, fuel, grammar, gmarks, input, seed,
      Lemma.and_true_intro(segBound(R.Seg{m, i, 0n, i, []}, grammar, input), True{}, db_intro(m, 0n, i, i, grammar, input, hm, Lemma.zero_le(List.length(&2, Core.Sym, Core.rhsOf(grammar, m))), hi, hi), {==}),
      hdec, seed_meas(fuel, grammar, gmarks, input, m, i, hf)),
    grow_keep(fuel, fuel, grammar, gmarks, input, seed, m, i, 0n, i, Lemma.or_true_left_intro(R.keyIs(m, i, 0n, i, R.Seg{m, i, 0n, i, []}), False{}, key_refl(m, i, 0n, i, []))))

import Base
import ../LEMMAS.bend as Lemma
import ./CORE.bend as Core
import ./GLL.bend as Gll
import ./GUARD.bend as Guard
import ./RIVAL.bend as R
import ./PROOF_GLL.bend as G
import ./PROOF_GUARD.bend as PG
import ./PROOF_DECIDE.bend as D
import ./PROOF_SPELL.bend as S

# NO RIVAL WITHOUT ITS SEGMENT. When the segments are closed (RIVAL.bend), every forest for a
# node whose prefix is a segment, read on the input with no step answered No by phase 1,
# completes the node in a segment (`walk`). So a closed set without m's whole segment over
# i .. e leaves no rival.

# ======== VERDICTS ========

def notNo(t: Guard.Tri) -> Bool:
  match t:
    case Guard.Yes{}:
      True{}
    case Guard.No{}:
      False{}
    case Guard.Unknown{}:
      True{}

def allNN(ys: +List<Core.Bsr>, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{+y, rest}:
      Bool.and(notNo(R.tri(fuel, grammar, gmarks, input, y)), allNN(rest, fuel, grammar, gmarks, input))

law clause_use:
  for t: Guard.Tri
  for -c: Bool
  for +hc: {R.clause(t, c) == True{} : Bool}
  for +hn: {notNo(t) == True{} : Bool}
  {c == True{} : Bool}

def clause_use(t, c, hc, hn):
  match t:
    case Guard.Yes{}:
      hc
    case Guard.No{}:
      Empty.absurd({c == True{} : Bool}, Lemma.false_is_not_true(hn))
    case Guard.Unknown{}:
      Empty.absurd({c == True{} : Bool}, Lemma.false_is_not_true(hc))

law when_use:
  for b: Bool
  for -c: Bool
  for +h: {R.whenB(b, c) == True{} : Bool}
  for +hb: {b == True{} : Bool}
  {c == True{} : Bool}

def when_use(b, c, h, hb):
  match b:
    case True{}:
      h
    case False{}:
      Empty.absurd({c == True{} : Bool}, Lemma.false_is_not_true(hb))

def ok_pick(t: Guard.Tri, +y: Core.Bsr, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>,
  +et: {Guard.stepTri(fuel, grammar, gmarks, input, y) == t : Guard.Tri},
  h: Guard.StepOk(grammar, gmarks, input, y)) -> {notNo(t) == True{} : Bool}:
  match t:
    case Guard.Yes{}:
      {==}
    case Guard.No{}:
      Empty.absurd({False{} == True{} : Bool}, PG.step_no(y, fuel, grammar, gmarks, input, et, h))
    case Guard.Unknown{}:
      {==}

def ok_nn(+y: Core.Bsr, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>,
  h: Guard.StepOk(grammar, gmarks, input, y)) -> {notNo(R.tri(fuel, grammar, gmarks, input, y)) == True{} : Bool}:
  ok_pick(Guard.stepTri(fuel, grammar, gmarks, input, y), y, fuel, grammar, gmarks, input, {==}, h)

def ok_split(+y: Core.Bsr, +rest: +List<Core.Bsr>, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>,
  h: Guard.StepOk(grammar, gmarks, input, y) & Guard.AllStepsOk(grammar, gmarks, input, rest),
  later: Guard.AllStepsOk(grammar, gmarks, input, rest) -> {allNN(rest, fuel, grammar, gmarks, input) == True{} : Bool})
  -> {allNN(y <> rest, fuel, grammar, gmarks, input) == True{} : Bool}:
  match h:
    case (a, b):
      Lemma.and_true_intro(notNo(R.tri(fuel, grammar, gmarks, input, y)), allNN(rest, fuel, grammar, gmarks, input), ok_nn(y, fuel, grammar, gmarks, input, a), later(b))

# Steps that keep their rules are answered No by none of them.
law all_ok_nn:
  for ys: +List<Core.Bsr>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +input: +List<Nat>
  for h: Guard.AllStepsOk(grammar, gmarks, input, ys)
  {allNN(ys, fuel, grammar, gmarks, input) == True{} : Bool}

def all_ok_nn(ys, fuel, grammar, gmarks, input, h):
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      ok_split(y, rest, fuel, grammar, gmarks, input, h, h2 => all_ok_nn(rest, fuel, grammar, gmarks, input, h2))

law nn_left:
  for xs: +List<Core.Bsr>
  for +ys: +List<Core.Bsr>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +input: +List<Nat>
  for +h: {allNN(List.append(&2, Core.Bsr, xs, ys), fuel, grammar, gmarks, input) == True{} : Bool}
  {allNN(xs, fuel, grammar, gmarks, input) == True{} : Bool}

def nn_left(xs, ys, fuel, grammar, gmarks, input, h):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +hx = {notNo(R.tri(fuel, grammar, gmarks, input, x)) : Bool}
      Lemma.and_true_intro(hx, allNN(rest, fuel, grammar, gmarks, input), Lemma.and_true_left(hx, allNN(List.append(&2, Core.Bsr, rest, ys), fuel, grammar, gmarks, input), h),
        nn_left(rest, ys, fuel, grammar, gmarks, input, Lemma.and_true_right_side(hx, allNN(List.append(&2, Core.Bsr, rest, ys), fuel, grammar, gmarks, input), h)))

law nn_right:
  for xs: +List<Core.Bsr>
  for +ys: +List<Core.Bsr>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +input: +List<Nat>
  for +h: {allNN(List.append(&2, Core.Bsr, xs, ys), fuel, grammar, gmarks, input) == True{} : Bool}
  {allNN(ys, fuel, grammar, gmarks, input) == True{} : Bool}

def nn_right(xs, ys, fuel, grammar, gmarks, input, h):
  match xs:
    case Nil{}:
      h
    case Con{+x, +rest}:
      nn_right(rest, ys, fuel, grammar, gmarks, input, Lemma.and_true_right_side(notNo(R.tri(fuel, grammar, gmarks, input, x)), allNN(List.append(&2, Core.Bsr, rest, ys), fuel, grammar, gmarks, input), h))

# ======== WHAT A CLOSED SET SAYS AT ONE OF ITS SEGMENTS ========

def ext_moved(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +segs: +List<R.Seg>,
  +q2: Nat, +ks2: Nat, +d2: Nat, +k2: Nat, +q: Nat, +ks: Nat, +d: Nat, +k: Nat,
  +eq: {q2 == q : Nat}, +eks: {ks2 == ks : Nat}, +ed: {d2 == d : Nat}, +ek: {k2 == k : Nat},
  +h: {R.extOk(Gll.nthSym(Core.rhsOf(grammar, q2), d2), fuel, grammar, gmarks, input, segs, q2, ks2, d2, k2) == True{} : Bool})
  -> {R.extOk(Gll.nthSym(Core.rhsOf(grammar, q), d), fuel, grammar, gmarks, input, segs, q, ks, d, k) == True{} : Bool}:
  %eq : {R.extOk(Gll.nthSym(Core.rhsOf(grammar, _), d), fuel, grammar, gmarks, input, segs, _, ks, d, k) == True{} : Bool}
  %eks : {R.extOk(Gll.nthSym(Core.rhsOf(grammar, q2), d), fuel, grammar, gmarks, input, segs, q2, _, d, k) == True{} : Bool}
  %ed : {R.extOk(Gll.nthSym(Core.rhsOf(grammar, q2), _), fuel, grammar, gmarks, input, segs, q2, ks2, _, k) == True{} : Bool}
  %ek : {R.extOk(Gll.nthSym(Core.rhsOf(grammar, q2), d2), fuel, grammar, gmarks, input, segs, q2, ks2, d2, _) == True{} : Bool}
  h

def ext_pick(+q2: Nat, +ks2: Nat, +d2: Nat, +k2: Nat, +fo: +List<Core.Tree>, +rest: +List<R.Seg>, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +segs: +List<R.Seg>,
  +q: Nat, +ks: Nat, +d: Nat, +k: Nat,
  +hh: {R.extOk(Gll.nthSym(Core.rhsOf(grammar, q2), d2), fuel, grammar, gmarks, input, segs, q2, ks2, d2, k2) == True{} : Bool},
  cases: Either<{R.keyIs(q, ks, d, k, R.Seg{q2, ks2, d2, k2, fo}) == True{} : Bool}, {R.hasSeg(q, ks, d, k, rest) == True{} : Bool}>,
  later: {R.hasSeg(q, ks, d, k, rest) == True{} : Bool} -> {R.extOk(Gll.nthSym(Core.rhsOf(grammar, q), d), fuel, grammar, gmarks, input, segs, q, ks, d, k) == True{} : Bool})
  -> {R.extOk(Gll.nthSym(Core.rhsOf(grammar, q), d), fuel, grammar, gmarks, input, segs, q, ks, d, k) == True{} : Bool}:
  match cases:
    case Inl{+e}:
      +r1 = {Bool.and(Nat.is_eq(ks2, ks), Bool.and(Nat.is_eq(d2, d), Nat.is_eq(k2, k))) : Bool}
      +r2 = {Bool.and(Nat.is_eq(d2, d), Nat.is_eq(k2, k)) : Bool}
      +t1 = Lemma.and_true_right_side(Nat.is_eq(q2, q), r1, e)
      +t2 = Lemma.and_true_right_side(Nat.is_eq(ks2, ks), r2, t1)
      ext_moved(fuel, grammar, gmarks, input, segs, q2, ks2, d2, k2, q, ks, d, k,
        Lemma.nat_eq_sound(q2, q, Lemma.and_true_left(Nat.is_eq(q2, q), r1, e)),
        Lemma.nat_eq_sound(ks2, ks, Lemma.and_true_left(Nat.is_eq(ks2, ks), r2, t1)),
        Lemma.nat_eq_sound(d2, d, Lemma.and_true_left(Nat.is_eq(d2, d), Nat.is_eq(k2, k), t2)),
        Lemma.nat_eq_sound(k2, k, Lemma.and_true_right_side(Nat.is_eq(d2, d), Nat.is_eq(k2, k), t2)), hh)
    case Inr{m}:
      later(m)

# A segment of a closed set lets its next item be read.
law ext_of:
  for ss: +List<R.Seg>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +input: +List<Nat>
  for +segs: +List<R.Seg>
  for +q: Nat
  for +ks: Nat
  for +d: Nat
  for +k: Nat
  for +cl: {R.closedAll(ss, fuel, grammar, gmarks, input, segs) == True{} : Bool}
  for +h: {R.hasSeg(q, ks, d, k, ss) == True{} : Bool}
  {R.extOk(Gll.nthSym(Core.rhsOf(grammar, q), d), fuel, grammar, gmarks, input, segs, q, ks, d, k) == True{} : Bool}

def ext_of(ss, fuel, grammar, gmarks, input, segs, q, ks, d, k, cl, h):
  match ss:
    case Nil{}:
      Empty.absurd({R.extOk(Gll.nthSym(Core.rhsOf(grammar, q), d), fuel, grammar, gmarks, input, segs, q, ks, d, k) == True{} : Bool}, Lemma.false_is_not_true(h))
    case Con{R.Seg{+q2, +ks2, +d2, +k2, +fo}, +rest}:
      +here = {R.extOk(Gll.nthSym(Core.rhsOf(grammar, q2), d2), fuel, grammar, gmarks, input, segs, q2, ks2, d2, k2) : Bool}
      +more = {R.closedAll(rest, fuel, grammar, gmarks, input, segs) : Bool}
      ext_pick(q2, ks2, d2, k2, fo, rest, fuel, grammar, gmarks, input, segs, q, ks, d, k, Lemma.and_true_left(here, more, cl),
        Lemma.or_true_cases(R.keyIs(q, ks, d, k, R.Seg{q2, ks2, d2, k2, fo}), R.hasSeg(q, ks, d, k, rest), h),
        m => ext_of(rest, fuel, grammar, gmarks, input, segs, q, ks, d, k, Lemma.and_true_right_side(here, more, cl), m))

def comp_moved(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +segs: +List<R.Seg>,
  +need: Core.Need, +p: Nat, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +e2: Nat, +e: Nat, +ee: {e2 == e : Nat},
  +h: {R.compOk(fuel, grammar, gmarks, input, segs, need, p, q, ks, d, k, e2) == True{} : Bool})
  -> {R.compOk(fuel, grammar, gmarks, input, segs, need, p, q, ks, d, k, e) == True{} : Bool}:
  %ee : {R.compOk(fuel, grammar, gmarks, input, segs, need, p, q, ks, d, k, _) == True{} : Bool}
  h

def comp_pick(+p2: Nat, +k2: Nat, +d2: Nat, +e2: Nat, +fo: +List<Core.Tree>, +rest: +List<R.Seg>, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +segs: +List<R.Seg>,
  +need: Core.Need, +p: Nat, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +e: Nat,
  +hh: {R.whenB(Bool.and(Nat.is_eq(p2, p), Bool.and(Nat.is_eq(k2, k), Nat.is_eq(d2, List.length(&2, Core.Sym, Core.rhsOf(grammar, p))))), R.compOk(fuel, grammar, gmarks, input, segs, need, p, q, ks, d, k, e2)) == True{} : Bool},
  cases: Either<{R.keyIs(p, k, List.length(&2, Core.Sym, Core.rhsOf(grammar, p)), e, R.Seg{p2, k2, d2, e2, fo}) == True{} : Bool}, {R.hasSeg(p, k, List.length(&2, Core.Sym, Core.rhsOf(grammar, p)), e, rest) == True{} : Bool}>,
  later: {R.hasSeg(p, k, List.length(&2, Core.Sym, Core.rhsOf(grammar, p)), e, rest) == True{} : Bool} -> {R.compOk(fuel, grammar, gmarks, input, segs, need, p, q, ks, d, k, e) == True{} : Bool})
  -> {R.compOk(fuel, grammar, gmarks, input, segs, need, p, q, ks, d, k, e) == True{} : Bool}:
  match cases:
    case Inl{+ek}:
      +len = {List.length(&2, Core.Sym, Core.rhsOf(grammar, p)) : Nat}
      +r1 = {Bool.and(Nat.is_eq(k2, k), Bool.and(Nat.is_eq(d2, len), Nat.is_eq(e2, e))) : Bool}
      +r2 = {Bool.and(Nat.is_eq(d2, len), Nat.is_eq(e2, e)) : Bool}
      +t1 = Lemma.and_true_right_side(Nat.is_eq(p2, p), r1, ek)
      +t2 = Lemma.and_true_right_side(Nat.is_eq(k2, k), r2, t1)
      +cond = Lemma.and_true_intro(Nat.is_eq(p2, p), Bool.and(Nat.is_eq(k2, k), Nat.is_eq(d2, len)), Lemma.and_true_left(Nat.is_eq(p2, p), r1, ek),
        Lemma.and_true_intro(Nat.is_eq(k2, k), Nat.is_eq(d2, len), Lemma.and_true_left(Nat.is_eq(k2, k), r2, t1), Lemma.and_true_left(Nat.is_eq(d2, len), Nat.is_eq(e2, e), t2)))
      comp_moved(fuel, grammar, gmarks, input, segs, need, p, q, ks, d, k, e2, e,
        Lemma.nat_eq_sound(e2, e, Lemma.and_true_right_side(Nat.is_eq(d2, len), Nat.is_eq(e2, e), t2)),
        when_use(Bool.and(Nat.is_eq(p2, p), Bool.and(Nat.is_eq(k2, k), Nat.is_eq(d2, len))), R.compOk(fuel, grammar, gmarks, input, segs, need, p, q, ks, d, k, e2), hh, cond))
    case Inr{m}:
      later(m)

# A completed segment of p in the set: the closed set lets the prefix read it.
law comps_of:
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
  for +e: Nat
  for +cs: {R.compsOk(ss, fuel, grammar, gmarks, input, segs, need, p, q, ks, d, k) == True{} : Bool}
  for +h: {R.hasSeg(p, k, List.length(&2, Core.Sym, Core.rhsOf(grammar, p)), e, ss) == True{} : Bool}
  {R.compOk(fuel, grammar, gmarks, input, segs, need, p, q, ks, d, k, e) == True{} : Bool}

def comps_of(ss, fuel, grammar, gmarks, input, segs, need, p, q, ks, d, k, e, cs, h):
  match ss:
    case Nil{}:
      Empty.absurd({R.compOk(fuel, grammar, gmarks, input, segs, need, p, q, ks, d, k, e) == True{} : Bool}, Lemma.false_is_not_true(h))
    case Con{R.Seg{+p2, +k2, +d2, +e2, +fo}, +rest}:
      +cond = {Bool.and(Nat.is_eq(p2, p), Bool.and(Nat.is_eq(k2, k), Nat.is_eq(d2, List.length(&2, Core.Sym, Core.rhsOf(grammar, p))))) : Bool}
      +here = {R.whenB(cond, R.compOk(fuel, grammar, gmarks, input, segs, need, p, q, ks, d, k, e2)) : Bool}
      +more = {R.compsOk(rest, fuel, grammar, gmarks, input, segs, need, p, q, ks, d, k) : Bool}
      comp_pick(p2, k2, d2, e2, fo, rest, fuel, grammar, gmarks, input, segs, need, p, q, ks, d, k, e, Lemma.and_true_left(here, more, cs),
        Lemma.or_true_cases(R.keyIs(p, k, List.length(&2, Core.Sym, Core.rhsOf(grammar, p)), e, R.Seg{p2, k2, d2, e2, fo}), R.hasSeg(p, k, List.length(&2, Core.Sym, Core.rhsOf(grammar, p)), e, rest), h),
        m => comps_of(rest, fuel, grammar, gmarks, input, segs, need, p, q, ks, d, k, e, Lemma.and_true_right_side(here, more, cs), m))

def ProdOk(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +segs: +List<R.Seg>,
  +need: Core.Need, +p: Nat, +q: Nat, +ks: Nat, +d: Nat, +k: Nat) -> Bool:
  Bool.and(R.hasSeg(p, k, 0n, k, segs), R.compsOk(segs, fuel, grammar, gmarks, input, segs, need, p, q, ks, d, k))

def prod_zero(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +segs: +List<R.Seg>,
  +need: Core.Need, +base: Nat, +q: Nat, +ks: Nat, +d: Nat, +k: Nat,
  +h: {ProdOk(fuel, grammar, gmarks, input, segs, need, base, q, ks, d, k) == True{} : Bool})
  -> {ProdOk(fuel, grammar, gmarks, input, segs, need, Nat.add(base, 0n), q, ks, d, k) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(base, 0n), base, Lemma.add_zero_right(base)) : {ProdOk(fuel, grammar, gmarks, input, segs, need, _, q, ks, d, k) == True{} : Bool}
  h

def prod_succ(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +segs: +List<R.Seg>,
  +need: Core.Need, +base: Nat, +n: Nat, +q: Nat, +ks: Nat, +d: Nat, +k: Nat,
  +h: {ProdOk(fuel, grammar, gmarks, input, segs, need, 1n+Nat.add(base, n), q, ks, d, k) == True{} : Bool})
  -> {ProdOk(fuel, grammar, gmarks, input, segs, need, Nat.add(base, 1n+n), q, ks, d, k) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(base, 1n+n), 1n+Nat.add(base, n), Lemma.add_succ_right(base, n)) : {ProdOk(fuel, grammar, gmarks, input, segs, need, _, q, ks, d, k) == True{} : Bool}
  h

# A production of x: the closed set starts it at k and lets each of its completions be read.
law prods_of:
  for g: +List<Core.Production>
  for n: Nat
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
  for +ps: {R.prodsOk(g, base, fuel, grammar, gmarks, input, segs, x, need, q, ks, d, k) == True{} : Bool}
  for +hl: {Core.lhsIs(g, n, x) == True{} : Bool}
  {ProdOk(fuel, grammar, gmarks, input, segs, need, Nat.add(base, n), q, ks, d, k) == True{} : Bool}

def prods_of(g, n, base, fuel, grammar, gmarks, input, segs, x, need, q, ks, d, k, ps, hl):
  match g n:
    case Nil{} +n0:
      Empty.absurd({ProdOk(fuel, grammar, gmarks, input, segs, need, Nat.add(base, n0), q, ks, d, k) == True{} : Bool}, Lemma.false_is_not_true(hl))
    case Con{Core.Production{+lhs, +rhs}, +rest} 0n:
      +here = {R.whenB(Nat.is_eq(lhs, x), ProdOk(fuel, grammar, gmarks, input, segs, need, base, q, ks, d, k)) : Bool}
      +more = {R.prodsOk(rest, 1n+base, fuel, grammar, gmarks, input, segs, x, need, q, ks, d, k) : Bool}
      prod_zero(fuel, grammar, gmarks, input, segs, need, base, q, ks, d, k,
        when_use(Nat.is_eq(lhs, x), ProdOk(fuel, grammar, gmarks, input, segs, need, base, q, ks, d, k), Lemma.and_true_left(here, more, ps), hl))
    case Con{Core.Production{+lhs, +rhs}, +rest} 1n+(+n2):
      +here = {R.whenB(Nat.is_eq(lhs, x), ProdOk(fuel, grammar, gmarks, input, segs, need, base, q, ks, d, k)) : Bool}
      +more = {R.prodsOk(rest, 1n+base, fuel, grammar, gmarks, input, segs, x, need, q, ks, d, k) : Bool}
      prod_succ(fuel, grammar, gmarks, input, segs, need, base, n2, q, ks, d, k,
        prods_of(rest, n2, 1n+base, fuel, grammar, gmarks, input, segs, x, need, q, ks, d, k, Lemma.and_true_right_side(here, more, ps), hl))

# ======== THE WALK ========

def ext_item(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +segs: +List<R.Seg>,
  +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +item: Maybe<&2, Core.Sym>,
  +en: {Gll.nthSym(Core.rhsOf(grammar, q), d) == item : Maybe<&2, Core.Sym>},
  +h: {R.extOk(Gll.nthSym(Core.rhsOf(grammar, q), d), fuel, grammar, gmarks, input, segs, q, ks, d, k) == True{} : Bool})
  -> {R.extOk(item, fuel, grammar, gmarks, input, segs, q, ks, d, k) == True{} : Bool}:
  %en : {R.extOk(_, fuel, grammar, gmarks, input, segs, q, ks, d, k) == True{} : Bool}
  h

def tok_to(+input: +List<Nat>, +k: Nat, +a: Nat, +t: Nat, +e: {a == t : Nat},
  +h: {Core.tokIs(Core.tokAt(input, k), a) == True{} : Bool}) -> {Core.tokIs(Core.tokAt(input, k), t) == True{} : Bool}:
  %e : {Core.tokIs(Core.tokAt(input, k), _) == True{} : Bool}
  h

def nn_at(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +q: Nat, +d: Nat, +ks: Nat, +k: Nat, +a: Nat, +b: Nat,
  +e: {a == b : Nat},
  +h: {notNo(R.tri(fuel, grammar, gmarks, input, Core.Bsr{q, d, ks, k, a})) == True{} : Bool})
  -> {notNo(R.tri(fuel, grammar, gmarks, input, Core.Bsr{q, d, ks, k, b})) == True{} : Bool}:
  %e : {notNo(R.tri(fuel, grammar, gmarks, input, Core.Bsr{q, d, ks, k, _})) == True{} : Bool}
  h

def own_at(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +q: Nat, +ts: +List<Core.Tree>, +d: Nat, +ks: Nat, +a: Nat, +b: Nat,
  +e: {a == b : Nat},
  +h: {allNN(Core.own(q, ts, d, ks, a), fuel, grammar, gmarks, input) == True{} : Bool})
  -> {allNN(Core.own(q, ts, d, ks, b), fuel, grammar, gmarks, input) == True{} : Bool}:
  %e : {allNN(Core.own(q, ts, d, ks, _), fuel, grammar, gmarks, input) == True{} : Bool}
  h

def seg_to(+segs: +List<R.Seg>, +q: Nat, +ks: Nat, +d: Nat, +a: Nat, +b: Nat, +e: {a == b : Nat},
  +h: {R.hasSeg(q, ks, d, a, segs) == True{} : Bool}) -> {R.hasSeg(q, ks, d, b, segs) == True{} : Bool}:
  %e : {R.hasSeg(q, ks, d, _, segs) == True{} : Bool}
  h

# The step that ends a node of p is not answered No: it is a step of the node, or there is
# none (Yes).
def end_nn(items: +List<Core.Sym>, ch: +List<Core.Tree>, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +p: Nat, +k: Nat,
  +ip: {Core.rhsOf(grammar, p) == items : +List<Core.Sym>},
  +rc: {Core.reads(ch, grammar, items, input, k) == True{} : Bool},
  +noC: {allNN(Core.own(p, ch, 0n, k, k), fuel, grammar, gmarks, input) == True{} : Bool})
  -> {notNo(R.endTri(Core.rhsOf(grammar, p), fuel, grammar, gmarks, input, p, k, Nat.add(k, Core.width(Core.Node{p, ch})))) == True{} : Bool}:
  match items ch:
    case Nil{} Nil{}:
      %Equal.sym(+List<Core.Sym>, Core.rhsOf(grammar, p), [], ip) : {notNo(R.endTri(_, fuel, grammar, gmarks, input, p, k, Nat.add(k, Core.width(Core.Node{p, []})))) == True{} : Bool}
      nn_at(fuel, grammar, gmarks, input, p, 0n, k, k, k, Nat.add(k, 0n), Equal.sym(Nat, Nat.add(k, 0n), k, Lemma.add_zero_right(k)),
        Lemma.and_true_left(notNo(R.tri(fuel, grammar, gmarks, input, Core.Bsr{p, 0n, k, k, k})), True{}, noC))
    case Con{+s, +r} +c:
      %Equal.sym(+List<Core.Sym>, Core.rhsOf(grammar, p), s <> r, ip) : {notNo(R.endTri(_, fuel, grammar, gmarks, input, p, k, Nat.add(k, Core.width(Core.Node{p, c})))) == True{} : Bool}
      {==}
    case Nil{} Con{Core.Leaf{+a}, +ts}:
      Empty.absurd({notNo(R.endTri(Core.rhsOf(grammar, p), fuel, grammar, gmarks, input, p, k, Nat.add(k, Core.width(Core.Node{p, Core.Leaf{a} <> ts})))) == True{} : Bool}, Lemma.false_is_not_true(rc))
    case Nil{} Con{Core.Node{+q2, +c2}, +ts}:
      Empty.absurd({notNo(R.endTri(Core.rhsOf(grammar, p), fuel, grammar, gmarks, input, p, k, Nat.add(k, Core.width(Core.Node{p, Core.Node{q2, c2} <> ts})))) == True{} : Bool}, Lemma.false_is_not_true(rc))

def end_d(+grammar: +List<Core.Production>, +segs: +List<R.Seg>, +q: Nat, +ks: Nat, +d: Nat, +k: Nat,
  +inv: {Nat.add(d, 0n) == List.length(&2, Core.Sym, Core.rhsOf(grammar, q)) : Nat},
  +hs: {R.hasSeg(q, ks, d, k, segs) == True{} : Bool}) -> {R.hasSeg(q, ks, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), k, segs) == True{} : Bool}:
  +ed = Equal.trans(Nat, d, Nat.add(d, 0n), List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), Equal.sym(Nat, Nat.add(d, 0n), d, Lemma.add_zero_right(d)), inv)
  %ed : {R.hasSeg(q, ks, _, k, segs) == True{} : Bool}
  hs

def inv_step(+d: Nat, +r: +List<Core.Sym>, +len: Nat,
  +inv: {Nat.add(d, 1n+List.length(&2, Core.Sym, r)) == len : Nat}) -> {Nat.add(1n+d, List.length(&2, Core.Sym, r)) == len : Nat}:
  Equal.trans(Nat, 1n+Nat.add(d, List.length(&2, Core.Sym, r)), Nat.add(d, 1n+List.length(&2, Core.Sym, r)), len,
    Equal.sym(Nat, Nat.add(d, 1n+List.length(&2, Core.Sym, r)), 1n+Nat.add(d, List.length(&2, Core.Sym, r)), Lemma.add_succ_right(d, List.length(&2, Core.Sym, r))), inv)

# A forest that reads the rest of a node's items from a segment, with no step answered No,
# completes the node in a segment of a closed set.
law walk:
  for f: +List<Core.Tree>
  for items: +List<Core.Sym>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +input: +List<Nat>
  for +segs: +List<R.Seg>
  for +q: Nat
  for +ks: Nat
  for +d: Nat
  for +k: Nat
  for +ie: {G.dropFrom(d, Core.rhsOf(grammar, q)) == items : +List<Core.Sym>}
  for +inv: {Nat.add(d, List.length(&2, Core.Sym, items)) == List.length(&2, Core.Sym, Core.rhsOf(grammar, q)) : Nat}
  for +r: {Core.reads(f, grammar, items, input, k) == True{} : Bool}
  for +hs: {R.hasSeg(q, ks, d, k, segs) == True{} : Bool}
  for +no: {allNN(Core.own(q, f, d, ks, k), fuel, grammar, gmarks, input) == True{} : Bool}
  for +ni: {allNN(Core.steps(f, k), fuel, grammar, gmarks, input) == True{} : Bool}
  for +cl: {R.closedAll(segs, fuel, grammar, gmarks, input, segs) == True{} : Bool}
  {R.hasSeg(q, ks, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), G.endOf(f, k), segs) == True{} : Bool}

def walk(f, items, fuel, grammar, gmarks, input, segs, q, ks, d, k, ie, inv, r, hs, no, ni, cl):
  match f items:
    case Nil{} Nil{}:
      end_d(grammar, segs, q, ks, d, k, inv, hs)
    case Nil{} Con{+s, +rest}:
      Empty.absurd({R.hasSeg(q, ks, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), k, segs) == True{} : Bool}, Lemma.false_is_not_true(r))
    case Con{Core.Leaf{+a}, +ts} Nil{}:
      Empty.absurd({R.hasSeg(q, ks, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), G.endOf(Core.Leaf{a} <> ts, k), segs) == True{} : Bool}, Lemma.false_is_not_true(r))
    case Con{Core.Node{+p, +ch}, +ts} Nil{}:
      Empty.absurd({R.hasSeg(q, ks, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), G.endOf(Core.Node{p, ch} <> ts, k), segs) == True{} : Bool}, Lemma.false_is_not_true(r))
    case Con{Core.Leaf{+a}, +ts} Con{Core.Nonterminal{+x, +need}, +rest}:
      Empty.absurd({R.hasSeg(q, ks, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), G.endOf(Core.Leaf{a} <> ts, k), segs) == True{} : Bool}, Lemma.false_is_not_true(r))
    case Con{Core.Node{+p, +ch}, +ts} Con{Core.Terminal{+t}, +rest}:
      Empty.absurd({R.hasSeg(q, ks, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), G.endOf(Core.Node{p, ch} <> ts, k), segs) == True{} : Bool}, Lemma.false_is_not_true(r))
    case Con{Core.Leaf{+a}, +ts} Con{Core.Terminal{+t}, +rest}:
      +more = {Bool.and(Core.tokIs(Core.tokAt(input, k), a), Core.reads(ts, grammar, rest, input, 1n+k)) : Bool}
      +ea = Lemma.nat_eq_sound(a, t, Lemma.and_true_left(Nat.is_eq(a, t), more, r))
      +rk = Lemma.and_true_left(Core.tokIs(Core.tokAt(input, k), a), Core.reads(ts, grammar, rest, input, 1n+k), Lemma.and_true_right_side(Nat.is_eq(a, t), more, r))
      +rt = Lemma.and_true_right_side(Core.tokIs(Core.tokAt(input, k), a), Core.reads(ts, grammar, rest, input, 1n+k), Lemma.and_true_right_side(Nat.is_eq(a, t), more, r))
      +ext = ext_item(fuel, grammar, gmarks, input, segs, q, ks, d, k, Some{Core.Terminal{t}}, G.nth_drop(Core.rhsOf(grammar, q), d, Core.Terminal{t}, rest, ie),
        ext_of(segs, fuel, grammar, gmarks, input, segs, q, ks, d, k, cl, hs))
      +far = Nat.add(k, Core.width(Core.Leaf{a}))
      +ef = {Lemma.add_one_right(k) : {far == 1n+k : Nat}}
      +y = {Core.Bsr{q, 1n+d, ks, k, 1n+k} : Core.Bsr}
      +hd = {notNo(R.tri(fuel, grammar, gmarks, input, Core.Bsr{q, 1n+d, ks, k, far})) : Bool}
      +ny = nn_at(fuel, grammar, gmarks, input, q, 1n+d, ks, k, far, 1n+k, ef, Lemma.and_true_left(hd, allNN(Core.own(q, ts, 1n+d, ks, far), fuel, grammar, gmarks, input), no))
      +noT = own_at(fuel, grammar, gmarks, input, q, ts, 1n+d, ks, far, 1n+k, ef, Lemma.and_true_right_side(hd, allNN(Core.own(q, ts, 1n+d, ks, far), fuel, grammar, gmarks, input), no))
      +c = {R.clause(R.tri(fuel, grammar, gmarks, input, y), R.hasSeg(q, ks, 1n+d, 1n+k, segs)) : Bool}
      +hs2 = clause_use(R.tri(fuel, grammar, gmarks, input, y), R.hasSeg(q, ks, 1n+d, 1n+k, segs),
        when_use(Core.tokIs(Core.tokAt(input, k), t), c, ext, tok_to(input, k, a, t, ea, rk)), ny)
      walk(ts, rest, fuel, grammar, gmarks, input, segs, q, ks, 1n+d, 1n+k, G.drop_next(Core.rhsOf(grammar, q), d, Core.Terminal{t}, rest, ie),
        inv_step(d, rest, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), inv), rt, hs2, noT, ni, cl)
    case Con{Core.Node{+p, +ch}, +ts} Con{Core.Nonterminal{+x, +need}, +rest}:
      +w = Core.width(Core.Node{p, ch})
      +far = Nat.add(k, w)
      +head = {Bool.and(Core.lhsIs(grammar, p, x), Core.needOk(need, w)) : Bool}
      +own = {Bool.and(head, Core.reads(ch, grammar, Core.rhsOf(grammar, p), input, k)) : Bool}
      +left = Lemma.and_true_left(own, Core.reads(ts, grammar, rest, input, far), r)
      +hl = Lemma.and_true_left(Core.lhsIs(grammar, p, x), Core.needOk(need, w), Lemma.and_true_left(head, Core.reads(ch, grammar, Core.rhsOf(grammar, p), input, k), left))
      +nk = Lemma.and_true_right_side(Core.lhsIs(grammar, p, x), Core.needOk(need, w), Lemma.and_true_left(head, Core.reads(ch, grammar, Core.rhsOf(grammar, p), input, k), left))
      +rc = Lemma.and_true_right_side(head, Core.reads(ch, grammar, Core.rhsOf(grammar, p), input, k), left)
      +rt = Lemma.and_true_right_side(own, Core.reads(ts, grammar, rest, input, far), r)
      +ext = ext_item(fuel, grammar, gmarks, input, segs, q, ks, d, k, Some{Core.Nonterminal{x, need}}, G.nth_drop(Core.rhsOf(grammar, q), d, Core.Nonterminal{x, need}, rest, ie),
        ext_of(segs, fuel, grammar, gmarks, input, segs, q, ks, d, k, cl, hs))
      +po = prods_of(grammar, p, 0n, fuel, grammar, gmarks, input, segs, x, need, q, ks, d, k, ext, hl)
      +hp = Lemma.and_true_left(R.hasSeg(p, k, 0n, k, segs), R.compsOk(segs, fuel, grammar, gmarks, input, segs, need, p, q, ks, d, k), po)
      +cs = Lemma.and_true_right_side(R.hasSeg(p, k, 0n, k, segs), R.compsOk(segs, fuel, grammar, gmarks, input, segs, need, p, q, ks, d, k), po)
      +sOwn = Core.own(p, ch, 0n, k, k)
      +sIn = List.append(&2, Core.Bsr, Core.steps(ch, k), Core.steps(ts, far))
      +noC = nn_left(sOwn, sIn, fuel, grammar, gmarks, input, ni)
      +niR = nn_right(sOwn, sIn, fuel, grammar, gmarks, input, ni)
      +niC = nn_left(Core.steps(ch, k), Core.steps(ts, far), fuel, grammar, gmarks, input, niR)
      +niT = nn_right(Core.steps(ch, k), Core.steps(ts, far), fuel, grammar, gmarks, input, niR)
      +done = seg_to(segs, p, k, List.length(&2, Core.Sym, Core.rhsOf(grammar, p)), G.endOf(ch, k), far, G.end_node(p, ch, k),
        walk(ch, Core.rhsOf(grammar, p), fuel, grammar, gmarks, input, segs, p, k, 0n, k, {==}, {==}, rc, hp, noC, niC, cl))
      +y = {Core.Bsr{q, 1n+d, ks, k, far} : Core.Bsr}
      +hd = {notNo(R.tri(fuel, grammar, gmarks, input, y)) : Bool}
      +ny = Lemma.and_true_left(hd, allNN(Core.own(q, ts, 1n+d, ks, far), fuel, grammar, gmarks, input), no)
      +noT = Lemma.and_true_right_side(hd, allNN(Core.own(q, ts, 1n+d, ks, far), fuel, grammar, gmarks, input), no)
      +c = {R.clause(R.tri(fuel, grammar, gmarks, input, y), R.hasSeg(q, ks, 1n+d, far, segs)) : Bool}
      +wn = {R.whenB(Gll.needHolds(need, k, far), c) : Bool}
      +comp = comps_of(segs, fuel, grammar, gmarks, input, segs, need, p, q, ks, d, k, far, cs, done)
      +et = end_nn(Core.rhsOf(grammar, p), ch, fuel, grammar, gmarks, input, p, k, {==}, rc, noC)
      +hs2 = clause_use(R.tri(fuel, grammar, gmarks, input, y), R.hasSeg(q, ks, 1n+d, far, segs),
        when_use(Gll.needHolds(need, k, far), c, clause_use(R.endTri(Core.rhsOf(grammar, p), fuel, grammar, gmarks, input, p, k, far), wn, comp, et), G.need_holds(need, w, k, nk)), ny)
      walk(ts, rest, fuel, grammar, gmarks, input, segs, q, ks, 1n+d, far, G.drop_next(Core.rhsOf(grammar, q), d, Core.Nonterminal{x, need}, rest, ie),
        inv_step(d, rest, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), inv), rt, hs2, noT, niT, cl)

# ======== THE TOKENS AT i ========

law take_spells:
  for l: Nat
  for xs: +List<Nat>
  {S.spells(Lemma.takeN(l, xs), xs, 0n) == True{} : Bool}

def take_spells(l, xs):
  match l xs:
    case 0n +ys:
      {==}
    case 1n+(+p) Nil{}:
      {==}
    case 1n+(+p) Con{+x, +xt}:
      Lemma.and_true_intro(Nat.is_eq(x, x), S.spells(Lemma.takeN(p, xt), x <> xt, 1n), Lemma.nat_eq_refl(x), D.spells_unshift(Lemma.takeN(p, xt), x, xt, 0n, take_spells(p, xt)))

# The tokens of the input from i on are spelled at i.
law slice_spells:
  for input: +List<Nat>
  for i: Nat
  for +l: Nat
  {S.spells(Lemma.slice(input, i, l), input, i) == True{} : Bool}

def slice_spells(input, i, l):
  match input i:
    case +xs 0n:
      take_spells(l, xs)
    case Nil{} 1n+(+p):
      %Equal.sym(+List<Nat>, Lemma.takeN(l, []), [], Lemma.take_nil(l)) : {S.spells(_, [], 1n+p) == True{} : Bool}
      {==}
    case Con{+x, +xt} 1n+(+p):
      D.spells_unshift(Lemma.slice(xt, p, l), x, xt, p, slice_spells(xt, p, l))

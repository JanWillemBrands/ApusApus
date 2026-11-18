import Base
import ../LEMMAS.bend as Lemma
import ./CORE.bend as Core
import ./GLL.bend as Gll
import ./GUARD.bend as Guard
import ./PREFER.bend as Prefer
import ./PROOF_SPELL.bend as S
import ./PROOF_DECIDE.bend as D
import ./PROOF_GUARD.bend as PG
import ./PROOF_GLL.bend as G
import ./RIVAL.bend as R
import ./PROOF_RIVAL.bend as PR

# PHASE 2'S VERDICT ON A STEP IS RIGHT. Yes: for no production that outranks the step's is
# there a rival (a closed set of segments without its whole segment, PROOF_RIVAL.bend, or
# an empty right side whose one step is answered No). No: the certificate is a rival: its
# forest reads the tokens, and its steps at i are answered Yes by phase 1.

# ======== SMALL FACTS ========

def first_yes(+a: Guard.Tri, +b: Guard.Tri, p: {a == Guard.Yes{} : Guard.Tri} & {b == Guard.Yes{} : Guard.Tri}) -> {a == Guard.Yes{} : Guard.Tri}:
  match p:
    case (x, y):
      x

def second_yes(+a: Guard.Tri, +b: Guard.Tri, p: {a == Guard.Yes{} : Guard.Tri} & {b == Guard.Yes{} : Guard.Tri}) -> {b == Guard.Yes{} : Guard.Tri}:
  match p:
    case (x, y):
      y

law all_yes_ok:
  for xs: +List<Core.Bsr>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +input: +List<Nat>
  for +h: {Prefer.allYes(xs, fuel, grammar, gmarks, input) == True{} : Bool}
  Guard.AllStepsOk(grammar, gmarks, input, xs)

def all_yes_ok(xs, fuel, grammar, gmarks, input, h):
  match xs:
    case Nil{}:
      Unit{}
    case Con{+x, +rest}:
      +t = {Guard.isYes(Guard.stepTri(fuel, grammar, gmarks, input, x)) : Bool}
      +more = {Prefer.allYes(rest, fuel, grammar, gmarks, input) : Bool}
      (PG.step_yes(x, fuel, grammar, gmarks, input, PG.yes_of(Guard.stepTri(fuel, grammar, gmarks, input, x), Lemma.and_true_left(t, more, h))),
       all_yes_ok(rest, fuel, grammar, gmarks, input, Lemma.and_true_right_side(t, more, h)))

law with_rival:
  for +ch: +List<Core.Tree>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +input: +List<Nat>
  for +m: Nat
  for +i: Nat
  for +j: Nat
  for +h: {Prefer.certWith(ch, fuel, grammar, gmarks, input, m, i, j) == True{} : Bool}
  Prefer.Rival(grammar, gmarks, input, m, i, j)

def with_rival(ch, fuel, grammar, gmarks, input, m, i, j, h):
  +w = Lemma.slice(input, i, Nat.sub(j, i))
  +fo = {Guard.forestOk(grammar, m, w, ch) : Bool}
  +ys = {Prefer.allYes(Core.steps([Core.Node{m, ch}], i), fuel, grammar, gmarks, input) : Bool}
  +ok = Lemma.and_true_left(fo, ys, h)
  +rd0 = {Core.reads(ch, grammar, Core.rhsOf(grammar, m), w, 0n) : Bool}
  +le0 = {Nat.is_eq(List.length(&2, Nat, Core.leaves(ch)), List.length(&2, Nat, w)) : Bool}
  +rd = Lemma.and_true_left(rd0, le0, ok)
  +ln = Lemma.nat_eq_sound(List.length(&2, Nat, Core.leaves(ch)), List.length(&2, Nat, w), Lemma.and_true_right_side(rd0, le0, ok))
  +fit = D.reads_fits(ch, Core.rhsOf(grammar, m), grammar, w, 0n, rd)
  +lv = S.spells_eq(Core.leaves(ch), w, S.reads_spells(ch, Core.rhsOf(grammar, m), grammar, w, 0n, rd), ln)
  stepsOk = all_yes_ok(Core.steps([Core.Node{m, ch}], i), fuel, grammar, gmarks, input, Lemma.and_true_right_side(fo, ys, h))
  {(ch, (fit, (lv, stepsOk))) : Prefer.Rival(grammar, gmarks, input, m, i, j)}

# ======== NO: THE STEP COMPLETES A BEATEN NODE ========

law cert_true:
  for b: Bool
  for +e: {Prefer.certTri(b) == Guard.No{} : Guard.Tri}
  {b == True{} : Bool}

def cert_true(b, e):
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, D.unknown_not_no(e))

law closed_not_no:
  for b: Bool
  for +e: {Prefer.closedTri(b) == Guard.No{} : Guard.Tri}
  Empty

def closed_not_no(b, e):
  match b:
    case True{}:
      D.yes_not_no(e)
    case False{}:
      D.unknown_not_no(e)

def found_no(found: Bool, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +m: Nat, +i: Nat, +j: Nat, +e: Nat, +segs: +List<R.Seg>,
  +h: {Prefer.foundTri(found, fuel, grammar, gmarks, input, m, i, j, e, segs) == Guard.No{} : Guard.Tri}) -> Prefer.Rival(grammar, gmarks, input, m, i, j):
  match found:
    case True{}:
      +ch = R.forestAt(m, i, List.length(&2, Core.Sym, Core.rhsOf(grammar, m)), e, segs)
      with_rival(ch, fuel, grammar, gmarks, input, m, i, j, cert_true(Prefer.certWith(ch, fuel, grammar, gmarks, input, m, i, j), h))
    case False{}:
      Empty.absurd(Prefer.Rival(grammar, gmarks, input, m, i, j), closed_not_no(Bool.and(R.closedAll(segs, fuel, grammar, gmarks, input, segs), R.hasSeg(m, i, 0n, i, segs)), h))

def root_no(t: Guard.Tri, +found: Bool, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +m: Nat, +i: Nat, +j: Nat, +e: Nat, +segs: +List<R.Seg>,
  +h: {Prefer.rootTri(t, found, fuel, grammar, gmarks, input, m, i, j, e, segs) == Guard.No{} : Guard.Tri}) -> Prefer.Rival(grammar, gmarks, input, m, i, j):
  match t:
    case Guard.Yes{}:
      found_no(found, fuel, grammar, gmarks, input, m, i, j, e, segs, h)
    case Guard.No{}:
      Empty.absurd(Prefer.Rival(grammar, gmarks, input, m, i, j), D.yes_not_no(h))
    case Guard.Unknown{}:
      Empty.absurd(Prefer.Rival(grammar, gmarks, input, m, i, j), D.unknown_not_no(h))

# The rival's end: after the tokens of i .. j.
def endAt(+input: +List<Nat>, +i: Nat, +j: Nat) -> Nat:
  Nat.add(i, List.length(&2, Nat, Lemma.slice(input, i, Nat.sub(j, i))))

def cand_no(b: Bool, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +input: +List<Nat>, +q: Nat, +m: Nat, +i: Nat, +j: Nat,
  +eb: {Prefer.outranking(grammar, rmarks, q, m) == b : Bool},
  +e: {Prefer.candTri(b, fuel, grammar, gmarks, input, m, i, j) == Guard.No{} : Guard.Tri}) -> Prefer.Beaten(grammar, gmarks, rmarks, input, q, i, j):
  match b:
    case False{}:
      Empty.absurd(Prefer.Beaten(grammar, gmarks, rmarks, input, q, i, j), D.yes_not_no(e))
    case True{}:
      +ee = endAt(input, i, j)
      +segs = R.segsFrom(fuel, grammar, gmarks, input, m, i)
      rv = root_no(R.endTri(Core.rhsOf(grammar, m), fuel, grammar, gmarks, input, m, i, ee), R.hasSeg(m, i, List.length(&2, Core.Sym, Core.rhsOf(grammar, m)), ee, segs),
        fuel, grammar, gmarks, input, m, i, j, ee, segs, e)
      {(m, (eb, rv)) : Prefer.Beaten(grammar, gmarks, rmarks, input, q, i, j)}

def from_cases(+rest: +List<Core.Production>, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +input: +List<Nat>, +q: Nat, +m: Nat, +i: Nat, +j: Nat,
  cases: Either<{Prefer.candTri(Prefer.outranking(grammar, rmarks, q, m), fuel, grammar, gmarks, input, m, i, j) == Guard.No{} : Guard.Tri}, {Prefer.candsFrom(rest, fuel, grammar, gmarks, rmarks, input, q, 1n+m, i, j) == Guard.No{} : Guard.Tri}>,
  later: {Prefer.candsFrom(rest, fuel, grammar, gmarks, rmarks, input, q, 1n+m, i, j) == Guard.No{} : Guard.Tri} -> Prefer.Beaten(grammar, gmarks, rmarks, input, q, i, j))
  -> Prefer.Beaten(grammar, gmarks, rmarks, input, q, i, j):
  match cases:
    case Inl{e1}:
      cand_no(Prefer.outranking(grammar, rmarks, q, m), fuel, grammar, gmarks, rmarks, input, q, m, i, j, {==}, e1)
    case Inr{e2}:
      later(e2)

law from_no:
  for prods: +List<Core.Production>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +rmarks: +List<Prefer.RankMark>
  for +input: +List<Nat>
  for +q: Nat
  for +m: Nat
  for +i: Nat
  for +j: Nat
  for +e: {Prefer.candsFrom(prods, fuel, grammar, gmarks, rmarks, input, q, m, i, j) == Guard.No{} : Guard.Tri}
  Prefer.Beaten(grammar, gmarks, rmarks, input, q, i, j)

def from_no(prods, fuel, grammar, gmarks, rmarks, input, q, m, i, j, e):
  match prods:
    case Nil{}:
      Empty.absurd(Prefer.Beaten(grammar, gmarks, rmarks, input, q, i, j), D.yes_not_no(e))
    case Con{+p, +rest}:
      from_cases(rest, fuel, grammar, gmarks, rmarks, input, q, m, i, j,
        D.and_no_cases(Prefer.candTri(Prefer.outranking(grammar, rmarks, q, m), fuel, grammar, gmarks, input, m, i, j), Prefer.candsFrom(rest, fuel, grammar, gmarks, rmarks, input, q, 1n+m, i, j), e),
        later => from_no(rest, fuel, grammar, gmarks, rmarks, input, q, 1n+m, i, j, later))

# A step answered No completes a beaten node, so it is not free.
law free_no:
  for x: Core.Bsr
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +rmarks: +List<Prefer.RankMark>
  for +input: +List<Nat>
  for +e: {Prefer.rankTri(fuel, grammar, gmarks, rmarks, input, x) == Guard.No{} : Guard.Tri}
  for h: Prefer.Free(grammar, gmarks, rmarks, input, x)
  Empty

def free_no(x, fuel, grammar, gmarks, rmarks, input, e, h):
  match x:
    case Core.Bsr{+q, +d, +i, +k, +j}:
      PG.only_no(Nat.is_eq(d, List.length(&2, Core.Sym, Core.rhsOf(grammar, q))), Prefer.candsFrom(grammar, fuel, grammar, gmarks, rmarks, input, q, 0n, i, j), Prefer.Beaten(grammar, gmarks, rmarks, input, q, i, j) -> Empty, e, h,
        en => nb => nb(from_no(grammar, fuel, grammar, gmarks, rmarks, input, q, 0n, i, j, en)))

# ======== YES: THE STEP IS FREE ========

law cert_not_yes:
  for b: Bool
  for +e: {Prefer.certTri(b) == Guard.Yes{} : Guard.Tri}
  Empty

def cert_not_yes(b, e):
  match b:
    case True{}:
      D.no_not_yes(e)
    case False{}:
      D.unknown_not_yes(e)

law closed_yes:
  for b: Bool
  for +e: {Prefer.closedTri(b) == Guard.Yes{} : Guard.Tri}
  {b == True{} : Bool}

def closed_yes(b, e):
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, D.unknown_not_yes(e))

def spell_rival(+ch: +List<Core.Tree>, +w: +List<Nat>, +input: +List<Nat>, +i: Nat,
  +lv: {Core.leaves(ch) == w : +List<Nat>}, +h: {S.spells(w, input, i) == True{} : Bool}) -> {S.spells(Core.leaves(ch), input, i) == True{} : Bool}:
  %Equal.sym(+List<Nat>, Core.leaves(ch), w, lv) : {S.spells(_, input, i) == True{} : Bool}
  h

# A rival completes m's segment from i in a closed set that starts m at i.
def rival_walk(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +m: Nat, +i: Nat, +j: Nat, +segs: +List<R.Seg>,
  +cl: {R.closedAll(segs, fuel, grammar, gmarks, input, segs) == True{} : Bool},
  +hr: {R.hasSeg(m, i, 0n, i, segs) == True{} : Bool},
  r: Prefer.Rival(grammar, gmarks, input, m, i, j)) -> {R.hasSeg(m, i, List.length(&2, Core.Sym, Core.rhsOf(grammar, m)), endAt(input, i, j), segs) == True{} : Bool}:
  match r:
    case (ch0, (fit0, (lv0, ok))):
      +ch = ch0
      +fit = fit0
      +w = Lemma.slice(input, i, Nat.sub(j, i))
      +lv = {lv0 : {Core.leaves(ch) == w : +List<Nat>}}
      +sOwn = Core.own(m, ch, 0n, i, i)
      +sIn = List.append(&2, Core.Bsr, Core.steps(ch, i), Core.steps([], Nat.add(i, Core.width(Core.Node{m, ch}))))
      +nn = PR.all_ok_nn(Core.steps([Core.Node{m, ch}], i), fuel, grammar, gmarks, input, ok)
      +noR = PR.nn_left(sOwn, sIn, fuel, grammar, gmarks, input, nn)
      +niR = PR.nn_left(Core.steps(ch, i), Core.steps([], Nat.add(i, Core.width(Core.Node{m, ch}))), fuel, grammar, gmarks, input, PR.nn_right(sOwn, sIn, fuel, grammar, gmarks, input, nn))
      +rd = D.fits_reads(ch, Core.rhsOf(grammar, m), grammar, input, i, fit, spell_rival(ch, w, input, i, lv, PR.slice_spells(input, i, Nat.sub(j, i))))
      +done = PR.walk(ch, Core.rhsOf(grammar, m), fuel, grammar, gmarks, input, segs, m, i, 0n, i, {==}, {==}, rd, hr, noR, niR, cl)
      +endE = Equal.trans(Nat, G.endOf(ch, i), Nat.add(i, List.length(&2, Nat, Core.leaves(ch))), endAt(input, i, j), G.end_eq(ch, i),
        Equal.cong(+List<Nat>, Nat, v => Nat.add(i, List.length(&2, Nat, v)), Core.leaves(ch), w, lv))
      PR.seg_to(segs, m, i, List.length(&2, Core.Sym, Core.rhsOf(grammar, m)), G.endOf(ch, i), endAt(input, i, j), endE, done)

def found_yes(found: Bool, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +m: Nat, +i: Nat, +j: Nat, +segs: +List<R.Seg>,
  +ef: {R.hasSeg(m, i, List.length(&2, Core.Sym, Core.rhsOf(grammar, m)), endAt(input, i, j), segs) == found : Bool},
  +h: {Prefer.foundTri(found, fuel, grammar, gmarks, input, m, i, j, endAt(input, i, j), segs) == Guard.Yes{} : Guard.Tri},
  r: Prefer.Rival(grammar, gmarks, input, m, i, j)) -> Empty:
  match found:
    case True{}:
      cert_not_yes(Prefer.certWith(R.forestAt(m, i, List.length(&2, Core.Sym, Core.rhsOf(grammar, m)), endAt(input, i, j), segs), fuel, grammar, gmarks, input, m, i, j), h)
    case False{}:
      +cl0 = {R.closedAll(segs, fuel, grammar, gmarks, input, segs) : Bool}
      +hr0 = {R.hasSeg(m, i, 0n, i, segs) : Bool}
      +b = closed_yes(Bool.and(cl0, hr0), h)
      +done = rival_walk(fuel, grammar, gmarks, input, m, i, j, segs, Lemma.and_true_left(cl0, hr0, b), Lemma.and_true_right_side(cl0, hr0, b), r)
      Lemma.true_is_not_false(Equal.trans(Bool, True{}, R.hasSeg(m, i, List.length(&2, Core.Sym, Core.rhsOf(grammar, m)), endAt(input, i, j), segs), False{},
        Equal.sym(Bool, R.hasSeg(m, i, List.length(&2, Core.Sym, Core.rhsOf(grammar, m)), endAt(input, i, j), segs), True{}, done), ef))

def no_on(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +m: Nat, +i: Nat, +a: Nat, +b: Nat,
  +e: {a == b : Nat}, +h: {Guard.stepTri(fuel, grammar, gmarks, input, Core.Bsr{m, 0n, i, i, a}) == Guard.No{} : Guard.Tri})
  -> {Guard.stepTri(fuel, grammar, gmarks, input, Core.Bsr{m, 0n, i, i, b}) == Guard.No{} : Guard.Tri}:
  %e : {Guard.stepTri(fuel, grammar, gmarks, input, Core.Bsr{m, 0n, i, i, _}) == Guard.No{} : Guard.Tri}
  h

def empty_kids(ch: +List<Core.Tree>, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +m: Nat, +i: Nat, +j: Nat,
  +fit: {Core.fits(ch, grammar, []) == True{} : Bool},
  +lv: {Core.leaves(ch) == Lemma.slice(input, i, Nat.sub(j, i)) : +List<Nat>},
  +et: {Guard.stepTri(fuel, grammar, gmarks, input, Core.Bsr{m, 0n, i, i, endAt(input, i, j)}) == Guard.No{} : Guard.Tri},
  ok: Guard.AllStepsOk(grammar, gmarks, input, Core.steps([Core.Node{m, ch}], i))) -> Empty:
  match ch:
    case Nil{}:
      +ew = Equal.cong(+List<Nat>, Nat, v => Nat.add(i, List.length(&2, Nat, v)), [], Lemma.slice(input, i, Nat.sub(j, i)), lv)
      +ei = Equal.trans(Nat, i, Nat.add(i, 0n), endAt(input, i, j), Equal.sym(Nat, Nat.add(i, 0n), i, Lemma.add_zero_right(i)), ew)
      +sOwn = Core.own(m, [], 0n, i, i)
      +sIn = List.append(&2, Core.Bsr, Core.steps([], i), Core.steps([], Nat.add(i, Core.width(Core.Node{m, []}))))
      +nn = PR.nn_left(sOwn, sIn, fuel, grammar, gmarks, input, PR.all_ok_nn(Core.steps([Core.Node{m, []}], i), fuel, grammar, gmarks, input, ok))
      +hn = Lemma.and_true_left(PR.notNo(R.tri(fuel, grammar, gmarks, input, Core.Bsr{m, 0n, i, i, i})), True{}, nn)
      +eno = no_on(fuel, grammar, gmarks, input, m, i, endAt(input, i, j), i, Equal.sym(Nat, i, endAt(input, i, j), ei), et)
      Lemma.false_is_not_true(Equal.trans(Bool, False{}, PR.notNo(R.tri(fuel, grammar, gmarks, input, Core.Bsr{m, 0n, i, i, i})), True{},
        Equal.sym(Bool, PR.notNo(R.tri(fuel, grammar, gmarks, input, Core.Bsr{m, 0n, i, i, i})), False{}, Equal.cong(Guard.Tri, Bool, v => PR.notNo(v), R.tri(fuel, grammar, gmarks, input, Core.Bsr{m, 0n, i, i, i}), Guard.No{}, eno)), hn))
    case Con{Core.Leaf{+a}, +ts}:
      Lemma.false_is_not_true(fit)
    case Con{Core.Node{+q2, +c2}, +ts}:
      Lemma.false_is_not_true(fit)

# m's right side is empty and its one step is answered No: the rival's own step breaks a rule.
def empty_rival(items: +List<Core.Sym>, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +m: Nat, +i: Nat, +j: Nat,
  +ip: {Core.rhsOf(grammar, m) == items : +List<Core.Sym>},
  +et: {R.endTri(items, fuel, grammar, gmarks, input, m, i, endAt(input, i, j)) == Guard.No{} : Guard.Tri},
  r: Prefer.Rival(grammar, gmarks, input, m, i, j)) -> Empty:
  match items:
    case Con{+s, +rest}:
      D.yes_not_no(et)
    case Nil{}:
      match r:
        case (ch0, (fit0, (lv0, ok))):
          +ch = ch0
          +w = Lemma.slice(input, i, Nat.sub(j, i))
          +fit = {(%ip : {Core.fits(ch, grammar, _) == True{} : Bool}
            fit0) : {Core.fits(ch, grammar, []) == True{} : Bool}}
          empty_kids(ch, fuel, grammar, gmarks, input, m, i, j, fit, lv0, et, ok)

def root_yes(t: Guard.Tri, +found: Bool, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +m: Nat, +i: Nat, +j: Nat, +segs: +List<R.Seg>,
  +et: {R.endTri(Core.rhsOf(grammar, m), fuel, grammar, gmarks, input, m, i, endAt(input, i, j)) == t : Guard.Tri},
  +ef: {R.hasSeg(m, i, List.length(&2, Core.Sym, Core.rhsOf(grammar, m)), endAt(input, i, j), segs) == found : Bool},
  +h: {Prefer.rootTri(t, found, fuel, grammar, gmarks, input, m, i, j, endAt(input, i, j), segs) == Guard.Yes{} : Guard.Tri},
  r: Prefer.Rival(grammar, gmarks, input, m, i, j)) -> Empty:
  match t:
    case Guard.Yes{}:
      found_yes(found, fuel, grammar, gmarks, input, m, i, j, segs, ef, h, r)
    case Guard.No{}:
      empty_rival(Core.rhsOf(grammar, m), fuel, grammar, gmarks, input, m, i, j, {==}, et, r)
    case Guard.Unknown{}:
      D.unknown_not_yes(h)

def cand_yes(b: Bool, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +input: +List<Nat>, +q: Nat, +m: Nat, +i: Nat, +j: Nat,
  +eb: {Prefer.outranking(grammar, rmarks, q, m) == b : Bool},
  +hb: {Prefer.outranking(grammar, rmarks, q, m) == True{} : Bool},
  +e: {Prefer.candTri(b, fuel, grammar, gmarks, input, m, i, j) == Guard.Yes{} : Guard.Tri},
  r: Prefer.Rival(grammar, gmarks, input, m, i, j)) -> Empty:
  match b:
    case False{}:
      Lemma.true_is_not_false(Equal.trans(Bool, True{}, Prefer.outranking(grammar, rmarks, q, m), False{}, Equal.sym(Bool, Prefer.outranking(grammar, rmarks, q, m), True{}, hb), eb))
    case True{}:
      +segs = R.segsFrom(fuel, grammar, gmarks, input, m, i)
      root_yes(R.endTri(Core.rhsOf(grammar, m), fuel, grammar, gmarks, input, m, i, endAt(input, i, j)), R.hasSeg(m, i, List.length(&2, Core.Sym, Core.rhsOf(grammar, m)), endAt(input, i, j), segs),
        fuel, grammar, gmarks, input, m, i, j, segs, {==}, {==}, e, r)

law at_zero:
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +rmarks: +List<Prefer.RankMark>
  for +input: +List<Nat>
  for +q: Nat
  for +base: Nat
  for +i: Nat
  for +j: Nat
  for +h: {Prefer.candTri(Prefer.outranking(grammar, rmarks, q, base), fuel, grammar, gmarks, input, base, i, j) == Guard.Yes{} : Guard.Tri}
  {Prefer.candTri(Prefer.outranking(grammar, rmarks, q, Nat.add(base, 0n)), fuel, grammar, gmarks, input, Nat.add(base, 0n), i, j) == Guard.Yes{} : Guard.Tri}

def at_zero(fuel, grammar, gmarks, rmarks, input, q, base, i, j, h):
  %Equal.sym(Nat, Nat.add(base, 0n), base, Lemma.add_zero_right(base)) : {Prefer.candTri(Prefer.outranking(grammar, rmarks, q, _), fuel, grammar, gmarks, input, _, i, j) == Guard.Yes{} : Guard.Tri}
  h

law at_succ:
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +rmarks: +List<Prefer.RankMark>
  for +input: +List<Nat>
  for +q: Nat
  for +base: Nat
  for +n: Nat
  for +i: Nat
  for +j: Nat
  for +h: {Prefer.candTri(Prefer.outranking(grammar, rmarks, q, 1n+Nat.add(base, n)), fuel, grammar, gmarks, input, 1n+Nat.add(base, n), i, j) == Guard.Yes{} : Guard.Tri}
  {Prefer.candTri(Prefer.outranking(grammar, rmarks, q, Nat.add(base, 1n+n)), fuel, grammar, gmarks, input, Nat.add(base, 1n+n), i, j) == Guard.Yes{} : Guard.Tri}

def at_succ(fuel, grammar, gmarks, rmarks, input, q, base, n, i, j, h):
  %Equal.sym(Nat, Nat.add(base, 1n+n), 1n+Nat.add(base, n), Lemma.add_succ_right(base, n)) : {Prefer.candTri(Prefer.outranking(grammar, rmarks, q, _), fuel, grammar, gmarks, input, _, i, j) == Guard.Yes{} : Guard.Tri}
  h

# A Yes over all productions is a Yes for each production of q's nonterminal.
law from_yes_at:
  for g: +List<Core.Production>
  for n: Nat
  for +base: Nat
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +rmarks: +List<Prefer.RankMark>
  for +input: +List<Nat>
  for +q: Nat
  for +i: Nat
  for +j: Nat
  for +h: {Core.lhsIs(g, n, Gll.lhsOf(grammar, q)) == True{} : Bool}
  for +e: {Prefer.candsFrom(g, fuel, grammar, gmarks, rmarks, input, q, base, i, j) == Guard.Yes{} : Guard.Tri}
  {Prefer.candTri(Prefer.outranking(grammar, rmarks, q, Nat.add(base, n)), fuel, grammar, gmarks, input, Nat.add(base, n), i, j) == Guard.Yes{} : Guard.Tri}

def from_yes_at(g, n, base, fuel, grammar, gmarks, rmarks, input, q, i, j, h, e):
  match g n:
    case Nil{} +n0:
      Empty.absurd({Prefer.candTri(Prefer.outranking(grammar, rmarks, q, Nat.add(base, n0)), fuel, grammar, gmarks, input, Nat.add(base, n0), i, j) == Guard.Yes{} : Guard.Tri}, Lemma.false_is_not_true(h))
    case Con{Core.Production{+lhs, +rhs}, +rest} 0n:
      +here = Prefer.candTri(Prefer.outranking(grammar, rmarks, q, base), fuel, grammar, gmarks, input, base, i, j)
      +more = Prefer.candsFrom(rest, fuel, grammar, gmarks, rmarks, input, q, 1n+base, i, j)
      both = D.and_yes(here, more, e)
      at_zero(fuel, grammar, gmarks, rmarks, input, q, base, i, j, first_yes(here, more, both))
    case Con{Core.Production{+lhs, +rhs}, +rest} 1n+(+n2):
      +here = Prefer.candTri(Prefer.outranking(grammar, rmarks, q, base), fuel, grammar, gmarks, input, base, i, j)
      +more = Prefer.candsFrom(rest, fuel, grammar, gmarks, rmarks, input, q, 1n+base, i, j)
      both = D.and_yes(here, more, e)
      at_succ(fuel, grammar, gmarks, rmarks, input, q, base, n2, i, j, from_yes_at(rest, n2, 1n+base, fuel, grammar, gmarks, rmarks, input, q, i, j, h, second_yes(here, more, both)))

def beaten_none(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +input: +List<Nat>, +q: Nat, +i: Nat, +j: Nat,
  +e: {Prefer.candsFrom(grammar, fuel, grammar, gmarks, rmarks, input, q, 0n, i, j) == Guard.Yes{} : Guard.Tri},
  bt: Prefer.Beaten(grammar, gmarks, rmarks, input, q, i, j)) -> Empty:
  match bt:
    case (m0, (ec0, r)):
      +m = m0
      +ec = ec0
      +lhs = Lemma.and_true_left(Core.lhsIs(grammar, m, Gll.lhsOf(grammar, q)), Prefer.outranks(Prefer.rankOf(rmarks, m), Prefer.rankOf(rmarks, q)), ec)
      +at = from_yes_at(grammar, m, 0n, fuel, grammar, gmarks, rmarks, input, q, i, j, lhs, e)
      cand_yes(Prefer.outranking(grammar, rmarks, q, m), fuel, grammar, gmarks, rmarks, input, q, m, i, j, {==}, ec, at, r)

# A step answered Yes is free.
law free_yes:
  for x: Core.Bsr
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +rmarks: +List<Prefer.RankMark>
  for +input: +List<Nat>
  for +e: {Prefer.rankTri(fuel, grammar, gmarks, rmarks, input, x) == Guard.Yes{} : Guard.Tri}
  Prefer.Free(grammar, gmarks, rmarks, input, x)

def free_yes(x, fuel, grammar, gmarks, rmarks, input, e):
  match x:
    case Core.Bsr{+q, +d, +i, +k, +j}:
      PG.only_yes(Nat.is_eq(d, List.length(&2, Core.Sym, Core.rhsOf(grammar, q))), Prefer.candsFrom(grammar, fuel, grammar, gmarks, rmarks, input, q, 0n, i, j), Prefer.Beaten(grammar, gmarks, rmarks, input, q, i, j) -> Empty, e,
        ey => bt => beaten_none(fuel, grammar, gmarks, rmarks, input, q, i, j, ey, bt))

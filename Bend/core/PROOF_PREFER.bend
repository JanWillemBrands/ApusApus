import Base
import ../LEMMAS.bend as Lemma
import ./CORE.bend as Core
import ./GLL.bend as Gll
import ./GUARD.bend as Guard
import ./PREFER.bend as Prefer
import ./PROOF_SPELL.bend as S
import ./PROOF_DECIDE.bend as D
import ./PROOF_GUARD.bend as PG

# PHASE 2'S VERDICT ON A STEP IS RIGHT. Yes: no production that outranks the step's derives
# its tokens (the exact parser says so, PROOF_DECIDE.bend), so there is no rival. No: the
# certificate is a rival: its forest reads the tokens, and its steps at i are answered Yes
# by phase 1.

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

def rival_no(t: Guard.Tri, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +m: Nat, +i: Nat, +j: Nat,
  +e: {Prefer.rivalPick(t, fuel, grammar, gmarks, input, m, i, j) == Guard.No{} : Guard.Tri}) -> Prefer.Rival(grammar, gmarks, input, m, i, j):
  match t:
    case Guard.No{}:
      Empty.absurd(Prefer.Rival(grammar, gmarks, input, m, i, j), D.yes_not_no(e))
    case Guard.Yes{}:
      with_rival(Prefer.rivalFor(fuel, grammar, m, Lemma.slice(input, i, Nat.sub(j, i))), fuel, grammar, gmarks, input, m, i, j, cert_true(Prefer.certFor(fuel, grammar, gmarks, input, m, i, j), e))
    case Guard.Unknown{}:
      with_rival(Prefer.rivalFor(fuel, grammar, m, Lemma.slice(input, i, Nat.sub(j, i))), fuel, grammar, gmarks, input, m, i, j, cert_true(Prefer.certFor(fuel, grammar, gmarks, input, m, i, j), e))

def cand_no(b: Bool, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +input: +List<Nat>, +q: Nat, +m: Nat, +i: Nat, +j: Nat,
  +eb: {Prefer.outranking(grammar, rmarks, q, m) == b : Bool},
  +e: {Prefer.candTri(b, fuel, grammar, gmarks, input, m, i, j) == Guard.No{} : Guard.Tri}) -> Prefer.Beaten(grammar, gmarks, rmarks, input, q, i, j):
  match b:
    case False{}:
      Empty.absurd(Prefer.Beaten(grammar, gmarks, rmarks, input, q, i, j), D.yes_not_no(e))
    case True{}:
      rv = rival_no(Guard.rhsTri(fuel, grammar, m, Lemma.slice(input, i, Nat.sub(j, i))), fuel, grammar, gmarks, input, m, i, j, e)
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

def rival_yes(t: Guard.Tri, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +m: Nat, +i: Nat, +j: Nat,
  +et: {Guard.rhsTri(fuel, grammar, m, Lemma.slice(input, i, Nat.sub(j, i))) == t : Guard.Tri},
  +e: {Prefer.rivalPick(t, fuel, grammar, gmarks, input, m, i, j) == Guard.Yes{} : Guard.Tri}) -> {Guard.rhsTri(fuel, grammar, m, Lemma.slice(input, i, Nat.sub(j, i))) == Guard.No{} : Guard.Tri}:
  match t:
    case Guard.No{}:
      et
    case Guard.Yes{}:
      Empty.absurd({Guard.rhsTri(fuel, grammar, m, Lemma.slice(input, i, Nat.sub(j, i))) == Guard.No{} : Guard.Tri}, cert_not_yes(Prefer.certFor(fuel, grammar, gmarks, input, m, i, j), e))
    case Guard.Unknown{}:
      Empty.absurd({Guard.rhsTri(fuel, grammar, m, Lemma.slice(input, i, Nat.sub(j, i))) == Guard.No{} : Guard.Tri}, cert_not_yes(Prefer.certFor(fuel, grammar, gmarks, input, m, i, j), e))

def rival_none(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +m: Nat, +i: Nat, +j: Nat,
  +en: {Guard.rhsTri(fuel, grammar, m, Lemma.slice(input, i, Nat.sub(j, i))) == Guard.No{} : Guard.Tri},
  r: Prefer.Rival(grammar, gmarks, input, m, i, j)) -> Empty:
  match r:
    case (ch0, (fit0, (lv0, rest))):
      +ch = ch0
      +fit = fit0
      +lv = lv0
      D.rhs_no(fuel, grammar, m, Lemma.slice(input, i, Nat.sub(j, i)), en, {(ch, (fit, lv)) : Core.Derives(grammar, Core.rhsOf(grammar, m), Lemma.slice(input, i, Nat.sub(j, i)))})

def cand_yes(b: Bool, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +input: +List<Nat>, +q: Nat, +m: Nat, +i: Nat, +j: Nat,
  +eb: {Prefer.outranking(grammar, rmarks, q, m) == b : Bool},
  +hb: {Prefer.outranking(grammar, rmarks, q, m) == True{} : Bool},
  +e: {Prefer.candTri(b, fuel, grammar, gmarks, input, m, i, j) == Guard.Yes{} : Guard.Tri},
  r: Prefer.Rival(grammar, gmarks, input, m, i, j)) -> Empty:
  match b:
    case False{}:
      Lemma.true_is_not_false(Equal.trans(Bool, True{}, Prefer.outranking(grammar, rmarks, q, m), False{}, Equal.sym(Bool, Prefer.outranking(grammar, rmarks, q, m), True{}, hb), eb))
    case True{}:
      rival_none(fuel, grammar, gmarks, input, m, i, j, rival_yes(Guard.rhsTri(fuel, grammar, m, Lemma.slice(input, i, Nat.sub(j, i))), fuel, grammar, gmarks, input, m, i, j, {==}, e), r)

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

import Base
import ./LEMMAS.bend as Lemma
import ./CORE.bend as Core
import ./GLL.bend as Gll
import ./GUARD.bend as Guard
import ./CLOSURE.bend as CL
import ./PREFER.bend as P
import ./RUN.bend as Run
import ./PROOF_RUN.bend as RN
import ./PROOF_CLOSURE.bend as PCL
import ./PROOF_RIVAL_GROW.bend as RG
import ./PROOF_RIVAL_SOUND.bend as RS

# THE VERDICTS ARE DECIDED. With fuel 1 + the size of the input's descriptor universe, every
# question phase 1 asks ("does q derive w", w cut from the input) is answered Yes or No by
# the closure (CLOSURE.bend), so phase 1 decides every step (`phase1_decides`), and phase
# 2's verdict is decided on every step within bounds (`phase2_decides`).

# ======== DOES PRODUCTION q DERIVE w? ========

def yes_dec(b: Bool, +h: {b == True{} : Bool}) -> {RG.decidedTri(Guard.yesIf(b)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(h))

def no_dec(b: Bool, +h: {b == True{} : Bool}) -> {RG.decidedTri(Guard.noIf(b)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(h))

def found_dec(found: Bool, +fuel: Nat, +grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +w: +List<Nat>, +ef: {CL.hasSeg(q, 0n, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), List.length(&2, Nat, w), CL.segsFrom(fuel, grammar, w, q, 0n)) == found : Bool},
  +hq: {Nat.is_le(1n+q, List.length(&2, Core.Production, grammar)) == True{} : Bool},
  +hw: {Nat.is_le(List.length(&2, Nat, w), List.length(&2, Nat, input)) == True{} : Bool}, +hf: {Nat.is_le(1n+List.length(&2, Gll.Desc, Run.univ(grammar, input)), fuel) == True{} : Bool})
  -> {RG.decidedTri(Guard.foundPick(found, grammar, q, w, CL.segsFrom(fuel, grammar, w, q, 0n))) == True{} : Bool}:
  match found:
    case True{}:
      yes_dec(Guard.forestOk(grammar, q, w, CL.forestAt(q, 0n, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), List.length(&2, Nat, w), CL.segsFrom(fuel, grammar, w, q, 0n))), PCL.closure_found(fuel, grammar, w, q, ef))
    case False{}:
      no_dec(Bool.and(CL.closedAll(CL.segsFrom(fuel, grammar, w, q, 0n), grammar, w, CL.segsFrom(fuel, grammar, w, q, 0n)), CL.hasSeg(q, 0n, 0n, 0n, CL.segsFrom(fuel, grammar, w, q, 0n))),
        PCL.closure_closed(fuel, grammar, w, input, q, 0n, hq, Lemma.zero_le(List.length(&2, Nat, w)), hw, hf))

def empty_dec(w: +List<Nat>) -> {RG.decidedTri(Guard.emptyTri(w)) == True{} : Bool}:
  match w:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      {==}

def real_dec(b: Bool, +fuel: Nat, +grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +w: +List<Nat>, +eb: {Core.lhsIs(grammar, q, Gll.lhsOf(grammar, q)) == b : Bool},
  +hw: {Nat.is_le(List.length(&2, Nat, w), List.length(&2, Nat, input)) == True{} : Bool}, +hf: {Nat.is_le(1n+List.length(&2, Gll.Desc, Run.univ(grammar, input)), fuel) == True{} : Bool})
  -> {RG.decidedTri(Guard.rhsPick(b, fuel, grammar, q, w)) == True{} : Bool}:
  match b:
    case True{}:
      found_dec(CL.hasSeg(q, 0n, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), List.length(&2, Nat, w), CL.segsFrom(fuel, grammar, w, q, 0n)), fuel, grammar, input, q, w, {==},
        RN.lhs_bound(grammar, q, Gll.lhsOf(grammar, q), eb), hw, hf)
    case False{}:
      empty_dec(w)

# Does production q derive w: decided, for w no longer than the input.
law rhs_dec:
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +q: Nat
  for +w: +List<Nat>
  for +hw: {Nat.is_le(List.length(&2, Nat, w), List.length(&2, Nat, input)) == True{} : Bool}
  for +hf: {Nat.is_le(1n+List.length(&2, Gll.Desc, Run.univ(grammar, input)), fuel) == True{} : Bool}
  {RG.decidedTri(Guard.rhsTri(fuel, grammar, q, w)) == True{} : Bool}

def rhs_dec(fuel, grammar, input, q, w, hw, hf):
  real_dec(Core.lhsIs(grammar, q, Gll.lhsOf(grammar, q)), fuel, grammar, input, q, w, {==}, hw, hf)

# ======== DECIDED ANSWERS COMBINE ========

def and_dec(a: Guard.Tri, b: Guard.Tri, +ha: {RG.decidedTri(a) == True{} : Bool}, +hb: {RG.decidedTri(b) == True{} : Bool}) -> {RG.decidedTri(Guard.andTri(a, b)) == True{} : Bool}:
  match a b:
    case Guard.Yes{} Guard.Yes{}:
      {==}
    case Guard.Yes{} Guard.No{}:
      {==}
    case Guard.No{} Guard.Yes{}:
      {==}
    case Guard.No{} Guard.No{}:
      {==}
    case Guard.Yes{} Guard.Unknown{}:
      Empty.absurd({RG.decidedTri(Guard.andTri(Guard.Yes{}, Guard.Unknown{})) == True{} : Bool}, Lemma.false_is_not_true(hb))
    case Guard.No{} Guard.Unknown{}:
      {==}
    case Guard.Unknown{} +b0:
      Empty.absurd({RG.decidedTri(Guard.andTri(Guard.Unknown{}, b0)) == True{} : Bool}, Lemma.false_is_not_true(ha))

def or_dec(a: Guard.Tri, b: Guard.Tri, +ha: {RG.decidedTri(a) == True{} : Bool}, +hb: {RG.decidedTri(b) == True{} : Bool}) -> {RG.decidedTri(Guard.orTri(a, b)) == True{} : Bool}:
  match a b:
    case Guard.Yes{} Guard.Yes{}:
      {==}
    case Guard.Yes{} Guard.No{}:
      {==}
    case Guard.No{} Guard.Yes{}:
      {==}
    case Guard.No{} Guard.No{}:
      {==}
    case Guard.Yes{} Guard.Unknown{}:
      {==}
    case Guard.No{} Guard.Unknown{}:
      Empty.absurd({RG.decidedTri(Guard.orTri(Guard.No{}, Guard.Unknown{})) == True{} : Bool}, Lemma.false_is_not_true(hb))
    case Guard.Unknown{} +b0:
      Empty.absurd({RG.decidedTri(Guard.orTri(Guard.Unknown{}, b0)) == True{} : Bool}, Lemma.false_is_not_true(ha))

def not_dec(a: Guard.Tri, +ha: {RG.decidedTri(a) == True{} : Bool}) -> {RG.decidedTri(Guard.notTri(a)) == True{} : Bool}:
  match a:
    case Guard.Yes{}:
      {==}
    case Guard.No{}:
      {==}
    case Guard.Unknown{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(ha))

def only_dec(b: Bool, +t: Guard.Tri, +ht: {RG.decidedTri(t) == True{} : Bool}) -> {RG.decidedTri(Guard.only(b, t)) == True{} : Bool}:
  match b:
    case True{}:
      ht
    case False{}:
      {==}

# ======== THE QUESTIONS OF THE RULES ========

def nt_pick_dec(b: Bool, +fuel: Nat, +grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +w: +List<Nat>, +hw: {Nat.is_le(List.length(&2, Nat, w), List.length(&2, Nat, input)) == True{} : Bool}, +hf: {Nat.is_le(1n+List.length(&2, Gll.Desc, Run.univ(grammar, input)), fuel) == True{} : Bool})
  -> {RG.decidedTri(Guard.ntPick(b, fuel, grammar, q, w)) == True{} : Bool}:
  match b:
    case True{}:
      rhs_dec(fuel, grammar, input, q, w, hw, hf)
    case False{}:
      {==}

law nt_from_dec:
  for prods: +List<Core.Production>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +x: Nat
  for +q: Nat
  for +w: +List<Nat>
  for +hw: {Nat.is_le(List.length(&2, Nat, w), List.length(&2, Nat, input)) == True{} : Bool}
  for +hf: {Nat.is_le(1n+List.length(&2, Gll.Desc, Run.univ(grammar, input)), fuel) == True{} : Bool}
  {RG.decidedTri(Guard.ntFrom(prods, fuel, grammar, x, q, w)) == True{} : Bool}

def nt_from_dec(prods, fuel, grammar, input, x, q, w, hw, hf):
  match prods:
    case Nil{}:
      {==}
    case Con{+p, +rest}:
      or_dec(Guard.ntPick(Core.lhsIs(grammar, q, x), fuel, grammar, q, w), Guard.ntFrom(rest, fuel, grammar, x, 1n+q, w),
        nt_pick_dec(Core.lhsIs(grammar, q, x), fuel, grammar, input, q, w, hw, hf), nt_from_dec(rest, fuel, grammar, input, x, 1n+q, w, hw, hf))

def nt_dec(+fuel: Nat, +grammar: +List<Core.Production>, +input: +List<Nat>, +x: Nat, +w: +List<Nat>, +hw: {Nat.is_le(List.length(&2, Nat, w), List.length(&2, Nat, input)) == True{} : Bool}, +hf: {Nat.is_le(1n+List.length(&2, Gll.Desc, Run.univ(grammar, input)), fuel) == True{} : Bool})
  -> {RG.decidedTri(Guard.ntTri(fuel, grammar, x, w)) == True{} : Bool}:
  nt_from_dec(grammar, fuel, grammar, input, x, 0n, w, hw, hf)

law ahead_from_dec:
  for m: Nat
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +x: Nat
  for +ahead: +List<Nat>
  for +ha: {Nat.is_le(List.length(&2, Nat, ahead), List.length(&2, Nat, input)) == True{} : Bool}
  for +hf: {Nat.is_le(1n+List.length(&2, Gll.Desc, Run.univ(grammar, input)), fuel) == True{} : Bool}
  {RG.decidedTri(Guard.aheadFrom(m, fuel, grammar, x, ahead)) == True{} : Bool}

def ahead_from_dec(m, fuel, grammar, input, x, ahead, ha, hf):
  match m:
    case 0n:
      nt_dec(fuel, grammar, input, x, [], Lemma.zero_le(List.length(&2, Nat, input)), hf)
    case 1n+(+p):
      or_dec(Guard.ntTri(fuel, grammar, x, Lemma.takeN(1n+p, ahead)), Guard.aheadFrom(p, fuel, grammar, x, ahead),
        nt_dec(fuel, grammar, input, x, Lemma.takeN(1n+p, ahead),
          Lemma.le_trans(List.length(&2, Nat, Lemma.takeN(1n+p, ahead)), List.length(&2, Nat, ahead), List.length(&2, Nat, input), Lemma.length_take_le(1n+p, ahead), ha), hf),
        ahead_from_dec(p, fuel, grammar, input, x, ahead, ha, hf))

law all_ahead_dec:
  for xs: +List<Nat>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +ahead: +List<Nat>
  for +ha: {Nat.is_le(List.length(&2, Nat, ahead), List.length(&2, Nat, input)) == True{} : Bool}
  for +hf: {Nat.is_le(1n+List.length(&2, Gll.Desc, Run.univ(grammar, input)), fuel) == True{} : Bool}
  {RG.decidedTri(Guard.allAheadTri(xs, fuel, grammar, ahead)) == True{} : Bool}

def all_ahead_dec(xs, fuel, grammar, input, ahead, ha, hf):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      and_dec(Guard.aheadTri(fuel, grammar, x, ahead), Guard.allAheadTri(rest, fuel, grammar, ahead),
        ahead_from_dec(List.length(&2, Nat, ahead), fuel, grammar, input, x, ahead, ha, hf), all_ahead_dec(rest, fuel, grammar, input, ahead, ha, hf))

law none_ahead_dec:
  for xs: +List<Nat>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +ahead: +List<Nat>
  for +ha: {Nat.is_le(List.length(&2, Nat, ahead), List.length(&2, Nat, input)) == True{} : Bool}
  for +hf: {Nat.is_le(1n+List.length(&2, Gll.Desc, Run.univ(grammar, input)), fuel) == True{} : Bool}
  {RG.decidedTri(Guard.noneAheadTri(xs, fuel, grammar, ahead)) == True{} : Bool}

def none_ahead_dec(xs, fuel, grammar, input, ahead, ha, hf):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      and_dec(Guard.notTri(Guard.aheadTri(fuel, grammar, x, ahead)), Guard.noneAheadTri(rest, fuel, grammar, ahead),
        not_dec(Guard.aheadTri(fuel, grammar, x, ahead), ahead_from_dec(List.length(&2, Nat, ahead), fuel, grammar, input, x, ahead, ha, hf)),
        none_ahead_dec(rest, fuel, grammar, input, ahead, ha, hf))

law none_derive_dec:
  for xs: +List<Nat>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +w: +List<Nat>
  for +hw: {Nat.is_le(List.length(&2, Nat, w), List.length(&2, Nat, input)) == True{} : Bool}
  for +hf: {Nat.is_le(1n+List.length(&2, Gll.Desc, Run.univ(grammar, input)), fuel) == True{} : Bool}
  {RG.decidedTri(Guard.noneDeriveTri(xs, fuel, grammar, w)) == True{} : Bool}

def none_derive_dec(xs, fuel, grammar, input, w, hw, hf):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      and_dec(Guard.notTri(Guard.ntTri(fuel, grammar, x, w)), Guard.noneDeriveTri(rest, fuel, grammar, w),
        not_dec(Guard.ntTri(fuel, grammar, x, w), nt_dec(fuel, grammar, input, x, w, hw, hf)), none_derive_dec(rest, fuel, grammar, input, w, hw, hf))

def edge_dec(ids: +List<Nat>, +fuel: Nat, +grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +w: +List<Nat>, +hw: {Nat.is_le(List.length(&2, Nat, w), List.length(&2, Nat, input)) == True{} : Bool}, +hf: {Nat.is_le(1n+List.length(&2, Gll.Desc, Run.univ(grammar, input)), fuel) == True{} : Bool})
  -> {RG.decidedTri(Guard.edgeTri(ids, fuel, grammar, q, w)) == True{} : Bool}:
  match ids:
    case Nil{}:
      not_dec(Guard.rhsTri(fuel, grammar, q, w), rhs_dec(fuel, grammar, input, q, w, hw, hf))
    case Con{+x, +rest}:
      none_derive_dec(x <> rest, fuel, grammar, input, w, hw, hf)

def drop_le(+input: +List<Nat>, +i: Nat) -> {Nat.is_le(List.length(&2, Nat, Lemma.dropN(i, input)), List.length(&2, Nat, input)) == True{} : Bool}:
  Lemma.length_drop_le(i, input)

def slice_le(+input: +List<Nat>, +k: Nat, +l: Nat) -> {Nat.is_le(List.length(&2, Nat, Lemma.slice(input, k, l)), List.length(&2, Nat, input)) == True{} : Bool}:
  Lemma.le_trans(List.length(&2, Nat, Lemma.takeN(l, Lemma.dropN(k, input))), List.length(&2, Nat, Lemma.dropN(k, input)), List.length(&2, Nat, input),
    Lemma.length_take_le(l, Lemma.dropN(k, input)), Lemma.length_drop_le(k, input))

# ======== PHASE 1 DECIDES ========

def rule_dec(g: Guard.Guard, +fuel: Nat, +grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +n: Nat, +d: Nat, +i: Nat, +k: Nat, +j: Nat, +hf: {Nat.is_le(1n+List.length(&2, Gll.Desc, Run.univ(grammar, input)), fuel) == True{} : Bool})
  -> {RG.decidedTri(Guard.ruleAt(g, fuel, grammar, input, q, n, d, i, k, j)) == True{} : Bool}:
  match g:
    case Guard.Ahead{+ids}:
      only_dec(Nat.is_eq(d, n), Guard.allAheadTri(ids, fuel, grammar, Lemma.dropN(i, input)), all_ahead_dec(ids, fuel, grammar, input, Lemma.dropN(i, input), drop_le(input, i), hf))
    case Guard.NotAhead{+ids}:
      only_dec(Nat.is_eq(d, n), Guard.noneAheadTri(ids, fuel, grammar, Lemma.dropN(i, input)), none_ahead_dec(ids, fuel, grammar, input, Lemma.dropN(i, input), drop_le(input, i), hf))
    case Guard.LeftAssoc{+ids}:
      only_dec(Bool.and(Nat.is_eq(d, n), Bool.not(Nat.is_eq(d, 0n))), Guard.edgeTri(ids, fuel, grammar, q, Lemma.slice(input, k, Nat.sub(j, k))),
        edge_dec(ids, fuel, grammar, input, q, Lemma.slice(input, k, Nat.sub(j, k)), slice_le(input, k, Nat.sub(j, k)), hf))
    case Guard.RightAssoc{+ids}:
      only_dec(Nat.is_eq(d, 1n), Guard.edgeTri(ids, fuel, grammar, q, Lemma.slice(input, k, Nat.sub(j, k))),
        edge_dec(ids, fuel, grammar, input, q, Lemma.slice(input, k, Nat.sub(j, k)), slice_le(input, k, Nat.sub(j, k)), hf))

law rules_dec:
  for gs: +List<Guard.Guard>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +q: Nat
  for +n: Nat
  for +d: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for +hf: {Nat.is_le(1n+List.length(&2, Gll.Desc, Run.univ(grammar, input)), fuel) == True{} : Bool}
  {RG.decidedTri(Guard.rulesAt(gs, fuel, grammar, input, q, n, d, i, k, j)) == True{} : Bool}

def rules_dec(gs, fuel, grammar, input, q, n, d, i, k, j, hf):
  match gs:
    case Nil{}:
      {==}
    case Con{+g, +rest}:
      and_dec(Guard.ruleAt(g, fuel, grammar, input, q, n, d, i, k, j), Guard.rulesAt(rest, fuel, grammar, input, q, n, d, i, k, j),
        rule_dec(g, fuel, grammar, input, q, n, d, i, k, j, hf), rules_dec(rest, fuel, grammar, input, q, n, d, i, k, j, hf))

# PHASE 1 DECIDES: with fuel 1 + the size of the input's descriptor universe, phase 1's
# verdict on every step is Yes or No.
law phase1_decides:
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +input: +List<Nat>
  for y: Core.Bsr
  for +hf: {Nat.is_le(1n+List.length(&2, Gll.Desc, Run.univ(grammar, input)), fuel) == True{} : Bool}
  {RG.decidedTri(Guard.stepTri(fuel, grammar, gmarks, input, y)) == True{} : Bool}

def phase1_decides(fuel, grammar, gmarks, input, y, hf):
  match y:
    case Core.Bsr{+q, +d, +i, +k, +j}:
      rules_dec(Guard.guardsOf(gmarks, q), fuel, grammar, input, q, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), d, i, k, j, hf)

law all_decided:
  for ys: +List<Core.Bsr>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +input: +List<Nat>
  for +hf: {Nat.is_le(1n+List.length(&2, Gll.Desc, Run.univ(grammar, input)), fuel) == True{} : Bool}
  {RG.allDecided(ys, fuel, grammar, gmarks, input) == True{} : Bool}

def all_decided(ys, fuel, grammar, gmarks, input, hf):
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      Lemma.and_true_intro(RG.decidedTri(Guard.stepTri(fuel, grammar, gmarks, input, y)), RG.allDecided(rest, fuel, grammar, gmarks, input),
        phase1_decides(fuel, grammar, gmarks, input, y, hf), all_decided(rest, fuel, grammar, gmarks, input, hf))

# The hypothesis of the rival laws holds.
def decided_holds(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +hf: {Nat.is_le(1n+List.length(&2, Gll.Desc, Run.univ(grammar, input)), fuel) == True{} : Bool})
  -> {RG.decided(fuel, grammar, gmarks, input) == True{} : Bool}:
  all_decided(RG.stepsOver(Run.univ(grammar, input), List.length(&2, Nat, input)), fuel, grammar, gmarks, input, hf)

# ======== PHASE 2 DECIDES ========

def cand_dec(b: Bool, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +m: Nat, +i: Nat, +j: Nat, +hm: {Nat.is_le(1n+m, List.length(&2, Core.Production, grammar)) == True{} : Bool}, +hi: {Nat.is_le(i, List.length(&2, Nat, input)) == True{} : Bool}, +hf: {Nat.is_le(1n+List.length(&2, Gll.Desc, Run.univ(grammar, input)), fuel) == True{} : Bool})
  -> {RG.decidedTri(P.candTri(b, fuel, grammar, gmarks, input, m, i, j)) == True{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      RS.rival_decided(fuel, grammar, gmarks, input, m, i, j, hm, hi, decided_holds(fuel, grammar, gmarks, input, hf), hf)

def shift_le(+a: Nat, +b: Nat, +c: Nat, +h: {Nat.is_le(1n+Nat.add(a, b), c) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, 1n+b), c) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(a, 1n+b), 1n+Nat.add(a, b), Lemma.add_succ_right(a, b)) : {Nat.is_le(_, c) == True{} : Bool}
  h

law cands_dec:
  for prods: +List<Core.Production>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +input: +List<Nat>
  for +rmarks: +List<P.RankMark>
  for +q: Nat
  for +m: Nat
  for +i: Nat
  for +j: Nat
  for +hg: {Nat.is_le(Nat.add(List.length(&2, Core.Production, prods), m), List.length(&2, Core.Production, grammar)) == True{} : Bool}
  for +hi: {Nat.is_le(i, List.length(&2, Nat, input)) == True{} : Bool}
  for +hf: {Nat.is_le(1n+List.length(&2, Gll.Desc, Run.univ(grammar, input)), fuel) == True{} : Bool}
  {RG.decidedTri(P.candsFrom(prods, fuel, grammar, gmarks, rmarks, input, q, m, i, j)) == True{} : Bool}

def cands_dec(prods, fuel, grammar, gmarks, input, rmarks, q, m, i, j, hg, hi, hf):
  match prods:
    case Nil{}:
      {==}
    case Con{+p, +rest}:
      +hm = Lemma.le_trans(1n+m, 1n+Nat.add(List.length(&2, Core.Production, rest), m), List.length(&2, Core.Production, grammar), Lemma.le_add_left(List.length(&2, Core.Production, rest), m), hg)
      and_dec(P.candTri(P.outranking(grammar, rmarks, q, m), fuel, grammar, gmarks, input, m, i, j), P.candsFrom(rest, fuel, grammar, gmarks, rmarks, input, q, 1n+m, i, j),
        cand_dec(P.outranking(grammar, rmarks, q, m), fuel, grammar, gmarks, input, m, i, j, hm, hi, hf),
        cands_dec(rest, fuel, grammar, gmarks, input, rmarks, q, 1n+m, i, j, shift_le(List.length(&2, Core.Production, rest), m, List.length(&2, Core.Production, grammar), hg), hi, hf))

def len_zero(+grammar: +List<Core.Production>) -> {Nat.is_le(Nat.add(List.length(&2, Core.Production, grammar), 0n), List.length(&2, Core.Production, grammar)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(List.length(&2, Core.Production, grammar), 0n), List.length(&2, Core.Production, grammar), Lemma.add_zero_right(List.length(&2, Core.Production, grammar))) : {Nat.is_le(_, List.length(&2, Core.Production, grammar)) == True{} : Bool}
  Lemma.le_refl(List.length(&2, Core.Production, grammar))

# PHASE 2 DECIDES: with fuel 1 + the size of the input's descriptor universe, phase 2's
# verdict on every step within bounds is Yes or No.
law phase2_decides:
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +input: +List<Nat>
  for +rmarks: +List<P.RankMark>
  for x: Core.Bsr
  for +hb: {Run.stepBound(x, grammar, input) == True{} : Bool}
  for +hf: {Nat.is_le(1n+List.length(&2, Gll.Desc, Run.univ(grammar, input)), fuel) == True{} : Bool}
  {RG.decidedTri(P.rankTri(fuel, grammar, gmarks, rmarks, input, x)) == True{} : Bool}

def phase2_decides(fuel, grammar, gmarks, input, rmarks, x, hb, hf):
  match x:
    case Core.Bsr{+q, +d, +i, +k, +j}:
      +db = Lemma.and_true_left(Run.descBound(Gll.Desc{q, d, i, j}, grammar, input), Nat.is_le(k, List.length(&2, Nat, input)), hb)
      only_dec(Nat.is_eq(d, List.length(&2, Core.Sym, Core.rhsOf(grammar, q))), P.candsFrom(grammar, fuel, grammar, gmarks, rmarks, input, q, 0n, i, j),
        cands_dec(grammar, fuel, grammar, gmarks, input, rmarks, q, 0n, i, j, len_zero(grammar), RG.db_ks(q, d, i, j, grammar, input, db), hf))

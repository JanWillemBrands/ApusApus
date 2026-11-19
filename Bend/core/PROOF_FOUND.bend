import Base
import ../LEMMAS.bend as Lemma
import ./CORE.bend as Core
import ./GLL.bend as Gll
import ./CHECK.bend as Check
import ./PRUNE.bend as Prune
import ./WITNESS.bend as W
import ./RUN.bend as Run
import ./PROOF_GLL.bend as G
import ./PROOF_PRUNE.bend as PP
import ./PROOF_WITNESS.bend as WC
import ./PROOF_NEEDS.bend as N
import ./PROOF_GROUND.bend as GD
import ./PROOF_COUNT.bend as C

# EVERY KEPT STEP HAS A WITNESS (WITNESS.bend). On steps that rest on earlier steps
# (PROOF_GROUND.bend) and needs that are closed and reached from the root in order
# (PROOF_NEEDS.bend), facts closed under the rules of the kept steps have a forest for every
# kept segment that a step completes (by induction in the steps' order), and a flagged one
# all the way up to a root segment (by induction in the needs' order). So the root search
# finds a witness for every kept step.

# ======== SOME OPTION ========

def optAny(+os: +List<W.Opt>) -> Bool:
  Bool.or(WC.optHas(True{}, os), WC.optHas(False{}, os))

def itemAny(+os: +List<W.Opt>) -> Bool:
  Bool.or(WC.itemHas(True{}, os), WC.itemHas(False{}, os))

def any_of(f: Bool, +os: +List<W.Opt>, +h: {WC.optHas(f, os) == True{} : Bool}) -> {optAny(os) == True{} : Bool}:
  match f:
    case True{}:
      Lemma.or_true_left_intro(WC.optHas(True{}, os), WC.optHas(False{}, os), h)
    case False{}:
      Lemma.or_true_right_intro(WC.optHas(True{}, os), WC.optHas(False{}, os), h)

def item_of(f: Bool, +os: +List<W.Opt>, +h: {WC.itemHas(f, os) == True{} : Bool}) -> {itemAny(os) == True{} : Bool}:
  match f:
    case True{}:
      Lemma.or_true_left_intro(WC.itemHas(True{}, os), WC.itemHas(False{}, os), h)
    case False{}:
      Lemma.or_true_right_intro(WC.itemHas(True{}, os), WC.itemHas(False{}, os), h)

def node_any_pick(+q2: Nat, +os: +List<W.Opt>, c: Either<{WC.optHas(True{}, os) == True{} : Bool}, {WC.optHas(False{}, os) == True{} : Bool}>) -> {itemAny(W.nodeOpts(q2, os)) == True{} : Bool}:
  match c:
    case Inl{h}:
      item_of(True{}, W.nodeOpts(q2, os), WC.node_has(q2, os, True{}, h))
    case Inr{h}:
      item_of(False{}, W.nodeOpts(q2, os), WC.node_has(q2, os, False{}, h))

def node_any(+q2: Nat, +os: +List<W.Opt>, +h: {optAny(os) == True{} : Bool}) -> {itemAny(W.nodeOpts(q2, os)) == True{} : Bool}:
  node_any_pick(q2, os, Lemma.or_true_cases(WC.optHas(True{}, os), WC.optHas(False{}, os), h))

def iapp_l(+xs: +List<W.Opt>, +ys2: +List<W.Opt>, c: Either<{WC.itemHas(True{}, xs) == True{} : Bool}, {WC.itemHas(False{}, xs) == True{} : Bool}>) -> {itemAny(List.append(&2, W.Opt, xs, ys2)) == True{} : Bool}:
  match c:
    case Inl{h}:
      item_of(True{}, List.append(&2, W.Opt, xs, ys2), WC.item_app_left(xs, ys2, True{}, h))
    case Inr{h}:
      item_of(False{}, List.append(&2, W.Opt, xs, ys2), WC.item_app_left(xs, ys2, False{}, h))

def iapp_r(+xs: +List<W.Opt>, +ys2: +List<W.Opt>, c: Either<{WC.itemHas(True{}, ys2) == True{} : Bool}, {WC.itemHas(False{}, ys2) == True{} : Bool}>) -> {itemAny(List.append(&2, W.Opt, xs, ys2)) == True{} : Bool}:
  match c:
    case Inl{h}:
      item_of(True{}, List.append(&2, W.Opt, xs, ys2), WC.item_app_right(xs, ys2, True{}, h))
    case Inr{h}:
      item_of(False{}, List.append(&2, W.Opt, xs, ys2), WC.item_app_right(xs, ys2, False{}, h))

def item_cases(+os: +List<W.Opt>, +h: {itemAny(os) == True{} : Bool}) -> Either<{WC.itemHas(True{}, os) == True{} : Bool}, {WC.itemHas(False{}, os) == True{} : Bool}>:
  Lemma.or_true_cases(WC.itemHas(True{}, os), WC.itemHas(False{}, os), h)

def opt_cases(+os: +List<W.Opt>, +h: {optAny(os) == True{} : Bool}) -> Either<{WC.optHas(True{}, os) == True{} : Bool}, {WC.optHas(False{}, os) == True{} : Bool}>:
  Lemma.or_true_cases(WC.optHas(True{}, os), WC.optHas(False{}, os), h)

# The empty prefix where a production starts and ends.
def empty_any(b: Bool, +grammar: +List<Core.Production>, +target: Core.Bsr, +q: Nat, +ks: Nat, +eb: {b == True{} : Bool}) -> {optAny(W.emptyPrefix(b, grammar, target, q, ks)) == True{} : Bool}:
  match b:
    case True{}:
      +sf = Bool.and(List.is_empty(&2, Core.Sym, Core.rhsOf(grammar, q)), Core.bsrEq(Core.Bsr{q, 0n, ks, ks, ks}, target))
      any_of(sf, [W.Opt{sf, []}], Lemma.or_true_left_intro(W.boolEq(sf, sf), False{}, WC.bool_eq_refl(sf)))
    case False{}:
      Empty.absurd({optAny([]) == True{} : Bool}, Lemma.false_is_not_true(eb))

def empty_at(+grammar: +List<Core.Production>, +target: Core.Bsr, +F: +List<W.Fact>, +q: Nat, +ks: Nat, +k: Nat, +e: {Nat.is_eq(ks, k) == True{} : Bool}) -> {optAny(W.optsAt(grammar, target, q, ks, 0n, k, F)) == True{} : Bool}:
  empty_any(Nat.is_eq(ks, k), grammar, target, q, ks, e)

def need_any(b: Bool, +os: +List<W.Opt>, +eb: {b == True{} : Bool}, +h: {itemAny(os) == True{} : Bool}) -> {itemAny(W.needIf(b, os)) == True{} : Bool}:
  match b:
    case True{}:
      h
    case False{}:
      Empty.absurd({itemAny([]) == True{} : Bool}, Lemma.false_is_not_true(eb))

def pick_any(b: Bool, +grammar: +List<Core.Production>, +target: Core.Bsr, +base: Nat, +len: Nat, +k: Nat, +j: Nat, +F: +List<W.Fact>,
  +eb: {b == True{} : Bool}, +h: {itemAny(W.nodeOpts(base, W.optsAt(grammar, target, base, k, len, j, F))) == True{} : Bool}) -> {itemAny(W.prodPick(b, grammar, target, base, len, k, j, F)) == True{} : Bool}:
  match b:
    case True{}:
      h
    case False{}:
      Empty.absurd({itemAny([]) == True{} : Bool}, Lemma.false_is_not_true(eb))

# ======== KEPT SEGMENTS THAT A STEP COMPLETES HAVE A FACT ========

def prod_any_pick(+lhs: Nat, +rest: +List<Core.Production>, +x: Nat, +base: Nat, +len: Nat, +k: Nat, +j: Nat, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +ys: +List<Core.Bsr>, +ns: +List<Prune.Seg>, +F: +List<W.Fact>, +older: +List<Core.Bsr>, +R: Bool, +rest_opts: +List<W.Opt>,
  +hk: {Prune.allSegsIn(Prune.keepSeg(Nat.is_eq(lhs, x), Prune.Seg{base, k, len, j}, Prune.prodSegs(rest, x, 1n+base, k, j)), ns) == True{} : Bool},
  cases: Either<{Bool.and(Nat.is_eq(lhs, x), Run.segDone(base, k, len, j, older)) == True{} : Bool}, {R == True{} : Bool}>,
  rec: @q2: Nat -> @ks2: Nat -> @d2: Nat -> @e2: Nat -> {Run.segDone(q2, ks2, d2, e2, older) == True{} : Bool} -> {Prune.segIn(Prune.Seg{q2, ks2, d2, e2}, ns) == True{} : Bool} -> {optAny(W.optsAt(grammar, target, q2, ks2, d2, e2, F)) == True{} : Bool},
  later: {R == True{} : Bool} -> {Prune.allSegsIn(Prune.prodSegs(rest, x, 1n+base, k, j), ns) == True{} : Bool} -> (@q2: Nat -> @ks2: Nat -> @d2: Nat -> @e2: Nat -> {Run.segDone(q2, ks2, d2, e2, older) == True{} : Bool} -> {Prune.segIn(Prune.Seg{q2, ks2, d2, e2}, ns) == True{} : Bool} -> {optAny(W.optsAt(grammar, target, q2, ks2, d2, e2, F)) == True{} : Bool}) -> {itemAny(rest_opts) == True{} : Bool})
  -> {itemAny(List.append(&2, W.Opt, W.prodPick(Nat.is_eq(lhs, x), grammar, target, base, len, k, j, F), rest_opts)) == True{} : Bool}:
  match cases:
    case Inl{+a}:
      +el = Lemma.and_true_left(Nat.is_eq(lhs, x), Run.segDone(base, k, len, j, older), a)
      +sk = PP.keep_seg_here(Nat.is_eq(lhs, x), Prune.Seg{base, k, len, j}, Prune.prodSegs(rest, x, 1n+base, k, j), ns, el, hk)
      iapp_l(W.prodPick(Nat.is_eq(lhs, x), grammar, target, base, len, k, j, F), rest_opts,
        item_cases(W.prodPick(Nat.is_eq(lhs, x), grammar, target, base, len, k, j, F), pick_any(Nat.is_eq(lhs, x), grammar, target, base, len, k, j, F, el,
          node_any(base, W.optsAt(grammar, target, base, k, len, j, F), rec(base, k, len, j, Lemma.and_true_right_side(Nat.is_eq(lhs, x), Run.segDone(base, k, len, j, older), a), sk)))))
    case Inr{h}:
      iapp_r(W.prodPick(Nat.is_eq(lhs, x), grammar, target, base, len, k, j, F), rest_opts,
        item_cases(rest_opts, later(h, PP.keep_seg_rest(Nat.is_eq(lhs, x), Prune.Seg{base, k, len, j}, Prune.prodSegs(rest, x, 1n+base, k, j), ns, hk), rec)))

# A nonterminal done from k to j, all of whose productions there are kept, is an item.
law prod_any:
  for g: +List<Core.Production>
  for +base: Nat
  for +x: Nat
  for +k: Nat
  for +j: Nat
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +target: Core.Bsr
  for +ys: +List<Core.Bsr>
  for +ns: +List<Prune.Seg>
  for +F: +List<W.Fact>
  for +older: +List<Core.Bsr>
  for +hp: {Run.prodDone(g, base, x, k, j, older) == True{} : Bool}
  for +hk: {Prune.allSegsIn(Prune.prodSegs(g, x, base, k, j), ns) == True{} : Bool}
  for rec: @q2: Nat -> @ks2: Nat -> @d2: Nat -> @e2: Nat -> {Run.segDone(q2, ks2, d2, e2, older) == True{} : Bool} -> {Prune.segIn(Prune.Seg{q2, ks2, d2, e2}, ns) == True{} : Bool} -> {optAny(W.optsAt(grammar, target, q2, ks2, d2, e2, F)) == True{} : Bool}
  {itemAny(W.prodOpts(g, grammar, target, base, x, k, j, F)) == True{} : Bool}

def prod_any(g, base, x, k, j, grammar, input, target, ys, ns, F, older, hp, hk, rec):
  match g:
    case Nil{}:
      Empty.absurd({itemAny([]) == True{} : Bool}, Lemma.false_is_not_true(hp))
    case Con{Core.Production{+lhs, +rhs}, +rest}:
      +len = List.length(&2, Core.Sym, rhs)
      +R = Run.prodDone(rest, 1n+base, x, k, j, older)
      prod_any_pick(lhs, rest, x, base, len, k, j, grammar, input, target, ys, ns, F, older, R, W.prodOpts(rest, grammar, target, 1n+base, x, k, j, F), hk,
        Lemma.or_true_cases(Bool.and(Nat.is_eq(lhs, x), Run.segDone(base, k, len, j, older)), R, hp),
        rec,
        h => hk2 => r2 => prod_any(rest, 1n+base, x, k, j, grammar, input, target, ys, ns, F, older, h, hk2, r2))

def item_any(item: Maybe<&2, Core.Sym>, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +ys: +List<Core.Bsr>, +ns: +List<Prune.Seg>, +F: +List<W.Fact>, +older: +List<Core.Bsr>, +k: Nat, +j: Nat,
  +hi: {Run.itemDone(item, grammar, input, k, j, older) == True{} : Bool},
  +hk: {Prune.allSegsIn(Prune.itemNeeds(item, grammar, k, j), ns) == True{} : Bool},
  rec: @q2: Nat -> @ks2: Nat -> @d2: Nat -> @e2: Nat -> {Run.segDone(q2, ks2, d2, e2, older) == True{} : Bool} -> {Prune.segIn(Prune.Seg{q2, ks2, d2, e2}, ns) == True{} : Bool} -> {optAny(W.optsAt(grammar, target, q2, ks2, d2, e2, F)) == True{} : Bool}) -> {itemAny(W.itemOpts(item, grammar, input, target, k, j, F)) == True{} : Bool}:
  match item:
    case Some{Core.Terminal{+t}}:
      item_of(False{}, W.leafIf(Bool.and(Core.tokIs(Core.tokAt(input, k), t), Nat.is_eq(j, 1n+k)), t), WC.leaf_pick(Bool.and(Core.tokIs(Core.tokAt(input, k), t), Nat.is_eq(j, 1n+k)), t, hi))
    case Some{Core.Nonterminal{+x, +need}}:
      +P = {Run.prodDone(grammar, 0n, x, k, j, older) : Bool}
      need_any(Gll.needHolds(need, k, j), W.prodOpts(grammar, grammar, target, 0n, x, k, j, F), Lemma.and_true_left(Gll.needHolds(need, k, j), P, hi),
        prod_any(grammar, 0n, x, k, j, grammar, input, target, ys, ns, F, older, Lemma.and_true_right_side(Gll.needHolds(need, k, j), P, hi), hk, rec))
    case None{}:
      Empty.absurd({itemAny([]) == True{} : Bool}, Lemma.false_is_not_true(hi))

def prefix_any(d0: Nat, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +ys: +List<Core.Bsr>, +ns: +List<Prune.Seg>, +F: +List<W.Fact>, +older: +List<Core.Bsr>, +q: Nat, +ks: Nat, +k: Nat,
  +hp: {Run.prefixDone(q, ks, d0, k, older) == True{} : Bool}, +hk: {Prune.segIn(Prune.Seg{q, ks, d0, k}, ns) == True{} : Bool}, rec: @q2: Nat -> @ks2: Nat -> @d2: Nat -> @e2: Nat -> {Run.segDone(q2, ks2, d2, e2, older) == True{} : Bool} -> {Prune.segIn(Prune.Seg{q2, ks2, d2, e2}, ns) == True{} : Bool} -> {optAny(W.optsAt(grammar, target, q2, ks2, d2, e2, F)) == True{} : Bool}) -> {optAny(W.optsAt(grammar, target, q, ks, d0, k, F)) == True{} : Bool}:
  match d0:
    case 0n:
      empty_at(grammar, target, F, q, ks, k, hp)
    case 1n+(+m):
      rec(q, ks, 1n+m, k, hp, hk)

def combine2(+f1: Bool, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +ys: +List<Core.Bsr>, +ns: +List<Prune.Seg>, +F: +List<W.Fact>, +ok: {Prune.allStepsOk(ys, grammar, ns) == True{} : Bool}, +cl: {WC.closedW(Prune.keep(ys, ns), grammar, input, target, F) == True{} : Bool}, +q: Nat, +i: Nat, +d0: Nat, +k: Nat, +j: Nat,
  +m: {Core.member(Core.Bsr{q, 1n+d0, i, k, j}, Prune.keep(ys, ns)) == True{} : Bool}, +hp: {WC.optHas(f1, W.optsAt(grammar, target, q, i, d0, k, F)) == True{} : Bool},
  ci: Either<{WC.itemHas(True{}, W.itemOpts(Gll.nthSym(Core.rhsOf(grammar, q), d0), grammar, input, target, k, j, F)) == True{} : Bool}, {WC.itemHas(False{}, W.itemOpts(Gll.nthSym(Core.rhsOf(grammar, q), d0), grammar, input, target, k, j, F)) == True{} : Bool}>)
  -> {optAny(W.optsAt(grammar, target, q, i, 1n+d0, j, F)) == True{} : Bool}:
  match ci:
    case Inl{hi}:
      any_of(Bool.or(Bool.or(f1, True{}), Core.bsrEq(Core.Bsr{q, 1n+d0, i, k, j}, target)), W.optsAt(grammar, target, q, i, 1n+d0, j, F), WC.step_fact(grammar, input, Prune.keep(ys, ns), target, F, cl, q, i, d0, k, j, f1, True{}, hp, hi, m))
    case Inr{hi}:
      any_of(Bool.or(Bool.or(f1, False{}), Core.bsrEq(Core.Bsr{q, 1n+d0, i, k, j}, target)), W.optsAt(grammar, target, q, i, 1n+d0, j, F), WC.step_fact(grammar, input, Prune.keep(ys, ns), target, F, cl, q, i, d0, k, j, f1, False{}, hp, hi, m))

def combine(+grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +ys: +List<Core.Bsr>, +ns: +List<Prune.Seg>, +F: +List<W.Fact>, +ok: {Prune.allStepsOk(ys, grammar, ns) == True{} : Bool}, +cl: {WC.closedW(Prune.keep(ys, ns), grammar, input, target, F) == True{} : Bool}, +q: Nat, +i: Nat, +d0: Nat, +k: Nat, +j: Nat,
  +m: {Core.member(Core.Bsr{q, 1n+d0, i, k, j}, Prune.keep(ys, ns)) == True{} : Bool},
  cp: Either<{WC.optHas(True{}, W.optsAt(grammar, target, q, i, d0, k, F)) == True{} : Bool}, {WC.optHas(False{}, W.optsAt(grammar, target, q, i, d0, k, F)) == True{} : Bool}>,
  ci: Either<{WC.itemHas(True{}, W.itemOpts(Gll.nthSym(Core.rhsOf(grammar, q), d0), grammar, input, target, k, j, F)) == True{} : Bool}, {WC.itemHas(False{}, W.itemOpts(Gll.nthSym(Core.rhsOf(grammar, q), d0), grammar, input, target, k, j, F)) == True{} : Bool}>)
  -> {optAny(W.optsAt(grammar, target, q, i, 1n+d0, j, F)) == True{} : Bool}:
  match cp:
    case Inl{hp}:
      combine2(True{}, grammar, input, target, ys, ns, F, ok, cl, q, i, d0, k, j, m, hp, ci)
    case Inr{hp}:
      combine2(False{}, grammar, input, target, ys, ns, F, ok, cl, q, i, d0, k, j, m, hp, ci)

def eq_trans_is(+a: Nat, +b: Nat, +c: Nat, +h1: {Nat.is_eq(a, b) == True{} : Bool}, +h2: {Nat.is_eq(b, c) == True{} : Bool}) -> {Nat.is_eq(a, c) == True{} : Bool}:
  +e = Equal.trans(Nat, a, b, c, Lemma.nat_eq_sound(a, b, h1), Lemma.nat_eq_sound(b, c, h2))
  %e : {Nat.is_eq(a, _) == True{} : Bool}
  Lemma.nat_eq_refl(a)

# A kept step resting on older steps: its segment has a fact.
def by_step(d: Nat, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +ys: +List<Core.Bsr>, +ns: +List<Prune.Seg>, +F: +List<W.Fact>, +ok: {Prune.allStepsOk(ys, grammar, ns) == True{} : Bool}, +cl: {WC.closedW(Prune.keep(ys, ns), grammar, input, target, F) == True{} : Bool}, +older: +List<Core.Bsr>, +q: Nat, +i: Nat, +k: Nat, +j: Nat,
  +hgr: {Run.groundedIn(Core.Bsr{q, d, i, k, j}, grammar, input, older) == True{} : Bool},
  +hk: {Prune.segIn(Prune.Seg{q, i, d, j}, ns) == True{} : Bool}, +my: {Core.member(Core.Bsr{q, d, i, k, j}, ys) == True{} : Bool},
  recP: @q2: Nat -> @ks2: Nat -> @d2: Nat -> @e2: Nat -> {Run.segDone(q2, ks2, d2, e2, older) == True{} : Bool} -> {Prune.segIn(Prune.Seg{q2, ks2, d2, e2}, ns) == True{} : Bool} -> {optAny(W.optsAt(grammar, target, q2, ks2, d2, e2, F)) == True{} : Bool}, recI: @q2: Nat -> @ks2: Nat -> @d2: Nat -> @e2: Nat -> {Run.segDone(q2, ks2, d2, e2, older) == True{} : Bool} -> {Prune.segIn(Prune.Seg{q2, ks2, d2, e2}, ns) == True{} : Bool} -> {optAny(W.optsAt(grammar, target, q2, ks2, d2, e2, F)) == True{} : Bool}) -> {optAny(W.optsAt(grammar, target, q, i, d, j, F)) == True{} : Bool}:
  match d:
    case 0n:
      +E = {List.is_empty(&2, Core.Sym, Core.rhsOf(grammar, q)) : Bool}
      +r = Lemma.and_true_right_side(E, Bool.and(Nat.is_eq(i, k), Nat.is_eq(k, j)), hgr)
      empty_at(grammar, target, F, q, i, j, eq_trans_is(i, k, j, Lemma.and_true_left(Nat.is_eq(i, k), Nat.is_eq(k, j), r), Lemma.and_true_right_side(Nat.is_eq(i, k), Nat.is_eq(k, j), r)))
    case 1n+(+d0):
      +PD = {Run.prefixDone(q, i, d0, k, older) : Bool}
      +ID = {Run.itemDone(Gll.nthSym(Core.rhsOf(grammar, q), d0), grammar, input, k, j, older) : Bool}
      +needs = PP.kept_needs(ys, grammar, ns, Core.Bsr{q, 1n+d0, i, k, j}, ok, my, hk)
      +IN = Prune.itemNeeds(Gll.nthSym(Core.rhsOf(grammar, q), d0), grammar, k, j)
      +pk = Lemma.and_true_left(Prune.segIn(Prune.Seg{q, i, d0, k}, ns), Prune.allSegsIn(IN, ns), needs)
      +ik = Lemma.and_true_right_side(Prune.segIn(Prune.Seg{q, i, d0, k}, ns), Prune.allSegsIn(IN, ns), needs)
      combine(grammar, input, target, ys, ns, F, ok, cl, q, i, d0, k, j, PP.kept_member(ys, ns, Core.Bsr{q, 1n+d0, i, k, j}, my, hk),
        opt_cases(W.optsAt(grammar, target, q, i, d0, k, F), prefix_any(d0, grammar, input, target, ys, ns, F, older, q, i, k, Lemma.and_true_left(PD, ID, hgr), pk, recP)),
        item_cases(W.itemOpts(Gll.nthSym(Core.rhsOf(grammar, q), d0), grammar, input, target, k, j, F), item_any(Gll.nthSym(Core.rhsOf(grammar, q), d0), grammar, input, target, ys, ns, F, older, k, j, Lemma.and_true_right_side(PD, ID, hgr), ik, recI)))

def opt_to(+grammar: +List<Core.Production>, +target: Core.Bsr, +F: +List<W.Fact>, +q: Nat, +ks: Nat, +d: Nat, +e: Nat, +q1: Nat, +i1: Nat, +d1: Nat, +j1: Nat,
  +e1: {q1 == q : Nat}, +e2: {i1 == ks : Nat}, +e3: {d1 == d : Nat}, +e4: {j1 == e : Nat},
  +h: {optAny(W.optsAt(grammar, target, q1, i1, d1, j1, F)) == True{} : Bool}) -> {optAny(W.optsAt(grammar, target, q, ks, d, e, F)) == True{} : Bool}:
  %e1 : {optAny(W.optsAt(grammar, target, _, ks, d, e, F)) == True{} : Bool}
  %e2 : {optAny(W.optsAt(grammar, target, q1, _, d, e, F)) == True{} : Bool}
  %e3 : {optAny(W.optsAt(grammar, target, q1, i1, _, e, F)) == True{} : Bool}
  %e4 : {optAny(W.optsAt(grammar, target, q1, i1, d1, _, F)) == True{} : Bool}
  h

def seg_to(+ns: +List<Prune.Seg>, +q: Nat, +ks: Nat, +d: Nat, +e: Nat, +q1: Nat, +i1: Nat, +d1: Nat, +j1: Nat,
  +e1: {q1 == q : Nat}, +e2: {i1 == ks : Nat}, +e3: {d1 == d : Nat}, +e4: {j1 == e : Nat},
  +h: {Prune.segIn(Prune.Seg{q, ks, d, e}, ns) == True{} : Bool}) -> {Prune.segIn(Prune.Seg{q1, i1, d1, j1}, ns) == True{} : Bool}:
  %Equal.sym(Nat, q1, q, e1) : {Prune.segIn(Prune.Seg{_, i1, d1, j1}, ns) == True{} : Bool}
  %Equal.sym(Nat, i1, ks, e2) : {Prune.segIn(Prune.Seg{q, _, d1, j1}, ns) == True{} : Bool}
  %Equal.sym(Nat, d1, d, e3) : {Prune.segIn(Prune.Seg{q, ks, _, j1}, ns) == True{} : Bool}
  %Equal.sym(Nat, j1, e, e4) : {Prune.segIn(Prune.Seg{q, ks, d, _}, ns) == True{} : Bool}
  h

def bottom_here(y: Core.Bsr, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +ys: +List<Core.Bsr>, +ns: +List<Prune.Seg>, +F: +List<W.Fact>, +ok: {Prune.allStepsOk(ys, grammar, ns) == True{} : Bool}, +cl: {WC.closedW(Prune.keep(ys, ns), grammar, input, target, F) == True{} : Bool}, +older: +List<Core.Bsr>, +q: Nat, +ks: Nat, +d: Nat, +e: Nat,
  +db: {Run.doneBy(q, ks, d, e, y) == True{} : Bool}, +hk: {Prune.segIn(Prune.Seg{q, ks, d, e}, ns) == True{} : Bool},
  +hgy: {Run.groundedIn(y, grammar, input, older) == True{} : Bool}, +my: {Core.member(y, ys) == True{} : Bool},
  recP: @q2: Nat -> @ks2: Nat -> @d2: Nat -> @e2: Nat -> {Run.segDone(q2, ks2, d2, e2, older) == True{} : Bool} -> {Prune.segIn(Prune.Seg{q2, ks2, d2, e2}, ns) == True{} : Bool} -> {optAny(W.optsAt(grammar, target, q2, ks2, d2, e2, F)) == True{} : Bool}, recI: @q2: Nat -> @ks2: Nat -> @d2: Nat -> @e2: Nat -> {Run.segDone(q2, ks2, d2, e2, older) == True{} : Bool} -> {Prune.segIn(Prune.Seg{q2, ks2, d2, e2}, ns) == True{} : Bool} -> {optAny(W.optsAt(grammar, target, q2, ks2, d2, e2, F)) == True{} : Bool}) -> {optAny(W.optsAt(grammar, target, q, ks, d, e, F)) == True{} : Bool}:
  match y:
    case Core.Bsr{+q1, +d1, +i1, +k1, +j1}:
      +A = {Nat.is_eq(q1, q) : Bool}
      +Bb = {Nat.is_eq(i1, ks) : Bool}
      +Cc = {Nat.is_eq(d1, d) : Bool}
      +Dd = {Nat.is_eq(j1, e) : Bool}
      +r1 = Lemma.and_true_right_side(A, Bool.and(Bb, Bool.and(Cc, Dd)), db)
      +r2 = Lemma.and_true_right_side(Bb, Bool.and(Cc, Dd), r1)
      +e1 = Lemma.nat_eq_sound(q1, q, Lemma.and_true_left(A, Bool.and(Bb, Bool.and(Cc, Dd)), db))
      +e2 = Lemma.nat_eq_sound(i1, ks, Lemma.and_true_left(Bb, Bool.and(Cc, Dd), r1))
      +e3 = Lemma.nat_eq_sound(d1, d, Lemma.and_true_left(Cc, Dd, r2))
      +e4 = Lemma.nat_eq_sound(j1, e, Lemma.and_true_right_side(Cc, Dd, r2))
      opt_to(grammar, target, F, q, ks, d, e, q1, i1, d1, j1, e1, e2, e3, e4,
        by_step(d1, grammar, input, target, ys, ns, F, ok, cl, older, q1, i1, k1, j1, hgy, seg_to(ns, q, ks, d, e, q1, i1, d1, j1, e1, e2, e3, e4, hk), my, recP, recI))

def bottom_pick(+y: Core.Bsr, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +ys: +List<Core.Bsr>, +ns: +List<Prune.Seg>, +F: +List<W.Fact>, +ok: {Prune.allStepsOk(ys, grammar, ns) == True{} : Bool}, +cl: {WC.closedW(Prune.keep(ys, ns), grammar, input, target, F) == True{} : Bool}, +older: +List<Core.Bsr>, +q: Nat, +ks: Nat, +d: Nat, +e: Nat, +hk: {Prune.segIn(Prune.Seg{q, ks, d, e}, ns) == True{} : Bool},
  +hgy: {Run.groundedIn(y, grammar, input, older) == True{} : Bool}, +my: {Core.member(y, ys) == True{} : Bool},
  cases: Either<{Run.doneBy(q, ks, d, e, y) == True{} : Bool}, {Run.segDone(q, ks, d, e, older) == True{} : Bool}>,
  later: {Run.segDone(q, ks, d, e, older) == True{} : Bool} -> {optAny(W.optsAt(grammar, target, q, ks, d, e, F)) == True{} : Bool}, recP: @q2: Nat -> @ks2: Nat -> @d2: Nat -> @e2: Nat -> {Run.segDone(q2, ks2, d2, e2, older) == True{} : Bool} -> {Prune.segIn(Prune.Seg{q2, ks2, d2, e2}, ns) == True{} : Bool} -> {optAny(W.optsAt(grammar, target, q2, ks2, d2, e2, F)) == True{} : Bool}, recI: @q2: Nat -> @ks2: Nat -> @d2: Nat -> @e2: Nat -> {Run.segDone(q2, ks2, d2, e2, older) == True{} : Bool} -> {Prune.segIn(Prune.Seg{q2, ks2, d2, e2}, ns) == True{} : Bool} -> {optAny(W.optsAt(grammar, target, q2, ks2, d2, e2, F)) == True{} : Bool}) -> {optAny(W.optsAt(grammar, target, q, ks, d, e, F)) == True{} : Bool}:
  match cases:
    case Inl{db}:
      bottom_here(y, grammar, input, target, ys, ns, F, ok, cl, older, q, ks, d, e, db, hk, hgy, my, recP, recI)
    case Inr{h}:
      later(h)

# BY INDUCTION IN THE STEPS' ORDER: every kept segment that some step completes has a fact.
law bottom:
  for ys2: +List<Core.Bsr>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +target: Core.Bsr
  for +ys: +List<Core.Bsr>
  for +ns: +List<Prune.Seg>
  for +F: +List<W.Fact>
  for +ok: {Prune.allStepsOk(ys, grammar, ns) == True{} : Bool}
  for +cl: {WC.closedW(Prune.keep(ys, ns), grammar, input, target, F) == True{} : Bool}
  for +q: Nat
  for +ks: Nat
  for +d: Nat
  for +e: Nat
  for +hs: {Run.segDone(q, ks, d, e, ys2) == True{} : Bool}
  for +hk: {Prune.segIn(Prune.Seg{q, ks, d, e}, ns) == True{} : Bool}
  for +hg: {Run.stepsGrounded(ys2, grammar, input) == True{} : Bool}
  for +sub: {Core.allIn(ys2, ys) == True{} : Bool}
  {optAny(W.optsAt(grammar, target, q, ks, d, e, F)) == True{} : Bool}

def bottom(ys2, grammar, input, target, ys, ns, F, ok, cl, q, ks, d, e, hs, hk, hg, sub):
  match ys2:
    case Nil{}:
      Empty.absurd({optAny(W.optsAt(grammar, target, q, ks, d, e, F)) == True{} : Bool}, Lemma.false_is_not_true(hs))
    case Con{+y, +older}:
      +hgy = Lemma.and_true_left(Run.groundedIn(y, grammar, input, older), Run.stepsGrounded(older, grammar, input), hg)
      +hgo = Lemma.and_true_right_side(Run.groundedIn(y, grammar, input, older), Run.stepsGrounded(older, grammar, input), hg)
      +my = Lemma.and_true_left(Core.member(y, ys), Core.allIn(older, ys), sub)
      +so = Lemma.and_true_right_side(Core.member(y, ys), Core.allIn(older, ys), sub)
      bottom_pick(y, grammar, input, target, ys, ns, F, ok, cl, older, q, ks, d, e, hk, hgy, my,
        Lemma.or_true_cases(Run.doneBy(q, ks, d, e, y), Run.segDone(q, ks, d, e, older), hs),
        h => bottom(older, grammar, input, target, ys, ns, F, ok, cl, q, ks, d, e, h, hk, hgo, so),
        q2 => ks2 => d2 => e2 => h1 => h2 => bottom(older, grammar, input, target, ys, ns, F, ok, cl, q2, ks2, d2, e2, h1, h2, hgo, so),
        q2 => ks2 => d2 => e2 => h1 => h2 => bottom(older, grammar, input, target, ys, ns, F, ok, cl, q2, ks2, d2, e2, h1, h2, hgo, so))

# ======== A FLAGGED FACT GOES UP TO A ROOT ========

def optsSeg(+grammar: +List<Core.Production>, +target: Core.Bsr, +F: +List<W.Fact>, z: Prune.Seg) -> +List<W.Opt>:
  match z:
    case Prune.Seg{+q, +ks, +d, +e}:
      W.optsAt(grammar, target, q, ks, d, e, F)

def flagAt(+grammar: +List<Core.Production>, +target: Core.Bsr, +F: +List<W.Fact>, +z: Prune.Seg) -> Bool:
  WC.optHas(True{}, optsSeg(grammar, target, F, z))

def flag_seg(+grammar: +List<Core.Production>, +target: Core.Bsr, +F: +List<W.Fact>, +a: Prune.Seg, +b: Prune.Seg, +e: {a == b : Prune.Seg}, +h: {flagAt(grammar, target, F, a) == True{} : Bool}) -> {flagAt(grammar, target, F, b) == True{} : Bool}:
  %e : {flagAt(grammar, target, F, _) == True{} : Bool}
  h

def item_mono(item: Maybe<&2, Core.Sym>, +grammar: +List<Core.Production>, +input: +List<Nat>, +k: Nat, +j: Nat, +ys1: +List<Core.Bsr>, +ys2: +List<Core.Bsr>,
  +sub: {Core.allIn(ys1, ys2) == True{} : Bool}, +h: {Run.itemDone(item, grammar, input, k, j, ys1) == True{} : Bool})
  -> {Run.itemDone(item, grammar, input, k, j, ys2) == True{} : Bool}:
  match item:
    case Some{Core.Terminal{+t}}:
      h
    case Some{Core.Nonterminal{+x, +need}}:
      +P = {Run.prodDone(grammar, 0n, x, k, j, ys1) : Bool}
      Lemma.and_true_intro(Gll.needHolds(need, k, j), Run.prodDone(grammar, 0n, x, k, j, ys2), Lemma.and_true_left(Gll.needHolds(need, k, j), P, h),
        GD.prod_mono(grammar, 0n, x, k, j, ys1, ys2, sub, Lemma.and_true_right_side(Gll.needHolds(need, k, j), P, h)))
    case None{}:
      h

def ground_mono(e: Core.Bsr, +grammar: +List<Core.Production>, +input: +List<Nat>, +ys1: +List<Core.Bsr>, +ys2: +List<Core.Bsr>,
  +sub: {Core.allIn(ys1, ys2) == True{} : Bool}, +h: {Run.groundedIn(e, grammar, input, ys1) == True{} : Bool})
  -> {Run.groundedIn(e, grammar, input, ys2) == True{} : Bool}:
  match e:
    case Core.Bsr{+q, 0n, +i, +k, +j}:
      h
    case Core.Bsr{+q, 1n+(+d), +i, +k, +j}:
      +PD = {Run.prefixDone(q, i, d, k, ys1) : Bool}
      +ID = {Run.itemDone(Gll.nthSym(Core.rhsOf(grammar, q), d), grammar, input, k, j, ys1) : Bool}
      Lemma.and_true_intro(Run.prefixDone(q, i, d, k, ys2), Run.itemDone(Gll.nthSym(Core.rhsOf(grammar, q), d), grammar, input, k, j, ys2),
        GD.prefix_mono(q, i, d, k, ys1, ys2, sub, Lemma.and_true_left(PD, ID, h)),
        item_mono(Gll.nthSym(Core.rhsOf(grammar, q), d), grammar, input, k, j, ys1, ys2, sub, Lemma.and_true_right_side(PD, ID, h)))

def grounded_pick2(+x: Core.Bsr, +y: Core.Bsr, +older: +List<Core.Bsr>, +grammar: +List<Core.Production>, +input: +List<Nat>,
  +hgy: {Run.groundedIn(y, grammar, input, older) == True{} : Bool}, +w: {Core.allIn(older, y <> older) == True{} : Bool},
  cases: Either<{Core.bsrEq(x, y) == True{} : Bool}, {Core.member(x, older) == True{} : Bool}>,
  later: {Core.member(x, older) == True{} : Bool} -> {Run.groundedIn(x, grammar, input, older) == True{} : Bool})
  -> {Run.groundedIn(x, grammar, input, y <> older) == True{} : Bool}:
  match cases:
    case Inl{b}:
      %Equal.sym(Core.Bsr, x, y, G.bsr_eq_sound(x, y, b)) : {Run.groundedIn(_, grammar, input, y <> older) == True{} : Bool}
      ground_mono(y, grammar, input, older, y <> older, w, hgy)
    case Inr{m}:
      ground_mono(x, grammar, input, older, y <> older, w, later(m))

def grounded_pick(+x: Core.Bsr, +y: Core.Bsr, +older: +List<Core.Bsr>, +grammar: +List<Core.Production>, +input: +List<Nat>,
  +hgy: {Run.groundedIn(y, grammar, input, older) == True{} : Bool},
  cases: Either<{Core.bsrEq(x, y) == True{} : Bool}, {Core.member(x, older) == True{} : Bool}>,
  later: {Core.member(x, older) == True{} : Bool} -> {Run.groundedIn(x, grammar, input, older) == True{} : Bool})
  -> {Run.groundedIn(x, grammar, input, y <> older) == True{} : Bool}:
  +w = C.step_weaken(older, y, older, C.step_refl(older))
  grounded_pick2(x, y, older, grammar, input, hgy, w, cases, later)

# A step of grounded steps rests on the whole list.
law grounded_at:
  for ys2: +List<Core.Bsr>
  for +x: Core.Bsr
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +m: {Core.member(x, ys2) == True{} : Bool}
  for +hg: {Run.stepsGrounded(ys2, grammar, input) == True{} : Bool}
  {Run.groundedIn(x, grammar, input, ys2) == True{} : Bool}

def grounded_at(ys2, x, grammar, input, m, hg):
  match ys2:
    case Nil{}:
      Empty.absurd({Run.groundedIn(x, grammar, input, []) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{+y, +older}:
      +G0 = {Run.groundedIn(y, grammar, input, older) : Bool}
      grounded_pick(x, y, older, grammar, input, Lemma.and_true_left(G0, Run.stepsGrounded(older, grammar, input), hg),
        Lemma.or_true_cases(Core.bsrEq(x, y), Core.member(x, older), m),
        m2 => grounded_at(older, x, grammar, input, m2, Lemma.and_true_right_side(G0, Run.stepsGrounded(older, grammar, input), hg)))

law seg_split:
  for xs: +List<Prune.Seg>
  for +zs: +List<Prune.Seg>
  for +z: Prune.Seg
  for +h: {Prune.segIn(z, List.append(&2, Prune.Seg, xs, zs)) == True{} : Bool}
  Either<{Prune.segIn(z, xs) == True{} : Bool}, {Prune.segIn(z, zs) == True{} : Bool}>

def split_more(+z: Prune.Seg, +y: Prune.Seg, +rest: +List<Prune.Seg>, +zs: +List<Prune.Seg>, c: Either<{Prune.segIn(z, rest) == True{} : Bool}, {Prune.segIn(z, zs) == True{} : Bool}>) -> Either<{Prune.segIn(z, y <> rest) == True{} : Bool}, {Prune.segIn(z, zs) == True{} : Bool}>:
  match c:
    case Inl{m}:
      Inl{Lemma.or_true_right_intro(Prune.segEq(z, y), Prune.segIn(z, rest), m)}
    case Inr{m}:
      Inr{m}

def split_pick(+z: Prune.Seg, +y: Prune.Seg, +rest: +List<Prune.Seg>, +zs: +List<Prune.Seg>,
  cases: Either<{Prune.segEq(z, y) == True{} : Bool}, {Prune.segIn(z, List.append(&2, Prune.Seg, rest, zs)) == True{} : Bool}>,
  later: {Prune.segIn(z, List.append(&2, Prune.Seg, rest, zs)) == True{} : Bool} -> Either<{Prune.segIn(z, rest) == True{} : Bool}, {Prune.segIn(z, zs) == True{} : Bool}>) -> Either<{Prune.segIn(z, y <> rest) == True{} : Bool}, {Prune.segIn(z, zs) == True{} : Bool}>:
  match cases:
    case Inl{e}:
      Inl{Lemma.or_true_left_intro(Prune.segEq(z, y), Prune.segIn(z, rest), e)}
    case Inr{m}:
      split_more(z, y, rest, zs, later(m))

def seg_split(xs, zs, z, h):
  match xs:
    case Nil{}:
      Inr{h}
    case Con{+y, +rest}:
      split_pick(z, y, rest, zs, Lemma.or_true_cases(Prune.segEq(z, y), Prune.segIn(z, List.append(&2, Prune.Seg, rest, zs)), h), m => seg_split(rest, zs, z, m))

def prod_flag_eq(+rest: +List<Core.Production>, +x: Nat, +z: Prune.Seg, +grammar: +List<Core.Production>, +target: Core.Bsr, +F: +List<W.Fact>, +base: Nat, +len: Nat, +k: Nat, +j: Nat, +restsegs: +List<Prune.Seg>,
  +fz: {flagAt(grammar, target, F, z) == True{} : Bool}, cases: Either<{Prune.segEq(z, Prune.Seg{base, k, len, j}) == True{} : Bool}, {Prune.segIn(z, restsegs) == True{} : Bool}>,
  later: {Prune.segIn(z, restsegs) == True{} : Bool} -> {WC.itemHas(True{}, W.prodOpts(rest, grammar, target, 1n+base, x, k, j, F)) == True{} : Bool})
  -> {WC.itemHas(True{}, List.append(&2, W.Opt, W.nodeOpts(base, W.optsAt(grammar, target, base, k, len, j, F)), W.prodOpts(rest, grammar, target, 1n+base, x, k, j, F))) == True{} : Bool}:
  match cases:
    case Inl{e}:
      +h = flag_seg(grammar, target, F, z, Prune.Seg{base, k, len, j}, N.seg_eq_sound(z, Prune.Seg{base, k, len, j}, e), fz)
      WC.item_app_left(W.nodeOpts(base, W.optsAt(grammar, target, base, k, len, j, F)), W.prodOpts(rest, grammar, target, 1n+base, x, k, j, F), True{}, WC.node_has(base, W.optsAt(grammar, target, base, k, len, j, F), True{}, h))
    case Inr{m}:
      WC.item_app_right(W.nodeOpts(base, W.optsAt(grammar, target, base, k, len, j, F)), W.prodOpts(rest, grammar, target, 1n+base, x, k, j, F), True{}, later(m))

def prod_flag_here(b: Bool, +rest: +List<Core.Production>, +x: Nat, +z: Prune.Seg, +grammar: +List<Core.Production>, +target: Core.Bsr, +F: +List<W.Fact>, +base: Nat, +len: Nat, +k: Nat, +j: Nat, +restsegs: +List<Prune.Seg>,
  +fz: {flagAt(grammar, target, F, z) == True{} : Bool}, +mz: {Prune.segIn(z, Prune.keepSeg(b, Prune.Seg{base, k, len, j}, restsegs)) == True{} : Bool},
  later: {Prune.segIn(z, restsegs) == True{} : Bool} -> {WC.itemHas(True{}, W.prodOpts(rest, grammar, target, 1n+base, x, k, j, F)) == True{} : Bool})
  -> {WC.itemHas(True{}, List.append(&2, W.Opt, W.prodPick(b, grammar, target, base, len, k, j, F), W.prodOpts(rest, grammar, target, 1n+base, x, k, j, F))) == True{} : Bool}:
  match b:
    case True{}:
      prod_flag_eq(rest, x, z, grammar, target, F, base, len, k, j, restsegs, fz, Lemma.or_true_cases(Prune.segEq(z, Prune.Seg{base, k, len, j}), Prune.segIn(z, restsegs), mz), later)
    case False{}:
      later(mz)


# A flagged whole production of x, where x is needed: a flagged item.
law prod_flag:
  for g: +List<Core.Production>
  for +base: Nat
  for +x: Nat
  for +k: Nat
  for +j: Nat
  for +grammar: +List<Core.Production>
  for +target: Core.Bsr
  for +F: +List<W.Fact>
  for +z: Prune.Seg
  for +mz: {Prune.segIn(z, Prune.prodSegs(g, x, base, k, j)) == True{} : Bool}
  for +fz: {flagAt(grammar, target, F, z) == True{} : Bool}
  {WC.itemHas(True{}, W.prodOpts(g, grammar, target, base, x, k, j, F)) == True{} : Bool}

def prod_flag(g, base, x, k, j, grammar, target, F, z, mz, fz):
  match g:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(mz))
    case Con{Core.Production{+lhs, +rhs}, +rest}:
      prod_flag_here(Nat.is_eq(lhs, x), rest, x, z, grammar, target, F, base, List.length(&2, Core.Sym, rhs), k, j, Prune.prodSegs(rest, x, 1n+base, k, j), fz, mz,
        m => prod_flag(rest, 1n+base, x, k, j, grammar, target, F, z, m, fz))

def root_eq(+rest: +List<Core.Production>, +start: Nat, +n: Nat, +z: Prune.Seg, +grammar: +List<Core.Production>, +target: Core.Bsr, +F: +List<W.Fact>, +base: Nat, +len: Nat, +restsegs: +List<Prune.Seg>,
  +fz: {flagAt(grammar, target, F, z) == True{} : Bool}, cases: Either<{Prune.segEq(z, Prune.Seg{base, 0n, len, n}) == True{} : Bool}, {Prune.segIn(z, restsegs) == True{} : Bool}>,
  later: {Prune.segIn(z, restsegs) == True{} : Bool} -> {WC.isTrees(W.rootFor(rest, grammar, target, 1n+base, start, n, F)) == True{} : Bool})
  -> {WC.isTrees(W.orElse(W.rootPick(True{}, grammar, target, base, len, n, F), W.rootFor(rest, grammar, target, 1n+base, start, n, F))) == True{} : Bool}:
  match cases:
    case Inl{e}:
      +h = flag_seg(grammar, target, F, z, Prune.Seg{base, 0n, len, n}, N.seg_eq_sound(z, Prune.Seg{base, 0n, len, n}, e), fz)
      WC.or_else_left(W.rootPick(True{}, grammar, target, base, len, n, F), W.rootFor(rest, grammar, target, 1n+base, start, n, F), WC.root_here(True{}, grammar, target, base, len, n, F, {==}, h))
    case Inr{m}:
      WC.or_else_right(W.rootPick(True{}, grammar, target, base, len, n, F), W.rootFor(rest, grammar, target, 1n+base, start, n, F), later(m))

def root_here2(b: Bool, +rest: +List<Core.Production>, +start: Nat, +n: Nat, +z: Prune.Seg, +grammar: +List<Core.Production>, +target: Core.Bsr, +F: +List<W.Fact>, +base: Nat, +len: Nat, +restsegs: +List<Prune.Seg>,
  +fz: {flagAt(grammar, target, F, z) == True{} : Bool}, +mz: {Prune.segIn(z, Prune.keepSeg(b, Prune.Seg{base, 0n, len, n}, restsegs)) == True{} : Bool},
  later: {Prune.segIn(z, restsegs) == True{} : Bool} -> {WC.isTrees(W.rootFor(rest, grammar, target, 1n+base, start, n, F)) == True{} : Bool})
  -> {WC.isTrees(W.orElse(W.rootPick(b, grammar, target, base, len, n, F), W.rootFor(rest, grammar, target, 1n+base, start, n, F))) == True{} : Bool}:
  match b:
    case True{}:
      root_eq(rest, start, n, z, grammar, target, F, base, len, restsegs, fz, Lemma.or_true_cases(Prune.segEq(z, Prune.Seg{base, 0n, len, n}), Prune.segIn(z, restsegs), mz), later)
    case False{}:
      later(mz)

# A flagged root segment: the root search finds a forest.
law root_from:
  for g: +List<Core.Production>
  for +base: Nat
  for +start: Nat
  for +n: Nat
  for +grammar: +List<Core.Production>
  for +target: Core.Bsr
  for +F: +List<W.Fact>
  for +z: Prune.Seg
  for +mz: {Prune.segIn(z, Prune.prodSegs(g, start, base, 0n, n)) == True{} : Bool}
  for +fz: {flagAt(grammar, target, F, z) == True{} : Bool}
  {WC.isTrees(W.rootFor(g, grammar, target, base, start, n, F)) == True{} : Bool}

def root_from(g, base, start, n, grammar, target, F, z, mz, fz):
  match g:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(mz))
    case Con{Core.Production{+lhs, +rhs}, +rest}:
      root_here2(Nat.is_eq(lhs, start), rest, start, n, z, grammar, target, F, base, List.length(&2, Core.Sym, rhs), Prune.prodSegs(rest, start, 1n+base, 0n, n), fz, mz,
        m => root_from(rest, 1n+base, start, n, grammar, target, F, z, m, fz))

def item_flag(item: Maybe<&2, Core.Sym>, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +ys: +List<Core.Bsr>, +ns: +List<Prune.Seg>, +F: +List<W.Fact>, +k: Nat, +j: Nat, +z: Prune.Seg,
  +hi: {Run.itemDone(item, grammar, input, k, j, ys) == True{} : Bool},
  +mi: {Prune.segIn(z, Prune.itemNeeds(item, grammar, k, j)) == True{} : Bool}, +fz: {flagAt(grammar, target, F, z) == True{} : Bool}) -> {WC.itemHas(True{}, W.itemOpts(item, grammar, input, target, k, j, F)) == True{} : Bool}:
  match item:
    case Some{Core.Nonterminal{+x, +need}}:
      +P = {Run.prodDone(grammar, 0n, x, k, j, ys) : Bool}
      WC.need_pick(Gll.needHolds(need, k, j), W.prodOpts(grammar, grammar, target, 0n, x, k, j, F), True{}, Lemma.and_true_left(Gll.needHolds(need, k, j), P, hi),
        prod_flag(grammar, 0n, x, k, j, grammar, target, F, z, mi, fz))
    case Some{Core.Terminal{+t}}:
      Empty.absurd({WC.itemHas(True{}, W.itemOpts(Some{Core.Terminal{t}}, grammar, input, target, k, j, F)) == True{} : Bool}, Lemma.false_is_not_true(mi))
    case None{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(mi))

def up_prefix2(+grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +ys: +List<Core.Bsr>, +ns: +List<Prune.Seg>, +F: +List<W.Fact>, +ok: {Prune.allStepsOk(ys, grammar, ns) == True{} : Bool}, +cl: {WC.closedW(Prune.keep(ys, ns), grammar, input, target, F) == True{} : Bool}, +q: Nat, +i: Nat, +d0: Nat, +k: Nat, +j: Nat, +m: {Core.member(Core.Bsr{q, 1n+d0, i, k, j}, Prune.keep(ys, ns)) == True{} : Bool},
  +fp: {WC.optHas(True{}, W.optsAt(grammar, target, q, i, d0, k, F)) == True{} : Bool},
  ci: Either<{WC.itemHas(True{}, W.itemOpts(Gll.nthSym(Core.rhsOf(grammar, q), d0), grammar, input, target, k, j, F)) == True{} : Bool}, {WC.itemHas(False{}, W.itemOpts(Gll.nthSym(Core.rhsOf(grammar, q), d0), grammar, input, target, k, j, F)) == True{} : Bool}>)
  -> {WC.optHas(True{}, W.optsAt(grammar, target, q, i, 1n+d0, j, F)) == True{} : Bool}:
  match ci:
    case Inl{hi}:
      WC.step_fact(grammar, input, Prune.keep(ys, ns), target, F, cl, q, i, d0, k, j, True{}, True{}, fp, hi, m)
    case Inr{hi}:
      WC.step_fact(grammar, input, Prune.keep(ys, ns), target, F, cl, q, i, d0, k, j, True{}, False{}, fp, hi, m)

def up_item2(+grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +ys: +List<Core.Bsr>, +ns: +List<Prune.Seg>, +F: +List<W.Fact>, +ok: {Prune.allStepsOk(ys, grammar, ns) == True{} : Bool}, +cl: {WC.closedW(Prune.keep(ys, ns), grammar, input, target, F) == True{} : Bool}, +q: Nat, +i: Nat, +d0: Nat, +k: Nat, +j: Nat, +m: {Core.member(Core.Bsr{q, 1n+d0, i, k, j}, Prune.keep(ys, ns)) == True{} : Bool},
  +fi: {WC.itemHas(True{}, W.itemOpts(Gll.nthSym(Core.rhsOf(grammar, q), d0), grammar, input, target, k, j, F)) == True{} : Bool},
  cp: Either<{WC.optHas(True{}, W.optsAt(grammar, target, q, i, d0, k, F)) == True{} : Bool}, {WC.optHas(False{}, W.optsAt(grammar, target, q, i, d0, k, F)) == True{} : Bool}>)
  -> {WC.optHas(True{}, W.optsAt(grammar, target, q, i, 1n+d0, j, F)) == True{} : Bool}:
  match cp:
    case Inl{hp}:
      WC.step_fact(grammar, input, Prune.keep(ys, ns), target, F, cl, q, i, d0, k, j, True{}, True{}, hp, fi, m)
    case Inr{hp}:
      WC.step_fact(grammar, input, Prune.keep(ys, ns), target, F, cl, q, i, d0, k, j, False{}, True{}, hp, fi, m)

def up_cases(+grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +ys: +List<Core.Bsr>, +ns: +List<Prune.Seg>, +F: +List<W.Fact>, +ok: {Prune.allStepsOk(ys, grammar, ns) == True{} : Bool}, +cl: {WC.closedW(Prune.keep(ys, ns), grammar, input, target, F) == True{} : Bool}, +hg: {Run.stepsGrounded(ys, grammar, input) == True{} : Bool}, +q: Nat, +i: Nat, +d0: Nat, +k: Nat, +j: Nat, +z: Prune.Seg, +fz: {flagAt(grammar, target, F, z) == True{} : Bool},
  +m: {Core.member(Core.Bsr{q, 1n+d0, i, k, j}, Prune.keep(ys, ns)) == True{} : Bool},
  +gr: {Run.groundedIn(Core.Bsr{q, 1n+d0, i, k, j}, grammar, input, ys) == True{} : Bool},
  +needs: {Prune.allSegsIn(Prune.Seg{q, i, d0, k} <> Prune.itemNeeds(Gll.nthSym(Core.rhsOf(grammar, q), d0), grammar, k, j), ns) == True{} : Bool},
  cases: Either<{Prune.segEq(z, Prune.Seg{q, i, d0, k}) == True{} : Bool}, {Prune.segIn(z, Prune.itemNeeds(Gll.nthSym(Core.rhsOf(grammar, q), d0), grammar, k, j)) == True{} : Bool}>)
  -> {WC.optHas(True{}, W.optsAt(grammar, target, q, i, 1n+d0, j, F)) == True{} : Bool}:
  match cases:
    case Inl{e}:
      +fp = flag_seg(grammar, target, F, z, Prune.Seg{q, i, d0, k}, N.seg_eq_sound(z, Prune.Seg{q, i, d0, k}, e), fz)
      up_prefix2(grammar, input, target, ys, ns, F, ok, cl, q, i, d0, k, j, m, fp,
        item_cases(W.itemOpts(Gll.nthSym(Core.rhsOf(grammar, q), d0), grammar, input, target, k, j, F), item_any(Gll.nthSym(Core.rhsOf(grammar, q), d0), grammar, input, target, ys, ns, F, ys, k, j, Lemma.and_true_right_side(Run.prefixDone(q, i, d0, k, ys), Run.itemDone(Gll.nthSym(Core.rhsOf(grammar, q), d0), grammar, input, k, j, ys), gr),
          Lemma.and_true_right_side(Prune.segIn(Prune.Seg{q, i, d0, k}, ns), Prune.allSegsIn(Prune.itemNeeds(Gll.nthSym(Core.rhsOf(grammar, q), d0), grammar, k, j), ns), needs), q2 => ks2 => d2 => e2 => h1 => h2 => bottom(ys, grammar, input, target, ys, ns, F, ok, cl, q2, ks2, d2, e2, h1, h2, hg, C.step_refl(ys)))))
    case Inr{mi}:
      up_item2(grammar, input, target, ys, ns, F, ok, cl, q, i, d0, k, j, m, item_flag(Gll.nthSym(Core.rhsOf(grammar, q), d0), grammar, input, target, ys, ns, F, k, j, z, Lemma.and_true_right_side(Run.prefixDone(q, i, d0, k, ys), Run.itemDone(Gll.nthSym(Core.rhsOf(grammar, q), d0), grammar, input, k, j, ys), gr), mi, fz),
        opt_cases(W.optsAt(grammar, target, q, i, d0, k, F), prefix_any(d0, grammar, input, target, ys, ns, F, ys, q, i, k, Lemma.and_true_left(Run.prefixDone(q, i, d0, k, ys), Run.itemDone(Gll.nthSym(Core.rhsOf(grammar, q), d0), grammar, input, k, j, ys), gr),
          Lemma.and_true_left(Prune.segIn(Prune.Seg{q, i, d0, k}, ns), Prune.allSegsIn(Prune.itemNeeds(Gll.nthSym(Core.rhsOf(grammar, q), d0), grammar, k, j), ns), needs), q2 => ks2 => d2 => e2 => h1 => h2 => bottom(ys, grammar, input, target, ys, ns, F, ok, cl, q2, ks2, d2, e2, h1, h2, hg, C.step_refl(ys)))))

# One step up: a flagged need of a kept step gives the step's segment a flagged fact.
def up_step(e: Core.Bsr, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +ys: +List<Core.Bsr>, +ns: +List<Prune.Seg>, +F: +List<W.Fact>, +ok: {Prune.allStepsOk(ys, grammar, ns) == True{} : Bool}, +cl: {WC.closedW(Prune.keep(ys, ns), grammar, input, target, F) == True{} : Bool}, +hg: {Run.stepsGrounded(ys, grammar, input) == True{} : Bool}, +z: Prune.Seg, +mz: {Prune.segIn(z, Prune.stepNeeds(grammar, e)) == True{} : Bool}, +fz: {flagAt(grammar, target, F, z) == True{} : Bool},
  +me: {Core.member(e, ys) == True{} : Bool}, +ke: {Prune.isKept(e, ns) == True{} : Bool}) -> {flagAt(grammar, target, F, Prune.segOf(e)) == True{} : Bool}:
  match e:
    case Core.Bsr{+q, 0n, +i, +k, +j}:
      Empty.absurd({flagAt(grammar, target, F, Prune.Seg{q, i, 0n, j}) == True{} : Bool}, Lemma.false_is_not_true(mz))
    case Core.Bsr{+q, 1n+(+d0), +i, +k, +j}:
      up_cases(grammar, input, target, ys, ns, F, ok, cl, hg, q, i, d0, k, j, z, fz, PP.kept_member(ys, ns, Core.Bsr{q, 1n+d0, i, k, j}, me, ke),
        grounded_at(ys, Core.Bsr{q, 1n+d0, i, k, j}, grammar, input, me, hg), PP.kept_needs(ys, grammar, ns, Core.Bsr{q, 1n+d0, i, k, j}, ok, me, ke),
        Lemma.or_true_cases(Prune.segEq(z, Prune.Seg{q, i, d0, k}), Prune.segIn(z, Prune.itemNeeds(Gll.nthSym(Core.rhsOf(grammar, q), d0), grammar, k, j)), mz))

def kept_to(+e: Core.Bsr, +w: Prune.Seg, +ns: +List<Prune.Seg>, +eq: {Prune.segOf(e) == w : Prune.Seg}, +h: {Prune.segIn(w, ns) == True{} : Bool}) -> {Prune.isKept(e, ns) == True{} : Bool}:
  %Equal.sym(Prune.Seg, Prune.segOf(e), w, eq) : {Prune.segIn(_, ns) == True{} : Bool}
  h

def pick_flag(b: Bool, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +ys: +List<Core.Bsr>, +ns: +List<Prune.Seg>, +F: +List<W.Fact>, +ok: {Prune.allStepsOk(ys, grammar, ns) == True{} : Bool}, +cl: {WC.closedW(Prune.keep(ys, ns), grammar, input, target, F) == True{} : Bool}, +hg: {Run.stepsGrounded(ys, grammar, input) == True{} : Bool}, +e: Core.Bsr, +w: Prune.Seg, +z: Prune.Seg, +fz: {flagAt(grammar, target, F, z) == True{} : Bool},
  +eb: {Prune.segEq(Prune.segOf(e), w) == b : Bool}, +mz: {Prune.segIn(z, Prune.stepPick(b, grammar, e)) == True{} : Bool},
  +me: {Core.member(e, ys) == True{} : Bool}, +kw: {Prune.segIn(w, ns) == True{} : Bool}) -> {flagAt(grammar, target, F, w) == True{} : Bool}:
  match b:
    case True{}:
      +eq = N.seg_eq_sound(Prune.segOf(e), w, eb)
      flag_seg(grammar, target, F, Prune.segOf(e), w, eq, up_step(e, grammar, input, target, ys, ns, F, ok, cl, hg, z, mz, fz, me, kept_to(e, w, ns, eq, kw)))
    case False{}:
      Empty.absurd({flagAt(grammar, target, F, w) == True{} : Bool}, Lemma.false_is_not_true(mz))

def walk_pick(+grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +ys: +List<Core.Bsr>, +ns: +List<Prune.Seg>, +F: +List<W.Fact>, +ok: {Prune.allStepsOk(ys, grammar, ns) == True{} : Bool}, +cl: {WC.closedW(Prune.keep(ys, ns), grammar, input, target, F) == True{} : Bool}, +hg: {Run.stepsGrounded(ys, grammar, input) == True{} : Bool}, +e: Core.Bsr, +rest: +List<Core.Bsr>, +w: Prune.Seg, +z: Prune.Seg, +fz: {flagAt(grammar, target, F, z) == True{} : Bool},
  +me: {Core.member(e, ys) == True{} : Bool}, +kw: {Prune.segIn(w, ns) == True{} : Bool},
  c: Either<{Prune.segIn(z, Prune.stepPick(Prune.segEq(Prune.segOf(e), w), grammar, e)) == True{} : Bool}, {Prune.segIn(z, Prune.segNeeds(rest, grammar, w)) == True{} : Bool}>,
  later: {Prune.segIn(z, Prune.segNeeds(rest, grammar, w)) == True{} : Bool} -> {flagAt(grammar, target, F, w) == True{} : Bool}) -> {flagAt(grammar, target, F, w) == True{} : Bool}:
  match c:
    case Inl{m}:
      pick_flag(Prune.segEq(Prune.segOf(e), w), grammar, input, target, ys, ns, F, ok, cl, hg, e, w, z, fz, {==}, m, me, kw)
    case Inr{m}:
      later(m)

# A flagged need of a kept segment gives the segment a flagged fact.
law needs_walk:
  for ws: +List<Core.Bsr>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +target: Core.Bsr
  for +ys: +List<Core.Bsr>
  for +ns: +List<Prune.Seg>
  for +F: +List<W.Fact>
  for +ok: {Prune.allStepsOk(ys, grammar, ns) == True{} : Bool}
  for +cl: {WC.closedW(Prune.keep(ys, ns), grammar, input, target, F) == True{} : Bool}
  for +hg: {Run.stepsGrounded(ys, grammar, input) == True{} : Bool}
  for +w: Prune.Seg
  for +z: Prune.Seg
  for +mz: {Prune.segIn(z, Prune.segNeeds(ws, grammar, w)) == True{} : Bool}
  for +fz: {flagAt(grammar, target, F, z) == True{} : Bool}
  for +sub: {Core.allIn(ws, ys) == True{} : Bool}
  for +kw: {Prune.segIn(w, ns) == True{} : Bool}
  {flagAt(grammar, target, F, w) == True{} : Bool}

def needs_walk(ws, grammar, input, target, ys, ns, F, ok, cl, hg, w, z, mz, fz, sub, kw):
  match ws:
    case Nil{}:
      Empty.absurd({flagAt(grammar, target, F, w) == True{} : Bool}, Lemma.false_is_not_true(mz))
    case Con{+e, +rest}:
      walk_pick(grammar, input, target, ys, ns, F, ok, cl, hg, e, rest, w, z, fz, Lemma.and_true_left(Core.member(e, ys), Core.allIn(rest, ys), sub), kw,
        seg_split(Prune.stepPick(Prune.segEq(Prune.segOf(e), w), grammar, e), Prune.segNeeds(rest, grammar, w), z, mz),
        m => needs_walk(rest, grammar, input, target, ys, ns, F, ok, cl, hg, w, z, m, fz, Lemma.and_true_right_side(Core.member(e, ys), Core.allIn(rest, ys), sub), kw))

def find_pick(+grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +ys: +List<Core.Bsr>, +ns: +List<Prune.Seg>, +F: +List<W.Fact>, +ok: {Prune.allStepsOk(ys, grammar, ns) == True{} : Bool}, +cl: {WC.closedW(Prune.keep(ys, ns), grammar, input, target, F) == True{} : Bool}, +hg: {Run.stepsGrounded(ys, grammar, input) == True{} : Bool}, +start: Nat, +w: Prune.Seg, +rest: +List<Prune.Seg>, +older: +List<Prune.Seg>, +z: Prune.Seg, +fz: {flagAt(grammar, target, F, z) == True{} : Bool},
  +mw: {Prune.segIn(w, older) == True{} : Bool}, +so: {Prune.allSegsIn(older, ns) == True{} : Bool},
  c: Either<{Prune.segIn(z, Prune.segNeeds(ys, grammar, w)) == True{} : Bool}, {N.anyNeed(z, rest, ys, grammar) == True{} : Bool}>,
  rec: @w2: Prune.Seg -> {Prune.segIn(w2, older) == True{} : Bool} -> {flagAt(grammar, target, F, w2) == True{} : Bool} -> {WC.isTrees(W.rootFor(grammar, grammar, target, 0n, start, List.length(&2, Nat, input), F)) == True{} : Bool},
  later: {N.anyNeed(z, rest, ys, grammar) == True{} : Bool} -> (@w2: Prune.Seg -> {Prune.segIn(w2, older) == True{} : Bool} -> {flagAt(grammar, target, F, w2) == True{} : Bool} -> {WC.isTrees(W.rootFor(grammar, grammar, target, 0n, start, List.length(&2, Nat, input), F)) == True{} : Bool}) -> {WC.isTrees(W.rootFor(grammar, grammar, target, 0n, start, List.length(&2, Nat, input), F)) == True{} : Bool}) -> {WC.isTrees(W.rootFor(grammar, grammar, target, 0n, start, List.length(&2, Nat, input), F)) == True{} : Bool}:
  match c:
    case Inl{m}:
      rec(w, mw, needs_walk(ys, grammar, input, target, ys, ns, F, ok, cl, hg, w, z, m, fz, C.step_refl(ys), N.seg_sub(older, w, ns, mw, so)))
    case Inr{h}:
      later(h, rec)

# Find the older segment whose need z is: it gets a flagged fact; go on from there.
law need_find:
  for ws: +List<Prune.Seg>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +target: Core.Bsr
  for +ys: +List<Core.Bsr>
  for +ns: +List<Prune.Seg>
  for +F: +List<W.Fact>
  for +ok: {Prune.allStepsOk(ys, grammar, ns) == True{} : Bool}
  for +cl: {WC.closedW(Prune.keep(ys, ns), grammar, input, target, F) == True{} : Bool}
  for +hg: {Run.stepsGrounded(ys, grammar, input) == True{} : Bool}
  for +start: Nat
  for +older: +List<Prune.Seg>
  for +z: Prune.Seg
  for +fz: {flagAt(grammar, target, F, z) == True{} : Bool}
  for +h: {N.anyNeed(z, ws, ys, grammar) == True{} : Bool}
  for +subw: {Prune.allSegsIn(ws, older) == True{} : Bool}
  for +so: {Prune.allSegsIn(older, ns) == True{} : Bool}
  for rec: @w2: Prune.Seg -> {Prune.segIn(w2, older) == True{} : Bool} -> {flagAt(grammar, target, F, w2) == True{} : Bool} -> {WC.isTrees(W.rootFor(grammar, grammar, target, 0n, start, List.length(&2, Nat, input), F)) == True{} : Bool}
  {WC.isTrees(W.rootFor(grammar, grammar, target, 0n, start, List.length(&2, Nat, input), F)) == True{} : Bool}

def need_find(ws, grammar, input, target, ys, ns, F, ok, cl, hg, start, older, z, fz, h, subw, so, rec):
  match ws:
    case Nil{}:
      Empty.absurd({WC.isTrees(W.rootFor(grammar, grammar, target, 0n, start, List.length(&2, Nat, input), F)) == True{} : Bool}, Lemma.false_is_not_true(h))
    case Con{+w, +rest}:
      find_pick(grammar, input, target, ys, ns, F, ok, cl, hg, start, w, rest, older, z, fz, Lemma.and_true_left(Prune.segIn(w, older), Prune.allSegsIn(rest, older), subw), so,
        Lemma.or_true_cases(Prune.segIn(z, Prune.segNeeds(ys, grammar, w)), N.anyNeed(z, rest, ys, grammar), h), rec,
        h2 => r2 => need_find(rest, grammar, input, target, ys, ns, F, ok, cl, hg, start, older, z, fz, h2, Lemma.and_true_right_side(Prune.segIn(w, older), Prune.allSegsIn(rest, older), subw), so, r2))

def just_pick(+grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +ys: +List<Core.Bsr>, +ns: +List<Prune.Seg>, +F: +List<W.Fact>, +ok: {Prune.allStepsOk(ys, grammar, ns) == True{} : Bool}, +cl: {WC.closedW(Prune.keep(ys, ns), grammar, input, target, F) == True{} : Bool}, +hg: {Run.stepsGrounded(ys, grammar, input) == True{} : Bool}, +start: Nat, +z: Prune.Seg, +older: +List<Prune.Seg>, +fz: {flagAt(grammar, target, F, z) == True{} : Bool}, +so: {Prune.allSegsIn(older, ns) == True{} : Bool},
  c: Either<{Prune.segIn(z, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))) == True{} : Bool}, {N.anyNeed(z, older, ys, grammar) == True{} : Bool}>,
  rec: @w2: Prune.Seg -> {Prune.segIn(w2, older) == True{} : Bool} -> {flagAt(grammar, target, F, w2) == True{} : Bool} -> {WC.isTrees(W.rootFor(grammar, grammar, target, 0n, start, List.length(&2, Nat, input), F)) == True{} : Bool}) -> {WC.isTrees(W.rootFor(grammar, grammar, target, 0n, start, List.length(&2, Nat, input), F)) == True{} : Bool}:
  match c:
    case Inl{mr}:
      root_from(grammar, 0n, start, List.length(&2, Nat, input), grammar, target, F, z, mr, fz)
    case Inr{h}:
      need_find(older, grammar, input, target, ys, ns, F, ok, cl, hg, start, older, z, fz, h, N.seg_refl(older), so, rec)

def up_pick(+grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +ys: +List<Core.Bsr>, +ns: +List<Prune.Seg>, +F: +List<W.Fact>, +ok: {Prune.allStepsOk(ys, grammar, ns) == True{} : Bool}, +cl: {WC.closedW(Prune.keep(ys, ns), grammar, input, target, F) == True{} : Bool}, +hg: {Run.stepsGrounded(ys, grammar, input) == True{} : Bool}, +start: Nat, +x: Prune.Seg, +z: Prune.Seg, +older: +List<Prune.Seg>, +fx: {flagAt(grammar, target, F, x) == True{} : Bool},
  +jz: {N.justBy(z, older, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))) == True{} : Bool}, +so: {Prune.allSegsIn(older, ns) == True{} : Bool},
  c: Either<{Prune.segEq(x, z) == True{} : Bool}, {Prune.segIn(x, older) == True{} : Bool}>,
  rec: @w2: Prune.Seg -> {Prune.segIn(w2, older) == True{} : Bool} -> {flagAt(grammar, target, F, w2) == True{} : Bool} -> {WC.isTrees(W.rootFor(grammar, grammar, target, 0n, start, List.length(&2, Nat, input), F)) == True{} : Bool}) -> {WC.isTrees(W.rootFor(grammar, grammar, target, 0n, start, List.length(&2, Nat, input), F)) == True{} : Bool}:
  match c:
    case Inl{e}:
      just_pick(grammar, input, target, ys, ns, F, ok, cl, hg, start, z, older, flag_seg(grammar, target, F, x, z, N.seg_eq_sound(x, z, e), fx), so,
        Lemma.or_true_cases(Prune.segIn(z, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))), N.anyNeed(z, older, ys, grammar), jz), rec)
    case Inr{m}:
      rec(x, m, fx)

# BY INDUCTION IN THE NEEDS' ORDER: a flagged needed segment leads to a root forest.
law up:
  for seen: +List<Prune.Seg>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +target: Core.Bsr
  for +ys: +List<Core.Bsr>
  for +ns: +List<Prune.Seg>
  for +F: +List<W.Fact>
  for +ok: {Prune.allStepsOk(ys, grammar, ns) == True{} : Bool}
  for +cl: {WC.closedW(Prune.keep(ys, ns), grammar, input, target, F) == True{} : Bool}
  for +hg: {Run.stepsGrounded(ys, grammar, input) == True{} : Bool}
  for +start: Nat
  for +x: Prune.Seg
  for +m: {Prune.segIn(x, seen) == True{} : Bool}
  for +sj: {N.seenJust(seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))) == True{} : Bool}
  for +ss: {Prune.allSegsIn(seen, ns) == True{} : Bool}
  for +fx: {flagAt(grammar, target, F, x) == True{} : Bool}
  {WC.isTrees(W.rootFor(grammar, grammar, target, 0n, start, List.length(&2, Nat, input), F)) == True{} : Bool}

def up(seen, grammar, input, target, ys, ns, F, ok, cl, hg, start, x, m, sj, ss, fx):
  match seen:
    case Nil{}:
      Empty.absurd({WC.isTrees(W.rootFor(grammar, grammar, target, 0n, start, List.length(&2, Nat, input), F)) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{+z, +older}:
      +J = {N.justBy(z, older, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))) : Bool}
      +sjo = Lemma.and_true_right_side(J, N.seenJust(older, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))), sj)
      +so = Lemma.and_true_right_side(Prune.segIn(z, ns), Prune.allSegsIn(older, ns), ss)
      up_pick(grammar, input, target, ys, ns, F, ok, cl, hg, start, x, z, older, fx, Lemma.and_true_left(J, N.seenJust(older, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))), sj), so,
        Lemma.or_true_cases(Prune.segEq(x, z), Prune.segIn(x, older), m),
        w2 => mw => fw => up(older, grammar, input, target, ys, ns, F, ok, cl, hg, start, w2, mw, sjo, so, fw))

# ---- The target's own segment ----

def kept_eq(+t: Core.Bsr, +e: Core.Bsr, +ns: +List<Prune.Seg>, +eq: {t == e : Core.Bsr}, +h: {Prune.isKept(e, ns) == True{} : Bool}) -> {Prune.isKept(t, ns) == True{} : Bool}:
  %Equal.sym(Core.Bsr, t, e, eq) : {Prune.isKept(_, ns) == True{} : Bool}
  h

def kept_head(+t: Core.Bsr, +e: Core.Bsr, +rest: +List<Core.Bsr>, +ns: +List<Prune.Seg>, +ek: {Prune.isKept(e, ns) == True{} : Bool},
  +q: {Core.bsrEq(t, e) == True{} : Bool}) -> {Core.member(t, e <> rest) == True{} : Bool} & {Prune.isKept(t, ns) == True{} : Bool}:
  +eq = G.bsr_eq_sound(t, e, q)
  (Lemma.or_true_left_intro(Core.bsrEq(t, e), Core.member(t, rest), q), kept_eq(t, e, ns, eq, ek))

def kept_more(+t: Core.Bsr, +e: Core.Bsr, +rest: +List<Core.Bsr>, +ns: +List<Prune.Seg>,
  p: {Core.member(t, rest) == True{} : Bool} & {Prune.isKept(t, ns) == True{} : Bool}) -> {Core.member(t, e <> rest) == True{} : Bool} & {Prune.isKept(t, ns) == True{} : Bool}:
  match p:
    case (+m, k):
      (Lemma.or_true_right_intro(Core.bsrEq(t, e), Core.member(t, rest), m), k)

def keep_back_or(+t: Core.Bsr, +e: Core.Bsr, +rest: +List<Core.Bsr>, +ns: +List<Prune.Seg>, +eb: {Prune.isKept(e, ns) == True{} : Bool},
  c: Either<{Core.bsrEq(t, e) == True{} : Bool}, {Core.member(t, Prune.keep(rest, ns)) == True{} : Bool}>,
  later: {Core.member(t, Prune.keep(rest, ns)) == True{} : Bool} -> {Core.member(t, rest) == True{} : Bool} & {Prune.isKept(t, ns) == True{} : Bool})
  -> {Core.member(t, e <> rest) == True{} : Bool} & {Prune.isKept(t, ns) == True{} : Bool}:
  match c:
    case Inl{q}:
      kept_head(t, e, rest, ns, eb, q)
    case Inr{m}:
      kept_more(t, e, rest, ns, later(m))

def keep_back_pick(b: Bool, +t: Core.Bsr, +e: Core.Bsr, +rest: +List<Core.Bsr>, +ns: +List<Prune.Seg>,
  +eb: {Prune.isKept(e, ns) == b : Bool}, +mt: {Core.member(t, Prune.keepPick(b, e, Prune.keep(rest, ns))) == True{} : Bool},
  later: {Core.member(t, Prune.keep(rest, ns)) == True{} : Bool} -> {Core.member(t, rest) == True{} : Bool} & {Prune.isKept(t, ns) == True{} : Bool})
  -> {Core.member(t, e <> rest) == True{} : Bool} & {Prune.isKept(t, ns) == True{} : Bool}:
  match b:
    case True{}:
      keep_back_or(t, e, rest, ns, eb, Lemma.or_true_cases(Core.bsrEq(t, e), Core.member(t, Prune.keep(rest, ns)), mt), later)
    case False{}:
      kept_more(t, e, rest, ns, later(mt))

# A kept step is a step, and its segment is needed.
law keep_back:
  for ys2: +List<Core.Bsr>
  for +ns: +List<Prune.Seg>
  for +t: Core.Bsr
  for +mt: {Core.member(t, Prune.keep(ys2, ns)) == True{} : Bool}
  {Core.member(t, ys2) == True{} : Bool} & {Prune.isKept(t, ns) == True{} : Bool}

def keep_back(ys2, ns, t, mt):
  match ys2:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool} & {Prune.isKept(t, ns) == True{} : Bool}, Lemma.false_is_not_true(mt))
    case Con{+e, +rest}:
      keep_back_pick(Prune.isKept(e, ns), t, e, rest, ns, {==}, mt, m => keep_back(rest, ns, t, m))

def bool_true(+sf: Bool, +h: {sf == True{} : Bool}) -> {W.boolEq(True{}, sf) == True{} : Bool}:
  %Equal.sym(Bool, sf, True{}, h) : {W.boolEq(True{}, _) == True{} : Bool}
  {==}

def zero_flag(b: Bool, +grammar: +List<Core.Production>, +tg: Core.Bsr, +q: Nat, +i: Nat, +eb: {b == True{} : Bool},
  +sf: {Bool.and(List.is_empty(&2, Core.Sym, Core.rhsOf(grammar, q)), Core.bsrEq(Core.Bsr{q, 0n, i, i, i}, tg)) == True{} : Bool})
  -> {WC.optHas(True{}, W.emptyPrefix(b, grammar, tg, q, i)) == True{} : Bool}:
  match b:
    case True{}:
      +s = Bool.and(List.is_empty(&2, Core.Sym, Core.rhsOf(grammar, q)), Core.bsrEq(Core.Bsr{q, 0n, i, i, i}, tg))
      Lemma.or_true_left_intro(W.boolEq(True{}, s), False{}, bool_true(s, sf))
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(eb))

def combT2(+f1: Bool, +grammar: +List<Core.Production>, +input: +List<Nat>, +ys: +List<Core.Bsr>, +ns: +List<Prune.Seg>, +F: +List<W.Fact>, +q: Nat, +i: Nat, +d0: Nat, +k: Nat, +j: Nat,
  +cl: {WC.closedW(Prune.keep(ys, ns), grammar, input, Core.Bsr{q, 1n+d0, i, k, j}, F) == True{} : Bool},
  +m: {Core.member(Core.Bsr{q, 1n+d0, i, k, j}, Prune.keep(ys, ns)) == True{} : Bool}, +hp: {WC.optHas(f1, W.optsAt(grammar, Core.Bsr{q, 1n+d0, i, k, j}, q, i, d0, k, F)) == True{} : Bool},
  ci: Either<{WC.itemHas(True{}, W.itemOpts(Gll.nthSym(Core.rhsOf(grammar, q), d0), grammar, input, Core.Bsr{q, 1n+d0, i, k, j}, k, j, F)) == True{} : Bool}, {WC.itemHas(False{}, W.itemOpts(Gll.nthSym(Core.rhsOf(grammar, q), d0), grammar, input, Core.Bsr{q, 1n+d0, i, k, j}, k, j, F)) == True{} : Bool}>)
  -> {WC.optHas(True{}, W.optsAt(grammar, Core.Bsr{q, 1n+d0, i, k, j}, q, i, 1n+d0, j, F)) == True{} : Bool}:
  match ci:
    case Inl{hi}:
      WC.flag_at(Bool.or(Bool.or(f1, True{}), Core.bsrEq(Core.Bsr{q, 1n+d0, i, k, j}, Core.Bsr{q, 1n+d0, i, k, j})), W.optsAt(grammar, Core.Bsr{q, 1n+d0, i, k, j}, q, i, 1n+d0, j, F), Lemma.or_true_right_intro(Bool.or(f1, True{}), Core.bsrEq(Core.Bsr{q, 1n+d0, i, k, j}, Core.Bsr{q, 1n+d0, i, k, j}), C.bsr_eq_refl(Core.Bsr{q, 1n+d0, i, k, j})),
        WC.step_fact(grammar, input, Prune.keep(ys, ns), Core.Bsr{q, 1n+d0, i, k, j}, F, cl, q, i, d0, k, j, f1, True{}, hp, hi, m))
    case Inr{hi}:
      WC.flag_at(Bool.or(Bool.or(f1, False{}), Core.bsrEq(Core.Bsr{q, 1n+d0, i, k, j}, Core.Bsr{q, 1n+d0, i, k, j})), W.optsAt(grammar, Core.Bsr{q, 1n+d0, i, k, j}, q, i, 1n+d0, j, F), Lemma.or_true_right_intro(Bool.or(f1, False{}), Core.bsrEq(Core.Bsr{q, 1n+d0, i, k, j}, Core.Bsr{q, 1n+d0, i, k, j}), C.bsr_eq_refl(Core.Bsr{q, 1n+d0, i, k, j})),
        WC.step_fact(grammar, input, Prune.keep(ys, ns), Core.Bsr{q, 1n+d0, i, k, j}, F, cl, q, i, d0, k, j, f1, False{}, hp, hi, m))

def combT(+grammar: +List<Core.Production>, +input: +List<Nat>, +ys: +List<Core.Bsr>, +ns: +List<Prune.Seg>, +F: +List<W.Fact>, +q: Nat, +i: Nat, +d0: Nat, +k: Nat, +j: Nat,
  +cl: {WC.closedW(Prune.keep(ys, ns), grammar, input, Core.Bsr{q, 1n+d0, i, k, j}, F) == True{} : Bool},
  +m: {Core.member(Core.Bsr{q, 1n+d0, i, k, j}, Prune.keep(ys, ns)) == True{} : Bool},
  cp: Either<{WC.optHas(True{}, W.optsAt(grammar, Core.Bsr{q, 1n+d0, i, k, j}, q, i, d0, k, F)) == True{} : Bool}, {WC.optHas(False{}, W.optsAt(grammar, Core.Bsr{q, 1n+d0, i, k, j}, q, i, d0, k, F)) == True{} : Bool}>,
  ci: Either<{WC.itemHas(True{}, W.itemOpts(Gll.nthSym(Core.rhsOf(grammar, q), d0), grammar, input, Core.Bsr{q, 1n+d0, i, k, j}, k, j, F)) == True{} : Bool}, {WC.itemHas(False{}, W.itemOpts(Gll.nthSym(Core.rhsOf(grammar, q), d0), grammar, input, Core.Bsr{q, 1n+d0, i, k, j}, k, j, F)) == True{} : Bool}>)
  -> {WC.optHas(True{}, W.optsAt(grammar, Core.Bsr{q, 1n+d0, i, k, j}, q, i, 1n+d0, j, F)) == True{} : Bool}:
  match cp:
    case Inl{hp}:
      combT2(True{}, grammar, input, ys, ns, F, q, i, d0, k, j, cl, m, hp, ci)
    case Inr{hp}:
      combT2(False{}, grammar, input, ys, ns, F, q, i, d0, k, j, cl, m, hp, ci)

def target_case(dd: Nat, +grammar: +List<Core.Production>, +input: +List<Nat>, +ys: +List<Core.Bsr>, +ns: +List<Prune.Seg>, +F: +List<W.Fact>, +q: Nat, +i: Nat, +k: Nat, +j: Nat,
  +ok: {Prune.allStepsOk(ys, grammar, ns) == True{} : Bool},
  +cl: {WC.closedW(Prune.keep(ys, ns), grammar, input, Core.Bsr{q, dd, i, k, j}, F) == True{} : Bool},
  +hg: {Run.stepsGrounded(ys, grammar, input) == True{} : Bool},
  +my: {Core.member(Core.Bsr{q, dd, i, k, j}, ys) == True{} : Bool}, +kt: {Prune.isKept(Core.Bsr{q, dd, i, k, j}, ns) == True{} : Bool})
  -> {WC.optHas(True{}, W.optsAt(grammar, Core.Bsr{q, dd, i, k, j}, q, i, dd, j, F)) == True{} : Bool}:
  match dd:
    case 0n:
      +gr = grounded_at(ys, Core.Bsr{q, 0n, i, k, j}, grammar, input, my, hg)
      +E = {List.is_empty(&2, Core.Sym, Core.rhsOf(grammar, q)) : Bool}
      +r = Lemma.and_true_right_side(E, Bool.and(Nat.is_eq(i, k), Nat.is_eq(k, j)), gr)
      +eik = Lemma.and_true_left(Nat.is_eq(i, k), Nat.is_eq(k, j), r)
      +eij = eq_trans_is(i, k, j, eik, Lemma.and_true_right_side(Nat.is_eq(i, k), Nat.is_eq(k, j), r))
      +T0 = {Core.Bsr{q, 0n, i, k, j} : Core.Bsr}
      +bq = Lemma.and_true_intro(Nat.is_eq(q, q), Bool.and(Nat.is_eq(i, i), Bool.and(Nat.is_eq(i, k), Nat.is_eq(i, j))), Lemma.nat_eq_refl(q),
        Lemma.and_true_intro(Nat.is_eq(i, i), Bool.and(Nat.is_eq(i, k), Nat.is_eq(i, j)), Lemma.nat_eq_refl(i), Lemma.and_true_intro(Nat.is_eq(i, k), Nat.is_eq(i, j), eik, eij)))
      zero_flag(Nat.is_eq(i, j), grammar, T0, q, i, eij,
        Lemma.and_true_intro(E, Core.bsrEq(Core.Bsr{q, 0n, i, i, i}, T0), Lemma.and_true_left(E, Bool.and(Nat.is_eq(i, k), Nat.is_eq(k, j)), gr), bq))
    case 1n+(+d0):
      +B = {Core.Bsr{q, 1n+d0, i, k, j} : Core.Bsr}
      +gr = grounded_at(ys, B, grammar, input, my, hg)
      +NTH = Gll.nthSym(Core.rhsOf(grammar, q), d0)
      +PD = {Run.prefixDone(q, i, d0, k, ys) : Bool}
      +ID = {Run.itemDone(NTH, grammar, input, k, j, ys) : Bool}
      +needs = PP.kept_needs(ys, grammar, ns, B, ok, my, kt)
      +IN = Prune.itemNeeds(NTH, grammar, k, j)
      combT(grammar, input, ys, ns, F, q, i, d0, k, j, cl, PP.kept_member(ys, ns, B, my, kt),
        opt_cases(W.optsAt(grammar, B, q, i, d0, k, F), prefix_any(d0, grammar, input, B, ys, ns, F, ys, q, i, k, Lemma.and_true_left(PD, ID, gr),
          Lemma.and_true_left(Prune.segIn(Prune.Seg{q, i, d0, k}, ns), Prune.allSegsIn(IN, ns), needs),
          q2 => ks2 => d2 => e2 => h1 => h2 => bottom(ys, grammar, input, B, ys, ns, F, ok, cl, q2, ks2, d2, e2, h1, h2, hg, C.step_refl(ys)))),
        item_cases(W.itemOpts(NTH, grammar, input, B, k, j, F), item_any(NTH, grammar, input, B, ys, ns, F, ys, k, j, Lemma.and_true_right_side(PD, ID, gr),
          Lemma.and_true_right_side(Prune.segIn(Prune.Seg{q, i, d0, k}, ns), Prune.allSegsIn(IN, ns), needs),
          q2 => ks2 => d2 => e2 => h1 => h2 => bottom(ys, grammar, input, B, ys, ns, F, ok, cl, q2, ks2, d2, e2, h1, h2, hg, C.step_refl(ys)))))

# The target, a kept step, gets a flagged fact for its own segment.
def target_flag(target: Core.Bsr, +grammar: +List<Core.Production>, +input: +List<Nat>, +ys: +List<Core.Bsr>, +ns: +List<Prune.Seg>, +F: +List<W.Fact>,
  +ok: {Prune.allStepsOk(ys, grammar, ns) == True{} : Bool},
  +cl: {WC.closedW(Prune.keep(ys, ns), grammar, input, target, F) == True{} : Bool},
  +hg: {Run.stepsGrounded(ys, grammar, input) == True{} : Bool},
  +my: {Core.member(target, ys) == True{} : Bool}, +kt: {Prune.isKept(target, ns) == True{} : Bool})
  -> {flagAt(grammar, target, F, Prune.segOf(target)) == True{} : Bool}:
  match target:
    case Core.Bsr{+q, +dd, +i, +k, +j}:
      target_case(dd, grammar, input, ys, ns, F, q, i, k, j, ok, cl, hg, my, kt)

def found2(+grammar: +List<Core.Production>, +input: +List<Nat>, +start: Nat, +target: Core.Bsr, +ys: +List<Core.Bsr>, +ns: +List<Prune.Seg>, +F: +List<W.Fact>,
  +ok: {Prune.allStepsOk(ys, grammar, ns) == True{} : Bool},
  +cl: {WC.closedW(Prune.keep(ys, ns), grammar, input, target, F) == True{} : Bool},
  +hg: {Run.stepsGrounded(ys, grammar, input) == True{} : Bool},
  +sj: {N.seenJust(ns, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))) == True{} : Bool},
  p: {Core.member(target, ys) == True{} : Bool} & {Prune.isKept(target, ns) == True{} : Bool}) -> {WC.isTrees(W.rootFor(grammar, grammar, target, 0n, start, List.length(&2, Nat, input), F)) == True{} : Bool}:
  match p:
    case (+my, +kt):
      up(ns, grammar, input, target, ys, ns, F, ok, cl, hg, start, Prune.segOf(target), kt, sj, N.seg_refl(ns), target_flag(target, grammar, input, ys, ns, F, ok, cl, hg, my, kt))

# EVERY KEPT STEP HAS A WITNESS: on steps resting on earlier steps, closed needs reached
# from the root in order, and witness facts closed under the kept steps, the root search
# finds a forest for any kept target.
law found_root:
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +start: Nat
  for +target: Core.Bsr
  for +ys: +List<Core.Bsr>
  for +ns: +List<Prune.Seg>
  for +F: +List<W.Fact>
  for +ok: {Prune.allStepsOk(ys, grammar, ns) == True{} : Bool}
  for +cl: {WC.closedW(Prune.keep(ys, ns), grammar, input, target, F) == True{} : Bool}
  for +hg: {Run.stepsGrounded(ys, grammar, input) == True{} : Bool}
  for +sj: {N.seenJust(ns, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))) == True{} : Bool}
  for +mt: {Core.member(target, Prune.keep(ys, ns)) == True{} : Bool}
  {WC.isTrees(W.rootFor(grammar, grammar, target, 0n, start, List.length(&2, Nat, input), F)) == True{} : Bool}

def found_root(grammar, input, start, target, ys, ns, F, ok, cl, hg, sj, mt):
  found2(grammar, input, start, target, ys, ns, F, ok, cl, hg, sj, keep_back(ys, ns, target, mt))


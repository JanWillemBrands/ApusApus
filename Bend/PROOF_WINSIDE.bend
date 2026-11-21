import Base
import ./LEMMAS.bend as Lemma
import ./CORE.bend as Core
import ./GLL.bend as Gll
import ./WITNESS.bend as W
import ./PROOF_GLL.bend as G
import ./PROOF_PRUNE.bend as PP
import ./PROOF_COUNT.bend as C
import ./PROOF_WITNESS.bend as WC
import ./PROOF_WSOUND.bend as WS

# THE WITNESS FORESTS STAY INSIDE THE STEPS (WITNESS.bend). Every fact's forest has all its
# steps in its node among the steps the search was given: a prefix grows by the step being
# processed, an item is a node of an earlier fact or a leaf, and a node of an empty right
# side is found only from its empty step. So every tree the search hands out uses only the
# given steps (`witness_in`, `cover_in`). WSOUND's soundness supplies lengths and ends.

# ======== INSIDE ========

def pIn(+grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +ps: +List<Core.Bsr>, +q: Nat, +ks: Nat, +fo: +List<Core.Tree>) -> Bool:
  Core.allIn(WS.stepsP(grammar, q, fo, ks), ps)

def optsIn(os: +List<W.Opt>, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +ps: +List<Core.Bsr>, +q: Nat, +ks: Nat) -> Bool:
  match os:
    case Nil{}:
      True{}
    case Con{W.Opt{+fl, +fo}, rest}:
      Bool.and(pIn(grammar, input, target, ps, q, ks, fo), optsIn(rest, grammar, input, target, ps, q, ks))

def itemsIn(os: +List<W.Opt>, +ps: +List<Core.Bsr>, +k: Nat) -> Bool:
  match os:
    case Nil{}:
      True{}
    case Con{W.Opt{+fl, +fo}, rest}:
      Bool.and(Core.allIn(Core.steps(fo, k), ps), itemsIn(rest, ps, k))

def factsIn(fs: +List<W.Fact>, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +ps: +List<Core.Bsr>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case Con{W.Fact{+q, +ks, +d, +e, +fl, +fo}, rest}:
      Bool.and(pIn(grammar, input, target, ps, q, ks, fo), factsIn(rest, grammar, input, target, ps))

# ======== PREFIX OPTIONS ========

def p_moved(+grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +ps: +List<Core.Bsr>, +q: Nat, +ks: Nat, +q2: Nat, +ks2: Nat, +fo: +List<Core.Tree>, +e1: {q == q2 : Nat}, +e2: {ks == ks2 : Nat},
  +h: {pIn(grammar, input, target, ps, q2, ks2, fo) == True{} : Bool}) -> {pIn(grammar, input, target, ps, q, ks, fo) == True{} : Bool}:
  %Equal.sym(Nat, q, q2, e1) : {pIn(grammar, input, target, ps, _, ks, fo) == True{} : Bool}
  %Equal.sym(Nat, ks, ks2, e2) : {pIn(grammar, input, target, ps, q2, _, fo) == True{} : Bool}
  h

def fi_pick(b: Bool, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +ps: +List<Core.Bsr>, +q: Nat, +ks: Nat, +d: Nat, +e: Nat, +q2: Nat, +ks2: Nat, +d2: Nat, +e2: Nat, +fl: Bool, +fo: +List<Core.Tree>, +more: +List<W.Opt>,
  +eb: {Bool.and(Nat.is_eq(q, q2), Bool.and(Nat.is_eq(ks, ks2), Bool.and(Nat.is_eq(d, d2), Nat.is_eq(e, e2)))) == b : Bool},
  +hp: {pIn(grammar, input, target, ps, q2, ks2, fo) == True{} : Bool}, +hr: {optsIn(more, grammar, input, target, ps, q, ks) == True{} : Bool})
  -> {optsIn(W.optIf(b, W.Opt{fl, fo}, more), grammar, input, target, ps, q, ks) == True{} : Bool}:
  match b:
    case True{}:
      +r1 = Lemma.and_true_right_side(Nat.is_eq(q, q2), Bool.and(Nat.is_eq(ks, ks2), Bool.and(Nat.is_eq(d, d2), Nat.is_eq(e, e2))), eb)
      Lemma.and_true_intro(pIn(grammar, input, target, ps, q, ks, fo), optsIn(more, grammar, input, target, ps, q, ks),
        p_moved(grammar, input, target, ps, q, ks, q2, ks2, fo,
          Lemma.nat_eq_sound(q, q2, Lemma.and_true_left(Nat.is_eq(q, q2), Bool.and(Nat.is_eq(ks, ks2), Bool.and(Nat.is_eq(d, d2), Nat.is_eq(e, e2))), eb)),
          Lemma.nat_eq_sound(ks, ks2, Lemma.and_true_left(Nat.is_eq(ks, ks2), Bool.and(Nat.is_eq(d, d2), Nat.is_eq(e, e2)), r1)), hp), hr)
    case False{}:
      hr

law found_in:
  for F: +List<W.Fact>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +target: Core.Bsr
  for +ps: +List<Core.Bsr>
  for +q: Nat
  for +ks: Nat
  for +d: Nat
  for +e: Nat
  for +hI: {factsIn(F, grammar, input, target, ps) == True{} : Bool}
  {optsIn(W.foundAt(q, ks, d, e, F), grammar, input, target, ps, q, ks) == True{} : Bool}

def found_in(F, grammar, input, target, ps, q, ks, d, e, hI):
  match F:
    case Nil{}:
      {==}
    case Con{W.Fact{+q2, +ks2, +d2, +e2, +fl, +fo}, +rest}:
      +p = {pIn(grammar, input, target, ps, q2, ks2, fo) : Bool}
      fi_pick(W.sameKey(q, ks, d, e, W.Fact{q2, ks2, d2, e2, fl, fo}), grammar, input, target, ps, q, ks, d, e, q2, ks2, d2, e2, fl, fo, W.foundAt(q, ks, d, e, rest), {==},
        Lemma.and_true_left(p, factsIn(rest, grammar, input, target, ps), hI),
        found_in(rest, grammar, input, target, ps, q, ks, d, e, Lemma.and_true_right_side(p, factsIn(rest, grammar, input, target, ps), hI)))

def start_in(b: Bool, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +ps: +List<Core.Bsr>, +q: Nat, +ks: Nat, +ne: {List.is_empty(&2, Core.Sym, Core.rhsOf(grammar, q)) == False{} : Bool})
  -> {optsIn(W.startIf(b), grammar, input, target, ps, q, ks) == True{} : Bool}:
  match b:
    case True{}:
      +b0 = {Core.Bsr{q, 0n, ks, ks, ks} : Core.Bsr}
      %Equal.sym(Bool, List.is_empty(&2, Core.Sym, Core.rhsOf(grammar, q)), False{}, ne) : {Bool.and(Core.allIn(List.append(&2, Core.Bsr, WS.emptyIf(_, b0), []), ps), True{}) == True{} : Bool}
      {==}
    case False{}:
      {==}

def zero_in(e: Bool, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +ps: +List<Core.Bsr>, +q: Nat, +ks: Nat, +k: Nat, +F: +List<W.Fact>, +ee: {List.is_empty(&2, Core.Sym, Core.rhsOf(grammar, q)) == e : Bool},
  +hI: {factsIn(F, grammar, input, target, ps) == True{} : Bool})
  -> {optsIn(W.zeroOpts(e, q, ks, k, F), grammar, input, target, ps, q, ks) == True{} : Bool}:
  match e:
    case True{}:
      found_in(F, grammar, input, target, ps, q, ks, 0n, k, hI)
    case False{}:
      start_in(Nat.is_eq(ks, k), grammar, input, target, ps, q, ks, ee)

def opts_at_in(+grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +ps: +List<Core.Bsr>, +F: +List<W.Fact>, +q: Nat, +ks: Nat, d: Nat, +k: Nat, +hI: {factsIn(F, grammar, input, target, ps) == True{} : Bool})
  -> {optsIn(W.optsAt(grammar, target, q, ks, d, k, F), grammar, input, target, ps, q, ks) == True{} : Bool}:
  match d:
    case 0n:
      zero_in(List.is_empty(&2, Core.Sym, Core.rhsOf(grammar, q)), grammar, input, target, ps, q, ks, k, F, {==}, hI)
    case 1n+(+m):
      found_in(F, grammar, input, target, ps, q, ks, 1n+m, k, hI)

# ======== ITEM OPTIONS ========

def all_nil(+xs: +List<Core.Bsr>, +ps: +List<Core.Bsr>, +h: {Core.allIn(xs, ps) == True{} : Bool}) -> {Core.allIn(List.append(&2, Core.Bsr, xs, []), ps) == True{} : Bool}:
  G.all_in_app(xs, [], ps, h, {==})

def empty_rhs(+grammar: +List<Core.Production>, +ps: +List<Core.Bsr>, +index: Nat, +k: Nat, +ip: {Core.rhsOf(grammar, index) == [] : +List<Core.Sym>},
  +h: {Core.allIn(List.append(&2, Core.Bsr, WS.emptyIf(List.is_empty(&2, Core.Sym, Core.rhsOf(grammar, index)), Core.Bsr{index, 0n, k, k, k}), []), ps) == True{} : Bool})
  -> {Core.allIn(List.append(&2, Core.Bsr, WS.emptyIf(List.is_empty(&2, Core.Sym, []), Core.Bsr{index, 0n, k, k, k}), []), ps) == True{} : Bool}:
  %ip : {Core.allIn(List.append(&2, Core.Bsr, WS.emptyIf(List.is_empty(&2, Core.Sym, _), Core.Bsr{index, 0n, k, k, k}), []), ps) == True{} : Bool}
  h

def node_empty(items: +List<Core.Sym>, +grammar: +List<Core.Production>, +input: +List<Nat>, +ps: +List<Core.Bsr>, +index: Nat, +k: Nat,
  +ip: {Core.rhsOf(grammar, index) == items : +List<Core.Sym>},
  +r: {Core.reads([], grammar, items, input, k) == True{} : Bool},
  +h: {Core.allIn(List.append(&2, Core.Bsr, WS.emptyIf(List.is_empty(&2, Core.Sym, Core.rhsOf(grammar, index)), Core.Bsr{index, 0n, k, k, k}), []), ps) == True{} : Bool})
  -> {Core.allIn([Core.Bsr{index, 0n, k, k, k}], ps) == True{} : Bool}:
  match items:
    case Nil{}:
      empty_rhs(grammar, ps, index, k, ip, h)
    case Con{+y, +yr}:
      Empty.absurd({Core.allIn([Core.Bsr{index, 0n, k, k, k}], ps) == True{} : Bool}, Lemma.false_is_not_true(r))

# A whole-node option inside the steps gives a node all of whose steps are inside.
def node_in(fo: +List<Core.Tree>, +grammar: +List<Core.Production>, +input: +List<Nat>, +ps: +List<Core.Bsr>, +index: Nat, +k: Nat,
  +r: {Core.reads(fo, grammar, Core.rhsOf(grammar, index), input, k) == True{} : Bool},
  +h: {Core.allIn(WS.stepsP(grammar, index, fo, k), ps) == True{} : Bool})
  -> {Core.allIn(Core.steps([Core.Node{index, fo}], k), ps) == True{} : Bool}:
  match fo:
    case Nil{}:
      node_empty(Core.rhsOf(grammar, index), grammar, input, ps, index, k, {==}, r, h)
    case Con{+t1, +r1}:
      +own = WC.ownNE(index, t1 <> r1, 0n, k, k)
      +st = Core.steps(t1 <> r1, k)
      %Equal.sym(+List<Core.Bsr>, Core.own(index, t1 <> r1, 0n, k, k), own, WC.own_first(index, t1, r1, 0n, k, k)) : {Core.allIn(List.append(&2, Core.Bsr, _, List.append(&2, Core.Bsr, st, Core.steps([], Nat.add(k, Core.width(Core.Node{index, t1 <> r1}))))), ps) == True{} : Bool}
      G.all_in_app(own, List.append(&2, Core.Bsr, st, []), ps, PP.in_app_left(own, st, ps, h), all_nil(st, ps, PP.in_app_right(own, st, ps, h)))

law nodeopts_in:
  for os: +List<W.Opt>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +target: Core.Bsr
  for +ps: +List<Core.Bsr>
  for +index: Nat
  for +k: Nat
  for +j: Nat
  for +hO: {WS.optsOk(os, grammar, input, target, index, k, List.length(&2, Core.Sym, Core.rhsOf(grammar, index)), j) == True{} : Bool}
  for +hI: {optsIn(os, grammar, input, target, ps, index, k) == True{} : Bool}
  {itemsIn(W.nodeOpts(index, os), ps, k) == True{} : Bool}

def nodeopts_in(os, grammar, input, target, ps, index, k, j, hO, hI):
  match os:
    case Nil{}:
      {==}
    case Con{W.Opt{+fl, +fo}, +rest}:
      +L = List.length(&2, Core.Sym, Core.rhsOf(grammar, index))
      +po = {WS.prefOk(grammar, input, target, index, k, L, j, fl, fo) : Bool}
      +pi = {pIn(grammar, input, target, ps, index, k, fo) : Bool}
      +rd = WS.reads_all(grammar, input, fo, Core.rhsOf(grammar, index), k, Lemma.and_true_left(Core.reads(fo, grammar, WS.takeN(L, Core.rhsOf(grammar, index)), input, k), Bool.and(Nat.is_eq(G.endOf(fo, k), j), WS.flagOk(fl, target, WS.stepsP(grammar, index, fo, k))), Lemma.and_true_left(po, WS.optsOk(rest, grammar, input, target, index, k, L, j), hO)))
      Lemma.and_true_intro(Core.allIn(Core.steps([Core.Node{index, fo}], k), ps), itemsIn(W.nodeOpts(index, rest), ps, k),
        node_in(fo, grammar, input, ps, index, k, rd, Lemma.and_true_left(pi, optsIn(rest, grammar, input, target, ps, index, k), hI)),
        nodeopts_in(rest, grammar, input, target, ps, index, k, j, Lemma.and_true_right_side(po, WS.optsOk(rest, grammar, input, target, index, k, L, j), hO), Lemma.and_true_right_side(pi, optsIn(rest, grammar, input, target, ps, index, k), hI)))

law items_app_in:
  for xs: +List<W.Opt>
  for +ys: +List<W.Opt>
  for +ps: +List<Core.Bsr>
  for +k: Nat
  for +hx: {itemsIn(xs, ps, k) == True{} : Bool}
  for +hy: {itemsIn(ys, ps, k) == True{} : Bool}
  {itemsIn(List.append(&2, W.Opt, xs, ys), ps, k) == True{} : Bool}

def items_app_in(xs, ys, ps, k, hx, hy):
  match xs:
    case Nil{}:
      hy
    case Con{W.Opt{+fl, +fo}, +rest}:
      Lemma.and_true_intro(Core.allIn(Core.steps(fo, k), ps), itemsIn(List.append(&2, W.Opt, rest, ys), ps, k), Lemma.and_true_left(Core.allIn(Core.steps(fo, k), ps), itemsIn(rest, ps, k), hx),
        items_app_in(rest, ys, ps, k, Lemma.and_true_right_side(Core.allIn(Core.steps(fo, k), ps), itemsIn(rest, ps, k), hx), hy))

def pick_in(b: Bool, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +ps: +List<Core.Bsr>, +F: +List<W.Fact>, +base: Nat, +lhs: Nat, +rhs: +List<Core.Sym>, +rest: +List<Core.Production>, +k: Nat, +j: Nat,
  +hg: {G.dropProds(base, grammar) == Core.Production{lhs, rhs} <> rest : +List<Core.Production>},
  +hF: {WS.factsOk(F, grammar, input, target) == True{} : Bool}, +hI: {factsIn(F, grammar, input, target, ps) == True{} : Bool})
  -> {itemsIn(W.prodPick(b, grammar, target, base, List.length(&2, Core.Sym, rhs), k, j, F), ps, k) == True{} : Bool}:
  match b:
    case True{}:
      +os = W.optsAt(grammar, target, base, k, List.length(&2, Core.Sym, rhs), j, F)
      nodeopts_in(os, grammar, input, target, ps, base, k, j,
        WS.opts_len(grammar, input, target, os, base, lhs, rhs, rest, k, j, hg, WS.opts_at_ok(grammar, input, target, F, base, k, List.length(&2, Core.Sym, rhs), j, hF)),
        opts_at_in(grammar, input, target, ps, F, base, k, List.length(&2, Core.Sym, rhs), j, hI))
    case False{}:
      {==}

law prod_in:
  for g: +List<Core.Production>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +target: Core.Bsr
  for +ps: +List<Core.Bsr>
  for +F: +List<W.Fact>
  for +base: Nat
  for +x: Nat
  for +k: Nat
  for +j: Nat
  for +hg: {G.dropProds(base, grammar) == g : +List<Core.Production>}
  for +hF: {WS.factsOk(F, grammar, input, target) == True{} : Bool}
  for +hI: {factsIn(F, grammar, input, target, ps) == True{} : Bool}
  {itemsIn(W.prodOpts(g, grammar, target, base, x, k, j, F), ps, k) == True{} : Bool}

def prod_in(g, grammar, input, target, ps, F, base, x, k, j, hg, hF, hI):
  match g:
    case Nil{}:
      {==}
    case Con{Core.Production{+lhs, +rhs}, +rest}:
      items_app_in(W.prodPick(Nat.is_eq(lhs, x), grammar, target, base, List.length(&2, Core.Sym, rhs), k, j, F), W.prodOpts(rest, grammar, target, 1n+base, x, k, j, F), ps, k,
        pick_in(Nat.is_eq(lhs, x), grammar, input, target, ps, F, base, lhs, rhs, rest, k, j, hg, hF, hI),
        prod_in(rest, grammar, input, target, ps, F, 1n+base, x, k, j, G.drop_step(base, grammar, lhs, rhs, rest, hg), hF, hI))

def leaf_in(b: Bool, +t: Nat, +ps: +List<Core.Bsr>, +k: Nat) -> {itemsIn(W.leafIf(b, t), ps, k) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def need_in(b: Bool, +os: +List<W.Opt>, +ps: +List<Core.Bsr>, +k: Nat, +h: {itemsIn(os, ps, k) == True{} : Bool}) -> {itemsIn(W.needIf(b, os), ps, k) == True{} : Bool}:
  match b:
    case True{}:
      h
    case False{}:
      {==}

def items_at_in(y: Core.Sym, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +ps: +List<Core.Bsr>, +F: +List<W.Fact>, +k: Nat, +j: Nat,
  +hF: {WS.factsOk(F, grammar, input, target) == True{} : Bool}, +hI: {factsIn(F, grammar, input, target, ps) == True{} : Bool})
  -> {itemsIn(W.itemOpts(Some{y}, grammar, input, target, k, j, F), ps, k) == True{} : Bool}:
  match y:
    case Core.Terminal{+t}:
      leaf_in(Bool.and(Core.tokIs(Core.tokAt(input, k), t), Nat.is_eq(j, 1n+k)), t, ps, k)
    case Core.Nonterminal{+x, +need}:
      need_in(Gll.needHolds(need, k, j), W.prodOpts(grammar, grammar, target, 0n, x, k, j, F), ps, k,
        prod_in(grammar, grammar, input, target, ps, F, 0n, x, k, j, {==}, hF, hI))

# ======== JOINING A PREFIX AND AN ITEM ========

def ai_ownS_ne(fo: +List<Core.Tree>, +grammar: +List<Core.Production>, +q: Nat, +ks: Nat, +ps: +List<Core.Bsr>, +h: {Core.allIn(WS.ownS(grammar, q, fo, ks), ps) == True{} : Bool})
  -> {Core.allIn(WC.ownNE(q, fo, 0n, ks, ks), ps) == True{} : Bool}:
  match fo:
    case Nil{}:
      {==}
    case Con{+t, +rest}:
      h

def mem_zero(+q: Nat, +d: Nat, +ks: Nat, +k: Nat, +j: Nat, +ps: +List<Core.Bsr>, +h: {Core.member(Core.Bsr{q, 1n+Nat.add(d, 0n), ks, k, j}, ps) == True{} : Bool})
  -> {Core.member(Core.Bsr{q, 1n+d, ks, k, j}, ps) == True{} : Bool}:
  %Lemma.add_zero_right(d) : {Core.member(Core.Bsr{q, 1n+_, ks, k, j}, ps) == True{} : Bool}
  h

def mem_succ(+q: Nat, +d: Nat, +n: Nat, +ks: Nat, +k: Nat, +j: Nat, +ps: +List<Core.Bsr>, +h: {Core.member(Core.Bsr{q, 1n+Nat.add(d, 1n+n), ks, k, j}, ps) == True{} : Bool})
  -> {Core.member(Core.Bsr{q, 1n+Nat.add(1n+d, n), ks, k, j}, ps) == True{} : Bool}:
  %Lemma.add_succ_right(d, n) : {Core.member(Core.Bsr{q, 1n+_, ks, k, j}, ps) == True{} : Bool}
  h

law ai_own_snoc:
  for +q: Nat
  for f: +List<Core.Tree>
  for +t: Core.Tree
  for +d: Nat
  for +ks: Nat
  for +k: Nat
  for +ps: +List<Core.Bsr>
  for +h1: {Core.allIn(WC.ownNE(q, f, d, ks, k), ps) == True{} : Bool}
  for +h2: {Core.member(Core.Bsr{q, 1n+Nat.add(d, List.length(&2, Core.Tree, f)), ks, WS.endW(f, k), Nat.add(WS.endW(f, k), Core.width(t))}, ps) == True{} : Bool}
  {Core.allIn(WC.ownNE(q, List.append(&2, Core.Tree, f, [t]), d, ks, k), ps) == True{} : Bool}

def ai_own_snoc(q, f, t, d, ks, k, ps, h1, h2):
  match f:
    case Nil{}:
      Lemma.and_true_intro(Core.member(Core.Bsr{q, 1n+d, ks, k, Nat.add(k, Core.width(t))}, ps), True{}, mem_zero(q, d, ks, k, Nat.add(k, Core.width(t)), ps, h2), {==})
    case Con{+s, +rest}:
      +far = Nat.add(k, Core.width(s))
      +b = {Core.Bsr{q, 1n+d, ks, k, far} : Core.Bsr}
      Lemma.and_true_intro(Core.member(b, ps), Core.allIn(WC.ownNE(q, List.append(&2, Core.Tree, rest, [t]), 1n+d, ks, far), ps),
        Lemma.and_true_left(Core.member(b, ps), Core.allIn(WC.ownNE(q, rest, 1n+d, ks, far), ps), h1),
        ai_own_snoc(q, rest, t, 1n+d, ks, far, ps, Lemma.and_true_right_side(Core.member(b, ps), Core.allIn(WC.ownNE(q, rest, 1n+d, ks, far), ps), h1),
          mem_succ(q, d, List.length(&2, Core.Tree, rest), ks, WS.endW(rest, far), Nat.add(WS.endW(rest, far), Core.width(t)), ps, h2)))

law ai_steps_snoc:
  for f: +List<Core.Tree>
  for +t: Core.Tree
  for +k: Nat
  for +ps: +List<Core.Bsr>
  for +h1: {Core.allIn(Core.steps(f, k), ps) == True{} : Bool}
  for +h2: {Core.allIn(Core.steps([t], G.endOf(f, k)), ps) == True{} : Bool}
  {Core.allIn(Core.steps(List.append(&2, Core.Tree, f, [t]), k), ps) == True{} : Bool}

def ai_steps_snoc(f, t, k, ps, h1, h2):
  match f:
    case Nil{}:
      h2
    case Con{Core.Leaf{+a}, +ts}:
      ai_steps_snoc(ts, t, 1n+k, ps, h1, h2)
    case Con{Core.Node{+q, +ch}, +ts}:
      +o = Core.own(q, ch, 0n, k, k)
      +w = Nat.add(k, Core.width(Core.Node{q, ch}))
      +rest = List.append(&2, Core.Bsr, Core.steps(ch, k), Core.steps(ts, w))
      +hr = PP.in_app_right(o, rest, ps, h1)
      G.all_in_app(o, List.append(&2, Core.Bsr, Core.steps(ch, k), Core.steps(List.append(&2, Core.Tree, ts, [t]), w)), ps, PP.in_app_left(o, rest, ps, h1),
        G.all_in_app(Core.steps(ch, k), Core.steps(List.append(&2, Core.Tree, ts, [t]), w), ps, PP.in_app_left(Core.steps(ch, k), Core.steps(ts, w), ps, hr),
          ai_steps_snoc(ts, t, w, ps, PP.in_app_right(Core.steps(ch, k), Core.steps(ts, w), ps, hr), h2)))

def own_cons(fo: +List<Core.Tree>, +grammar: +List<Core.Production>, +q: Nat, +t: Core.Tree, +ks: Nat)
  -> {WS.ownS(grammar, q, List.append(&2, Core.Tree, fo, [t]), ks) == WC.ownNE(q, List.append(&2, Core.Tree, fo, [t]), 0n, ks, ks) : +List<Core.Bsr>}:
  match fo:
    case Nil{}:
      {==}
    case Con{+s, +rest}:
      {==}

def steps_to(+t: Core.Tree, +ps: +List<Core.Bsr>, +a: Nat, +b: Nat, +e: {a == b : Nat}, +h: {Core.allIn(Core.steps([t], b), ps) == True{} : Bool})
  -> {Core.allIn(Core.steps([t], a), ps) == True{} : Bool}:
  %Equal.sym(Nat, a, b, e) : {Core.allIn(Core.steps([t], _), ps) == True{} : Bool}
  h

def p_cons(+grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +ps: +List<Core.Bsr>, +q: Nat, +ks: Nat, +fo: +List<Core.Tree>, +t: Core.Tree,
  +h: {Core.allIn(List.append(&2, Core.Bsr, WC.ownNE(q, List.append(&2, Core.Tree, fo, [t]), 0n, ks, ks), Core.steps(List.append(&2, Core.Tree, fo, [t]), ks)), ps) == True{} : Bool})
  -> {pIn(grammar, input, target, ps, q, ks, List.append(&2, Core.Tree, fo, [t])) == True{} : Bool}:
  %Equal.sym(+List<Core.Bsr>, WS.ownS(grammar, q, List.append(&2, Core.Tree, fo, [t]), ks), WC.ownNE(q, List.append(&2, Core.Tree, fo, [t]), 0n, ks, ks), own_cons(fo, grammar, q, t, ks)) : {Core.allIn(List.append(&2, Core.Bsr, _, Core.steps(List.append(&2, Core.Tree, fo, [t]), ks)), ps) == True{} : Bool}
  h

# A prefix inside the steps and an item inside them, joined by a step of the set.
def one_in(+grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +ps: +List<Core.Bsr>, +f1: Bool, +fo: +List<Core.Tree>, +t: Core.Tree, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +j: Nat, +y: Core.Sym, +rest: +List<Core.Sym>,
  +ie: {G.dropFrom(d, Core.rhsOf(grammar, q)) == y <> rest : +List<Core.Sym>},
  +hp: {WS.prefOk(grammar, input, target, q, ks, d, k, f1, fo) == True{} : Bool},
  +hpi: {pIn(grammar, input, target, ps, q, ks, fo) == True{} : Bool},
  +ej0: {Nat.is_eq(G.endOf([t], k), j) == True{} : Bool},
  +hti: {Core.allIn(Core.steps([t], k), ps) == True{} : Bool}, +me: {Core.member(Core.Bsr{q, 1n+d, ks, k, j}, ps) == True{} : Bool})
  -> {pIn(grammar, input, target, ps, q, ks, List.append(&2, Core.Tree, fo, [t])) == True{} : Bool}:
  +R = {Core.reads(fo, grammar, WS.takeN(d, Core.rhsOf(grammar, q)), input, ks) : Bool}
  +E = {Nat.is_eq(G.endOf(fo, ks), k) : Bool}
  +Fl = {WS.flagOk(f1, target, WS.stepsP(grammar, q, fo, ks)) : Bool}
  +r1 = Lemma.and_true_left(R, Bool.and(E, Fl), hp)
  +ek = Lemma.nat_eq_sound(G.endOf(fo, ks), k, Lemma.and_true_left(E, Fl, Lemma.and_true_right_side(R, Bool.and(E, Fl), hp)))
  +ej = Lemma.nat_eq_sound(G.endOf([t], k), j, ej0)
  +len = Equal.trans(Nat, List.length(&2, Core.Tree, fo), List.length(&2, Core.Sym, WS.takeN(d, Core.rhsOf(grammar, q))), d, PP.reads_length(fo, WS.takeN(d, Core.rhsOf(grammar, q)), grammar, input, ks, r1), WS.take_len(d, Core.rhsOf(grammar, q), y, rest, ie))
  +ew = WS.endW(fo, ks)
  +eK = Equal.trans(Nat, ew, G.endOf(fo, ks), k, WS.end_w(fo, ks), ek)
  +eJ = Equal.trans(Nat, Nat.add(ew, Core.width(t)), Nat.add(k, Core.width(t)), j, Equal.cong(Nat, Nat, v => Nat.add(v, Core.width(t)), ew, k, eK),
    Equal.trans(Nat, Nat.add(k, Core.width(t)), G.endOf([t], k), j, Equal.sym(Nat, G.endOf([t], k), Nat.add(k, Core.width(t)), WS.end_one(t, k)), ej))
  +mb = WS.bsr_fields(q, d, List.length(&2, Core.Tree, fo), ks, k, ew, j, Nat.add(ew, Core.width(t)), ps,
    Equal.sym(Nat, List.length(&2, Core.Tree, fo), d, len), Equal.sym(Nat, ew, k, eK), Equal.sym(Nat, Nat.add(ew, Core.width(t)), j, eJ), me)
  +own0 = WS.ownS(grammar, q, fo, ks)
  +st0 = Core.steps(fo, ks)
  +f2 = List.append(&2, Core.Tree, fo, [t])
  p_cons(grammar, input, target, ps, q, ks, fo, t,
    G.all_in_app(WC.ownNE(q, f2, 0n, ks, ks), Core.steps(f2, ks), ps,
      ai_own_snoc(q, fo, t, 0n, ks, ks, ps, ai_ownS_ne(fo, grammar, q, ks, ps, PP.in_app_left(own0, st0, ps, hpi)), mb),
      ai_steps_snoc(fo, t, ks, ps, PP.in_app_right(own0, st0, ps, hpi), steps_to(t, ps, G.endOf(fo, ks), k, ek, hti))))

law with_in:
  for P: +List<W.Opt>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +target: Core.Bsr
  for +ps: +List<Core.Bsr>
  for +t: Core.Tree
  for +f2: Bool
  for +q: Nat
  for +ks: Nat
  for +d: Nat
  for +k: Nat
  for +j: Nat
  for +y: Core.Sym
  for +rest: +List<Core.Sym>
  for +ie: {G.dropFrom(d, Core.rhsOf(grammar, q)) == y <> rest : +List<Core.Sym>}
  for +hP: {WS.optsOk(P, grammar, input, target, q, ks, d, k) == True{} : Bool}
  for +hPi: {optsIn(P, grammar, input, target, ps, q, ks) == True{} : Bool}
  for +ej0: {Nat.is_eq(G.endOf([t], k), j) == True{} : Bool}
  for +hti: {Core.allIn(Core.steps([t], k), ps) == True{} : Bool}
  for +me: {Core.member(Core.Bsr{q, 1n+d, ks, k, j}, ps) == True{} : Bool}
  {optsIn(W.withTree(t, f2, P), grammar, input, target, ps, q, ks) == True{} : Bool}

def with_in(P, grammar, input, target, ps, t, f2, q, ks, d, k, j, y, rest, ie, hP, hPi, ej0, hti, me):
  match P:
    case Nil{}:
      {==}
    case Con{W.Opt{+f1, +fo}, +restP}:
      +po = {WS.prefOk(grammar, input, target, q, ks, d, k, f1, fo) : Bool}
      +pi = {pIn(grammar, input, target, ps, q, ks, fo) : Bool}
      Lemma.and_true_intro(pIn(grammar, input, target, ps, q, ks, List.append(&2, Core.Tree, fo, [t])), optsIn(W.withTree(t, f2, restP), grammar, input, target, ps, q, ks),
        one_in(grammar, input, target, ps, f1, fo, t, q, ks, d, k, j, y, rest, ie, Lemma.and_true_left(po, WS.optsOk(restP, grammar, input, target, q, ks, d, k), hP), Lemma.and_true_left(pi, optsIn(restP, grammar, input, target, ps, q, ks), hPi), ej0, hti, me),
        with_in(restP, grammar, input, target, ps, t, f2, q, ks, d, k, j, y, rest, ie, Lemma.and_true_right_side(po, WS.optsOk(restP, grammar, input, target, q, ks, d, k), hP), Lemma.and_true_right_side(pi, optsIn(restP, grammar, input, target, ps, q, ks), hPi), ej0, hti, me))

def join_one_in(fo2: +List<Core.Tree>, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +ps: +List<Core.Bsr>, +f2: Bool, +P: +List<W.Opt>, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +j: Nat, +y: Core.Sym, +rest: +List<Core.Sym>,
  +ie: {G.dropFrom(d, Core.rhsOf(grammar, q)) == y <> rest : +List<Core.Sym>},
  +hP: {WS.optsOk(P, grammar, input, target, q, ks, d, k) == True{} : Bool}, +hPi: {optsIn(P, grammar, input, target, ps, q, ks) == True{} : Bool},
  +hit: {WS.itemOk(grammar, input, target, y, k, j, f2, fo2) == True{} : Bool}, +hii: {Core.allIn(Core.steps(fo2, k), ps) == True{} : Bool}, +me: {Core.member(Core.Bsr{q, 1n+d, ks, k, j}, ps) == True{} : Bool})
  -> {optsIn(W.withTreeList(fo2, f2, P), grammar, input, target, ps, q, ks) == True{} : Bool}:
  match fo2:
    case Nil{}:
      {==}
    case Con{+t, Nil{}}:
      +R = {Core.reads([t], grammar, [y], input, k) : Bool}
      +E = {Nat.is_eq(G.endOf([t], k), j) : Bool}
      +Fl = {WS.flagOk(f2, target, Core.steps([t], k)) : Bool}
      with_in(P, grammar, input, target, ps, t, f2, q, ks, d, k, j, y, rest, ie, hP, hPi, Lemma.and_true_left(E, Fl, Lemma.and_true_right_side(R, Bool.and(E, Fl), hit)), hii, me)
    case Con{+t, Con{+t2, +more}}:
      {==}

law opts_app_in:
  for xs: +List<W.Opt>
  for +ys: +List<W.Opt>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +target: Core.Bsr
  for +ps: +List<Core.Bsr>
  for +q: Nat
  for +ks: Nat
  for +hx: {optsIn(xs, grammar, input, target, ps, q, ks) == True{} : Bool}
  for +hy: {optsIn(ys, grammar, input, target, ps, q, ks) == True{} : Bool}
  {optsIn(List.append(&2, W.Opt, xs, ys), grammar, input, target, ps, q, ks) == True{} : Bool}

def opts_app_in(xs, ys, grammar, input, target, ps, q, ks, hx, hy):
  match xs:
    case Nil{}:
      hy
    case Con{W.Opt{+fl, +fo}, +rest}:
      Lemma.and_true_intro(pIn(grammar, input, target, ps, q, ks, fo), optsIn(List.append(&2, W.Opt, rest, ys), grammar, input, target, ps, q, ks), Lemma.and_true_left(pIn(grammar, input, target, ps, q, ks, fo), optsIn(rest, grammar, input, target, ps, q, ks), hx),
        opts_app_in(rest, ys, grammar, input, target, ps, q, ks, Lemma.and_true_right_side(pIn(grammar, input, target, ps, q, ks, fo), optsIn(rest, grammar, input, target, ps, q, ks), hx), hy))

law join_in:
  for +P: +List<W.Opt>
  for I: +List<W.Opt>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +target: Core.Bsr
  for +ps: +List<Core.Bsr>
  for +q: Nat
  for +ks: Nat
  for +d: Nat
  for +k: Nat
  for +j: Nat
  for +y: Core.Sym
  for +rest: +List<Core.Sym>
  for +ie: {G.dropFrom(d, Core.rhsOf(grammar, q)) == y <> rest : +List<Core.Sym>}
  for +hP: {WS.optsOk(P, grammar, input, target, q, ks, d, k) == True{} : Bool}
  for +hPi: {optsIn(P, grammar, input, target, ps, q, ks) == True{} : Bool}
  for +hI: {WS.itemsOk(I, grammar, input, target, y, k, j) == True{} : Bool}
  for +hIi: {itemsIn(I, ps, k) == True{} : Bool}
  for +me: {Core.member(Core.Bsr{q, 1n+d, ks, k, j}, ps) == True{} : Bool}
  {optsIn(W.joinAll(P, I), grammar, input, target, ps, q, ks) == True{} : Bool}

def join_in(P, I, grammar, input, target, ps, q, ks, d, k, j, y, rest, ie, hP, hPi, hI, hIi, me):
  match I:
    case Nil{}:
      {==}
    case Con{W.Opt{+f2, +fo2}, +restI}:
      +io = {WS.itemOk(grammar, input, target, y, k, j, f2, fo2) : Bool}
      +ii = {Core.allIn(Core.steps(fo2, k), ps) : Bool}
      opts_app_in(W.withTreeList(fo2, f2, P), W.joinAll(P, restI), grammar, input, target, ps, q, ks,
        join_one_in(fo2, grammar, input, target, ps, f2, P, q, ks, d, k, j, y, rest, ie, hP, hPi, Lemma.and_true_left(io, WS.itemsOk(restI, grammar, input, target, y, k, j), hI), Lemma.and_true_left(ii, itemsIn(restI, ps, k), hIi), me),
        join_in(P, restI, grammar, input, target, ps, q, ks, d, k, j, y, rest, ie, hP, hPi, Lemma.and_true_right_side(io, WS.itemsOk(restI, grammar, input, target, y, k, j), hI), Lemma.and_true_right_side(ii, itemsIn(restI, ps, k), hIi), me))

law mark_in:
  for os: +List<W.Opt>
  for +here: Bool
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +target: Core.Bsr
  for +ps: +List<Core.Bsr>
  for +q: Nat
  for +ks: Nat
  for +h: {optsIn(os, grammar, input, target, ps, q, ks) == True{} : Bool}
  {optsIn(W.markIf(here, os), grammar, input, target, ps, q, ks) == True{} : Bool}

def mark_in(os, here, grammar, input, target, ps, q, ks, h):
  match os:
    case Nil{}:
      {==}
    case Con{W.Opt{+f, +fo}, +rest}:
      Lemma.and_true_intro(pIn(grammar, input, target, ps, q, ks, fo), optsIn(W.markIf(here, rest), grammar, input, target, ps, q, ks), Lemma.and_true_left(pIn(grammar, input, target, ps, q, ks, fo), optsIn(rest, grammar, input, target, ps, q, ks), h),
        mark_in(rest, here, grammar, input, target, ps, q, ks, Lemma.and_true_right_side(pIn(grammar, input, target, ps, q, ks, fo), optsIn(rest, grammar, input, target, ps, q, ks), h)))

law facts_of_in:
  for os: +List<W.Opt>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +target: Core.Bsr
  for +ps: +List<Core.Bsr>
  for +q: Nat
  for +ks: Nat
  for +dt: Nat
  for +e: Nat
  for +h: {optsIn(os, grammar, input, target, ps, q, ks) == True{} : Bool}
  {factsIn(W.factsOf(q, ks, dt, e, os), grammar, input, target, ps) == True{} : Bool}

def facts_of_in(os, grammar, input, target, ps, q, ks, dt, e, h):
  match os:
    case Nil{}:
      {==}
    case Con{W.Opt{+fl, +fo}, +rest}:
      Lemma.and_true_intro(pIn(grammar, input, target, ps, q, ks, fo), factsIn(W.factsOf(q, ks, dt, e, rest), grammar, input, target, ps), Lemma.and_true_left(pIn(grammar, input, target, ps, q, ks, fo), optsIn(rest, grammar, input, target, ps, q, ks), h),
        facts_of_in(rest, grammar, input, target, ps, q, ks, dt, e, Lemma.and_true_right_side(pIn(grammar, input, target, ps, q, ks, fo), optsIn(rest, grammar, input, target, ps, q, ks), h)))

def join_item_in(item: Maybe<&2, Core.Sym>, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +ps: +List<Core.Bsr>, +F: +List<W.Fact>, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +j: Nat,
  +hF: {WS.factsOk(F, grammar, input, target) == True{} : Bool}, +hI: {factsIn(F, grammar, input, target, ps) == True{} : Bool},
  +ei: {Gll.nthSym(Core.rhsOf(grammar, q), d) == item : Maybe<&2, Core.Sym>}, +me: {Core.member(Core.Bsr{q, 1n+d, ks, k, j}, ps) == True{} : Bool})
  -> {optsIn(W.joinAll(W.optsAt(grammar, target, q, ks, d, k, F), W.itemOpts(item, grammar, input, target, k, j, F)), grammar, input, target, ps, q, ks) == True{} : Bool}:
  match item:
    case Some{+y}:
      join_in(W.optsAt(grammar, target, q, ks, d, k, F), W.itemOpts(Some{y}, grammar, input, target, k, j, F), grammar, input, target, ps, q, ks, d, k, j, y, G.dropFrom(1n+d, Core.rhsOf(grammar, q)), WS.nth_rev(Core.rhsOf(grammar, q), d, y, ei),
        WS.opts_at_ok(grammar, input, target, F, q, ks, d, k, hF), opts_at_in(grammar, input, target, ps, F, q, ks, d, k, hI),
        WS.items_at(y, grammar, input, target, F, k, j, hF), items_at_in(y, grammar, input, target, ps, F, k, j, hF, hI), me)
    case None{}:
      {==}

# ======== ONE STEP, ONE ROUND, THE FIXPOINT ========

def zmem(+q: Nat, +ks: Nat, +k: Nat, +j: Nat, +ps: +List<Core.Bsr>, +e1: {ks == k : Nat}, +e2: {k == j : Nat},
  +h: {Core.member(Core.Bsr{q, 0n, ks, k, j}, ps) == True{} : Bool}) -> {Core.member(Core.Bsr{q, 0n, ks, ks, ks}, ps) == True{} : Bool}:
  %Equal.sym(Nat, ks, k, e1) : {Core.member(Core.Bsr{q, 0n, ks, _, _}, ps) == True{} : Bool}
  %Equal.sym(Nat, k, j, e2) : {Core.member(Core.Bsr{q, 0n, ks, k, _}, ps) == True{} : Bool}
  h

def zp_in(+grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +ps: +List<Core.Bsr>, +q: Nat, +ks: Nat, +ee: {List.is_empty(&2, Core.Sym, Core.rhsOf(grammar, q)) == True{} : Bool},
  +m: {Core.member(Core.Bsr{q, 0n, ks, ks, ks}, ps) == True{} : Bool}) -> {pIn(grammar, input, target, ps, q, ks, []) == True{} : Bool}:
  %Equal.sym(Bool, List.is_empty(&2, Core.Sym, Core.rhsOf(grammar, q)), True{}, ee) : {Core.allIn(List.append(&2, Core.Bsr, WS.emptyIf(_, Core.Bsr{q, 0n, ks, ks, ks}), []), ps) == True{} : Bool}
  Lemma.and_true_intro(Core.member(Core.Bsr{q, 0n, ks, ks, ks}, ps), True{}, m, {==})

def zero_facts_in(b: Bool, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +ps: +List<Core.Bsr>, +q: Nat, +ks: Nat, +k: Nat, +j: Nat, +fl: Bool,
  +eb: {Bool.and(List.is_empty(&2, Core.Sym, Core.rhsOf(grammar, q)), Bool.and(Nat.is_eq(ks, k), Nat.is_eq(k, j))) == b : Bool},
  +me: {Core.member(Core.Bsr{q, 0n, ks, k, j}, ps) == True{} : Bool})
  -> {factsIn(W.zeroFacts(b, q, ks, j, fl), grammar, input, target, ps) == True{} : Bool}:
  match b:
    case True{}:
      +E = {List.is_empty(&2, Core.Sym, Core.rhsOf(grammar, q)) : Bool}
      +r = Lemma.and_true_right_side(E, Bool.and(Nat.is_eq(ks, k), Nat.is_eq(k, j)), eb)
      Lemma.and_true_intro(pIn(grammar, input, target, ps, q, ks, []), True{},
        zp_in(grammar, input, target, ps, q, ks, Lemma.and_true_left(E, Bool.and(Nat.is_eq(ks, k), Nat.is_eq(k, j)), eb),
          zmem(q, ks, k, j, ps, Lemma.nat_eq_sound(ks, k, Lemma.and_true_left(Nat.is_eq(ks, k), Nat.is_eq(k, j), r)), Lemma.nat_eq_sound(k, j, Lemma.and_true_right_side(Nat.is_eq(ks, k), Nat.is_eq(k, j), r)), me)), {==})
    case False{}:
      {==}

# The facts a step of the set makes from facts inside it are inside it.
def step_in(+grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +ps: +List<Core.Bsr>, +F: +List<W.Fact>, e: Core.Bsr, +me: {Core.member(e, ps) == True{} : Bool},
  +hF: {WS.factsOk(F, grammar, input, target) == True{} : Bool}, +hI: {factsIn(F, grammar, input, target, ps) == True{} : Bool})
  -> {factsIn(W.stepFacts(grammar, input, target, F, e), grammar, input, target, ps) == True{} : Bool}:
  match e:
    case Core.Bsr{+q, 0n, +ks, +k, +j}:
      zero_facts_in(Bool.and(List.is_empty(&2, Core.Sym, Core.rhsOf(grammar, q)), Bool.and(Nat.is_eq(ks, k), Nat.is_eq(k, j))), grammar, input, target, ps, q, ks, k, j, Core.bsrEq(Core.Bsr{q, 0n, ks, k, j}, target), {==}, me)
    case Core.Bsr{+q, 1n+(+d), +ks, +k, +j}:
      +os = W.joinAll(W.optsAt(grammar, target, q, ks, d, k, F), W.itemOpts(Gll.nthSym(Core.rhsOf(grammar, q), d), grammar, input, target, k, j, F))
      facts_of_in(W.markIf(Core.bsrEq(Core.Bsr{q, 1n+d, ks, k, j}, target), os), grammar, input, target, ps, q, ks, 1n+d, j,
        mark_in(os, Core.bsrEq(Core.Bsr{q, 1n+d, ks, k, j}, target), grammar, input, target, ps, q, ks, join_item_in(Gll.nthSym(Core.rhsOf(grammar, q), d), grammar, input, target, ps, F, q, ks, d, k, j, hF, hI, {==}, me)))

def fact_cons(f: W.Fact, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +ps: +List<Core.Bsr>, +F: +List<W.Fact>, +hf: {factsIn([f], grammar, input, target, ps) == True{} : Bool}, +hI: {factsIn(F, grammar, input, target, ps) == True{} : Bool}) -> {factsIn(f <> F, grammar, input, target, ps) == True{} : Bool}:
  match f:
    case W.Fact{+q, +ks, +d, +e, +fl, +fo}:
      Lemma.and_true_intro(pIn(grammar, input, target, ps, q, ks, fo), factsIn(F, grammar, input, target, ps), Lemma.and_true_left(pIn(grammar, input, target, ps, q, ks, fo), True{}, hf), hI)

def pick_in2(have: Bool, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +ps: +List<Core.Bsr>, +f: W.Fact, +F: +List<W.Fact>, +hf: {factsIn([f], grammar, input, target, ps) == True{} : Bool}, +hI: {factsIn(F, grammar, input, target, ps) == True{} : Bool})
  -> {factsIn(W.addPick(have, f, F), grammar, input, target, ps) == True{} : Bool}:
  match have:
    case True{}:
      hI
    case False{}:
      fact_cons(f, grammar, input, target, ps, F, hf, hI)

law add_in:
  for new: +List<W.Fact>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +target: Core.Bsr
  for +ps: +List<Core.Bsr>
  for +F: +List<W.Fact>
  for +hn: {factsIn(new, grammar, input, target, ps) == True{} : Bool}
  for +hI: {factsIn(F, grammar, input, target, ps) == True{} : Bool}
  {factsIn(W.addNew(new, F), grammar, input, target, ps) == True{} : Bool}

def add_in(new, grammar, input, target, ps, F, hn, hI):
  match new:
    case Nil{}:
      hI
    case Con{W.Fact{+q, +ks, +d, +e, +f, +fo}, +rest}:
      +p = {pIn(grammar, input, target, ps, q, ks, fo) : Bool}
      add_in(rest, grammar, input, target, ps, W.addPick(W.hasFact(q, ks, d, e, f, F), W.Fact{q, ks, d, e, f, fo}, F), Lemma.and_true_right_side(p, factsIn(rest, grammar, input, target, ps), hn),
        pick_in2(W.hasFact(q, ks, d, e, f, F), grammar, input, target, ps, W.Fact{q, ks, d, e, f, fo}, F, Lemma.and_true_intro(p, True{}, Lemma.and_true_left(p, factsIn(rest, grammar, input, target, ps), hn), {==}), hI))

law round_in:
  for xs: +List<Core.Bsr>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +target: Core.Bsr
  for +ps: +List<Core.Bsr>
  for +F: +List<W.Fact>
  for +sub: {Core.allIn(xs, ps) == True{} : Bool}
  for +hF: {WS.factsOk(F, grammar, input, target) == True{} : Bool}
  for +hI: {factsIn(F, grammar, input, target, ps) == True{} : Bool}
  {factsIn(W.roundOf(xs, grammar, input, target, F), grammar, input, target, ps) == True{} : Bool}

def round_in(xs, grammar, input, target, ps, F, sub, hF, hI):
  match xs:
    case Nil{}:
      hI
    case Con{+e, +rest}:
      +sf = W.stepFacts(grammar, input, target, F, e)
      round_in(rest, grammar, input, target, ps, W.addNew(sf, F), Lemma.and_true_right_side(Core.member(e, ps), Core.allIn(rest, ps), sub),
        WS.add_ok(sf, grammar, input, target, F, WS.step_ok(grammar, input, target, F, e, hF), hF),
        add_in(sf, grammar, input, target, ps, F, step_in(grammar, input, target, ps, F, e, Lemma.and_true_left(Core.member(e, ps), Core.allIn(rest, ps), sub), hF, hI), hI))

law grow_in:
  for fuel: Nat
  for done: Bool
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +target: Core.Bsr
  for +ps: +List<Core.Bsr>
  for +F: +List<W.Fact>
  for +hF: {WS.factsOk(F, grammar, input, target) == True{} : Bool}
  for +hI: {factsIn(F, grammar, input, target, ps) == True{} : Bool}
  {factsIn(W.grow(fuel, done, ps, grammar, input, target, F), grammar, input, target, ps) == True{} : Bool}

def grow_in(fuel, done, grammar, input, target, ps, F, hF, hI):
  match fuel:
    case 0n:
      hI
    case 1n+(+f):
      match done:
        case True{}:
          hI
        case False{}:
          grow_in(f, W.closedW(ps, grammar, input, target, W.roundOf(ps, grammar, input, target, F)), grammar, input, target, ps, W.roundOf(ps, grammar, input, target, F), WS.round_ok(ps, grammar, input, target, F, hF), round_in(ps, grammar, input, target, ps, F, C.step_refl(ps), hF, hI))

law fix_in:
  for fuel: Nat
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +target: Core.Bsr
  for +ps: +List<Core.Bsr>
  for +F: +List<W.Fact>
  for +hF: {WS.factsOk(F, grammar, input, target) == True{} : Bool}
  for +hI: {factsIn(F, grammar, input, target, ps) == True{} : Bool}
  {factsIn(W.fixpoint(fuel, ps, grammar, input, target, F), grammar, input, target, ps) == True{} : Bool}

def fix_in(fuel, grammar, input, target, ps, F, hF, hI):
  grow_in(fuel, W.closedW(ps, grammar, input, target, F), grammar, input, target, ps, F, hF, hI)

# ======== WHAT THE SEARCH HANDS OUT ========

def treesIn(fs: +List<Core.Tree>, +ps: +List<Core.Bsr>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case Con{+t, rest}:
      Bool.and(Core.allIn(Core.steps([t], 0n), ps), treesIn(rest, ps))

def rootIn(m: Maybe<&2, +List<Core.Tree>>, +ps: +List<Core.Bsr>) -> Bool:
  match m:
    case Some{+fs}:
      treesIn(fs, ps)
    case None{}:
      True{}

def fp_in(fl: Bool, +t: Core.Tree, +later: Maybe<&2, +List<Core.Tree>>, +ps: +List<Core.Bsr>,
  +ht: {Core.allIn(Core.steps([t], 0n), ps) == True{} : Bool}, +hr: {rootIn(later, ps) == True{} : Bool})
  -> {rootIn(W.flaggedPick(fl, [t], later), ps) == True{} : Bool}:
  match fl:
    case True{}:
      Lemma.and_true_intro(Core.allIn(Core.steps([t], 0n), ps), True{}, ht, {==})
    case False{}:
      hr

law first_in:
  for os: +List<W.Opt>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +target: Core.Bsr
  for +ps: +List<Core.Bsr>
  for +index: Nat
  for +hO: {WS.optsOk(os, grammar, input, target, index, 0n, List.length(&2, Core.Sym, Core.rhsOf(grammar, index)), List.length(&2, Nat, input)) == True{} : Bool}
  for +hOi: {optsIn(os, grammar, input, target, ps, index, 0n) == True{} : Bool}
  {rootIn(W.firstFlagged(W.nodeOpts(index, os)), ps) == True{} : Bool}

def first_in(os, grammar, input, target, ps, index, hO, hOi):
  match os:
    case Nil{}:
      {==}
    case Con{W.Opt{+fl, +fo}, +rest}:
      +L = List.length(&2, Core.Sym, Core.rhsOf(grammar, index))
      +po = {WS.prefOk(grammar, input, target, index, 0n, L, List.length(&2, Nat, input), fl, fo) : Bool}
      +pi = {pIn(grammar, input, target, ps, index, 0n, fo) : Bool}
      +rd = WS.reads_all(grammar, input, fo, Core.rhsOf(grammar, index), 0n, Lemma.and_true_left(Core.reads(fo, grammar, WS.takeN(L, Core.rhsOf(grammar, index)), input, 0n), Bool.and(Nat.is_eq(G.endOf(fo, 0n), List.length(&2, Nat, input)), WS.flagOk(fl, target, WS.stepsP(grammar, index, fo, 0n))), Lemma.and_true_left(po, WS.optsOk(rest, grammar, input, target, index, 0n, L, List.length(&2, Nat, input)), hO)))
      fp_in(fl, Core.Node{index, fo}, W.firstFlagged(W.nodeOpts(index, rest)), ps,
        node_in(fo, grammar, input, ps, index, 0n, rd, Lemma.and_true_left(pi, optsIn(rest, grammar, input, target, ps, index, 0n), hOi)),
        first_in(rest, grammar, input, target, ps, index, Lemma.and_true_right_side(po, WS.optsOk(rest, grammar, input, target, index, 0n, L, List.length(&2, Nat, input)), hO), Lemma.and_true_right_side(pi, optsIn(rest, grammar, input, target, ps, index, 0n), hOi)))

def root_pick_in(b: Bool, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +ps: +List<Core.Bsr>, +F: +List<W.Fact>, +base: Nat, +lhs: Nat, +rhs: +List<Core.Sym>, +rest: +List<Core.Production>,
  +hg: {G.dropProds(base, grammar) == Core.Production{lhs, rhs} <> rest : +List<Core.Production>},
  +hF: {WS.factsOk(F, grammar, input, target) == True{} : Bool}, +hI: {factsIn(F, grammar, input, target, ps) == True{} : Bool})
  -> {rootIn(W.rootPick(b, grammar, target, base, List.length(&2, Core.Sym, rhs), List.length(&2, Nat, input), F), ps) == True{} : Bool}:
  match b:
    case True{}:
      +os = W.optsAt(grammar, target, base, 0n, List.length(&2, Core.Sym, rhs), List.length(&2, Nat, input), F)
      first_in(os, grammar, input, target, ps, base,
        WS.opts_len(grammar, input, target, os, base, lhs, rhs, rest, 0n, List.length(&2, Nat, input), hg, WS.opts_at_ok(grammar, input, target, F, base, 0n, List.length(&2, Core.Sym, rhs), List.length(&2, Nat, input), hF)),
        opts_at_in(grammar, input, target, ps, F, base, 0n, List.length(&2, Core.Sym, rhs), List.length(&2, Nat, input), hI))
    case False{}:
      {==}

def or_else_in(a: Maybe<&2, +List<Core.Tree>>, +b: Maybe<&2, +List<Core.Tree>>, +ps: +List<Core.Bsr>, +ha: {rootIn(a, ps) == True{} : Bool}, +hb: {rootIn(b, ps) == True{} : Bool})
  -> {rootIn(W.orElse(a, b), ps) == True{} : Bool}:
  match a:
    case Some{+x}:
      ha
    case None{}:
      hb

law root_in:
  for g: +List<Core.Production>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +target: Core.Bsr
  for +ps: +List<Core.Bsr>
  for +F: +List<W.Fact>
  for +base: Nat
  for +start: Nat
  for +hg: {G.dropProds(base, grammar) == g : +List<Core.Production>}
  for +hF: {WS.factsOk(F, grammar, input, target) == True{} : Bool}
  for +hI: {factsIn(F, grammar, input, target, ps) == True{} : Bool}
  {rootIn(W.rootFor(g, grammar, target, base, start, List.length(&2, Nat, input), F), ps) == True{} : Bool}

def root_in(g, grammar, input, target, ps, F, base, start, hg, hF, hI):
  match g:
    case Nil{}:
      {==}
    case Con{Core.Production{+lhs, +rhs}, +rest}:
      or_else_in(W.rootPick(Nat.is_eq(lhs, start), grammar, target, base, List.length(&2, Core.Sym, rhs), List.length(&2, Nat, input), F), W.rootFor(rest, grammar, target, 1n+base, start, List.length(&2, Nat, input), F), ps,
        root_pick_in(Nat.is_eq(lhs, start), grammar, input, target, ps, F, base, lhs, rhs, rest, hg, hF, hI),
        root_in(rest, grammar, input, target, ps, F, 1n+base, start, G.drop_step(base, grammar, lhs, rhs, rest, hg), hF, hI))

# THE WITNESS SEARCH STAYS INSIDE: whatever it hands out uses only the given steps.
law witness_in:
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +ps: +List<Core.Bsr>
  for +target: Core.Bsr
  {rootIn(W.witnessFor(fuel, grammar, start, input, ps, target), ps) == True{} : Bool}

def witness_in(fuel, grammar, start, input, ps, target):
  +F = W.fixpoint(fuel, ps, grammar, input, target, [])
  root_in(grammar, grammar, input, target, ps, F, 0n, start, {==}, WS.fix_ok(fuel, ps, grammar, input, target, [], {==}), fix_in(fuel, grammar, input, target, ps, [], {==}, {==}))

def aw_fs(fs: +List<Core.Tree>, +ws: +List<Core.Tree>, +ps: +List<Core.Bsr>, +hm: {treesIn(fs, ps) == True{} : Bool}, +hw: {treesIn(ws, ps) == True{} : Bool})
  -> {treesIn(W.addWitness(Some{fs}, ws), ps) == True{} : Bool}:
  match fs:
    case Nil{}:
      hw
    case Con{+t, Nil{}}:
      Lemma.and_true_intro(Core.allIn(Core.steps([t], 0n), ps), treesIn(ws, ps), Lemma.and_true_left(Core.allIn(Core.steps([t], 0n), ps), True{}, hm), hw)
    case Con{+t, Con{+t2, +more}}:
      hw

def aw_in(m: Maybe<&2, +List<Core.Tree>>, +ws: +List<Core.Tree>, +ps: +List<Core.Bsr>, +hm: {rootIn(m, ps) == True{} : Bool}, +hw: {treesIn(ws, ps) == True{} : Bool})
  -> {treesIn(W.addWitness(m, ws), ps) == True{} : Bool}:
  match m:
    case Some{+fs}:
      aw_fs(fs, ws, ps, hm, hw)
    case None{}:
      hw

def cp_in(b: Bool, +fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +ps: +List<Core.Bsr>, +e: Core.Bsr, +ws: +List<Core.Tree>, +hw: {treesIn(ws, ps) == True{} : Bool})
  -> {treesIn(W.coverPick(b, fuel, grammar, start, input, ps, e, ws), ps) == True{} : Bool}:
  match b:
    case True{}:
      hw
    case False{}:
      aw_in(W.witnessFor(fuel, grammar, start, input, ps, e), ws, ps, witness_in(fuel, grammar, start, input, ps, e), hw)

# THE COVER LOOP STAYS INSIDE: every tree it hands out uses only the given steps.
law cover_in:
  for todo: +List<Core.Bsr>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +ps: +List<Core.Bsr>
  for +ws: +List<Core.Tree>
  for +hw: {treesIn(ws, ps) == True{} : Bool}
  {treesIn(W.cover(todo, fuel, grammar, start, input, ps, ws), ps) == True{} : Bool}

def cover_in(todo, fuel, grammar, start, input, ps, ws, hw):
  match todo:
    case Nil{}:
      hw
    case Con{+e, +rest}:
      cover_in(rest, fuel, grammar, start, input, ps, W.coverPick(W.coveredBy(e, ws), fuel, grammar, start, input, ps, e, ws),
        cp_in(W.coveredBy(e, ws), fuel, grammar, start, input, ps, e, ws, hw))

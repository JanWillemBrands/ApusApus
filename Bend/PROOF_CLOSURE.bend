import Base
import ./LEMMAS.bend as Lemma
import ./CORE.bend as Core
import ./GLL.bend as Gll
import ./CLOSURE.bend as C
import ./PROOF_GLL.bend as G
import ./RUN.bend as Run
import ./PROOF_COUNT.bend as PC
import ./PROOF_RUN.bend as RN
import ./PROOF_WSOUND.bend as WS

# THE CLOSURE DECIDES DERIVATION (CLOSURE.bend). When the segments are closed, every forest
# that reads the rest of a node's items from a segment completes the node in a segment
# (`walk`): a closed set with q's start and without q's whole segment over w shows that q
# does not derive w. With enough rounds the segments end closed (`closure_closed`), and
# every segment's forest reads its prefix of items (`closure_sound`).

# ======== WHAT A CLOSED SET SAYS AT ONE OF ITS SEGMENTS ========

law when_use:
  for b: Bool
  for -c: Bool
  for +h: {C.whenB(b, c) == True{} : Bool}
  for +hb: {b == True{} : Bool}
  {c == True{} : Bool}

def when_use(b, c, h, hb):
  match b:
    case True{}:
      h
    case False{}:
      Empty.absurd({c == True{} : Bool}, Lemma.false_is_not_true(hb))

def ext_moved(+grammar: +List<Core.Production>, +input: +List<Nat>, +segs: +List<C.Seg>,
  +q2: Nat, +ks2: Nat, +d2: Nat, +k2: Nat, +q: Nat, +ks: Nat, +d: Nat, +k: Nat,
  +eq: {q2 == q : Nat}, +eks: {ks2 == ks : Nat}, +ed: {d2 == d : Nat}, +ek: {k2 == k : Nat},
  +h: {C.extOk(Gll.nthSym(Core.rhsOf(grammar, q2), d2), grammar, input, segs, q2, ks2, d2, k2) == True{} : Bool})
  -> {C.extOk(Gll.nthSym(Core.rhsOf(grammar, q), d), grammar, input, segs, q, ks, d, k) == True{} : Bool}:
  %eq : {C.extOk(Gll.nthSym(Core.rhsOf(grammar, _), d), grammar, input, segs, _, ks, d, k) == True{} : Bool}
  %eks : {C.extOk(Gll.nthSym(Core.rhsOf(grammar, q2), d), grammar, input, segs, q2, _, d, k) == True{} : Bool}
  %ed : {C.extOk(Gll.nthSym(Core.rhsOf(grammar, q2), _), grammar, input, segs, q2, ks2, _, k) == True{} : Bool}
  %ek : {C.extOk(Gll.nthSym(Core.rhsOf(grammar, q2), d2), grammar, input, segs, q2, ks2, d2, _) == True{} : Bool}
  h

def ext_pick(+q2: Nat, +ks2: Nat, +d2: Nat, +k2: Nat, +fo: +List<Core.Tree>, +rest: +List<C.Seg>, +grammar: +List<Core.Production>, +input: +List<Nat>, +segs: +List<C.Seg>,
  +q: Nat, +ks: Nat, +d: Nat, +k: Nat,
  +hh: {C.extOk(Gll.nthSym(Core.rhsOf(grammar, q2), d2), grammar, input, segs, q2, ks2, d2, k2) == True{} : Bool},
  cases: Either<{C.keyIs(q, ks, d, k, C.Seg{q2, ks2, d2, k2, fo}) == True{} : Bool}, {C.hasSeg(q, ks, d, k, rest) == True{} : Bool}>,
  later: {C.hasSeg(q, ks, d, k, rest) == True{} : Bool} -> {C.extOk(Gll.nthSym(Core.rhsOf(grammar, q), d), grammar, input, segs, q, ks, d, k) == True{} : Bool})
  -> {C.extOk(Gll.nthSym(Core.rhsOf(grammar, q), d), grammar, input, segs, q, ks, d, k) == True{} : Bool}:
  match cases:
    case Inl{+e}:
      +r1 = {Bool.and(Nat.is_eq(ks2, ks), Bool.and(Nat.is_eq(d2, d), Nat.is_eq(k2, k))) : Bool}
      +r2 = {Bool.and(Nat.is_eq(d2, d), Nat.is_eq(k2, k)) : Bool}
      +t1 = Lemma.and_true_right_side(Nat.is_eq(q2, q), r1, e)
      +t2 = Lemma.and_true_right_side(Nat.is_eq(ks2, ks), r2, t1)
      ext_moved(grammar, input, segs, q2, ks2, d2, k2, q, ks, d, k,
        Lemma.nat_eq_sound(q2, q, Lemma.and_true_left(Nat.is_eq(q2, q), r1, e)),
        Lemma.nat_eq_sound(ks2, ks, Lemma.and_true_left(Nat.is_eq(ks2, ks), r2, t1)),
        Lemma.nat_eq_sound(d2, d, Lemma.and_true_left(Nat.is_eq(d2, d), Nat.is_eq(k2, k), t2)),
        Lemma.nat_eq_sound(k2, k, Lemma.and_true_right_side(Nat.is_eq(d2, d), Nat.is_eq(k2, k), t2)), hh)
    case Inr{m}:
      later(m)

# A segment of a closed set lets its next item be read.
law ext_of:
  for ss: +List<C.Seg>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +segs: +List<C.Seg>
  for +q: Nat
  for +ks: Nat
  for +d: Nat
  for +k: Nat
  for +cl: {C.closedAll(ss, grammar, input, segs) == True{} : Bool}
  for +h: {C.hasSeg(q, ks, d, k, ss) == True{} : Bool}
  {C.extOk(Gll.nthSym(Core.rhsOf(grammar, q), d), grammar, input, segs, q, ks, d, k) == True{} : Bool}

def ext_of(ss, grammar, input, segs, q, ks, d, k, cl, h):
  match ss:
    case Nil{}:
      Empty.absurd({C.extOk(Gll.nthSym(Core.rhsOf(grammar, q), d), grammar, input, segs, q, ks, d, k) == True{} : Bool}, Lemma.false_is_not_true(h))
    case Con{C.Seg{+q2, +ks2, +d2, +k2, +fo}, +rest}:
      +here = {C.extOk(Gll.nthSym(Core.rhsOf(grammar, q2), d2), grammar, input, segs, q2, ks2, d2, k2) : Bool}
      +more = {C.closedAll(rest, grammar, input, segs) : Bool}
      ext_pick(q2, ks2, d2, k2, fo, rest, grammar, input, segs, q, ks, d, k, Lemma.and_true_left(here, more, cl),
        Lemma.or_true_cases(C.keyIs(q, ks, d, k, C.Seg{q2, ks2, d2, k2, fo}), C.hasSeg(q, ks, d, k, rest), h),
        m => ext_of(rest, grammar, input, segs, q, ks, d, k, Lemma.and_true_right_side(here, more, cl), m))

def comp_moved(+segs: +List<C.Seg>, +need: Core.Need, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +e2: Nat, +e: Nat, +ee: {e2 == e : Nat},
  +h: {C.compOk(segs, need, q, ks, d, k, e2) == True{} : Bool})
  -> {C.compOk(segs, need, q, ks, d, k, e) == True{} : Bool}:
  %ee : {C.compOk(segs, need, q, ks, d, k, _) == True{} : Bool}
  h

def comp_pick(+p2: Nat, +k2: Nat, +d2: Nat, +e2: Nat, +fo: +List<Core.Tree>, +rest: +List<C.Seg>, +grammar: +List<Core.Production>, +segs: +List<C.Seg>,
  +need: Core.Need, +p: Nat, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +e: Nat,
  +hh: {C.whenB(Bool.and(Nat.is_eq(p2, p), Bool.and(Nat.is_eq(k2, k), Nat.is_eq(d2, List.length(&2, Core.Sym, Core.rhsOf(grammar, p))))), C.compOk(segs, need, q, ks, d, k, e2)) == True{} : Bool},
  cases: Either<{C.keyIs(p, k, List.length(&2, Core.Sym, Core.rhsOf(grammar, p)), e, C.Seg{p2, k2, d2, e2, fo}) == True{} : Bool}, {C.hasSeg(p, k, List.length(&2, Core.Sym, Core.rhsOf(grammar, p)), e, rest) == True{} : Bool}>,
  later: {C.hasSeg(p, k, List.length(&2, Core.Sym, Core.rhsOf(grammar, p)), e, rest) == True{} : Bool} -> {C.compOk(segs, need, q, ks, d, k, e) == True{} : Bool})
  -> {C.compOk(segs, need, q, ks, d, k, e) == True{} : Bool}:
  match cases:
    case Inl{+ek}:
      +len = {List.length(&2, Core.Sym, Core.rhsOf(grammar, p)) : Nat}
      +r1 = {Bool.and(Nat.is_eq(k2, k), Bool.and(Nat.is_eq(d2, len), Nat.is_eq(e2, e))) : Bool}
      +r2 = {Bool.and(Nat.is_eq(d2, len), Nat.is_eq(e2, e)) : Bool}
      +t1 = Lemma.and_true_right_side(Nat.is_eq(p2, p), r1, ek)
      +t2 = Lemma.and_true_right_side(Nat.is_eq(k2, k), r2, t1)
      +cond = Lemma.and_true_intro(Nat.is_eq(p2, p), Bool.and(Nat.is_eq(k2, k), Nat.is_eq(d2, len)), Lemma.and_true_left(Nat.is_eq(p2, p), r1, ek),
        Lemma.and_true_intro(Nat.is_eq(k2, k), Nat.is_eq(d2, len), Lemma.and_true_left(Nat.is_eq(k2, k), r2, t1), Lemma.and_true_left(Nat.is_eq(d2, len), Nat.is_eq(e2, e), t2)))
      comp_moved(segs, need, q, ks, d, k, e2, e,
        Lemma.nat_eq_sound(e2, e, Lemma.and_true_right_side(Nat.is_eq(d2, len), Nat.is_eq(e2, e), t2)),
        when_use(Bool.and(Nat.is_eq(p2, p), Bool.and(Nat.is_eq(k2, k), Nat.is_eq(d2, len))), C.compOk(segs, need, q, ks, d, k, e2), hh, cond))
    case Inr{m}:
      later(m)

# A completed segment of p in the set: the closed set lets the prefix read it.
law comps_of:
  for ss: +List<C.Seg>
  for +grammar: +List<Core.Production>
  for +segs: +List<C.Seg>
  for +need: Core.Need
  for +p: Nat
  for +q: Nat
  for +ks: Nat
  for +d: Nat
  for +k: Nat
  for +e: Nat
  for +cs: {C.compsOk(ss, grammar, segs, need, p, q, ks, d, k) == True{} : Bool}
  for +h: {C.hasSeg(p, k, List.length(&2, Core.Sym, Core.rhsOf(grammar, p)), e, ss) == True{} : Bool}
  {C.compOk(segs, need, q, ks, d, k, e) == True{} : Bool}

def comps_of(ss, grammar, segs, need, p, q, ks, d, k, e, cs, h):
  match ss:
    case Nil{}:
      Empty.absurd({C.compOk(segs, need, q, ks, d, k, e) == True{} : Bool}, Lemma.false_is_not_true(h))
    case Con{C.Seg{+p2, +k2, +d2, +e2, +fo}, +rest}:
      +cond = {Bool.and(Nat.is_eq(p2, p), Bool.and(Nat.is_eq(k2, k), Nat.is_eq(d2, List.length(&2, Core.Sym, Core.rhsOf(grammar, p))))) : Bool}
      +here = {C.whenB(cond, C.compOk(segs, need, q, ks, d, k, e2)) : Bool}
      +more = {C.compsOk(rest, grammar, segs, need, p, q, ks, d, k) : Bool}
      comp_pick(p2, k2, d2, e2, fo, rest, grammar, segs, need, p, q, ks, d, k, e, Lemma.and_true_left(here, more, cs),
        Lemma.or_true_cases(C.keyIs(p, k, List.length(&2, Core.Sym, Core.rhsOf(grammar, p)), e, C.Seg{p2, k2, d2, e2, fo}), C.hasSeg(p, k, List.length(&2, Core.Sym, Core.rhsOf(grammar, p)), e, rest), h),
        m => comps_of(rest, grammar, segs, need, p, q, ks, d, k, e, Lemma.and_true_right_side(here, more, cs), m))

def ProdOk(+grammar: +List<Core.Production>, +segs: +List<C.Seg>, +need: Core.Need, +p: Nat, +q: Nat, +ks: Nat, +d: Nat, +k: Nat) -> Bool:
  Bool.and(C.hasSeg(p, k, 0n, k, segs), C.compsOk(segs, grammar, segs, need, p, q, ks, d, k))

def prod_zero(+grammar: +List<Core.Production>, +segs: +List<C.Seg>, +need: Core.Need, +base: Nat, +q: Nat, +ks: Nat, +d: Nat, +k: Nat,
  +h: {ProdOk(grammar, segs, need, base, q, ks, d, k) == True{} : Bool})
  -> {ProdOk(grammar, segs, need, Nat.add(base, 0n), q, ks, d, k) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(base, 0n), base, Lemma.add_zero_right(base)) : {ProdOk(grammar, segs, need, _, q, ks, d, k) == True{} : Bool}
  h

def prod_succ(+grammar: +List<Core.Production>, +segs: +List<C.Seg>, +need: Core.Need, +base: Nat, +n: Nat, +q: Nat, +ks: Nat, +d: Nat, +k: Nat,
  +h: {ProdOk(grammar, segs, need, 1n+Nat.add(base, n), q, ks, d, k) == True{} : Bool})
  -> {ProdOk(grammar, segs, need, Nat.add(base, 1n+n), q, ks, d, k) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(base, 1n+n), 1n+Nat.add(base, n), Lemma.add_succ_right(base, n)) : {ProdOk(grammar, segs, need, _, q, ks, d, k) == True{} : Bool}
  h

# A production of x: the closed set starts it at k and lets each of its completions be read.
law prods_of:
  for g: +List<Core.Production>
  for n: Nat
  for +base: Nat
  for +grammar: +List<Core.Production>
  for +segs: +List<C.Seg>
  for +x: Nat
  for +need: Core.Need
  for +q: Nat
  for +ks: Nat
  for +d: Nat
  for +k: Nat
  for +ps: {C.prodsOk(g, base, grammar, segs, x, need, q, ks, d, k) == True{} : Bool}
  for +hl: {Core.lhsIs(g, n, x) == True{} : Bool}
  {ProdOk(grammar, segs, need, Nat.add(base, n), q, ks, d, k) == True{} : Bool}

def prods_of(g, n, base, grammar, segs, x, need, q, ks, d, k, ps, hl):
  match g n:
    case Nil{} +n0:
      Empty.absurd({ProdOk(grammar, segs, need, Nat.add(base, n0), q, ks, d, k) == True{} : Bool}, Lemma.false_is_not_true(hl))
    case Con{Core.Production{+lhs, +rhs}, +rest} 0n:
      +here = {C.whenB(Nat.is_eq(lhs, x), ProdOk(grammar, segs, need, base, q, ks, d, k)) : Bool}
      +more = {C.prodsOk(rest, 1n+base, grammar, segs, x, need, q, ks, d, k) : Bool}
      prod_zero(grammar, segs, need, base, q, ks, d, k,
        when_use(Nat.is_eq(lhs, x), ProdOk(grammar, segs, need, base, q, ks, d, k), Lemma.and_true_left(here, more, ps), hl))
    case Con{Core.Production{+lhs, +rhs}, +rest} 1n+(+n2):
      +here = {C.whenB(Nat.is_eq(lhs, x), ProdOk(grammar, segs, need, base, q, ks, d, k)) : Bool}
      +more = {C.prodsOk(rest, 1n+base, grammar, segs, x, need, q, ks, d, k) : Bool}
      prod_succ(grammar, segs, need, base, n2, q, ks, d, k,
        prods_of(rest, n2, 1n+base, grammar, segs, x, need, q, ks, d, k, Lemma.and_true_right_side(here, more, ps), hl))

# ======== THE WALK ========

def ext_item(+grammar: +List<Core.Production>, +input: +List<Nat>, +segs: +List<C.Seg>, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +item: Maybe<&2, Core.Sym>,
  +en: {Gll.nthSym(Core.rhsOf(grammar, q), d) == item : Maybe<&2, Core.Sym>},
  +h: {C.extOk(Gll.nthSym(Core.rhsOf(grammar, q), d), grammar, input, segs, q, ks, d, k) == True{} : Bool})
  -> {C.extOk(item, grammar, input, segs, q, ks, d, k) == True{} : Bool}:
  %en : {C.extOk(_, grammar, input, segs, q, ks, d, k) == True{} : Bool}
  h

def tok_to(+input: +List<Nat>, +k: Nat, +a: Nat, +t: Nat, +e: {a == t : Nat},
  +h: {Core.tokIs(Core.tokAt(input, k), a) == True{} : Bool}) -> {Core.tokIs(Core.tokAt(input, k), t) == True{} : Bool}:
  %e : {Core.tokIs(Core.tokAt(input, k), _) == True{} : Bool}
  h

def seg_to(+segs: +List<C.Seg>, +q: Nat, +ks: Nat, +d: Nat, +a: Nat, +b: Nat, +e: {a == b : Nat},
  +h: {C.hasSeg(q, ks, d, a, segs) == True{} : Bool}) -> {C.hasSeg(q, ks, d, b, segs) == True{} : Bool}:
  %e : {C.hasSeg(q, ks, d, _, segs) == True{} : Bool}
  h

def end_d(+grammar: +List<Core.Production>, +segs: +List<C.Seg>, +q: Nat, +ks: Nat, +d: Nat, +k: Nat,
  +inv: {Nat.add(d, 0n) == List.length(&2, Core.Sym, Core.rhsOf(grammar, q)) : Nat},
  +hs: {C.hasSeg(q, ks, d, k, segs) == True{} : Bool}) -> {C.hasSeg(q, ks, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), k, segs) == True{} : Bool}:
  +ed = Equal.trans(Nat, d, Nat.add(d, 0n), List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), Equal.sym(Nat, Nat.add(d, 0n), d, Lemma.add_zero_right(d)), inv)
  %ed : {C.hasSeg(q, ks, _, k, segs) == True{} : Bool}
  hs

def inv_step(+d: Nat, +r: +List<Core.Sym>, +len: Nat,
  +inv: {Nat.add(d, 1n+List.length(&2, Core.Sym, r)) == len : Nat}) -> {Nat.add(1n+d, List.length(&2, Core.Sym, r)) == len : Nat}:
  Equal.trans(Nat, 1n+Nat.add(d, List.length(&2, Core.Sym, r)), Nat.add(d, 1n+List.length(&2, Core.Sym, r)), len,
    Equal.sym(Nat, Nat.add(d, 1n+List.length(&2, Core.Sym, r)), 1n+Nat.add(d, List.length(&2, Core.Sym, r)), Lemma.add_succ_right(d, List.length(&2, Core.Sym, r))), inv)

# A forest that reads the rest of a node's items from a segment completes the node in a
# segment of a closed set.
law walk:
  for f: +List<Core.Tree>
  for items: +List<Core.Sym>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +segs: +List<C.Seg>
  for +q: Nat
  for +ks: Nat
  for +d: Nat
  for +k: Nat
  for +ie: {G.dropFrom(d, Core.rhsOf(grammar, q)) == items : +List<Core.Sym>}
  for +inv: {Nat.add(d, List.length(&2, Core.Sym, items)) == List.length(&2, Core.Sym, Core.rhsOf(grammar, q)) : Nat}
  for +r: {Core.reads(f, grammar, items, input, k) == True{} : Bool}
  for +hs: {C.hasSeg(q, ks, d, k, segs) == True{} : Bool}
  for +cl: {C.closedAll(segs, grammar, input, segs) == True{} : Bool}
  {C.hasSeg(q, ks, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), G.endOf(f, k), segs) == True{} : Bool}

def walk(f, items, grammar, input, segs, q, ks, d, k, ie, inv, r, hs, cl):
  match f items:
    case Nil{} Nil{}:
      end_d(grammar, segs, q, ks, d, k, inv, hs)
    case Nil{} Con{+s, +rest}:
      Empty.absurd({C.hasSeg(q, ks, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), k, segs) == True{} : Bool}, Lemma.false_is_not_true(r))
    case Con{Core.Leaf{+a}, +ts} Nil{}:
      Empty.absurd({C.hasSeg(q, ks, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), G.endOf(Core.Leaf{a} <> ts, k), segs) == True{} : Bool}, Lemma.false_is_not_true(r))
    case Con{Core.Node{+p, +ch}, +ts} Nil{}:
      Empty.absurd({C.hasSeg(q, ks, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), G.endOf(Core.Node{p, ch} <> ts, k), segs) == True{} : Bool}, Lemma.false_is_not_true(r))
    case Con{Core.Leaf{+a}, +ts} Con{Core.Nonterminal{+x, +need}, +rest}:
      Empty.absurd({C.hasSeg(q, ks, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), G.endOf(Core.Leaf{a} <> ts, k), segs) == True{} : Bool}, Lemma.false_is_not_true(r))
    case Con{Core.Node{+p, +ch}, +ts} Con{Core.Terminal{+t}, +rest}:
      Empty.absurd({C.hasSeg(q, ks, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), G.endOf(Core.Node{p, ch} <> ts, k), segs) == True{} : Bool}, Lemma.false_is_not_true(r))
    case Con{Core.Leaf{+a}, +ts} Con{Core.Terminal{+t}, +rest}:
      +more = {Bool.and(Core.tokIs(Core.tokAt(input, k), a), Core.reads(ts, grammar, rest, input, 1n+k)) : Bool}
      +ea = Lemma.nat_eq_sound(a, t, Lemma.and_true_left(Nat.is_eq(a, t), more, r))
      +rk = Lemma.and_true_left(Core.tokIs(Core.tokAt(input, k), a), Core.reads(ts, grammar, rest, input, 1n+k), Lemma.and_true_right_side(Nat.is_eq(a, t), more, r))
      +rt = Lemma.and_true_right_side(Core.tokIs(Core.tokAt(input, k), a), Core.reads(ts, grammar, rest, input, 1n+k), Lemma.and_true_right_side(Nat.is_eq(a, t), more, r))
      +ext = ext_item(grammar, input, segs, q, ks, d, k, Some{Core.Terminal{t}}, G.nth_drop(Core.rhsOf(grammar, q), d, Core.Terminal{t}, rest, ie),
        ext_of(segs, grammar, input, segs, q, ks, d, k, cl, hs))
      +hs2 = when_use(Core.tokIs(Core.tokAt(input, k), t), C.hasSeg(q, ks, 1n+d, 1n+k, segs), ext, tok_to(input, k, a, t, ea, rk))
      walk(ts, rest, grammar, input, segs, q, ks, 1n+d, 1n+k, G.drop_next(Core.rhsOf(grammar, q), d, Core.Terminal{t}, rest, ie),
        inv_step(d, rest, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), inv), rt, hs2, cl)
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
      +ext = ext_item(grammar, input, segs, q, ks, d, k, Some{Core.Nonterminal{x, need}}, G.nth_drop(Core.rhsOf(grammar, q), d, Core.Nonterminal{x, need}, rest, ie),
        ext_of(segs, grammar, input, segs, q, ks, d, k, cl, hs))
      +po = prods_of(grammar, p, 0n, grammar, segs, x, need, q, ks, d, k, ext, hl)
      +hp = Lemma.and_true_left(C.hasSeg(p, k, 0n, k, segs), C.compsOk(segs, grammar, segs, need, p, q, ks, d, k), po)
      +cs = Lemma.and_true_right_side(C.hasSeg(p, k, 0n, k, segs), C.compsOk(segs, grammar, segs, need, p, q, ks, d, k), po)
      +done = seg_to(segs, p, k, List.length(&2, Core.Sym, Core.rhsOf(grammar, p)), G.endOf(ch, k), far, G.end_node(p, ch, k),
        walk(ch, Core.rhsOf(grammar, p), grammar, input, segs, p, k, 0n, k, {==}, {==}, rc, hp, cl))
      +comp = comps_of(segs, grammar, segs, need, p, q, ks, d, k, far, cs, done)
      +hs2 = when_use(Gll.needHolds(need, k, far), C.hasSeg(q, ks, 1n+d, far, segs), comp, G.need_holds(need, w, k, nk))
      walk(ts, rest, grammar, input, segs, q, ks, 1n+d, far, G.drop_next(Core.rhsOf(grammar, q), d, Core.Nonterminal{x, need}, rest, ie),
        inv_step(d, rest, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), inv), rt, hs2, cl)

# ======== SEGMENTS, COUNTED ========

def segBound(s: C.Seg, +grammar: +List<Core.Production>, +input: +List<Nat>) -> Bool:
  match s:
    case C.Seg{+q, +ks, +d, +e, f}:
      Run.descBound(Gll.Desc{q, d, ks, e}, grammar, input)

def segsBounded(segs: +List<C.Seg>, +grammar: +List<Core.Production>, +input: +List<Nat>) -> Bool:
  match segs:
    case Nil{}:
      True{}
    case Con{+s, rest}:
      Bool.and(segBound(s, grammar, input), segsBounded(rest, grammar, input))

# A segment's key as a descriptor: (q, ks, d, e) as Desc{q, d, ks, e}.
def segDescs(segs: +List<C.Seg>) -> +List<Gll.Desc>:
  match segs:
    case Nil{}:
      []
    case Con{C.Seg{+q, +ks, +d, +e, f}, rest}:
      Gll.Desc{q, d, ks, e} <> segDescs(rest)

def rMeas(+grammar: +List<Core.Production>, +input: +List<Nat>, +segs: +List<C.Seg>) -> Nat:
  Run.countNot(Run.univ(grammar, input), segDescs(segs))

def allHave(ss: +List<C.Seg>, +segs: +List<C.Seg>) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case Con{C.Seg{+q, +ks, +d, +e, f}, rest}:
      Bool.and(C.hasSeg(q, ks, d, e, segs), allHave(rest, segs))

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

def key_refl(+q: Nat, +ks: Nat, +d: Nat, +e: Nat, +f: +List<Core.Tree>) -> {C.keyIs(q, ks, d, e, C.Seg{q, ks, d, e, f}) == True{} : Bool}:
  Lemma.and_true_intro(Nat.is_eq(q, q), Bool.and(Nat.is_eq(ks, ks), Bool.and(Nat.is_eq(d, d), Nat.is_eq(e, e))), Lemma.nat_eq_refl(q),
    Lemma.and_true_intro(Nat.is_eq(ks, ks), Bool.and(Nat.is_eq(d, d), Nat.is_eq(e, e)), Lemma.nat_eq_refl(ks),
      Lemma.and_true_intro(Nat.is_eq(d, d), Nat.is_eq(e, e), Lemma.nat_eq_refl(d), Lemma.nat_eq_refl(e))))

def key_at(+q: Nat, +ks: Nat, +d: Nat, +e: Nat, +q2: Nat, +ks2: Nat, +d2: Nat, +e2: Nat, +f: +List<Core.Tree>,
  +ed: {Gll.Desc{q, d, ks, e} == Gll.Desc{q2, d2, ks2, e2} : Gll.Desc}) -> {C.keyIs(q, ks, d, e, C.Seg{q2, ks2, d2, e2, f}) == True{} : Bool}:
  %Equal.cong(Gll.Desc, Nat, v => dQ(v), Gll.Desc{q, d, ks, e}, Gll.Desc{q2, d2, ks2, e2}, ed) : {C.keyIs(q, ks, d, e, C.Seg{_, ks2, d2, e2, f}) == True{} : Bool}
  %Equal.cong(Gll.Desc, Nat, v => dD(v), Gll.Desc{q, d, ks, e}, Gll.Desc{q2, d2, ks2, e2}, ed) : {C.keyIs(q, ks, d, e, C.Seg{q, ks2, _, e2, f}) == True{} : Bool}
  %Equal.cong(Gll.Desc, Nat, v => dK(v), Gll.Desc{q, d, ks, e}, Gll.Desc{q2, d2, ks2, e2}, ed) : {C.keyIs(q, ks, d, e, C.Seg{q, _, d, e2, f}) == True{} : Bool}
  %Equal.cong(Gll.Desc, Nat, v => dI(v), Gll.Desc{q, d, ks, e}, Gll.Desc{q2, d2, ks2, e2}, ed) : {C.keyIs(q, ks, d, e, C.Seg{q, ks, d, _, f}) == True{} : Bool}
  key_refl(q, ks, d, e, f)

def sd_pick(+q: Nat, +ks: Nat, +d: Nat, +e: Nat, +q2: Nat, +ks2: Nat, +d2: Nat, +e2: Nat, +f: +List<Core.Tree>, +rest: +List<C.Seg>,
  cases: Either<{Gll.descEq(Gll.Desc{q, d, ks, e}, Gll.Desc{q2, d2, ks2, e2}) == True{} : Bool}, {Gll.descIn(Gll.Desc{q, d, ks, e}, segDescs(rest)) == True{} : Bool}>,
  later: {Gll.descIn(Gll.Desc{q, d, ks, e}, segDescs(rest)) == True{} : Bool} -> {C.hasSeg(q, ks, d, e, rest) == True{} : Bool})
  -> {C.hasSeg(q, ks, d, e, C.Seg{q2, ks2, d2, e2, f} <> rest) == True{} : Bool}:
  match cases:
    case Inl{h}:
      Lemma.or_true_left_intro(C.keyIs(q, ks, d, e, C.Seg{q2, ks2, d2, e2, f}), C.hasSeg(q, ks, d, e, rest),
        key_at(q, ks, d, e, q2, ks2, d2, e2, f, G.desc_eq_sound(Gll.Desc{q, d, ks, e}, Gll.Desc{q2, d2, ks2, e2}, h)))
    case Inr{m}:
      Lemma.or_true_right_intro(C.keyIs(q, ks, d, e, C.Seg{q2, ks2, d2, e2, f}), C.hasSeg(q, ks, d, e, rest), later(m))

# A key counted is a segment of the set.
law sd_back:
  for segs: +List<C.Seg>
  for +q: Nat
  for +ks: Nat
  for +d: Nat
  for +e: Nat
  for +h: {Gll.descIn(Gll.Desc{q, d, ks, e}, segDescs(segs)) == True{} : Bool}
  {C.hasSeg(q, ks, d, e, segs) == True{} : Bool}

def sd_back(segs, q, ks, d, e, h):
  match segs:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(h))
    case Con{C.Seg{+q2, +ks2, +d2, +e2, +f}, +rest}:
      sd_pick(q, ks, d, e, q2, ks2, d2, e2, f, rest, Lemma.or_true_cases(Gll.descEq(Gll.Desc{q, d, ks, e}, Gll.Desc{q2, d2, ks2, e2}), Gll.descIn(Gll.Desc{q, d, ks, e}, segDescs(rest)), h),
        m => sd_back(rest, q, ks, d, e, m))

def sd_out(b: Bool, +q: Nat, +ks: Nat, +d: Nat, +e: Nat, +segs: +List<C.Seg>, +eb: {Gll.descIn(Gll.Desc{q, d, ks, e}, segDescs(segs)) == b : Bool},
  +out: {C.hasSeg(q, ks, d, e, segs) == False{} : Bool}) -> {Gll.descIn(Gll.Desc{q, d, ks, e}, segDescs(segs)) == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({Gll.descIn(Gll.Desc{q, d, ks, e}, segDescs(segs)) == False{} : Bool}, Lemma.true_is_not_false(Equal.trans(Bool, True{}, C.hasSeg(q, ks, d, e, segs), False{}, Equal.sym(Bool, C.hasSeg(q, ks, d, e, segs), True{}, sd_back(segs, q, ks, d, e, eb)), out)))
    case False{}:
      eb

law seg_descs_app:
  for a: +List<C.Seg>
  for +b: +List<C.Seg>
  {segDescs(List.append(&2, C.Seg, a, b)) == List.append(&2, Gll.Desc, segDescs(a), segDescs(b)) : +List<Gll.Desc>}

def seg_descs_app(a, b):
  match a:
    case Nil{}:
      {==}
    case Con{C.Seg{+q, +ks, +d, +e, +f}, +rest}:
      %seg_descs_app(rest, b) : {Gll.Desc{q, d, ks, e} <> segDescs(List.append(&2, C.Seg, rest, b)) == Gll.Desc{q, d, ks, e} <> _ : +List<Gll.Desc>}
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
        PC.desc_in_app_left(ys, c, x, Lemma.and_true_left(Gll.descIn(x, ys), Run.subDescs(rest, ys), h)),
        sub_app(rest, ys, c, Lemma.and_true_right_side(Gll.descIn(x, ys), Run.subDescs(rest, ys), h)))

# A new segment within bounds, added at the end: one fewer unseen key.
def r_drop(+grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +ks: Nat, +d: Nat, +e: Nat, +f: +List<Core.Tree>, +segs: +List<C.Seg>,
  +hb: {Run.descBound(Gll.Desc{q, d, ks, e}, grammar, input) == True{} : Bool}, +out: {C.hasSeg(q, ks, d, e, segs) == False{} : Bool})
  -> {Nat.is_le(1n+rMeas(grammar, input, List.append(&2, C.Seg, segs, [C.Seg{q, ks, d, e, f}])), rMeas(grammar, input, segs)) == True{} : Bool}:
  +U = Run.univ(grammar, input)
  +D = {Gll.Desc{q, d, ks, e} : Gll.Desc}
  %Equal.sym(+List<Gll.Desc>, segDescs(List.append(&2, C.Seg, segs, [C.Seg{q, ks, d, e, f}])), List.append(&2, Gll.Desc, segDescs(segs), [D]), seg_descs_app(segs, [C.Seg{q, ks, d, e, f}])) : {Nat.is_le(1n+Run.countNot(U, _), rMeas(grammar, input, segs)) == True{} : Bool}
  Lemma.le_trans(1n+Run.countNot(U, List.append(&2, Gll.Desc, segDescs(segs), [D])), 1n+Run.countNot(U, D <> segDescs(segs)), Run.countNot(U, segDescs(segs)),
    PC.count_mono(U, D <> segDescs(segs), List.append(&2, Gll.Desc, segDescs(segs), [D]),
      Lemma.and_true_intro(Gll.descIn(D, List.append(&2, Gll.Desc, segDescs(segs), [D])), Run.subDescs(segDescs(segs), List.append(&2, Gll.Desc, segDescs(segs), [D])),
        PC.desc_in_app_right(segDescs(segs), [D], D, PC.desc_head(q, d, ks, e, [])),
        sub_app(segDescs(segs), segDescs(segs), [D], PC.desc_refl(segDescs(segs))))),
    PC.count_drop(U, segDescs(segs), D, PC.bound_mem(D, grammar, input, hb), sd_out(Gll.descIn(D, segDescs(segs)), q, ks, d, e, segs, {==}, out)))

# ======== ADDING NEW SEGMENTS ========

law hs_app_left:
  for a: +List<C.Seg>
  for +b: +List<C.Seg>
  for +q: Nat
  for +ks: Nat
  for +d: Nat
  for +e: Nat
  for +h: {C.hasSeg(q, ks, d, e, a) == True{} : Bool}
  {C.hasSeg(q, ks, d, e, List.append(&2, C.Seg, a, b)) == True{} : Bool}

def hs_app_pick(+s: C.Seg, +rest: +List<C.Seg>, +b: +List<C.Seg>, +q: Nat, +ks: Nat, +d: Nat, +e: Nat,
  cases: Either<{C.keyIs(q, ks, d, e, s) == True{} : Bool}, {C.hasSeg(q, ks, d, e, rest) == True{} : Bool}>,
  later: {C.hasSeg(q, ks, d, e, rest) == True{} : Bool} -> {C.hasSeg(q, ks, d, e, List.append(&2, C.Seg, rest, b)) == True{} : Bool})
  -> {C.hasSeg(q, ks, d, e, s <> List.append(&2, C.Seg, rest, b)) == True{} : Bool}:
  match cases:
    case Inl{h}:
      Lemma.or_true_left_intro(C.keyIs(q, ks, d, e, s), C.hasSeg(q, ks, d, e, List.append(&2, C.Seg, rest, b)), h)
    case Inr{m}:
      Lemma.or_true_right_intro(C.keyIs(q, ks, d, e, s), C.hasSeg(q, ks, d, e, List.append(&2, C.Seg, rest, b)), later(m))

def hs_app_left(a, b, q, ks, d, e, h):
  match a:
    case Nil{}:
      Empty.absurd({C.hasSeg(q, ks, d, e, b) == True{} : Bool}, Lemma.false_is_not_true(h))
    case Con{+s, +rest}:
      hs_app_pick(s, rest, b, q, ks, d, e, Lemma.or_true_cases(C.keyIs(q, ks, d, e, s), C.hasSeg(q, ks, d, e, rest), h), m => hs_app_left(rest, b, q, ks, d, e, m))

law sb_app:
  for a: +List<C.Seg>
  for +b: +List<C.Seg>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +ha: {segsBounded(a, grammar, input) == True{} : Bool}
  for +hb: {segsBounded(b, grammar, input) == True{} : Bool}
  {segsBounded(List.append(&2, C.Seg, a, b), grammar, input) == True{} : Bool}

def sb_app(a, b, grammar, input, ha, hb):
  match a:
    case Nil{}:
      hb
    case Con{+s, +rest}:
      Lemma.and_true_intro(segBound(s, grammar, input), segsBounded(List.append(&2, C.Seg, rest, b), grammar, input), Lemma.and_true_left(segBound(s, grammar, input), segsBounded(rest, grammar, input), ha),
        sb_app(rest, b, grammar, input, Lemma.and_true_right_side(segBound(s, grammar, input), segsBounded(rest, grammar, input), ha), hb))

def pick_bounded(have: Bool, +s: C.Seg, +segs: +List<C.Seg>, +grammar: +List<Core.Production>, +input: +List<Nat>, +hs: {segBound(s, grammar, input) == True{} : Bool}, +h: {segsBounded(segs, grammar, input) == True{} : Bool})
  -> {segsBounded(C.addPick(have, s, segs), grammar, input) == True{} : Bool}:
  match have:
    case True{}:
      h
    case False{}:
      sb_app(segs, [s], grammar, input, h, Lemma.and_true_intro(segBound(s, grammar, input), True{}, hs, {==}))

# Adding keeps the segments within bounds.
law an_bounded:
  for new: +List<C.Seg>
  for +segs: +List<C.Seg>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +hn: {segsBounded(new, grammar, input) == True{} : Bool}
  for +hs: {segsBounded(segs, grammar, input) == True{} : Bool}
  {segsBounded(C.addNew(new, segs), grammar, input) == True{} : Bool}

def an_bounded(new, segs, grammar, input, hn, hs):
  match new:
    case Nil{}:
      hs
    case Con{C.Seg{+q, +ks, +d, +e, +f}, +rest}:
      an_bounded(rest, C.addPick(C.hasSeg(q, ks, d, e, segs), C.Seg{q, ks, d, e, f}, segs), grammar, input,
        Lemma.and_true_right_side(segBound(C.Seg{q, ks, d, e, f}, grammar, input), segsBounded(rest, grammar, input), hn),
        pick_bounded(C.hasSeg(q, ks, d, e, segs), C.Seg{q, ks, d, e, f}, segs, grammar, input,
          Lemma.and_true_left(segBound(C.Seg{q, ks, d, e, f}, grammar, input), segsBounded(rest, grammar, input), hn), hs))

def pick_keep(have: Bool, +s: C.Seg, +segs: +List<C.Seg>, +q: Nat, +ks: Nat, +d: Nat, +e: Nat, +h: {C.hasSeg(q, ks, d, e, segs) == True{} : Bool})
  -> {C.hasSeg(q, ks, d, e, C.addPick(have, s, segs)) == True{} : Bool}:
  match have:
    case True{}:
      h
    case False{}:
      hs_app_left(segs, [s], q, ks, d, e, h)

# Adding keeps every segment.
law an_keep:
  for new: +List<C.Seg>
  for +segs: +List<C.Seg>
  for +q: Nat
  for +ks: Nat
  for +d: Nat
  for +e: Nat
  for +h: {C.hasSeg(q, ks, d, e, segs) == True{} : Bool}
  {C.hasSeg(q, ks, d, e, C.addNew(new, segs)) == True{} : Bool}

def an_keep(new, segs, q, ks, d, e, h):
  match new:
    case Nil{}:
      h
    case Con{C.Seg{+q2, +ks2, +d2, +e2, +f}, +rest}:
      an_keep(rest, C.addPick(C.hasSeg(q2, ks2, d2, e2, segs), C.Seg{q2, ks2, d2, e2, f}, segs), q, ks, d, e,
        pick_keep(C.hasSeg(q2, ks2, d2, e2, segs), C.Seg{q2, ks2, d2, e2, f}, segs, q, ks, d, e, h))

def ASame(+new: +List<C.Seg>, +segs: +List<C.Seg>) -> Type:
  {C.addNew(new, segs) == segs : +List<C.Seg>} & {allHave(new, segs) == True{} : Bool}

def ARes(+grammar: +List<Core.Production>, +input: +List<Nat>, +new: +List<C.Seg>, +segs: +List<C.Seg>) -> Type:
  Either<ASame(new, segs), {Nat.is_le(1n+rMeas(grammar, input, C.addNew(new, segs)), rMeas(grammar, input, segs)) == True{} : Bool}>

def AResB(+b: Bool, +grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +ks: Nat, +d: Nat, +e: Nat, +f: +List<Core.Tree>, +rest: +List<C.Seg>, +segs: +List<C.Seg>) -> Type:
  Either<({C.addNew(rest, C.addPick(b, C.Seg{q, ks, d, e, f}, segs)) == segs : +List<C.Seg>} & {Bool.and(C.hasSeg(q, ks, d, e, segs), allHave(rest, segs)) == True{} : Bool}),
    {Nat.is_le(1n+rMeas(grammar, input, C.addNew(rest, C.addPick(b, C.Seg{q, ks, d, e, f}, segs))), rMeas(grammar, input, segs)) == True{} : Bool}>

def rmeas_eq(+grammar: +List<Core.Production>, +input: +List<Nat>, +a: +List<C.Seg>, +b: +List<C.Seg>, +eq: {a == b : +List<C.Seg>}) -> {Nat.is_le(rMeas(grammar, input, a), rMeas(grammar, input, b)) == True{} : Bool}:
  %eq : {Nat.is_le(rMeas(grammar, input, a), rMeas(grammar, input, _)) == True{} : Bool}
  Lemma.le_refl(rMeas(grammar, input, a))

def rmeas_to(+grammar: +List<Core.Production>, +input: +List<Nat>, +a: +List<C.Seg>, +b: +List<C.Seg>, +x: Nat, +eq: {a == b : +List<C.Seg>},
  +h: {Nat.is_le(1n+x, rMeas(grammar, input, a)) == True{} : Bool}) -> {Nat.is_le(1n+x, rMeas(grammar, input, b)) == True{} : Bool}:
  %eq : {Nat.is_le(1n+x, rMeas(grammar, input, _)) == True{} : Bool}
  h

def asame_le(+grammar: +List<Core.Production>, +input: +List<Nat>, +new: +List<C.Seg>, +segs: +List<C.Seg>, p: ASame(new, segs)) -> {Nat.is_le(rMeas(grammar, input, C.addNew(new, segs)), rMeas(grammar, input, segs)) == True{} : Bool}:
  match p:
    case (+eq, +have):
      rmeas_eq(grammar, input, C.addNew(new, segs), segs, eq)

def ares_le(+grammar: +List<Core.Production>, +input: +List<Nat>, +new: +List<C.Seg>, +segs: +List<C.Seg>, r: ARes(grammar, input, new, segs)) -> {Nat.is_le(rMeas(grammar, input, C.addNew(new, segs)), rMeas(grammar, input, segs)) == True{} : Bool}:
  match r:
    case Inl{p}:
      asame_le(grammar, input, new, segs, p)
    case Inr{m}:
      Lemma.le_of_succ_le(rMeas(grammar, input, C.addNew(new, segs)), rMeas(grammar, input, segs), m)

def ab_have2(+grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +ks: Nat, +d: Nat, +e: Nat, +f: +List<Core.Tree>, +rest: +List<C.Seg>, +segs: +List<C.Seg>, +eb: {C.hasSeg(q, ks, d, e, segs) == True{} : Bool}, p: ASame(rest, segs))
  -> AResB(True{}, grammar, input, q, ks, d, e, f, rest, segs):
  match p:
    case (+eq, +have):
      Inl{(eq, Lemma.and_true_intro(C.hasSeg(q, ks, d, e, segs), allHave(rest, segs), eb, have))}

def ab_have(+grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +ks: Nat, +d: Nat, +e: Nat, +f: +List<Core.Tree>, +rest: +List<C.Seg>, +segs: +List<C.Seg>, +eb: {C.hasSeg(q, ks, d, e, segs) == True{} : Bool}, r: ARes(grammar, input, rest, segs))
  -> AResB(True{}, grammar, input, q, ks, d, e, f, rest, segs):
  match r:
    case Inl{p}:
      ab_have2(grammar, input, q, ks, d, e, f, rest, segs, eb, p)
    case Inr{m}:
      Inr{m}

def ares_b(b: Bool, +grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +ks: Nat, +d: Nat, +e: Nat, +f: +List<Core.Tree>, +rest: +List<C.Seg>, +segs: +List<C.Seg>, +eb: {C.hasSeg(q, ks, d, e, segs) == b : Bool},
  +hb: {Run.descBound(Gll.Desc{q, d, ks, e}, grammar, input) == True{} : Bool},
  later: @a: +List<C.Seg> -> ARes(grammar, input, rest, a)) -> AResB(b, grammar, input, q, ks, d, e, f, rest, segs):
  match b:
    case True{}:
      ab_have(grammar, input, q, ks, d, e, f, rest, segs, eb, later(segs))
    case False{}:
      +s2 = List.append(&2, C.Seg, segs, [C.Seg{q, ks, d, e, f}])
      Inr{Lemma.le_trans(1n+rMeas(grammar, input, C.addNew(rest, s2)), 1n+rMeas(grammar, input, s2), rMeas(grammar, input, segs),
        ares_le(grammar, input, rest, s2, later(s2)), r_drop(grammar, input, q, ks, d, e, f, segs, hb, eb))}

# Adding segments within bounds: all keys were there and nothing changed, or the count drops.
law ares:
  for new: +List<C.Seg>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +segs: +List<C.Seg>
  for +hn: {segsBounded(new, grammar, input) == True{} : Bool}
  ARes(grammar, input, new, segs)

def ares(new, grammar, input, segs, hn):
  match new:
    case Nil{}:
      Inl{({==}, {==})}
    case Con{C.Seg{+q, +ks, +d, +e, +f}, +rest}:
      ares_b(C.hasSeg(q, ks, d, e, segs), grammar, input, q, ks, d, e, f, rest, segs, {==},
        Lemma.and_true_left(segBound(C.Seg{q, ks, d, e, f}, grammar, input), segsBounded(rest, grammar, input), hn),
        a => ares(rest, grammar, input, a, Lemma.and_true_right_side(segBound(C.Seg{q, ks, d, e, f}, grammar, input), segsBounded(rest, grammar, input), hn)))

# ======== GROWTH STAYS WITHIN BOUNDS ========
#
# The closure grows on w; its segments are counted against a longer input (the one phase 1's
# questions are cut from), so one fuel bound serves every question.

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

def seg_if_any(b: Bool, +s: C.Seg, +grammar: +List<Core.Production>, +input: +List<Nat>, +hs: {segBound(s, grammar, input) == True{} : Bool})
  -> {segsBounded(C.segIf(b, s), grammar, input) == True{} : Bool}:
  match b:
    case True{}:
      Lemma.and_true_intro(segBound(s, grammar, input), True{}, hs, {==})
    case False{}:
      {==}

def seg_if_tok(b: Bool, +x: Bool, +y: Bool, +s: C.Seg, +grammar: +List<Core.Production>, +input: +List<Nat>, +eb: {Bool.and(x, y) == b : Bool},
  f: {x == True{} : Bool} -> {segBound(s, grammar, input) == True{} : Bool})
  -> {segsBounded(C.segIf(b, s), grammar, input) == True{} : Bool}:
  match b:
    case True{}:
      Lemma.and_true_intro(segBound(s, grammar, input), True{}, f(Lemma.and_true_left(x, y, eb)), {==})
    case False{}:
      {==}

def base_shift(+a: Nat, +b: Nat, +c: Nat, +h: {Nat.is_le(1n+Nat.add(a, b), c) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, 1n+b), c) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(a, 1n+b), 1n+Nat.add(a, b), Lemma.add_succ_right(a, b)) : {Nat.is_le(_, c) == True{} : Bool}
  h

def add_len_zero(+grammar: +List<Core.Production>) -> {Nat.is_le(Nat.add(List.length(&2, Core.Production, grammar), 0n), List.length(&2, Core.Production, grammar)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(List.length(&2, Core.Production, grammar), 0n), List.length(&2, Core.Production, grammar), Lemma.add_zero_right(List.length(&2, Core.Production, grammar))) : {Nat.is_le(_, List.length(&2, Core.Production, grammar)) == True{} : Bool}
  Lemma.le_refl(List.length(&2, Core.Production, grammar))


def seg_if_when(b: Bool, +s: C.Seg, +grammar: +List<Core.Production>, +input: +List<Nat>,
  f: {b == True{} : Bool} -> {segBound(s, grammar, input) == True{} : Bool})
  -> {segsBounded(C.segIf(b, s), grammar, input) == True{} : Bool}:
  match b:
    case True{}:
      Lemma.and_true_intro(segBound(s, grammar, input), True{}, f({==}), {==})
    case False{}:
      {==}

law cw_bounded:
  for ss: +List<C.Seg>
  for +grammar: +List<Core.Production>
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
  {segsBounded(C.completeWith(ss, grammar, need, p, q, ks, d, k, f), grammar, input) == True{} : Bool}

def cw_bounded(ss, grammar, input, need, p, q, ks, d, k, f, hss, hq, hd, hks):
  match ss:
    case Nil{}:
      {==}
    case Con{C.Seg{+p2, +k2, +d2, +e, +fp}, +rest}:
      +hh = Lemma.and_true_left(segBound(C.Seg{p2, k2, d2, e, fp}, grammar, input), segsBounded(rest, grammar, input), hss)
      +hit = Bool.and(Bool.and(Nat.is_eq(p2, p), Bool.and(Nat.is_eq(k2, k), Nat.is_eq(d2, List.length(&2, Core.Sym, Core.rhsOf(grammar, p))))), Gll.needHolds(need, k, e))
      sb_app(C.segIf(hit, C.Seg{q, ks, 1n+d, e, List.append(&2, Core.Tree, f, [Core.Node{p, fp}])}), C.completeWith(rest, grammar, need, p, q, ks, d, k, f), grammar, input,
        seg_if_any(hit, C.Seg{q, ks, 1n+d, e, List.append(&2, Core.Tree, f, [Core.Node{p, fp}])}, grammar, input,
          db_intro(q, 1n+d, ks, e, grammar, input, hq, hd, hks, db_e(p2, d2, k2, e, grammar, input, hh))),
        cw_bounded(rest, grammar, input, need, p, q, ks, d, k, f, Lemma.and_true_right_side(segBound(C.Seg{p2, k2, d2, e, fp}, grammar, input), segsBounded(rest, grammar, input), hss), hq, hd, hks))

def prod_pick_bounded(b: Bool, +segs: +List<C.Seg>, +grammar: +List<Core.Production>, +input: +List<Nat>, +need: Core.Need, +p: Nat, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +f: +List<Core.Tree>,
  +hs: {segsBounded(segs, grammar, input) == True{} : Bool}, +hq: {Nat.is_le(1n+q, List.length(&2, Core.Production, grammar)) == True{} : Bool},
  +hd: {Nat.is_le(1n+d, List.length(&2, Core.Sym, Core.rhsOf(grammar, q))) == True{} : Bool}, +hks: {Nat.is_le(ks, List.length(&2, Nat, input)) == True{} : Bool})
  -> {segsBounded(C.prodPick(b, segs, grammar, need, p, q, ks, d, k, f), grammar, input) == True{} : Bool}:
  match b:
    case True{}:
      cw_bounded(segs, grammar, input, need, p, q, ks, d, k, f, hs, hq, hd, hks)
    case False{}:
      {==}

law gp_bounded:
  for g: +List<Core.Production>
  for +base: Nat
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +segs: +List<C.Seg>
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
  {segsBounded(C.growProds(g, base, grammar, segs, x, need, q, ks, d, k, f), grammar, input) == True{} : Bool}

def gp_bounded(g, base, grammar, input, segs, x, need, q, ks, d, k, f, hg, hs, hq, hd, hks, hk):
  match g:
    case Nil{}:
      {==}
    case Con{Core.Production{+lhs, +rhs}, +rest}:
      +hb = Lemma.le_trans(1n+base, 1n+Nat.add(List.length(&2, Core.Production, rest), base), List.length(&2, Core.Production, grammar), Lemma.le_add_left(List.length(&2, Core.Production, rest), base), hg)
      sb_app(C.segIf(Nat.is_eq(lhs, x), C.Seg{base, k, 0n, k, []}),
        List.append(&2, C.Seg, C.prodPick(Nat.is_eq(lhs, x), segs, grammar, need, base, q, ks, d, k, f), C.growProds(rest, 1n+base, grammar, segs, x, need, q, ks, d, k, f)), grammar, input,
        seg_if_any(Nat.is_eq(lhs, x), C.Seg{base, k, 0n, k, []}, grammar, input,
          db_intro(base, 0n, k, k, grammar, input, hb, Lemma.zero_le(List.length(&2, Core.Sym, Core.rhsOf(grammar, base))), hk, hk)),
        sb_app(C.prodPick(Nat.is_eq(lhs, x), segs, grammar, need, base, q, ks, d, k, f), C.growProds(rest, 1n+base, grammar, segs, x, need, q, ks, d, k, f), grammar, input,
          prod_pick_bounded(Nat.is_eq(lhs, x), segs, grammar, input, need, base, q, ks, d, k, f, hs, hq, hd, hks),
          gp_bounded(rest, 1n+base, grammar, input, segs, x, need, q, ks, d, k, f, base_shift(List.length(&2, Core.Production, rest), base, List.length(&2, Core.Production, grammar), hg), hs, hq, hd, hks, hk)))

def gi_sym(sym: Core.Sym, +grammar: +List<Core.Production>, +w: +List<Nat>, +input: +List<Nat>, +segs: +List<C.Seg>, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +f: +List<Core.Tree>,
  +ei: {Gll.nthSym(Core.rhsOf(grammar, q), d) == Some{sym} : Maybe<&2, Core.Sym>}, +hw: {Nat.is_le(List.length(&2, Nat, w), List.length(&2, Nat, input)) == True{} : Bool},
  +hq: {Nat.is_le(1n+q, List.length(&2, Core.Production, grammar)) == True{} : Bool}, +hks: {Nat.is_le(ks, List.length(&2, Nat, input)) == True{} : Bool}, +hk: {Nat.is_le(k, List.length(&2, Nat, input)) == True{} : Bool},
  +hs: {segsBounded(segs, grammar, input) == True{} : Bool})
  -> {segsBounded(C.growItem(Some{sym}, grammar, w, segs, q, ks, d, k, f), grammar, input) == True{} : Bool}:
  match sym:
    case Core.Terminal{+t}:
      seg_if_when(Core.tokIs(Core.tokAt(w, k), t),
        C.Seg{q, ks, 1n+d, 1n+k, List.append(&2, Core.Tree, f, [Core.Leaf{t}])}, grammar, input,
        ht => db_intro(q, 1n+d, ks, 1n+k, grammar, input, hq, RN.nth_lt(Core.rhsOf(grammar, q), d, Core.Terminal{t}, ei), hks,
          Lemma.le_trans(1n+k, List.length(&2, Nat, w), List.length(&2, Nat, input), RN.tok_lt(w, k, t, ht), hw)))
    case Core.Nonterminal{+x, +need}:
      gp_bounded(grammar, 0n, grammar, input, segs, x, need, q, ks, d, k, f, add_len_zero(grammar), hs, hq, RN.nth_lt(Core.rhsOf(grammar, q), d, Core.Nonterminal{x, need}, ei), hks, hk)

def gi_bounded(item: Maybe<&2, Core.Sym>, +grammar: +List<Core.Production>, +w: +List<Nat>, +input: +List<Nat>, +segs: +List<C.Seg>, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +f: +List<Core.Tree>,
  +ei: {Gll.nthSym(Core.rhsOf(grammar, q), d) == item : Maybe<&2, Core.Sym>}, +hw: {Nat.is_le(List.length(&2, Nat, w), List.length(&2, Nat, input)) == True{} : Bool},
  +hq: {Nat.is_le(1n+q, List.length(&2, Core.Production, grammar)) == True{} : Bool}, +hks: {Nat.is_le(ks, List.length(&2, Nat, input)) == True{} : Bool}, +hk: {Nat.is_le(k, List.length(&2, Nat, input)) == True{} : Bool},
  +hs: {segsBounded(segs, grammar, input) == True{} : Bool})
  -> {segsBounded(C.growItem(item, grammar, w, segs, q, ks, d, k, f), grammar, input) == True{} : Bool}:
  match item:
    case Some{+sym}:
      gi_sym(sym, grammar, w, input, segs, q, ks, d, k, f, ei, hw, hq, hks, hk, hs)
    case None{}:
      {==}

law ga_bounded:
  for ss: +List<C.Seg>
  for +grammar: +List<Core.Production>
  for +w: +List<Nat>
  for +input: +List<Nat>
  for +segs: +List<C.Seg>
  for +hw: {Nat.is_le(List.length(&2, Nat, w), List.length(&2, Nat, input)) == True{} : Bool}
  for +hss: {segsBounded(ss, grammar, input) == True{} : Bool}
  for +hs: {segsBounded(segs, grammar, input) == True{} : Bool}
  {segsBounded(C.growAll(ss, grammar, w, segs), grammar, input) == True{} : Bool}

def ga_bounded(ss, grammar, w, input, segs, hw, hss, hs):
  match ss:
    case Nil{}:
      {==}
    case Con{C.Seg{+q, +ks, +d, +k, +f}, +rest}:
      +hh = Lemma.and_true_left(segBound(C.Seg{q, ks, d, k, f}, grammar, input), segsBounded(rest, grammar, input), hss)
      sb_app(C.growItem(Gll.nthSym(Core.rhsOf(grammar, q), d), grammar, w, segs, q, ks, d, k, f), C.growAll(rest, grammar, w, segs), grammar, input,
        gi_bounded(Gll.nthSym(Core.rhsOf(grammar, q), d), grammar, w, input, segs, q, ks, d, k, f, {==}, hw, db_q(q, d, ks, k, grammar, input, hh), db_ks(q, d, ks, k, grammar, input, hh), db_e(q, d, ks, k, grammar, input, hh), hs),
        ga_bounded(rest, grammar, w, input, segs, hw, Lemma.and_true_right_side(segBound(C.Seg{q, ks, d, k, f}, grammar, input), segsBounded(rest, grammar, input), hss), hs))

# ======== A ROUND THAT ADDS NOTHING: THE SET IS CLOSED ========

law ah_left:
  for a: +List<C.Seg>
  for +b: +List<C.Seg>
  for +segs: +List<C.Seg>
  for +h: {allHave(List.append(&2, C.Seg, a, b), segs) == True{} : Bool}
  {allHave(a, segs) == True{} : Bool}

def ah_left(a, b, segs, h):
  match a:
    case Nil{}:
      {==}
    case Con{C.Seg{+q, +ks, +d, +e, +f}, +rest}:
      Lemma.and_true_intro(C.hasSeg(q, ks, d, e, segs), allHave(rest, segs), Lemma.and_true_left(C.hasSeg(q, ks, d, e, segs), allHave(List.append(&2, C.Seg, rest, b), segs), h),
        ah_left(rest, b, segs, Lemma.and_true_right_side(C.hasSeg(q, ks, d, e, segs), allHave(List.append(&2, C.Seg, rest, b), segs), h)))

law ah_right:
  for a: +List<C.Seg>
  for +b: +List<C.Seg>
  for +segs: +List<C.Seg>
  for +h: {allHave(List.append(&2, C.Seg, a, b), segs) == True{} : Bool}
  {allHave(b, segs) == True{} : Bool}

def ah_right(a, b, segs, h):
  match a:
    case Nil{}:
      h
    case Con{C.Seg{+q, +ks, +d, +e, +f}, +rest}:
      ah_right(rest, b, segs, Lemma.and_true_right_side(C.hasSeg(q, ks, d, e, segs), allHave(List.append(&2, C.Seg, rest, b), segs), h))

def seg_has(b: Bool, +q: Nat, +ks: Nat, +d: Nat, +e: Nat, +f: +List<Core.Tree>, +segs: +List<C.Seg>, +eb: {b == True{} : Bool},
  +h: {allHave(C.segIf(b, C.Seg{q, ks, d, e, f}), segs) == True{} : Bool}) -> {C.hasSeg(q, ks, d, e, segs) == True{} : Bool}:
  match b:
    case True{}:
      Lemma.and_true_left(C.hasSeg(q, ks, d, e, segs), True{}, h)
    case False{}:
      Empty.absurd({C.hasSeg(q, ks, d, e, segs) == True{} : Bool}, Lemma.false_is_not_true(eb))

def when_by(b: Bool, +c: Bool, f: {b == True{} : Bool} -> {c == True{} : Bool}) -> {C.whenB(b, c) == True{} : Bool}:
  match b:
    case True{}:
      f({==})
    case False{}:
      {==}


def comp_in(+grammar: +List<Core.Production>, +segs: +List<C.Seg>, +need: Core.Need, +p: Nat, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +f: +List<Core.Tree>, +p2: Nat, +k2: Nat, +d2: Nat, +e: Nat, +fp: +List<Core.Tree>,
  +hm: {Bool.and(Nat.is_eq(p2, p), Bool.and(Nat.is_eq(k2, k), Nat.is_eq(d2, List.length(&2, Core.Sym, Core.rhsOf(grammar, p))))) == True{} : Bool},
  +h: {allHave(C.segIf(Bool.and(Bool.and(Nat.is_eq(p2, p), Bool.and(Nat.is_eq(k2, k), Nat.is_eq(d2, List.length(&2, Core.Sym, Core.rhsOf(grammar, p))))), Gll.needHolds(need, k, e)), C.Seg{q, ks, 1n+d, e, List.append(&2, Core.Tree, f, [Core.Node{p, fp}])}), segs) == True{} : Bool})
  -> {C.compOk(segs, need, q, ks, d, k, e) == True{} : Bool}:
  when_by(Gll.needHolds(need, k, e), C.hasSeg(q, ks, 1n+d, e, segs),
    hn => seg_has(Bool.and(Bool.and(Nat.is_eq(p2, p), Bool.and(Nat.is_eq(k2, k), Nat.is_eq(d2, List.length(&2, Core.Sym, Core.rhsOf(grammar, p))))), Gll.needHolds(need, k, e)), q, ks, 1n+d, e, List.append(&2, Core.Tree, f, [Core.Node{p, fp}]), segs,
      Lemma.and_true_intro(Bool.and(Nat.is_eq(p2, p), Bool.and(Nat.is_eq(k2, k), Nat.is_eq(d2, List.length(&2, Core.Sym, Core.rhsOf(grammar, p))))), Gll.needHolds(need, k, e), hm, hn), h))

law comps_ok:
  for ss: +List<C.Seg>
  for +grammar: +List<Core.Production>
  for +segs: +List<C.Seg>
  for +need: Core.Need
  for +p: Nat
  for +q: Nat
  for +ks: Nat
  for +d: Nat
  for +k: Nat
  for +f: +List<Core.Tree>
  for +h: {allHave(C.completeWith(ss, grammar, need, p, q, ks, d, k, f), segs) == True{} : Bool}
  {C.compsOk(ss, grammar, segs, need, p, q, ks, d, k) == True{} : Bool}

def comps_ok(ss, grammar, segs, need, p, q, ks, d, k, f, h):
  match ss:
    case Nil{}:
      {==}
    case Con{C.Seg{+p2, +k2, +d2, +e, +fp}, +rest}:
      +s1 = C.segIf(Bool.and(Bool.and(Nat.is_eq(p2, p), Bool.and(Nat.is_eq(k2, k), Nat.is_eq(d2, List.length(&2, Core.Sym, Core.rhsOf(grammar, p))))), Gll.needHolds(need, k, e)), C.Seg{q, ks, 1n+d, e, List.append(&2, Core.Tree, f, [Core.Node{p, fp}])})
      +s2 = C.completeWith(rest, grammar, need, p, q, ks, d, k, f)
      +h1 = ah_left(s1, s2, segs, h)
      Lemma.and_true_intro(C.whenB(Bool.and(Nat.is_eq(p2, p), Bool.and(Nat.is_eq(k2, k), Nat.is_eq(d2, List.length(&2, Core.Sym, Core.rhsOf(grammar, p))))), C.compOk(segs, need, q, ks, d, k, e)), C.compsOk(rest, grammar, segs, need, p, q, ks, d, k),
        when_by(Bool.and(Nat.is_eq(p2, p), Bool.and(Nat.is_eq(k2, k), Nat.is_eq(d2, List.length(&2, Core.Sym, Core.rhsOf(grammar, p))))), C.compOk(segs, need, q, ks, d, k, e), hm => comp_in(grammar, segs, need, p, q, ks, d, k, f, p2, k2, d2, e, fp, hm, h1)),
        comps_ok(rest, grammar, segs, need, p, q, ks, d, k, f, ah_right(s1, s2, segs, h)))

def pp_when(b: Bool, +grammar: +List<Core.Production>, +segs: +List<C.Seg>, +need: Core.Need, +base: Nat, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +f: +List<Core.Tree>,
  +h1: {allHave(C.segIf(b, C.Seg{base, k, 0n, k, []}), segs) == True{} : Bool},
  +h2: {allHave(C.prodPick(b, segs, grammar, need, base, q, ks, d, k, f), segs) == True{} : Bool})
  -> {C.whenB(b, Bool.and(C.hasSeg(base, k, 0n, k, segs), C.compsOk(segs, grammar, segs, need, base, q, ks, d, k))) == True{} : Bool}:
  match b:
    case True{}:
      Lemma.and_true_intro(C.hasSeg(base, k, 0n, k, segs), C.compsOk(segs, grammar, segs, need, base, q, ks, d, k),
        seg_has(True{}, base, k, 0n, k, [], segs, {==}, h1), comps_ok(segs, grammar, segs, need, base, q, ks, d, k, f, h2))
    case False{}:
      {==}

law prods_ok:
  for g: +List<Core.Production>
  for +base: Nat
  for +grammar: +List<Core.Production>
  for +segs: +List<C.Seg>
  for +x: Nat
  for +need: Core.Need
  for +q: Nat
  for +ks: Nat
  for +d: Nat
  for +k: Nat
  for +f: +List<Core.Tree>
  for +h: {allHave(C.growProds(g, base, grammar, segs, x, need, q, ks, d, k, f), segs) == True{} : Bool}
  {C.prodsOk(g, base, grammar, segs, x, need, q, ks, d, k) == True{} : Bool}

def prods_ok(g, base, grammar, segs, x, need, q, ks, d, k, f, h):
  match g:
    case Nil{}:
      {==}
    case Con{Core.Production{+lhs, +rhs}, +rest}:
      +a1 = C.segIf(Nat.is_eq(lhs, x), C.Seg{base, k, 0n, k, []})
      +a2 = C.prodPick(Nat.is_eq(lhs, x), segs, grammar, need, base, q, ks, d, k, f)
      +a3 = C.growProds(rest, 1n+base, grammar, segs, x, need, q, ks, d, k, f)
      +h23 = ah_right(a1, List.append(&2, C.Seg, a2, a3), segs, h)
      Lemma.and_true_intro(C.whenB(Nat.is_eq(lhs, x), Bool.and(C.hasSeg(base, k, 0n, k, segs), C.compsOk(segs, grammar, segs, need, base, q, ks, d, k))), C.prodsOk(rest, 1n+base, grammar, segs, x, need, q, ks, d, k),
        pp_when(Nat.is_eq(lhs, x), grammar, segs, need, base, q, ks, d, k, f, ah_left(a1, List.append(&2, C.Seg, a2, a3), segs, h), ah_left(a2, a3, segs, h23)),
        prods_ok(rest, 1n+base, grammar, segs, x, need, q, ks, d, k, f, ah_right(a2, a3, segs, h23)))

def ext_sym(sym: Core.Sym, +grammar: +List<Core.Production>, +w: +List<Nat>, +segs: +List<C.Seg>, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +f: +List<Core.Tree>,
  +h: {allHave(C.growItem(Some{sym}, grammar, w, segs, q, ks, d, k, f), segs) == True{} : Bool})
  -> {C.extOk(Some{sym}, grammar, w, segs, q, ks, d, k) == True{} : Bool}:
  match sym:
    case Core.Terminal{+t}:
      when_by(Core.tokIs(Core.tokAt(w, k), t), C.hasSeg(q, ks, 1n+d, 1n+k, segs),
        ht => seg_has(Core.tokIs(Core.tokAt(w, k), t), q, ks, 1n+d, 1n+k, List.append(&2, Core.Tree, f, [Core.Leaf{t}]), segs, ht, h))
    case Core.Nonterminal{+x, +need}:
      prods_ok(grammar, 0n, grammar, segs, x, need, q, ks, d, k, f, h)

def ext_ok(item: Maybe<&2, Core.Sym>, +grammar: +List<Core.Production>, +w: +List<Nat>, +segs: +List<C.Seg>, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +f: +List<Core.Tree>,
  +h: {allHave(C.growItem(item, grammar, w, segs, q, ks, d, k, f), segs) == True{} : Bool})
  -> {C.extOk(item, grammar, w, segs, q, ks, d, k) == True{} : Bool}:
  match item:
    case Some{+sym}:
      ext_sym(sym, grammar, w, segs, q, ks, d, k, f, h)
    case None{}:
      {==}

# A round whose segments are all present: the set is closed.
law closed_from:
  for ss: +List<C.Seg>
  for +grammar: +List<Core.Production>
  for +w: +List<Nat>
  for +segs: +List<C.Seg>
  for +h: {allHave(C.growAll(ss, grammar, w, segs), segs) == True{} : Bool}
  {C.closedAll(ss, grammar, w, segs) == True{} : Bool}

def closed_from(ss, grammar, w, segs, h):
  match ss:
    case Nil{}:
      {==}
    case Con{C.Seg{+q, +ks, +d, +k, +f}, +rest}:
      +a1 = C.growItem(Gll.nthSym(Core.rhsOf(grammar, q), d), grammar, w, segs, q, ks, d, k, f)
      +a2 = C.growAll(rest, grammar, w, segs)
      Lemma.and_true_intro(C.extOk(Gll.nthSym(Core.rhsOf(grammar, q), d), grammar, w, segs, q, ks, d, k), C.closedAll(rest, grammar, w, segs),
        ext_ok(Gll.nthSym(Core.rhsOf(grammar, q), d), grammar, w, segs, q, ks, d, k, f, ah_left(a1, a2, segs, h)),
        closed_from(rest, grammar, w, segs, ah_right(a1, a2, segs, h)))

# ======== THE GROWTH ENDS CLOSED ========

def GSame(+grammar: +List<Core.Production>, +w: +List<Nat>, +segs: +List<C.Seg>) -> Type:
  {C.addNew(C.growAll(segs, grammar, w, segs), segs) == segs : +List<C.Seg>} & {C.closedAll(segs, grammar, w, segs) == True{} : Bool}

def GRes(+grammar: +List<Core.Production>, +w: +List<Nat>, +input: +List<Nat>, +segs: +List<C.Seg>) -> Type:
  Either<GSame(grammar, w, segs), {Nat.is_le(1n+rMeas(grammar, input, C.addNew(C.growAll(segs, grammar, w, segs), segs)), rMeas(grammar, input, segs)) == True{} : Bool}>

def g_same(+grammar: +List<Core.Production>, +w: +List<Nat>, +input: +List<Nat>, +segs: +List<C.Seg>, p: ASame(C.growAll(segs, grammar, w, segs), segs)) -> GRes(grammar, w, input, segs):
  match p:
    case (+eq, +have):
      Inl{(eq, closed_from(segs, grammar, w, segs, have))}

def g_round(+grammar: +List<Core.Production>, +w: +List<Nat>, +input: +List<Nat>, +segs: +List<C.Seg>, r: ARes(grammar, input, C.growAll(segs, grammar, w, segs), segs)) -> GRes(grammar, w, input, segs):
  match r:
    case Inl{p}:
      g_same(grammar, w, input, segs, p)
    case Inr{m}:
      Inr{m}

law until_keep:
  for n: Nat
  for done: Bool
  for +grammar: +List<Core.Production>
  for +w: +List<Nat>
  for +segs: +List<C.Seg>
  for +q: Nat
  for +ks: Nat
  for +d: Nat
  for +e: Nat
  for +h: {C.hasSeg(q, ks, d, e, segs) == True{} : Bool}
  {C.hasSeg(q, ks, d, e, C.growUntil(n, done, grammar, w, segs)) == True{} : Bool}

def until_keep(n, done, grammar, w, segs, q, ks, d, e, h):
  match n:
    case 0n:
      h
    case 1n+(+p):
      match done:
        case True{}:
          h
        case False{}:
          until_keep(p, C.closedAll(C.addNew(C.growAll(segs, grammar, w, segs), segs), grammar, w, C.addNew(C.growAll(segs, grammar, w, segs), segs)), grammar, w, C.addNew(C.growAll(segs, grammar, w, segs), segs), q, ks, d, e, an_keep(C.growAll(segs, grammar, w, segs), segs, q, ks, d, e, h))

law grow_keep:
  for n: Nat
  for +grammar: +List<Core.Production>
  for +w: +List<Nat>
  for +segs: +List<C.Seg>
  for +q: Nat
  for +ks: Nat
  for +d: Nat
  for +e: Nat
  for +h: {C.hasSeg(q, ks, d, e, segs) == True{} : Bool}
  {C.hasSeg(q, ks, d, e, C.grow(n, grammar, w, segs)) == True{} : Bool}

def grow_keep(n, grammar, w, segs, q, ks, d, e, h):
  until_keep(n, C.closedAll(segs, grammar, w, segs), grammar, w, segs, q, ks, d, e, h)

# Segments that are not closed are not left alone by a round.
def closed_clash(+grammar: +List<Core.Production>, +w: +List<Nat>, +segs: +List<C.Seg>,
  +hd: {C.closedAll(segs, grammar, w, segs) == False{} : Bool}, +cl: {C.closedAll(segs, grammar, w, segs) == True{} : Bool}) -> {False{} == True{} : Bool}:
  %hd : {_ == True{} : Bool}
  cl

def gfix_same(+f: Nat, +grammar: +List<Core.Production>, +w: +List<Nat>, +segs: +List<C.Seg>, p: GSame(grammar, w, segs),
  +hd: {C.closedAll(segs, grammar, w, segs) == False{} : Bool}) -> {C.closedAll(C.growUntil(f, C.closedAll(C.addNew(C.growAll(segs, grammar, w, segs), segs), grammar, w, C.addNew(C.growAll(segs, grammar, w, segs), segs)), grammar, w, C.addNew(C.growAll(segs, grammar, w, segs), segs)), grammar, w, C.growUntil(f, C.closedAll(C.addNew(C.growAll(segs, grammar, w, segs), segs), grammar, w, C.addNew(C.growAll(segs, grammar, w, segs), segs)), grammar, w, C.addNew(C.growAll(segs, grammar, w, segs), segs))) == True{} : Bool}:
  match p:
    case (eq, +cl):
      Empty.absurd({C.closedAll(C.growUntil(f, C.closedAll(C.addNew(C.growAll(segs, grammar, w, segs), segs), grammar, w, C.addNew(C.growAll(segs, grammar, w, segs), segs)), grammar, w, C.addNew(C.growAll(segs, grammar, w, segs), segs)), grammar, w, C.growUntil(f, C.closedAll(C.addNew(C.growAll(segs, grammar, w, segs), segs), grammar, w, C.addNew(C.growAll(segs, grammar, w, segs), segs)), grammar, w, C.addNew(C.growAll(segs, grammar, w, segs), segs))) == True{} : Bool}, Lemma.false_is_not_true(closed_clash(grammar, w, segs, hd, cl)))

def gfix_step(+f: Nat, +grammar: +List<Core.Production>, +w: +List<Nat>, +input: +List<Nat>, +segs: +List<C.Seg>, r: GRes(grammar, w, input, segs),
  +hd: {C.closedAll(segs, grammar, w, segs) == False{} : Bool},
  +hf: {Nat.is_le(rMeas(grammar, input, segs), f) == True{} : Bool},
  later: {Nat.is_le(1n+rMeas(grammar, input, C.addNew(C.growAll(segs, grammar, w, segs), segs)), f) == True{} : Bool} -> {C.closedAll(C.growUntil(f, C.closedAll(C.addNew(C.growAll(segs, grammar, w, segs), segs), grammar, w, C.addNew(C.growAll(segs, grammar, w, segs), segs)), grammar, w, C.addNew(C.growAll(segs, grammar, w, segs), segs)), grammar, w, C.growUntil(f, C.closedAll(C.addNew(C.growAll(segs, grammar, w, segs), segs), grammar, w, C.addNew(C.growAll(segs, grammar, w, segs), segs)), grammar, w, C.addNew(C.growAll(segs, grammar, w, segs), segs))) == True{} : Bool})
  -> {C.closedAll(C.growUntil(f, C.closedAll(C.addNew(C.growAll(segs, grammar, w, segs), segs), grammar, w, C.addNew(C.growAll(segs, grammar, w, segs), segs)), grammar, w, C.addNew(C.growAll(segs, grammar, w, segs), segs)), grammar, w, C.growUntil(f, C.closedAll(C.addNew(C.growAll(segs, grammar, w, segs), segs), grammar, w, C.addNew(C.growAll(segs, grammar, w, segs), segs)), grammar, w, C.addNew(C.growAll(segs, grammar, w, segs), segs))) == True{} : Bool}:
  match r:
    case Inl{p}:
      gfix_same(f, grammar, w, segs, p, hd)
    case Inr{m}:
      later(Lemma.le_trans(1n+rMeas(grammar, input, C.addNew(C.growAll(segs, grammar, w, segs), segs)), rMeas(grammar, input, segs), f, m, hf))

# Growing segments whose closedness is `done` ends closed when there are more rounds than
# the count: a round either adds a segment (the count drops) or finds them closed already.
law until_closed:
  for n: Nat
  for done: Bool
  for +grammar: +List<Core.Production>
  for +w: +List<Nat>
  for +input: +List<Nat>
  for +segs: +List<C.Seg>
  for +hw: {Nat.is_le(List.length(&2, Nat, w), List.length(&2, Nat, input)) == True{} : Bool}
  for +hs: {segsBounded(segs, grammar, input) == True{} : Bool}
  for +hd: {C.closedAll(segs, grammar, w, segs) == done : Bool}
  for +hf: {Nat.is_le(1n+rMeas(grammar, input, segs), n) == True{} : Bool}
  {C.closedAll(C.growUntil(n, done, grammar, w, segs), grammar, w, C.growUntil(n, done, grammar, w, segs)) == True{} : Bool}

def until_closed(n, done, grammar, w, input, segs, hw, hs, hd, hf):
  match n:
    case 0n:
      Empty.absurd({C.closedAll(C.growUntil(0n, done, grammar, w, segs), grammar, w, C.growUntil(0n, done, grammar, w, segs)) == True{} : Bool}, Lemma.false_is_not_true(hf))
    case 1n+(+f):
      match done:
        case True{}:
          hd
        case False{}:
          gfix_step(f, grammar, w, input, segs, g_round(grammar, w, input, segs, ares(C.growAll(segs, grammar, w, segs), grammar, input, segs, ga_bounded(segs, grammar, w, input, segs, hw, hs, hs))), hd, hf,
            h2 => until_closed(f, C.closedAll(C.addNew(C.growAll(segs, grammar, w, segs), segs), grammar, w, C.addNew(C.growAll(segs, grammar, w, segs), segs)), grammar, w, input, C.addNew(C.growAll(segs, grammar, w, segs), segs), hw, an_bounded(C.growAll(segs, grammar, w, segs), segs, grammar, input, ga_bounded(segs, grammar, w, input, segs, hw, hs, hs), hs), {==}, h2))

law closure_fix:
  for n: Nat
  for +grammar: +List<Core.Production>
  for +w: +List<Nat>
  for +input: +List<Nat>
  for +segs: +List<C.Seg>
  for +hw: {Nat.is_le(List.length(&2, Nat, w), List.length(&2, Nat, input)) == True{} : Bool}
  for +hs: {segsBounded(segs, grammar, input) == True{} : Bool}
  for +hf: {Nat.is_le(1n+rMeas(grammar, input, segs), n) == True{} : Bool}
  {C.closedAll(C.grow(n, grammar, w, segs), grammar, w, C.grow(n, grammar, w, segs)) == True{} : Bool}

def closure_fix(n, grammar, w, input, segs, hw, hs, hf):
  until_closed(n, C.closedAll(segs, grammar, w, segs), grammar, w, input, segs, hw, hs, {==}, hf)

def len_to2(+fuel: Nat, +us: +List<Gll.Desc>, +hf: {Nat.is_le(1n+List.length(&2, Gll.Desc, us), fuel) == True{} : Bool})
  -> {Nat.is_le(1n+Run.countNot(us, []), fuel) == True{} : Bool}:
  %Equal.sym(Nat, Run.countNot(us, []), List.length(&2, Gll.Desc, us), PC.count_empty(us)) : {Nat.is_le(1n+_, fuel) == True{} : Bool}
  hf

def seed_meas(+fuel: Nat, +grammar: +List<Core.Production>, +input: +List<Nat>, +m: Nat, +i: Nat, +hf: {Nat.is_le(1n+List.length(&2, Gll.Desc, Run.univ(grammar, input)), fuel) == True{} : Bool})
  -> {Nat.is_le(1n+rMeas(grammar, input, [C.Seg{m, i, 0n, i, []}]), fuel) == True{} : Bool}:
  Lemma.le_trans(1n+rMeas(grammar, input, [C.Seg{m, i, 0n, i, []}]), 1n+Run.countNot(Run.univ(grammar, input), []), fuel,
    PC.count_mono(Run.univ(grammar, input), [], segDescs([C.Seg{m, i, 0n, i, []}]), {==}), len_to2(fuel, Run.univ(grammar, input), hf))

# THE CLOSURE ENDS CLOSED: for a production m within the grammar and a start i within w,
# with w no longer than the input and fuel 1 + the size of the input's descriptor universe,
# the segments grown on w from m at i are closed and have m's start.
law closure_closed:
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +w: +List<Nat>
  for +input: +List<Nat>
  for +m: Nat
  for +i: Nat
  for +hm: {Nat.is_le(1n+m, List.length(&2, Core.Production, grammar)) == True{} : Bool}
  for +hi: {Nat.is_le(i, List.length(&2, Nat, w)) == True{} : Bool}
  for +hw: {Nat.is_le(List.length(&2, Nat, w), List.length(&2, Nat, input)) == True{} : Bool}
  for +hf: {Nat.is_le(1n+List.length(&2, Gll.Desc, Run.univ(grammar, input)), fuel) == True{} : Bool}
  {Bool.and(C.closedAll(C.segsFrom(fuel, grammar, w, m, i), grammar, w, C.segsFrom(fuel, grammar, w, m, i)), C.hasSeg(m, i, 0n, i, C.segsFrom(fuel, grammar, w, m, i))) == True{} : Bool}

def closure_closed(fuel, grammar, w, input, m, i, hm, hi, hw, hf):
  +seed = {[C.Seg{m, i, 0n, i, []}] : +List<C.Seg>}
  +hi2 = Lemma.le_trans(i, List.length(&2, Nat, w), List.length(&2, Nat, input), hi, hw)
  Lemma.and_true_intro(C.closedAll(C.segsFrom(fuel, grammar, w, m, i), grammar, w, C.segsFrom(fuel, grammar, w, m, i)), C.hasSeg(m, i, 0n, i, C.segsFrom(fuel, grammar, w, m, i)),
    closure_fix(fuel, grammar, w, input, seed, hw,
      Lemma.and_true_intro(segBound(C.Seg{m, i, 0n, i, []}, grammar, input), True{}, db_intro(m, 0n, i, i, grammar, input, hm, Lemma.zero_le(List.length(&2, Core.Sym, Core.rhsOf(grammar, m))), hi2, hi2), {==}),
      seed_meas(fuel, grammar, input, m, i, hf)),
    grow_keep(fuel, grammar, w, seed, m, i, 0n, i, Lemma.or_true_left_intro(C.keyIs(m, i, 0n, i, C.Seg{m, i, 0n, i, []}), False{}, key_refl(m, i, 0n, i, []))))

# ======== EVERY SEGMENT'S FOREST READS ITS ITEMS ========

# Segment (q, ks, d, e) with forest f: f reads the first d items of q on w from ks to e.
def segOk(+grammar: +List<Core.Production>, +w: +List<Nat>, s: C.Seg) -> Bool:
  match s:
    case C.Seg{+q, +ks, +d, +e, +f}:
      Bool.and(Core.reads(f, grammar, WS.takeN(d, Core.rhsOf(grammar, q)), w, ks),
        Bool.and(Nat.is_eq(G.endOf(f, ks), e), Nat.is_eq(List.length(&2, Core.Tree, f), d)))

def segsOk(segs: +List<C.Seg>, +grammar: +List<Core.Production>, +w: +List<Nat>) -> Bool:
  match segs:
    case Nil{}:
      True{}
    case Con{+s, rest}:
      Bool.and(segOk(grammar, w, s), segsOk(rest, grammar, w))

def symOf(m: Maybe<&2, Core.Sym>, +dflt: Core.Sym) -> Core.Sym:
  match m:
    case Some{+y}:
      y
    case None{}:
      dflt

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

def reads_at(+t: Core.Tree, +y: Core.Sym, +grammar: +List<Core.Production>, +w: +List<Nat>, +a: Nat, +b: Nat, +e: {a == b : Nat},
  +h: {Core.reads([t], grammar, [y], w, b) == True{} : Bool}) -> {Core.reads([t], grammar, [y], w, a) == True{} : Bool}:
  %Equal.sym(Nat, a, b, e) : {Core.reads([t], grammar, [y], w, _) == True{} : Bool}
  h

def reads_take(+f: +List<Core.Tree>, +grammar: +List<Core.Production>, +w: +List<Nat>, +ks: Nat, +d: Nat, +items: +List<Core.Sym>, +y: Core.Sym,
  +ie: {G.dropFrom(d, items) == y <> G.dropFrom(1n+d, items) : +List<Core.Sym>},
  +h: {Core.reads(f, grammar, List.append(&2, Core.Sym, WS.takeN(d, items), [y]), w, ks) == True{} : Bool})
  -> {Core.reads(f, grammar, WS.takeN(1n+d, items), w, ks) == True{} : Bool}:
  %Equal.sym(+List<Core.Sym>, WS.takeN(1n+d, items), List.append(&2, Core.Sym, WS.takeN(d, items), [y]), WS.take_snoc(d, items, y, G.dropFrom(1n+d, items), ie)) : {Core.reads(f, grammar, _, w, ks) == True{} : Bool}
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
def snoc_ok(+grammar: +List<Core.Production>, +w: +List<Nat>, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +f: +List<Core.Tree>, +t: Core.Tree, +y: Core.Sym, +e2: Nat,
  +ei: {Gll.nthSym(Core.rhsOf(grammar, q), d) == Some{y} : Maybe<&2, Core.Sym>},
  +hp: {segOk(grammar, w, C.Seg{q, ks, d, k, f}) == True{} : Bool},
  +hr: {Core.reads([t], grammar, [y], w, k) == True{} : Bool},
  +he: {G.endOf([t], k) == e2 : Nat})
  -> {segOk(grammar, w, C.Seg{q, ks, 1n+d, e2, List.append(&2, Core.Tree, f, [t])}) == True{} : Bool}:
  +RD = {Core.reads(f, grammar, WS.takeN(d, Core.rhsOf(grammar, q)), w, ks) : Bool}
  +EN = {Nat.is_eq(G.endOf(f, ks), k) : Bool}
  +LN = {Nat.is_eq(List.length(&2, Core.Tree, f), d) : Bool}
  +r1 = Lemma.and_true_left(RD, Bool.and(EN, LN), hp)
  +r2 = Lemma.and_true_right_side(RD, Bool.and(EN, LN), hp)
  +ek = Lemma.nat_eq_sound(G.endOf(f, ks), k, Lemma.and_true_left(EN, LN, r2))
  +ed = Lemma.nat_eq_sound(List.length(&2, Core.Tree, f), d, Lemma.and_true_right_side(EN, LN, r2))
  +f2 = List.append(&2, Core.Tree, f, [t])
  +rd = reads_take(f2, grammar, w, ks, d, Core.rhsOf(grammar, q), y, nth_to_drop(Core.rhsOf(grammar, q), d, y, ei),
    WS.reads_snoc(f, WS.takeN(d, Core.rhsOf(grammar, q)), grammar, w, ks, t, y, r1, reads_at(t, y, grammar, w, G.endOf(f, ks), k, ek, hr)))
  Lemma.and_true_intro(Core.reads(f2, grammar, WS.takeN(1n+d, Core.rhsOf(grammar, q)), w, ks), Bool.and(Nat.is_eq(G.endOf(f2, ks), e2), Nat.is_eq(List.length(&2, Core.Tree, f2), 1n+d)), rd,
    Lemma.and_true_intro(Nat.is_eq(G.endOf(f2, ks), e2), Nat.is_eq(List.length(&2, Core.Tree, f2), 1n+d),
      eq_is(G.endOf(f2, ks), e2, end_to(f, t, ks, k, e2, ek, he)), eq_is(List.length(&2, Core.Tree, f2), 1n+d, len_to(f, t, d, ed))))

def seed_ok(+grammar: +List<Core.Production>, +w: +List<Nat>, +base: Nat, +k: Nat) -> {segOk(grammar, w, C.Seg{base, k, 0n, k, []}) == True{} : Bool}:
  Lemma.and_true_intro(True{}, Bool.and(Nat.is_eq(k, k), True{}), {==}, Lemma.and_true_intro(Nat.is_eq(k, k), True{}, Lemma.nat_eq_refl(k), {==}))

def leaf_ok(+grammar: +List<Core.Production>, +w: +List<Nat>, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +f: +List<Core.Tree>, +t: Nat,
  +ei: {Gll.nthSym(Core.rhsOf(grammar, q), d) == Some{Core.Terminal{t}} : Maybe<&2, Core.Sym>},
  +hp: {segOk(grammar, w, C.Seg{q, ks, d, k, f}) == True{} : Bool},
  +ht: {Core.tokIs(Core.tokAt(w, k), t) == True{} : Bool})
  -> {segOk(grammar, w, C.Seg{q, ks, 1n+d, 1n+k, List.append(&2, Core.Tree, f, [Core.Leaf{t}])}) == True{} : Bool}:
  snoc_ok(grammar, w, q, ks, d, k, f, Core.Leaf{t}, Core.Terminal{t}, 1n+k, ei, hp,
    Lemma.and_true_intro(Nat.is_eq(t, t), Bool.and(Core.tokIs(Core.tokAt(w, k), t), True{}), Lemma.nat_eq_refl(t), Lemma.and_true_intro(Core.tokIs(Core.tokAt(w, k), t), True{}, ht, {==})),
    {==})

def node_ok(+grammar: +List<Core.Production>, +w: +List<Nat>, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +f: +List<Core.Tree>, +p: Nat, +x: Nat, +need: Core.Need, +e: Nat, +fp: +List<Core.Tree>,
  +ei: {Gll.nthSym(Core.rhsOf(grammar, q), d) == Some{Core.Nonterminal{x, need}} : Maybe<&2, Core.Sym>},
  +hp: {segOk(grammar, w, C.Seg{q, ks, d, k, f}) == True{} : Bool},
  +hc: {segOk(grammar, w, C.Seg{p, k, List.length(&2, Core.Sym, Core.rhsOf(grammar, p)), e, fp}) == True{} : Bool},
  +hl: {Core.lhsIs(grammar, p, x) == True{} : Bool},
  +hn: {Gll.needHolds(need, k, e) == True{} : Bool})
  -> {segOk(grammar, w, C.Seg{q, ks, 1n+d, e, List.append(&2, Core.Tree, f, [Core.Node{p, fp}])}) == True{} : Bool}:
  +RD = {Core.reads(fp, grammar, WS.takeN(List.length(&2, Core.Sym, Core.rhsOf(grammar, p)), Core.rhsOf(grammar, p)), w, k) : Bool}
  +EN = {Nat.is_eq(G.endOf(fp, k), e) : Bool}
  +LN = {Nat.is_eq(List.length(&2, Core.Tree, fp), List.length(&2, Core.Sym, Core.rhsOf(grammar, p))) : Bool}
  +r2 = Lemma.and_true_right_side(RD, Bool.and(EN, LN), hc)
  +rd = WS.reads_all(grammar, w, fp, Core.rhsOf(grammar, p), k, Lemma.and_true_left(RD, Bool.and(EN, LN), hc))
  +ec = Lemma.nat_eq_sound(G.endOf(fp, k), e, Lemma.and_true_left(EN, LN, r2))
  +wd = Core.width(Core.Node{p, fp})
  +hw = Equal.trans(Nat, Nat.add(k, wd), G.endOf(fp, k), e, Equal.sym(Nat, G.endOf(fp, k), Nat.add(k, wd), G.end_node(p, fp, k)), ec)
  +nk = WS.need_ok(need, k, wd, WS.need_to(need, k, e, Nat.add(k, wd), hw, hn))
  +head = {Bool.and(Core.lhsIs(grammar, p, x), Core.needOk(need, wd)) : Bool}
  +own = {Bool.and(head, Core.reads(fp, grammar, Core.rhsOf(grammar, p), w, k)) : Bool}
  +hr = Lemma.and_true_intro(own, True{}, Lemma.and_true_intro(head, Core.reads(fp, grammar, Core.rhsOf(grammar, p), w, k), Lemma.and_true_intro(Core.lhsIs(grammar, p, x), Core.needOk(need, wd), hl, nk), rd), {==})
  snoc_ok(grammar, w, q, ks, d, k, f, Core.Node{p, fp}, Core.Nonterminal{x, need}, e, ei, hp, hr, hw)

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
  for a: +List<C.Seg>
  for +b: +List<C.Seg>
  for +grammar: +List<Core.Production>
  for +w: +List<Nat>
  for +ha: {segsOk(a, grammar, w) == True{} : Bool}
  for +hb: {segsOk(b, grammar, w) == True{} : Bool}
  {segsOk(List.append(&2, C.Seg, a, b), grammar, w) == True{} : Bool}

def so_app(a, b, grammar, w, ha, hb):
  match a:
    case Nil{}:
      hb
    case Con{+s, +rest}:
      Lemma.and_true_intro(segOk(grammar, w, s), segsOk(List.append(&2, C.Seg, rest, b), grammar, w), Lemma.and_true_left(segOk(grammar, w, s), segsOk(rest, grammar, w), ha),
        so_app(rest, b, grammar, w, Lemma.and_true_right_side(segOk(grammar, w, s), segsOk(rest, grammar, w), ha), hb))

def seg_if_ok(b: Bool, +s: C.Seg, +grammar: +List<Core.Production>, +w: +List<Nat>, f: {b == True{} : Bool} -> {segOk(grammar, w, s) == True{} : Bool}) -> {segsOk(C.segIf(b, s), grammar, w) == True{} : Bool}:
  match b:
    case True{}:
      Lemma.and_true_intro(segOk(grammar, w, s), True{}, f({==}), {==})
    case False{}:
      {==}

def seg_to3(+grammar: +List<Core.Production>, +w: +List<Nat>, +p2: Nat, +k2: Nat, +d2: Nat, +e: Nat, +fp: +List<Core.Tree>, +p: Nat, +k: Nat, +d: Nat,
  +e1: {p2 == p : Nat}, +e2: {k2 == k : Nat}, +e3: {d2 == d : Nat}, +h: {segOk(grammar, w, C.Seg{p2, k2, d2, e, fp}) == True{} : Bool})
  -> {segOk(grammar, w, C.Seg{p, k, d, e, fp}) == True{} : Bool}:
  %e1 : {segOk(grammar, w, C.Seg{_, k, d, e, fp}) == True{} : Bool}
  %e2 : {segOk(grammar, w, C.Seg{p2, _, d, e, fp}) == True{} : Bool}
  %e3 : {segOk(grammar, w, C.Seg{p2, k2, _, e, fp}) == True{} : Bool}
  h

def hit_ok(+grammar: +List<Core.Production>, +w: +List<Nat>, +need: Core.Need, +p: Nat, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +f: +List<Core.Tree>, +x: Nat, +p2: Nat, +k2: Nat, +d2: Nat, +e: Nat, +fp: +List<Core.Tree>,
  +hh: {segOk(grammar, w, C.Seg{p2, k2, d2, e, fp}) == True{} : Bool}, +hp: {segOk(grammar, w, C.Seg{q, ks, d, k, f}) == True{} : Bool},
  +ei: {Gll.nthSym(Core.rhsOf(grammar, q), d) == Some{Core.Nonterminal{x, need}} : Maybe<&2, Core.Sym>}, +hl: {Core.lhsIs(grammar, p, x) == True{} : Bool},
  +hit: {Bool.and(Bool.and(Nat.is_eq(p2, p), Bool.and(Nat.is_eq(k2, k), Nat.is_eq(d2, List.length(&2, Core.Sym, Core.rhsOf(grammar, p))))), Gll.needHolds(need, k, e)) == True{} : Bool})
  -> {segOk(grammar, w, C.Seg{q, ks, 1n+d, e, List.append(&2, Core.Tree, f, [Core.Node{p, fp}])}) == True{} : Bool}:
  +m = Lemma.and_true_left(Bool.and(Nat.is_eq(p2, p), Bool.and(Nat.is_eq(k2, k), Nat.is_eq(d2, List.length(&2, Core.Sym, Core.rhsOf(grammar, p))))), Gll.needHolds(need, k, e), hit)
  +m2 = Lemma.and_true_right_side(Nat.is_eq(p2, p), Bool.and(Nat.is_eq(k2, k), Nat.is_eq(d2, List.length(&2, Core.Sym, Core.rhsOf(grammar, p)))), m)
  +hc = seg_to3(grammar, w, p2, k2, d2, e, fp, p, k, List.length(&2, Core.Sym, Core.rhsOf(grammar, p)),
    Lemma.nat_eq_sound(p2, p, Lemma.and_true_left(Nat.is_eq(p2, p), Bool.and(Nat.is_eq(k2, k), Nat.is_eq(d2, List.length(&2, Core.Sym, Core.rhsOf(grammar, p)))), m)),
    Lemma.nat_eq_sound(k2, k, Lemma.and_true_left(Nat.is_eq(k2, k), Nat.is_eq(d2, List.length(&2, Core.Sym, Core.rhsOf(grammar, p))), m2)),
    Lemma.nat_eq_sound(d2, List.length(&2, Core.Sym, Core.rhsOf(grammar, p)), Lemma.and_true_right_side(Nat.is_eq(k2, k), Nat.is_eq(d2, List.length(&2, Core.Sym, Core.rhsOf(grammar, p))), m2)), hh)
  node_ok(grammar, w, q, ks, d, k, f, p, x, need, e, fp, ei, hp, hc, hl, Lemma.and_true_right_side(Bool.and(Nat.is_eq(p2, p), Bool.and(Nat.is_eq(k2, k), Nat.is_eq(d2, List.length(&2, Core.Sym, Core.rhsOf(grammar, p))))), Gll.needHolds(need, k, e), hit))

law cw_ok:
  for ss: +List<C.Seg>
  for +grammar: +List<Core.Production>
  for +w: +List<Nat>
  for +need: Core.Need
  for +p: Nat
  for +q: Nat
  for +ks: Nat
  for +d: Nat
  for +k: Nat
  for +f: +List<Core.Tree>
  for +x: Nat
  for +hss: {segsOk(ss, grammar, w) == True{} : Bool}
  for +hp: {segOk(grammar, w, C.Seg{q, ks, d, k, f}) == True{} : Bool}
  for +ei: {Gll.nthSym(Core.rhsOf(grammar, q), d) == Some{Core.Nonterminal{x, need}} : Maybe<&2, Core.Sym>}
  for +hl: {Core.lhsIs(grammar, p, x) == True{} : Bool}
  {segsOk(C.completeWith(ss, grammar, need, p, q, ks, d, k, f), grammar, w) == True{} : Bool}

def cw_ok(ss, grammar, w, need, p, q, ks, d, k, f, x, hss, hp, ei, hl):
  match ss:
    case Nil{}:
      {==}
    case Con{C.Seg{+p2, +k2, +d2, +e, +fp}, +rest}:
      +hh = Lemma.and_true_left(segOk(grammar, w, C.Seg{p2, k2, d2, e, fp}), segsOk(rest, grammar, w), hss)
      +hit = Bool.and(Bool.and(Nat.is_eq(p2, p), Bool.and(Nat.is_eq(k2, k), Nat.is_eq(d2, List.length(&2, Core.Sym, Core.rhsOf(grammar, p))))), Gll.needHolds(need, k, e))
      +ns = {C.Seg{q, ks, 1n+d, e, List.append(&2, Core.Tree, f, [Core.Node{p, fp}])} : C.Seg}
      so_app(C.segIf(hit, ns), C.completeWith(rest, grammar, need, p, q, ks, d, k, f), grammar, w,
        seg_if_ok(hit, ns, grammar, w, h => hit_ok(grammar, w, need, p, q, ks, d, k, f, x, p2, k2, d2, e, fp, hh, hp, ei, hl, h)),
        cw_ok(rest, grammar, w, need, p, q, ks, d, k, f, x, Lemma.and_true_right_side(segOk(grammar, w, C.Seg{p2, k2, d2, e, fp}), segsOk(rest, grammar, w), hss), hp, ei, hl))

def pp_ok(b: Bool, +segs: +List<C.Seg>, +grammar: +List<Core.Production>, +w: +List<Nat>, +need: Core.Need, +base: Nat, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +f: +List<Core.Tree>, +x: Nat,
  +lhs: Nat, +rhs: +List<Core.Sym>, +rest: +List<Core.Production>, +eb: {Nat.is_eq(lhs, x) == b : Bool},
  +hsuf: {dropP(base, grammar) == Core.Production{lhs, rhs} <> rest : +List<Core.Production>},
  +hs: {segsOk(segs, grammar, w) == True{} : Bool}, +hp: {segOk(grammar, w, C.Seg{q, ks, d, k, f}) == True{} : Bool},
  +ei: {Gll.nthSym(Core.rhsOf(grammar, q), d) == Some{Core.Nonterminal{x, need}} : Maybe<&2, Core.Sym>})
  -> {segsOk(C.prodPick(b, segs, grammar, need, base, q, ks, d, k, f), grammar, w) == True{} : Bool}:
  match b:
    case True{}:
      cw_ok(segs, grammar, w, need, base, q, ks, d, k, f, x, hs, hp, ei, lhs_from_drop(grammar, base, lhs, rhs, rest, x, hsuf, eb))
    case False{}:
      {==}

law gp_ok:
  for g: +List<Core.Production>
  for +base: Nat
  for +grammar: +List<Core.Production>
  for +w: +List<Nat>
  for +segs: +List<C.Seg>
  for +x: Nat
  for +need: Core.Need
  for +q: Nat
  for +ks: Nat
  for +d: Nat
  for +k: Nat
  for +f: +List<Core.Tree>
  for +hsuf: {dropP(base, grammar) == g : +List<Core.Production>}
  for +hs: {segsOk(segs, grammar, w) == True{} : Bool}
  for +hp: {segOk(grammar, w, C.Seg{q, ks, d, k, f}) == True{} : Bool}
  for +ei: {Gll.nthSym(Core.rhsOf(grammar, q), d) == Some{Core.Nonterminal{x, need}} : Maybe<&2, Core.Sym>}
  {segsOk(C.growProds(g, base, grammar, segs, x, need, q, ks, d, k, f), grammar, w) == True{} : Bool}

def gp_ok(g, base, grammar, w, segs, x, need, q, ks, d, k, f, hsuf, hs, hp, ei):
  match g:
    case Nil{}:
      {==}
    case Con{Core.Production{+lhs, +rhs}, +rest}:
      +a2 = C.prodPick(Nat.is_eq(lhs, x), segs, grammar, need, base, q, ks, d, k, f)
      +a3 = C.growProds(rest, 1n+base, grammar, segs, x, need, q, ks, d, k, f)
      so_app(C.segIf(Nat.is_eq(lhs, x), C.Seg{base, k, 0n, k, []}), List.append(&2, C.Seg, a2, a3), grammar, w,
        seg_if_ok(Nat.is_eq(lhs, x), C.Seg{base, k, 0n, k, []}, grammar, w, h => seed_ok(grammar, w, base, k)),
        so_app(a2, a3, grammar, w, pp_ok(Nat.is_eq(lhs, x), segs, grammar, w, need, base, q, ks, d, k, f, x, lhs, rhs, rest, {==}, hsuf, hs, hp, ei),
          gp_ok(rest, 1n+base, grammar, w, segs, x, need, q, ks, d, k, f, drop_step(grammar, base, Core.Production{lhs, rhs}, rest, hsuf), hs, hp, ei)))

def gi_sym_ok(sym: Core.Sym, +grammar: +List<Core.Production>, +w: +List<Nat>, +segs: +List<C.Seg>, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +f: +List<Core.Tree>,
  +ei: {Gll.nthSym(Core.rhsOf(grammar, q), d) == Some{sym} : Maybe<&2, Core.Sym>},
  +hs: {segsOk(segs, grammar, w) == True{} : Bool}, +hp: {segOk(grammar, w, C.Seg{q, ks, d, k, f}) == True{} : Bool})
  -> {segsOk(C.growItem(Some{sym}, grammar, w, segs, q, ks, d, k, f), grammar, w) == True{} : Bool}:
  match sym:
    case Core.Terminal{+t}:
      seg_if_ok(Core.tokIs(Core.tokAt(w, k), t), C.Seg{q, ks, 1n+d, 1n+k, List.append(&2, Core.Tree, f, [Core.Leaf{t}])}, grammar, w,
        ht => leaf_ok(grammar, w, q, ks, d, k, f, t, ei, hp, ht))
    case Core.Nonterminal{+x, +need}:
      gp_ok(grammar, 0n, grammar, w, segs, x, need, q, ks, d, k, f, {==}, hs, hp, ei)

def gi_ok(item: Maybe<&2, Core.Sym>, +grammar: +List<Core.Production>, +w: +List<Nat>, +segs: +List<C.Seg>, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +f: +List<Core.Tree>,
  +ei: {Gll.nthSym(Core.rhsOf(grammar, q), d) == item : Maybe<&2, Core.Sym>},
  +hs: {segsOk(segs, grammar, w) == True{} : Bool}, +hp: {segOk(grammar, w, C.Seg{q, ks, d, k, f}) == True{} : Bool})
  -> {segsOk(C.growItem(item, grammar, w, segs, q, ks, d, k, f), grammar, w) == True{} : Bool}:
  match item:
    case Some{+sym}:
      gi_sym_ok(sym, grammar, w, segs, q, ks, d, k, f, ei, hs, hp)
    case None{}:
      {==}

law ga_ok:
  for ss: +List<C.Seg>
  for +grammar: +List<Core.Production>
  for +w: +List<Nat>
  for +segs: +List<C.Seg>
  for +hss: {segsOk(ss, grammar, w) == True{} : Bool}
  for +hs: {segsOk(segs, grammar, w) == True{} : Bool}
  {segsOk(C.growAll(ss, grammar, w, segs), grammar, w) == True{} : Bool}

def ga_ok(ss, grammar, w, segs, hss, hs):
  match ss:
    case Nil{}:
      {==}
    case Con{C.Seg{+q, +ks, +d, +k, +f}, +rest}:
      so_app(C.growItem(Gll.nthSym(Core.rhsOf(grammar, q), d), grammar, w, segs, q, ks, d, k, f), C.growAll(rest, grammar, w, segs), grammar, w,
        gi_ok(Gll.nthSym(Core.rhsOf(grammar, q), d), grammar, w, segs, q, ks, d, k, f, {==}, hs, Lemma.and_true_left(segOk(grammar, w, C.Seg{q, ks, d, k, f}), segsOk(rest, grammar, w), hss)),
        ga_ok(rest, grammar, w, segs, Lemma.and_true_right_side(segOk(grammar, w, C.Seg{q, ks, d, k, f}), segsOk(rest, grammar, w), hss), hs))

def pick_ok(have: Bool, +s: C.Seg, +segs: +List<C.Seg>, +grammar: +List<Core.Production>, +w: +List<Nat>, +h1: {segOk(grammar, w, s) == True{} : Bool}, +hs: {segsOk(segs, grammar, w) == True{} : Bool})
  -> {segsOk(C.addPick(have, s, segs), grammar, w) == True{} : Bool}:
  match have:
    case True{}:
      hs
    case False{}:
      so_app(segs, [s], grammar, w, hs, Lemma.and_true_intro(segOk(grammar, w, s), True{}, h1, {==}))

law an_ok:
  for new: +List<C.Seg>
  for +segs: +List<C.Seg>
  for +grammar: +List<Core.Production>
  for +w: +List<Nat>
  for +hn: {segsOk(new, grammar, w) == True{} : Bool}
  for +hs: {segsOk(segs, grammar, w) == True{} : Bool}
  {segsOk(C.addNew(new, segs), grammar, w) == True{} : Bool}

def an_ok(new, segs, grammar, w, hn, hs):
  match new:
    case Nil{}:
      hs
    case Con{C.Seg{+q, +ks, +d, +e, +f}, +rest}:
      an_ok(rest, C.addPick(C.hasSeg(q, ks, d, e, segs), C.Seg{q, ks, d, e, f}, segs), grammar, w, Lemma.and_true_right_side(segOk(grammar, w, C.Seg{q, ks, d, e, f}), segsOk(rest, grammar, w), hn),
        pick_ok(C.hasSeg(q, ks, d, e, segs), C.Seg{q, ks, d, e, f}, segs, grammar, w, Lemma.and_true_left(segOk(grammar, w, C.Seg{q, ks, d, e, f}), segsOk(rest, grammar, w), hn), hs))

law until_ok:
  for n: Nat
  for done: Bool
  for +grammar: +List<Core.Production>
  for +w: +List<Nat>
  for +segs: +List<C.Seg>
  for +hs: {segsOk(segs, grammar, w) == True{} : Bool}
  {segsOk(C.growUntil(n, done, grammar, w, segs), grammar, w) == True{} : Bool}

def until_ok(n, done, grammar, w, segs, hs):
  match n:
    case 0n:
      hs
    case 1n+(+p):
      match done:
        case True{}:
          hs
        case False{}:
          until_ok(p, C.closedAll(C.addNew(C.growAll(segs, grammar, w, segs), segs), grammar, w, C.addNew(C.growAll(segs, grammar, w, segs), segs)), grammar, w, C.addNew(C.growAll(segs, grammar, w, segs), segs), an_ok(C.growAll(segs, grammar, w, segs), segs, grammar, w, ga_ok(segs, grammar, w, segs, hs, hs), hs))

law grow_ok:
  for n: Nat
  for +grammar: +List<Core.Production>
  for +w: +List<Nat>
  for +segs: +List<C.Seg>
  for +hs: {segsOk(segs, grammar, w) == True{} : Bool}
  {segsOk(C.grow(n, grammar, w, segs), grammar, w) == True{} : Bool}

def grow_ok(n, grammar, w, segs, hs):
  until_ok(n, C.closedAll(segs, grammar, w, segs), grammar, w, segs, hs)

# ======== THE FIRST FOREST OF A KEY ========

def seg_to4(+grammar: +List<Core.Production>, +w: +List<Nat>, +q2: Nat, +ks2: Nat, +d2: Nat, +e2: Nat, +fo: +List<Core.Tree>, +q: Nat, +ks: Nat, +d: Nat, +e: Nat,
  +e1: {q2 == q : Nat}, +ek: {ks2 == ks : Nat}, +ed: {d2 == d : Nat}, +ee: {e2 == e : Nat}, +h: {segOk(grammar, w, C.Seg{q2, ks2, d2, e2, fo}) == True{} : Bool})
  -> {segOk(grammar, w, C.Seg{q, ks, d, e, fo}) == True{} : Bool}:
  %e1 : {segOk(grammar, w, C.Seg{_, ks, d, e, fo}) == True{} : Bool}
  %ek : {segOk(grammar, w, C.Seg{q2, _, d, e, fo}) == True{} : Bool}
  %ed : {segOk(grammar, w, C.Seg{q2, ks2, _, e, fo}) == True{} : Bool}
  %ee : {segOk(grammar, w, C.Seg{q2, ks2, d2, _, fo}) == True{} : Bool}
  h

def key_seg(+grammar: +List<Core.Production>, +w: +List<Nat>, +q: Nat, +ks: Nat, +d: Nat, +e: Nat, +q2: Nat, +ks2: Nat, +d2: Nat, +e2: Nat, +fo: +List<Core.Tree>,
  +hk: {C.keyIs(q, ks, d, e, C.Seg{q2, ks2, d2, e2, fo}) == True{} : Bool}, +h: {segOk(grammar, w, C.Seg{q2, ks2, d2, e2, fo}) == True{} : Bool})
  -> {segOk(grammar, w, C.Seg{q, ks, d, e, fo}) == True{} : Bool}:
  +r1 = Lemma.and_true_right_side(Nat.is_eq(q2, q), Bool.and(Nat.is_eq(ks2, ks), Bool.and(Nat.is_eq(d2, d), Nat.is_eq(e2, e))), hk)
  +r2 = Lemma.and_true_right_side(Nat.is_eq(ks2, ks), Bool.and(Nat.is_eq(d2, d), Nat.is_eq(e2, e)), r1)
  seg_to4(grammar, w, q2, ks2, d2, e2, fo, q, ks, d, e,
    Lemma.nat_eq_sound(q2, q, Lemma.and_true_left(Nat.is_eq(q2, q), Bool.and(Nat.is_eq(ks2, ks), Bool.and(Nat.is_eq(d2, d), Nat.is_eq(e2, e))), hk)),
    Lemma.nat_eq_sound(ks2, ks, Lemma.and_true_left(Nat.is_eq(ks2, ks), Bool.and(Nat.is_eq(d2, d), Nat.is_eq(e2, e)), r1)),
    Lemma.nat_eq_sound(d2, d, Lemma.and_true_left(Nat.is_eq(d2, d), Nat.is_eq(e2, e), r2)),
    Lemma.nat_eq_sound(e2, e, Lemma.and_true_right_side(Nat.is_eq(d2, d), Nat.is_eq(e2, e), r2)), h)

def fa_pick(b: Bool, +grammar: +List<Core.Production>, +w: +List<Nat>, +q: Nat, +ks: Nat, +d: Nat, +e: Nat, +q2: Nat, +ks2: Nat, +d2: Nat, +e2: Nat, +fo: +List<Core.Tree>, +rest: +List<C.Seg>,
  +eb: {C.keyIs(q, ks, d, e, C.Seg{q2, ks2, d2, e2, fo}) == b : Bool},
  +hh: {Bool.or(b, C.hasSeg(q, ks, d, e, rest)) == True{} : Bool},
  +h1: {segOk(grammar, w, C.Seg{q2, ks2, d2, e2, fo}) == True{} : Bool},
  later: {C.hasSeg(q, ks, d, e, rest) == True{} : Bool} -> {segOk(grammar, w, C.Seg{q, ks, d, e, C.forestAt(q, ks, d, e, rest)}) == True{} : Bool})
  -> {segOk(grammar, w, C.Seg{q, ks, d, e, C.forestPick(b, fo, C.forestAt(q, ks, d, e, rest))}) == True{} : Bool}:
  match b:
    case True{}:
      key_seg(grammar, w, q, ks, d, e, q2, ks2, d2, e2, fo, eb, h1)
    case False{}:
      later(hh)

# The forest handed out for a key is the forest of a sound segment with that key.
law forest_at_ok:
  for segs: +List<C.Seg>
  for +grammar: +List<Core.Production>
  for +w: +List<Nat>
  for +q: Nat
  for +ks: Nat
  for +d: Nat
  for +e: Nat
  for +hs: {segsOk(segs, grammar, w) == True{} : Bool}
  for +hh: {C.hasSeg(q, ks, d, e, segs) == True{} : Bool}
  {segOk(grammar, w, C.Seg{q, ks, d, e, C.forestAt(q, ks, d, e, segs)}) == True{} : Bool}

def forest_at_ok(segs, grammar, w, q, ks, d, e, hs, hh):
  match segs:
    case Nil{}:
      Empty.absurd({segOk(grammar, w, C.Seg{q, ks, d, e, []}) == True{} : Bool}, Lemma.false_is_not_true(hh))
    case Con{C.Seg{+q2, +ks2, +d2, +e2, +fo}, +rest}:
      fa_pick(C.keyIs(q, ks, d, e, C.Seg{q2, ks2, d2, e2, fo}), grammar, w, q, ks, d, e, q2, ks2, d2, e2, fo, rest, {==}, hh,
        Lemma.and_true_left(segOk(grammar, w, C.Seg{q2, ks2, d2, e2, fo}), segsOk(rest, grammar, w), hs),
        h2 => forest_at_ok(rest, grammar, w, q, ks, d, e, Lemma.and_true_right_side(segOk(grammar, w, C.Seg{q2, ks2, d2, e2, fo}), segsOk(rest, grammar, w), hs), h2))


# THE CLOSURE'S FOREST IS SOUND: a segment of the closure from q at 0 that completes q over
# w carries a forest that reads q's right side on w and spells all of it.
law closure_found:
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +w: +List<Nat>
  for +q: Nat
  for +hh: {C.hasSeg(q, 0n, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), List.length(&2, Nat, w), C.segsFrom(fuel, grammar, w, q, 0n)) == True{} : Bool}
  {Bool.and(Core.reads(C.forestAt(q, 0n, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), List.length(&2, Nat, w), C.segsFrom(fuel, grammar, w, q, 0n)), grammar, Core.rhsOf(grammar, q), w, 0n),
    Nat.is_eq(List.length(&2, Nat, Core.leaves(C.forestAt(q, 0n, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), List.length(&2, Nat, w), C.segsFrom(fuel, grammar, w, q, 0n)))), List.length(&2, Nat, w))) == True{} : Bool}

def found_split(+grammar: +List<Core.Production>, +w: +List<Nat>, +q: Nat, +ch: +List<Core.Tree>,
  +hc: {segOk(grammar, w, C.Seg{q, 0n, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), List.length(&2, Nat, w), ch}) == True{} : Bool})
  -> {Bool.and(Core.reads(ch, grammar, Core.rhsOf(grammar, q), w, 0n), Nat.is_eq(List.length(&2, Nat, Core.leaves(ch)), List.length(&2, Nat, w))) == True{} : Bool}:
  +n = List.length(&2, Nat, w)
  +RD = {Core.reads(ch, grammar, WS.takeN(List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), Core.rhsOf(grammar, q)), w, 0n) : Bool}
  +EN = {Nat.is_eq(G.endOf(ch, 0n), n) : Bool}
  +LN = {Nat.is_eq(List.length(&2, Core.Tree, ch), List.length(&2, Core.Sym, Core.rhsOf(grammar, q))) : Bool}
  +r2 = Lemma.and_true_right_side(RD, Bool.and(EN, LN), hc)
  +ec = Lemma.nat_eq_sound(G.endOf(ch, 0n), n, Lemma.and_true_left(EN, LN, r2))
  +el = Equal.trans(Nat, List.length(&2, Nat, Core.leaves(ch)), G.endOf(ch, 0n), n, Equal.sym(Nat, G.endOf(ch, 0n), List.length(&2, Nat, Core.leaves(ch)), G.end_eq(ch, 0n)), ec)
  Lemma.and_true_intro(Core.reads(ch, grammar, Core.rhsOf(grammar, q), w, 0n), Nat.is_eq(List.length(&2, Nat, Core.leaves(ch)), n),
    WS.reads_all(grammar, w, ch, Core.rhsOf(grammar, q), 0n, Lemma.and_true_left(RD, Bool.and(EN, LN), hc)), eq_is(List.length(&2, Nat, Core.leaves(ch)), n, el))

def closure_found(fuel, grammar, w, q, hh):
  +segs = C.segsFrom(fuel, grammar, w, q, 0n)
  found_split(grammar, w, q, C.forestAt(q, 0n, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), List.length(&2, Nat, w), segs),
    forest_at_ok(segs, grammar, w, q, 0n, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), List.length(&2, Nat, w),
      grow_ok(fuel, grammar, w, [C.Seg{q, 0n, 0n, 0n, []}], Lemma.and_true_intro(segOk(grammar, w, C.Seg{q, 0n, 0n, 0n, []}), True{}, seed_ok(grammar, w, q, 0n), {==})), hh))

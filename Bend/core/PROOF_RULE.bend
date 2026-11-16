import Base
import ../LEMMAS.bend as Lemma
import ./PROOF_BASICS.bend as B
import ./CORE.bend as Core
import ./SETS.bend as Sets
import ./GLL.bend as Gll
import ./PREFER.bend as Prefer

# ON A WELL-FORMED GRAMMAR NO RIVAL COMES BACK TO ITS OWN CHOICE. A rival of production m
# (m outranks a sibling q) is children for m. If they held a node of m's own nonterminal
# over all of their tokens, the nodes on the way down would each be the whole of their
# parent, every sibling reading nothing: a cycle through m that reads no input, which
# noPreferenceCycle rules out. The way down is the chain FullAt describes.

# A node of x over all n tokens of the forest, reached through nodes over all n tokens:
# at each level one tree spans everything and its siblings read nothing.
def FullAt(+grammar: +List<Core.Production>, fs: +List<Core.Tree>, +n: Nat, +x: Nat) -> Type:
  match fs:
    case Nil{}:
      Empty
    case Con{Core.Leaf{+a}, +ts}:
      {Core.leaves([Core.Leaf{a}]) == [] : +List<Nat>} & FullAt(grammar, ts, n, x)
    case Con{Core.Node{+p, +cs}, +ts}:
      Either<({Core.width(Core.Node{p, cs}) == n : Nat} & {Core.leaves(ts) == [] : +List<Nat>} & Either<{Core.lhsIs(grammar, p, x) == True{} : Bool}, FullAt(grammar, cs, n, x)>),
        ({Core.leaves([Core.Node{p, cs}]) == [] : +List<Nat>} & FullAt(grammar, ts, n, x))>

# ======== SMALL FACTS ========

law lhs_same:
  for g: +List<Core.Production>
  for p: Nat
  for +x: Nat
  for +y: Nat
  for +hx: {Core.lhsIs(g, p, x) == True{} : Bool}
  for +hy: {Core.lhsIs(g, p, y) == True{} : Bool}
  {x == y : Nat}

def lhs_same(g, p, x, y, hx, hy):
  match g p:
    case Nil{} +p0:
      Empty.absurd({x == y : Nat}, Lemma.false_is_not_true(hx))
    case Con{Core.Production{+lhs, +rhs}, +rest} 0n:
      Equal.trans(Nat, x, lhs, y, Equal.sym(Nat, lhs, x, Lemma.nat_eq_sound(lhs, x, hx)), Lemma.nat_eq_sound(lhs, y, hy))
    case Con{Core.Production{+lhs, +rhs}, +rest} 1n+(+n):
      lhs_same(rest, n, x, y, hx, hy)

law nat_join_left:
  for a: +List<Nat>
  for +b: +List<Nat>
  for +c: +List<Nat>
  for +h: {Sets.allNatIn(Sets.joinNats(a, b), c) == True{} : Bool}
  {Sets.allNatIn(a, c) == True{} : Bool}

def nat_join_left(a, b, c, h):
  match a:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Lemma.and_true_intro(Sets.natIn(x, c), Sets.allNatIn(rest, c), Lemma.and_true_left(Sets.natIn(x, c), Sets.allNatIn(Sets.joinNats(rest, b), c), h),
        nat_join_left(rest, b, c, Lemma.and_true_right_side(Sets.natIn(x, c), Sets.allNatIn(Sets.joinNats(rest, b), c), h)))

law nat_join_right:
  for a: +List<Nat>
  for +b: +List<Nat>
  for +c: +List<Nat>
  for +h: {Sets.allNatIn(Sets.joinNats(a, b), c) == True{} : Bool}
  {Sets.allNatIn(b, c) == True{} : Bool}

def nat_join_right(a, b, c, h):
  match a:
    case Nil{}:
      h
    case Con{+x, +rest}:
      nat_join_right(rest, b, c, Lemma.and_true_right_side(Sets.natIn(x, c), Sets.allNatIn(Sets.joinNats(rest, b), c), h))

law edge_true:
  for b: Bool
  for +s: Core.Sym
  for +c: +List<Nat>
  for +hb: {b == True{} : Bool}
  for +h: {Sets.allNatIn(Prefer.edgeIf(b, s), c) == True{} : Bool}
  {Sets.allNatIn(Prefer.ntList(s), c) == True{} : Bool}

def edge_true(b, s, c, hb, h):
  match b:
    case True{}:
      h
    case False{}:
      Empty.absurd({Sets.allNatIn(Prefer.ntList(s), c) == True{} : Bool}, Lemma.false_is_not_true(hb))

# ======== THE CLOSED SETS ========

law closed_null:
  for g: +List<Core.Production>
  for p: Nat
  for +y: Nat
  for +nulls: +List<Nat>
  for +cn: {Sets.nullsClosed(g, nulls) == True{} : Bool}
  for +hl: {Core.lhsIs(g, p, y) == True{} : Bool}
  for +ha: {Sets.allNull(Core.rhsOf(g, p), nulls) == True{} : Bool}
  {Sets.natIn(y, nulls) == True{} : Bool}

def closed_null(g, p, y, nulls, cn, hl, ha):
  match g p:
    case Nil{} +p0:
      Empty.absurd({Sets.natIn(y, nulls) == True{} : Bool}, Lemma.false_is_not_true(hl))
    case Con{Core.Production{+lhs, +rhs}, +rest} 0n:
      +here = {Bool.or(Bool.not(Sets.allNull(rhs, nulls)), Sets.natIn(lhs, nulls)) : Bool}
      +hn = B.or_not_true(Sets.allNull(rhs, nulls), Sets.natIn(lhs, nulls), ha, Lemma.and_true_left(here, Sets.nullsClosed(rest, nulls), cn))
      %Lemma.nat_eq_sound(lhs, y, hl) : {Sets.natIn(_, nulls) == True{} : Bool}
      hn
    case Con{Core.Production{+lhs, +rhs}, +rest} 1n+(+n):
      +here = {Bool.or(Bool.not(Sets.allNull(rhs, nulls)), Sets.natIn(lhs, nulls)) : Bool}
      closed_null(rest, n, y, nulls, Lemma.and_true_right_side(here, Sets.nullsClosed(rest, nulls), cn), hl, ha)

law reach_closed_at:
  for g: +List<Core.Production>
  for p: Nat
  for +y: Nat
  for +nulls: +List<Nat>
  for +r: +List<Nat>
  for +cr: {Prefer.reachClosed(g, nulls, r) == True{} : Bool}
  for +hl: {Core.lhsIs(g, p, y) == True{} : Bool}
  for +hy: {Sets.natIn(y, r) == True{} : Bool}
  {Sets.allNatIn(Prefer.edgesFrom(Core.rhsOf(g, p), True{}, nulls), r) == True{} : Bool}

def reach_closed_at(g, p, y, nulls, r, cr, hl, hy):
  match g p:
    case Nil{} +p0:
      Empty.absurd({Sets.allNatIn(Prefer.edgesFrom([], True{}, nulls), r) == True{} : Bool}, Lemma.false_is_not_true(hl))
    case Con{Core.Production{+lhs, +rhs}, +rest} 0n:
      +here = {Bool.or(Bool.not(Sets.natIn(lhs, r)), Sets.allNatIn(Prefer.edgesFrom(rhs, True{}, nulls), r)) : Bool}
      +same = Lemma.nat_eq_sound(lhs, y, hl)
      +hlr = {(%Equal.sym(Nat, lhs, y, same) : {Sets.natIn(_, r) == True{} : Bool}
        hy) : {Sets.natIn(lhs, r) == True{} : Bool}}
      B.or_not_true(Sets.natIn(lhs, r), Sets.allNatIn(Prefer.edgesFrom(rhs, True{}, nulls), r), hlr, Lemma.and_true_left(here, Prefer.reachClosed(rest, nulls, r), cr))
    case Con{Core.Production{+lhs, +rhs}, +rest} 1n+(+n):
      +here = {Bool.or(Bool.not(Sets.natIn(lhs, r)), Sets.allNatIn(Prefer.edgesFrom(rhs, True{}, nulls), r)) : Bool}
      reach_closed_at(rest, n, y, nulls, r, Lemma.and_true_right_side(here, Prefer.reachClosed(rest, nulls, r), cr), hl, hy)

# ======== A FOREST THAT READS NOTHING ========

def need_null(need: Core.Need, +p: Nat, +cs: +List<Core.Tree>, +y: Nat, +nulls: +List<Nat>,
  +hneed: {Core.needOk(need, Core.width(Core.Node{p, cs})) == True{} : Bool},
  +zc: {Core.leaves(cs) == [] : +List<Nat>},
  +hy: {Sets.natIn(y, nulls) == True{} : Bool}) -> {Sets.needNull(need, y, nulls) == True{} : Bool}:
  match need:
    case Core.Something{}:
      +w = Core.width(Core.Node{p, cs})
      +ew = Equal.cong(+List<Nat>, Nat, v => List.length(&2, Nat, List.append(&2, Nat, v, [])), Core.leaves(cs), [], zc)
      +en = Equal.cong(Nat, Bool, v => Bool.not(Nat.is_eq(v, 0n)), w, 0n, ew)
      Empty.absurd({False{} == True{} : Bool}, Lemma.true_is_not_false(Equal.trans(Bool, True{}, Bool.not(Nat.is_eq(w, 0n)), False{}, Equal.sym(Bool, Bool.not(Nat.is_eq(w, 0n)), True{}, hneed), en)))
    case Core.Anything{}:
      hy
    case Core.Nothing{}:
      hy

def zero_node(+p: Nat, +cs: +List<Core.Tree>, +ts: +List<Core.Tree>, +y: Nat, +need: Core.Need, +rest: +List<Core.Sym>, +grammar: +List<Core.Production>, +nulls: +List<Nat>,
  +cn: {Sets.nullsClosed(grammar, nulls) == True{} : Bool},
  +fit: {Core.fits(Core.Node{p, cs} <> ts, grammar, Core.Nonterminal{y, need} <> rest) == True{} : Bool},
  +zc: {Core.leaves(cs) == [] : +List<Nat>},
  +zt: {Core.leaves(ts) == [] : +List<Nat>},
  inner: {Core.fits(cs, grammar, Core.rhsOf(grammar, p)) == True{} : Bool} -> {Core.leaves(cs) == [] : +List<Nat>} -> {Sets.allNull(Core.rhsOf(grammar, p), nulls) == True{} : Bool},
  later: {Core.fits(ts, grammar, rest) == True{} : Bool} -> {Core.leaves(ts) == [] : +List<Nat>} -> {Sets.allNull(rest, nulls) == True{} : Bool})
  -> {Sets.allNull(Core.Nonterminal{y, need} <> rest, nulls) == True{} : Bool}:
  +lh = {Core.lhsIs(grammar, p, y) : Bool}
  +nd = {Core.needOk(need, Core.width(Core.Node{p, cs})) : Bool}
  +fc = {Core.fits(cs, grammar, Core.rhsOf(grammar, p)) : Bool}
  +head = Lemma.and_true_left(Bool.and(Bool.and(lh, nd), fc), Core.fits(ts, grammar, rest), fit)
  +hl = Lemma.and_true_left(lh, nd, Lemma.and_true_left(Bool.and(lh, nd), fc, head))
  +hn = Lemma.and_true_right_side(lh, nd, Lemma.and_true_left(Bool.and(lh, nd), fc, head))
  +hc = Lemma.and_true_right_side(Bool.and(lh, nd), fc, head)
  +hy = closed_null(grammar, p, y, nulls, cn, hl, inner(hc, zc))
  Lemma.and_true_intro(Sets.needNull(need, y, nulls), Sets.allNull(rest, nulls), need_null(need, p, cs, y, nulls, hn, zc, hy),
    later(Lemma.and_true_right_side(Bool.and(Bool.and(lh, nd), fc), Core.fits(ts, grammar, rest), fit), zt))

# Every item of a forest that reads nothing can read nothing.
law zero_nulls:
  for fs: +List<Core.Tree>
  for items: +List<Core.Sym>
  for +grammar: +List<Core.Production>
  for +nulls: +List<Nat>
  for +cn: {Sets.nullsClosed(grammar, nulls) == True{} : Bool}
  for +fit: {Core.fits(fs, grammar, items) == True{} : Bool}
  for +z: {Core.leaves(fs) == [] : +List<Nat>}
  {Sets.allNull(items, nulls) == True{} : Bool}

def zero_nulls(fs, items, grammar, nulls, cn, fit, z):
  match fs items:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+s, +rest}:
      Empty.absurd({Sets.allNull(s <> rest, nulls) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Core.Leaf{+a}, +ts} +its:
      Empty.absurd({Sets.allNull(its, nulls) == True{} : Bool}, Lemma.nil_is_not_cons(a, Core.leaves(ts), Equal.sym(+List<Nat>, a <> Core.leaves(ts), [], z)))
    case Con{Core.Node{+p, +cs}, +ts} Nil{}:
      Empty.absurd({Sets.allNull([], nulls) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Core.Node{+p, +cs}, +ts} Con{Core.Terminal{+t}, +rest}:
      Empty.absurd({Sets.allNull(Core.Terminal{t} <> rest, nulls) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Core.Node{+p, +cs}, +ts} Con{Core.Nonterminal{+y, +need}, +rest}:
      +zc = B.append_nil_left(Core.leaves(cs), Core.leaves(ts), z)
      +zt = B.append_nil_right(Core.leaves(cs), Core.leaves(ts), z)
      zero_node(p, cs, ts, y, need, rest, grammar, nulls, cn, fit, zc, zt,
        f1 => z1 => zero_nulls(cs, Core.rhsOf(grammar, p), grammar, nulls, cn, f1, z1),
        f2 => z2 => zero_nulls(ts, rest, grammar, nulls, cn, f2, z2))

# ======== THE WALK DOWN ========

def here_pick(+p: Nat, +cs: +List<Core.Tree>, +y: Nat, +x: Nat, +n: Nat, +grammar: +List<Core.Production>, +r: +List<Nat>,
  +hl: {Core.lhsIs(grammar, p, y) == True{} : Bool},
  +ny: {Sets.natIn(y, r) == True{} : Bool},
  inner: Either<{Core.lhsIs(grammar, p, x) == True{} : Bool}, FullAt(grammar, cs, n, x)>,
  later: FullAt(grammar, cs, n, x) -> {Sets.natIn(x, r) == True{} : Bool}) -> {Sets.natIn(x, r) == True{} : Bool}:
  match inner:
    case Inl{hx}:
      %lhs_same(grammar, p, y, x, hl, hx) : {Sets.natIn(_, r) == True{} : Bool}
      ny
    case Inr{f}:
      later(f)

def here_at(+p: Nat, +cs: +List<Core.Tree>, +ts: +List<Core.Tree>, +y: Nat, +need: Core.Need, +rest: +List<Core.Sym>, +pre: Bool, +grammar: +List<Core.Production>, +nulls: +List<Nat>, +r: +List<Nat>, +n: Nat, +x: Nat,
  +cn: {Sets.nullsClosed(grammar, nulls) == True{} : Bool},
  +cr: {Prefer.reachClosed(grammar, nulls, r) == True{} : Bool},
  +hpre: {pre == True{} : Bool},
  +fit: {Core.fits(Core.Node{p, cs} <> ts, grammar, Core.Nonterminal{y, need} <> rest) == True{} : Bool},
  +inR: {Sets.allNatIn(Prefer.edgesFrom(Core.Nonterminal{y, need} <> rest, pre, nulls), r) == True{} : Bool},
  +wn: {Core.width(Core.Node{p, cs}) == n : Nat},
  +zt: {Core.leaves(ts) == [] : +List<Nat>},
  inner: Either<{Core.lhsIs(grammar, p, x) == True{} : Bool}, FullAt(grammar, cs, n, x)>,
  later: {Core.fits(cs, grammar, Core.rhsOf(grammar, p)) == True{} : Bool} -> {Sets.allNatIn(Prefer.edgesFrom(Core.rhsOf(grammar, p), True{}, nulls), r) == True{} : Bool} -> FullAt(grammar, cs, n, x) -> {Sets.natIn(x, r) == True{} : Bool})
  -> {Sets.natIn(x, r) == True{} : Bool}:
  +s = {Core.Nonterminal{y, need} : Core.Sym}
  +lh = {Core.lhsIs(grammar, p, y) : Bool}
  +nd = {Core.needOk(need, Core.width(Core.Node{p, cs})) : Bool}
  +fc = {Core.fits(cs, grammar, Core.rhsOf(grammar, p)) : Bool}
  +ft = {Core.fits(ts, grammar, rest) : Bool}
  +head = Lemma.and_true_left(Bool.and(Bool.and(lh, nd), fc), ft, fit)
  +hl = Lemma.and_true_left(lh, nd, Lemma.and_true_left(Bool.and(lh, nd), fc, head))
  +hc = Lemma.and_true_right_side(Bool.and(lh, nd), fc, head)
  +an = zero_nulls(ts, rest, grammar, nulls, cn, Lemma.and_true_right_side(Bool.and(Bool.and(lh, nd), fc), ft, fit), zt)
  +b = {Bool.and(pre, Sets.allNull(rest, nulls)) : Bool}
  +hb = Lemma.and_true_intro(pre, Sets.allNull(rest, nulls), hpre, an)
  +left = nat_join_left(Prefer.edgeIf(b, s), Prefer.edgesFrom(rest, Bool.and(pre, Sets.itemNull(s, nulls)), nulls), r, inR)
  +ny = Lemma.and_true_left(Sets.natIn(y, r), True{}, edge_true(b, s, r, hb, left))
  +inCs = reach_closed_at(grammar, p, y, nulls, r, cr, hl, ny)
  here_pick(p, cs, y, x, n, grammar, r, hl, ny, inner, f => later(hc, inCs, f))

def there_at(+p: Nat, +cs: +List<Core.Tree>, +ts: +List<Core.Tree>, +y: Nat, +need: Core.Need, +rest: +List<Core.Sym>, +pre: Bool, +grammar: +List<Core.Production>, +nulls: +List<Nat>, +r: +List<Nat>, +n: Nat, +x: Nat,
  +cn: {Sets.nullsClosed(grammar, nulls) == True{} : Bool},
  +hpre: {pre == True{} : Bool},
  +fit: {Core.fits(Core.Node{p, cs} <> ts, grammar, Core.Nonterminal{y, need} <> rest) == True{} : Bool},
  +inR: {Sets.allNatIn(Prefer.edgesFrom(Core.Nonterminal{y, need} <> rest, pre, nulls), r) == True{} : Bool},
  +zh: {Core.leaves([Core.Node{p, cs}]) == [] : +List<Nat>},
  f: FullAt(grammar, ts, n, x),
  later: {Bool.and(pre, Sets.itemNull(Core.Nonterminal{y, need}, nulls)) == True{} : Bool} -> {Core.fits(ts, grammar, rest) == True{} : Bool} -> {Sets.allNatIn(Prefer.edgesFrom(rest, Bool.and(pre, Sets.itemNull(Core.Nonterminal{y, need}, nulls)), nulls), r) == True{} : Bool} -> FullAt(grammar, ts, n, x) -> {Sets.natIn(x, r) == True{} : Bool})
  -> {Sets.natIn(x, r) == True{} : Bool}:
  +s = {Core.Nonterminal{y, need} : Core.Sym}
  +hd = {Bool.and(Bool.and(Core.lhsIs(grammar, p, y), Core.needOk(need, Core.width(Core.Node{p, cs}))), Core.fits(cs, grammar, Core.rhsOf(grammar, p))) : Bool}
  +ft = {Core.fits(ts, grammar, rest) : Bool}
  +one = Lemma.and_true_intro(hd, True{}, Lemma.and_true_left(hd, ft, fit), {==})
  +sn = Lemma.and_true_left(Sets.itemNull(s, nulls), True{}, zero_nulls([Core.Node{p, cs}], [s], grammar, nulls, cn, one, zh))
  +b = {Bool.and(pre, Sets.allNull(rest, nulls)) : Bool}
  +right = nat_join_right(Prefer.edgeIf(b, s), Prefer.edgesFrom(rest, Bool.and(pre, Sets.itemNull(s, nulls)), nulls), r, inR)
  later(Lemma.and_true_intro(pre, Sets.itemNull(s, nulls), hpre, sn), Lemma.and_true_right_side(hd, ft, fit), right, f)

def node_at(+p: Nat, +cs: +List<Core.Tree>, +ts: +List<Core.Tree>, +y: Nat, +need: Core.Need, +rest: +List<Core.Sym>, +pre: Bool, +grammar: +List<Core.Production>, +nulls: +List<Nat>, +r: +List<Nat>, +n: Nat, +x: Nat,
  +cn: {Sets.nullsClosed(grammar, nulls) == True{} : Bool},
  +cr: {Prefer.reachClosed(grammar, nulls, r) == True{} : Bool},
  +hpre: {pre == True{} : Bool},
  +fit: {Core.fits(Core.Node{p, cs} <> ts, grammar, Core.Nonterminal{y, need} <> rest) == True{} : Bool},
  +inR: {Sets.allNatIn(Prefer.edgesFrom(Core.Nonterminal{y, need} <> rest, pre, nulls), r) == True{} : Bool},
  full: FullAt(grammar, Core.Node{p, cs} <> ts, n, x),
  down: {Core.fits(cs, grammar, Core.rhsOf(grammar, p)) == True{} : Bool} -> {Sets.allNatIn(Prefer.edgesFrom(Core.rhsOf(grammar, p), True{}, nulls), r) == True{} : Bool} -> FullAt(grammar, cs, n, x) -> {Sets.natIn(x, r) == True{} : Bool},
  along: {Bool.and(pre, Sets.itemNull(Core.Nonterminal{y, need}, nulls)) == True{} : Bool} -> {Core.fits(ts, grammar, rest) == True{} : Bool} -> {Sets.allNatIn(Prefer.edgesFrom(rest, Bool.and(pre, Sets.itemNull(Core.Nonterminal{y, need}, nulls)), nulls), r) == True{} : Bool} -> FullAt(grammar, ts, n, x) -> {Sets.natIn(x, r) == True{} : Bool})
  -> {Sets.natIn(x, r) == True{} : Bool}:
  match full:
    case Inl{(wn, (zt, inner))}:
      here_at(p, cs, ts, y, need, rest, pre, grammar, nulls, r, n, x, cn, cr, hpre, fit, inR, wn, zt, inner, down)
    case Inr{(zh, f)}:
      there_at(p, cs, ts, y, need, rest, pre, grammar, nulls, r, n, x, cn, hpre, fit, inR, zh, f, along)

# Walking down a chain of nodes over all the tokens, from a nonterminal in the closed set r,
# stays in r; the chain ends at x, so x is in r.
law walk:
  for fs: +List<Core.Tree>
  for items: +List<Core.Sym>
  for +pre: Bool
  for +grammar: +List<Core.Production>
  for +nulls: +List<Nat>
  for +r: +List<Nat>
  for +n: Nat
  for +x: Nat
  for +cn: {Sets.nullsClosed(grammar, nulls) == True{} : Bool}
  for +cr: {Prefer.reachClosed(grammar, nulls, r) == True{} : Bool}
  for +hpre: {pre == True{} : Bool}
  for +fit: {Core.fits(fs, grammar, items) == True{} : Bool}
  for +inR: {Sets.allNatIn(Prefer.edgesFrom(items, pre, nulls), r) == True{} : Bool}
  for full: FullAt(grammar, fs, n, x)
  {Sets.natIn(x, r) == True{} : Bool}

def walk(fs, items, pre, grammar, nulls, r, n, x, cn, cr, hpre, fit, inR, full):
  match fs items:
    case Nil{} +its:
      Empty.absurd({Sets.natIn(x, r) == True{} : Bool}, full)
    case Con{Core.Leaf{+a}, +ts} +its:
      match full:
        case (z, f):
          Empty.absurd({Sets.natIn(x, r) == True{} : Bool}, Lemma.nil_is_not_cons(a, [], Equal.sym(+List<Nat>, [a], [], z)))
    case Con{Core.Node{+p, +cs}, +ts} Nil{}:
      Empty.absurd({Sets.natIn(x, r) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Core.Node{+p, +cs}, +ts} Con{Core.Terminal{+t}, +rest}:
      Empty.absurd({Sets.natIn(x, r) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Core.Node{+p, +cs}, +ts} Con{Core.Nonterminal{+y, +need}, +rest}:
      node_at(p, cs, ts, y, need, rest, pre, grammar, nulls, r, n, x, cn, cr, hpre, fit, inR, full,
        fc => ir => f => walk(cs, Core.rhsOf(grammar, p), True{}, grammar, nulls, r, n, x, cn, cr, {==}, fc, ir, f),
        hp => ft => ir => f => walk(ts, rest, Bool.and(pre, Sets.itemNull(Core.Nonterminal{y, need}, nulls)), grammar, nulls, r, n, x, cn, cr, hp, ft, ir, f))

# ======== THE CHECK, PRODUCTION BY PRODUCTION ========

law below_at:
  for g: +List<Core.Production>
  for k: Nat
  for +base: Nat
  for +z: Nat
  for +grammar: +List<Core.Production>
  for +marks: +List<Prefer.RankMark>
  for +m: Nat
  for +h: {Core.lhsIs(g, k, z) == True{} : Bool}
  for +e: {Prefer.outranking(grammar, marks, Nat.add(base, k), m) == True{} : Bool}
  {Prefer.belowFrom(g, grammar, marks, m, base) == True{} : Bool}

def below_at(g, k, base, z, grammar, marks, m, h, e):
  match g k:
    case Nil{} +k0:
      Empty.absurd({Prefer.belowFrom([], grammar, marks, m, base) == True{} : Bool}, Lemma.false_is_not_true(h))
    case Con{Core.Production{+lhs, +rhs}, +rest} 0n:
      +e0 = {(%Lemma.add_zero_right(base) : {Prefer.outranking(grammar, marks, _, m) == True{} : Bool}
        e) : {Prefer.outranking(grammar, marks, base, m) == True{} : Bool}}
      Lemma.or_true_left_intro(Prefer.outranking(grammar, marks, base, m), Prefer.belowFrom(rest, grammar, marks, m, 1n+base), e0)
    case Con{Core.Production{+lhs, +rhs}, +rest} 1n+(+k2):
      +e1 = {(%Lemma.add_succ_right(base, k2) : {Prefer.outranking(grammar, marks, _, m) == True{} : Bool}
        e) : {Prefer.outranking(grammar, marks, 1n+Nat.add(base, k2), m) == True{} : Bool}}
      Lemma.or_true_right_intro(Prefer.outranking(grammar, marks, base, m), Prefer.belowFrom(rest, grammar, marks, m, 1n+base), below_at(rest, k2, 1n+base, z, grammar, marks, m, h, e1))

law prods_at:
  for g: +List<Core.Production>
  for k: Nat
  for +base: Nat
  for +z: Nat
  for +grammar: +List<Core.Production>
  for +marks: +List<Prefer.RankMark>
  for +nulls: +List<Nat>
  for +h: {Core.lhsIs(g, k, z) == True{} : Bool}
  for +e: {Prefer.prodsOk(g, grammar, marks, nulls, base) == True{} : Bool}
  for +hb: {Prefer.belowFrom(grammar, grammar, marks, Nat.add(base, k), 0n) == True{} : Bool}
  {Prefer.cycleFree(grammar, nulls, Nat.add(base, k)) == True{} : Bool}

def prods_at(g, k, base, z, grammar, marks, nulls, h, e, hb):
  match g k:
    case Nil{} +k0:
      Empty.absurd({Prefer.cycleFree(grammar, nulls, Nat.add(base, k0)) == True{} : Bool}, Lemma.false_is_not_true(h))
    case Con{Core.Production{+lhs, +rhs}, +rest} 0n:
      +bl = {Prefer.belowFrom(grammar, grammar, marks, base, 0n) : Bool}
      +here = {Bool.or(Bool.not(bl), Prefer.cycleFree(grammar, nulls, base)) : Bool}
      +hb0 = {(%Lemma.add_zero_right(base) : {Prefer.belowFrom(grammar, grammar, marks, _, 0n) == True{} : Bool}
        hb) : {bl == True{} : Bool}}
      +cf = B.or_not_true(bl, Prefer.cycleFree(grammar, nulls, base), hb0, Lemma.and_true_left(here, Prefer.prodsOk(rest, grammar, marks, nulls, 1n+base), e))
      %Equal.sym(Nat, Nat.add(base, 0n), base, Lemma.add_zero_right(base)) : {Prefer.cycleFree(grammar, nulls, _) == True{} : Bool}
      cf
    case Con{Core.Production{+lhs, +rhs}, +rest} 1n+(+k2):
      +here = {Bool.or(Bool.not(Prefer.belowFrom(grammar, grammar, marks, base, 0n)), Prefer.cycleFree(grammar, nulls, base)) : Bool}
      +hb1 = {(%Lemma.add_succ_right(base, k2) : {Prefer.belowFrom(grammar, grammar, marks, _, 0n) == True{} : Bool}
        hb) : {Prefer.belowFrom(grammar, grammar, marks, 1n+Nat.add(base, k2), 0n) == True{} : Bool}}
      %Equal.sym(Nat, Nat.add(base, 1n+k2), 1n+Nat.add(base, k2), Lemma.add_succ_right(base, k2)) : {Prefer.cycleFree(grammar, nulls, _) == True{} : Bool}
      prods_at(rest, k2, 1n+base, z, grammar, marks, nulls, h, Lemma.and_true_right_side(here, Prefer.prodsOk(rest, grammar, marks, nulls, 1n+base), e), hb1)

# ======== THE THEOREM ========

# NO RIVAL COMES BACK TO ITS OWN CHOICE: on a grammar without a preference cycle, children
# for a production m that outranks q never hold a node of m's own nonterminal over all
# their tokens.
law no_self_rival:
  for +grammar: +List<Core.Production>
  for +marks: +List<Prefer.RankMark>
  for +q: Nat
  for +m: Nat
  for +ch: +List<Core.Tree>
  for +real: {Core.lhsIs(grammar, q, Gll.lhsOf(grammar, q)) == True{} : Bool}
  for +o: {Prefer.outranking(grammar, marks, q, m) == True{} : Bool}
  for +wf: {Prefer.noPreferenceCycle(grammar, marks) == True{} : Bool}
  for +fit: {Core.fits(ch, grammar, Core.rhsOf(grammar, m)) == True{} : Bool}
  for full: FullAt(grammar, ch, List.length(&2, Nat, Core.leaves(ch)), Gll.lhsOf(grammar, m))
  Empty

def no_self_rival(grammar, marks, q, m, ch, real, o, wf, fit, full):
  +nulls = Sets.growNulls(1n+List.length(&2, Core.Production, grammar), grammar, [])
  +po0 = {Prefer.prodsOk(grammar, grammar, marks, nulls, 0n) : Bool}
  +cn = Lemma.and_true_left(Sets.nullsClosed(grammar, nulls), po0, wf)
  +po = Lemma.and_true_right_side(Sets.nullsClosed(grammar, nulls), po0, wf)
  +hm = Lemma.and_true_left(Core.lhsIs(grammar, m, Gll.lhsOf(grammar, q)), Prefer.outranks(Prefer.rankOf(marks, m), Prefer.rankOf(marks, q)), o)
  +below = below_at(grammar, q, 0n, Gll.lhsOf(grammar, q), grammar, marks, m, real, o)
  +cf = prods_at(grammar, m, 0n, Gll.lhsOf(grammar, q), grammar, marks, nulls, hm, po, below)
  +es = Prefer.edgesFrom(Core.rhsOf(grammar, m), True{}, nulls)
  +r = Prefer.growReach(1n+List.length(&2, Core.Production, grammar), grammar, nulls, es)
  +x = Gll.lhsOf(grammar, m)
  +cr = Lemma.and_true_left(Prefer.reachClosed(grammar, nulls, r), Bool.and(Sets.allNatIn(es, r), Bool.not(Sets.natIn(x, r))), cf)
  +rest = Lemma.and_true_right_side(Prefer.reachClosed(grammar, nulls, r), Bool.and(Sets.allNatIn(es, r), Bool.not(Sets.natIn(x, r))), cf)
  +inR = Lemma.and_true_left(Sets.allNatIn(es, r), Bool.not(Sets.natIn(x, r)), rest)
  +out = Lemma.and_true_right_side(Sets.allNatIn(es, r), Bool.not(Sets.natIn(x, r)), rest)
  B.not_both(Sets.natIn(x, r), walk(ch, Core.rhsOf(grammar, m), True{}, grammar, nulls, r, List.length(&2, Nat, Core.leaves(ch)), x, cn, cr, {==}, fit, inR, full), out)

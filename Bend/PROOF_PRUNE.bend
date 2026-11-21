import Base
import ./LEMMAS.bend as Lemma
import ./CORE.bend as Core
import ./GLL.bend as Gll
import ./CHECK.bend as Check
import ./PRUNE.bend as Prune
import ./PROOF_GLL.bend as G

# PRUNING KEEPS EVERY STEP OF EVERY PARSE TREE.
#
# Walk a forest of a node from its end: the segment at the end of the node is needed;
# the forest's last step completes it, so that step is kept, and a kept step needs the
# segment before it and, after a nonterminal, the whole of the child's production. So the
# need moves left one item at a time and down into every child.

# ======== LISTS ========

law in_app_left:
  for xs: +List<Core.Bsr>
  for +ys: +List<Core.Bsr>
  for +set: +List<Core.Bsr>
  for +h: {Core.allIn(List.append(&2, Core.Bsr, xs, ys), set) == True{} : Bool}
  {Core.allIn(xs, set) == True{} : Bool}

def in_app_left(xs, ys, set, h):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Lemma.and_true_intro(Core.member(x, set), Core.allIn(rest, set),
        Lemma.and_true_left(Core.member(x, set), Core.allIn(List.append(&2, Core.Bsr, rest, ys), set), h),
        in_app_left(rest, ys, set, Lemma.and_true_right_side(Core.member(x, set), Core.allIn(List.append(&2, Core.Bsr, rest, ys), set), h)))

law in_app_right:
  for xs: +List<Core.Bsr>
  for +ys: +List<Core.Bsr>
  for +set: +List<Core.Bsr>
  for +h: {Core.allIn(List.append(&2, Core.Bsr, xs, ys), set) == True{} : Bool}
  {Core.allIn(ys, set) == True{} : Bool}

def in_app_right(xs, ys, set, h):
  match xs:
    case Nil{}:
      h
    case Con{+x, +rest}:
      in_app_right(rest, ys, set, Lemma.and_true_right_side(Core.member(x, set), Core.allIn(List.append(&2, Core.Bsr, rest, ys), set), h))

law reads_length:
  for f: +List<Core.Tree>
  for items: +List<Core.Sym>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +k: Nat
  for +r: {Core.reads(f, grammar, items, input, k) == True{} : Bool}
  {List.length(&2, Core.Tree, f) == List.length(&2, Core.Sym, items) : Nat}

def reads_length(f, items, grammar, input, k, r):
  match f items:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+s, +rest}:
      Empty.absurd({0n == 1n+List.length(&2, Core.Sym, rest) : Nat}, Lemma.false_is_not_true(r))
    case Con{Core.Leaf{+a}, +ts} Nil{}:
      Empty.absurd({1n+List.length(&2, Core.Tree, ts) == 0n : Nat}, Lemma.false_is_not_true(r))
    case Con{Core.Leaf{+a}, +ts} Con{Core.Terminal{+t}, +rest}:
      +more = {Bool.and(Core.tokIs(Core.tokAt(input, k), a), Core.reads(ts, grammar, rest, input, 1n+k)) : Bool}
      +n = reads_length(ts, rest, grammar, input, 1n+k, Lemma.and_true_right_side(Core.tokIs(Core.tokAt(input, k), a), Core.reads(ts, grammar, rest, input, 1n+k), Lemma.and_true_right_side(Nat.is_eq(a, t), more, r)))
      Equal.cong(Nat, Nat, v => 1n+v, List.length(&2, Core.Tree, ts), List.length(&2, Core.Sym, rest), n)
    case Con{Core.Leaf{+a}, +ts} Con{Core.Nonterminal{+x, +need}, +rest}:
      Empty.absurd({1n+List.length(&2, Core.Tree, ts) == 1n+List.length(&2, Core.Sym, rest) : Nat}, Lemma.false_is_not_true(r))
    case Con{Core.Node{+q, +ch}, +ts} Nil{}:
      Empty.absurd({1n+List.length(&2, Core.Tree, ts) == 0n : Nat}, Lemma.false_is_not_true(r))
    case Con{Core.Node{+q, +ch}, +ts} Con{Core.Terminal{+t}, +rest}:
      Empty.absurd({1n+List.length(&2, Core.Tree, ts) == 1n+List.length(&2, Core.Sym, rest) : Nat}, Lemma.false_is_not_true(r))
    case Con{Core.Node{+q, +ch}, +ts} Con{Core.Nonterminal{+x, +need}, +rest}:
      +own = {Bool.and(Bool.and(Core.lhsIs(grammar, q, x), Core.needOk(need, Core.width(Core.Node{q, ch}))), Core.reads(ch, grammar, Core.rhsOf(grammar, q), input, k)) : Bool}
      +after = {Core.reads(ts, grammar, rest, input, Nat.add(k, Core.width(Core.Node{q, ch}))) : Bool}
      +n = reads_length(ts, rest, grammar, input, Nat.add(k, Core.width(Core.Node{q, ch})), Lemma.and_true_right_side(own, after, r))
      Equal.cong(Nat, Nat, v => 1n+v, List.length(&2, Core.Tree, ts), List.length(&2, Core.Sym, rest), n)

# ======== THE NEEDS, ONE CONDITION AT A TIME ========

law keep_seg_here:
  for b: Bool
  for +s: Prune.Seg
  for +ss: +List<Prune.Seg>
  for +ns: +List<Prune.Seg>
  for +eb: {b == True{} : Bool}
  for +h: {Prune.allSegsIn(Prune.keepSeg(b, s, ss), ns) == True{} : Bool}
  {Prune.segIn(s, ns) == True{} : Bool}

def keep_seg_here(b, s, ss, ns, eb, h):
  match b:
    case True{}:
      Lemma.and_true_left(Prune.segIn(s, ns), Prune.allSegsIn(ss, ns), h)
    case False{}:
      Empty.absurd({Prune.segIn(s, ns) == True{} : Bool}, Lemma.false_is_not_true(eb))

law keep_seg_rest:
  for b: Bool
  for +s: Prune.Seg
  for +ss: +List<Prune.Seg>
  for +ns: +List<Prune.Seg>
  for +h: {Prune.allSegsIn(Prune.keepSeg(b, s, ss), ns) == True{} : Bool}
  {Prune.allSegsIn(ss, ns) == True{} : Bool}

def keep_seg_rest(b, s, ss, ns, h):
  match b:
    case True{}:
      Lemma.and_true_right_side(Prune.segIn(s, ns), Prune.allSegsIn(ss, ns), h)
    case False{}:
      h

law prod_seg_in:
  for g: +List<Core.Production>
  for q: Nat
  for +x: Nat
  for +base: Nat
  for +k: Nat
  for +j: Nat
  for +ns: +List<Prune.Seg>
  for +h: {Core.lhsIs(g, q, x) == True{} : Bool}
  for +all: {Prune.allSegsIn(Prune.prodSegs(g, x, base, k, j), ns) == True{} : Bool}
  {Prune.segIn(Prune.Seg{Nat.add(base, q), k, List.length(&2, Core.Sym, Core.rhsOf(g, q)), j}, ns) == True{} : Bool}

def prod_seg_in(g, q, x, base, k, j, ns, h, all):
  match g q:
    case Nil{} +q0:
      Empty.absurd({Prune.segIn(Prune.Seg{Nat.add(base, q0), k, List.length(&2, Core.Sym, Core.rhsOf([], q0)), j}, ns) == True{} : Bool}, Lemma.false_is_not_true(h))
    case Con{Core.Production{+lhs, +rhs}, +rest} 0n:
      %Equal.sym(Nat, Nat.add(base, 0n), base, Lemma.add_zero_right(base)) : {Prune.segIn(Prune.Seg{_, k, List.length(&2, Core.Sym, rhs), j}, ns) == True{} : Bool}
      keep_seg_here(Nat.is_eq(lhs, x), Prune.Seg{base, k, List.length(&2, Core.Sym, rhs), j}, Prune.prodSegs(rest, x, 1n+base, k, j), ns, h, all)
    case Con{Core.Production{+lhs, +rhs}, +rest} 1n+(+n):
      %Equal.sym(Nat, Nat.add(base, 1n+n), 1n+Nat.add(base, n), Lemma.add_succ_right(base, n)) : {Prune.segIn(Prune.Seg{_, k, List.length(&2, Core.Sym, Core.rhsOf(rest, n)), j}, ns) == True{} : Bool}
      prod_seg_in(rest, n, x, 1n+base, k, j, ns, h, keep_seg_rest(Nat.is_eq(lhs, x), Prune.Seg{base, k, List.length(&2, Core.Sym, rhs), j}, Prune.prodSegs(rest, x, 1n+base, k, j), ns, all))

def step_ok_pick(+x: Core.Bsr, +y: Core.Bsr, +rest: +List<Core.Bsr>, +grammar: +List<Core.Production>, +ns: +List<Prune.Seg>,
  cases: Either<{Core.bsrEq(x, y) == True{} : Bool}, {Core.member(x, rest) == True{} : Bool}>,
  +here: {Prune.stepOk(grammar, ns, y) == True{} : Bool},
  later: {Core.member(x, rest) == True{} : Bool} -> {Prune.stepOk(grammar, ns, x) == True{} : Bool})
  -> {Prune.stepOk(grammar, ns, x) == True{} : Bool}:
  match cases:
    case Inl{e}:
      %Equal.sym(Core.Bsr, x, y, G.bsr_eq_sound(x, y, e)) : {Prune.stepOk(grammar, ns, _) == True{} : Bool}
      here
    case Inr{m}:
      later(m)

law step_ok_of:
  for ys: +List<Core.Bsr>
  for +grammar: +List<Core.Production>
  for +ns: +List<Prune.Seg>
  for +x: Core.Bsr
  for +all: {Prune.allStepsOk(ys, grammar, ns) == True{} : Bool}
  for +m: {Core.member(x, ys) == True{} : Bool}
  {Prune.stepOk(grammar, ns, x) == True{} : Bool}

def step_ok_of(ys, grammar, ns, x, all, m):
  match ys:
    case Nil{}:
      Empty.absurd({Prune.stepOk(grammar, ns, x) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{+y, +rest}:
      step_ok_pick(x, y, rest, grammar, ns, Lemma.or_true_cases(Core.bsrEq(x, y), Core.member(x, rest), m),
        Lemma.and_true_left(Prune.stepOk(grammar, ns, y), Prune.allStepsOk(rest, grammar, ns), all),
        later => step_ok_of(rest, grammar, ns, x, Lemma.and_true_right_side(Prune.stepOk(grammar, ns, y), Prune.allStepsOk(rest, grammar, ns), all), later))

law or_not_true:
  for b: Bool
  for +c: Bool
  for +h: {Bool.or(Bool.not(b), c) == True{} : Bool}
  for +eb: {b == True{} : Bool}
  {c == True{} : Bool}

def or_not_true(b, c, h, eb):
  match b:
    case True{}:
      h
    case False{}:
      Empty.absurd({c == True{} : Bool}, Lemma.false_is_not_true(eb))

# A kept step of the parser's set brings its needs along.
law kept_needs:
  for +ys: +List<Core.Bsr>
  for +grammar: +List<Core.Production>
  for +ns: +List<Prune.Seg>
  for +x: Core.Bsr
  for +all: {Prune.allStepsOk(ys, grammar, ns) == True{} : Bool}
  for +m: {Core.member(x, ys) == True{} : Bool}
  for +kept: {Prune.isKept(x, ns) == True{} : Bool}
  {Prune.allSegsIn(Prune.stepNeeds(grammar, x), ns) == True{} : Bool}

def kept_needs(ys, grammar, ns, x, all, m, kept):
  or_not_true(Prune.isKept(x, ns), Prune.allSegsIn(Prune.stepNeeds(grammar, x), ns), step_ok_of(ys, grammar, ns, x, all, m), kept)

def kept_pick(b: Bool, +x: Core.Bsr, +y: Core.Bsr, +rest: +List<Core.Bsr>, +ns: +List<Prune.Seg>,
  +eb: {b == Prune.isKept(y, ns) : Bool},
  cases: Either<{Core.bsrEq(x, y) == True{} : Bool}, {Core.member(x, rest) == True{} : Bool}>,
  +kept: {Prune.isKept(x, ns) == True{} : Bool},
  later: {Core.member(x, rest) == True{} : Bool} -> {Core.member(x, Prune.keep(rest, ns)) == True{} : Bool})
  -> {Core.member(x, Prune.keepPick(b, y, Prune.keep(rest, ns))) == True{} : Bool}:
  match b cases:
    case True{} Inl{+e}:
      Lemma.or_true_left_intro(Core.bsrEq(x, y), Core.member(x, Prune.keep(rest, ns)), e)
    case True{} Inr{m}:
      Lemma.or_true_right_intro(Core.bsrEq(x, y), Core.member(x, Prune.keep(rest, ns)), later(m))
    case False{} Inl{+e}:
      +same = G.bsr_eq_sound(x, y, e)
      +ky = Equal.trans(Bool, Prune.isKept(y, ns), Prune.isKept(x, ns), True{}, Equal.cong(Core.Bsr, Bool, v => Prune.isKept(v, ns), y, x, Equal.sym(Core.Bsr, x, y, same)), kept)
      Empty.absurd({Core.member(x, Prune.keep(rest, ns)) == True{} : Bool}, Lemma.false_is_not_true(Equal.trans(Bool, False{}, Prune.isKept(y, ns), True{}, eb, ky)))
    case False{} Inr{m}:
      later(m)

# A kept step of the parser's set is in the pruned set.
law kept_member:
  for ys: +List<Core.Bsr>
  for +ns: +List<Prune.Seg>
  for +x: Core.Bsr
  for +m: {Core.member(x, ys) == True{} : Bool}
  for +kept: {Prune.isKept(x, ns) == True{} : Bool}
  {Core.member(x, Prune.keep(ys, ns)) == True{} : Bool}

def kept_member(ys, ns, x, m, kept):
  match ys:
    case Nil{}:
      Empty.absurd({Core.member(x, []) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{+y, +rest}:
      kept_pick(Prune.isKept(y, ns), x, y, rest, ns, {==}, Lemma.or_true_cases(Core.bsrEq(x, y), Core.member(x, rest), m), kept,
        later => kept_member(rest, ns, x, later, kept))

# ======== THE WALK, FROM THE RIGHT ========

# What the walk shows for a forest read from k, the rest of production q from dot d, in a
# node started at ks: the segment where the forest starts is needed, and the forest's own
# steps and all steps below it are kept.
def Pruned(+ns: +List<Prune.Seg>, +kept: +List<Core.Bsr>, +q: Nat, +ks: Nat, +f: +List<Core.Tree>, +d: Nat, +k: Nat) -> Type:
  {Prune.segIn(Prune.Seg{q, ks, d, k}, ns) == True{} : Bool} &
  {Core.allIn(Core.own(q, f, d, ks, k), kept) == True{} : Bool} &
  {Core.allIn(Core.steps(f, k), kept) == True{} : Bool}

law seg_start:
  for +q: Nat
  for +ks: Nat
  for +d: Nat
  for +k: Nat
  for +ns: +List<Prune.Seg>
  for +h: {Prune.segIn(Prune.Seg{q, ks, Nat.add(d, 0n), k}, ns) == True{} : Bool}
  {Prune.segIn(Prune.Seg{q, ks, d, k}, ns) == True{} : Bool}

def seg_start(q, ks, d, k, ns, h):
  %Lemma.add_zero_right(d) : {Prune.segIn(Prune.Seg{q, ks, _, k}, ns) == True{} : Bool}
  h

law seg_next:
  for +q: Nat
  for +ks: Nat
  for +d: Nat
  for +n: Nat
  for +e: Nat
  for +ns: +List<Prune.Seg>
  for +h: {Prune.segIn(Prune.Seg{q, ks, Nat.add(d, 1n+n), e}, ns) == True{} : Bool}
  {Prune.segIn(Prune.Seg{q, ks, Nat.add(1n+d, n), e}, ns) == True{} : Bool}

def seg_next(q, ks, d, n, e, ns, h):
  %Lemma.add_succ_right(d, n) : {Prune.segIn(Prune.Seg{q, ks, _, e}, ns) == True{} : Bool}
  h

law empty_kept:
  for dot: Nat
  for +q: Nat
  for +ks: Nat
  for +k: Nat
  for +ys: +List<Core.Bsr>
  for +ns: +List<Prune.Seg>
  for +iy: {Core.allIn(Core.emptyAt(dot, q, ks, k), ys) == True{} : Bool}
  for +seg: {Prune.segIn(Prune.Seg{q, ks, dot, k}, ns) == True{} : Bool}
  {Core.allIn(Core.emptyAt(dot, q, ks, k), Prune.keep(ys, ns)) == True{} : Bool}

def empty_kept(dot, q, ks, k, ys, ns, iy, seg):
  match dot:
    case 0n:
      +x = {Core.Bsr{q, 0n, ks, k, k} : Core.Bsr}
      Lemma.and_true_intro(Core.member(x, Prune.keep(ys, ns)), True{}, kept_member(ys, ns, x, Lemma.and_true_left(Core.member(x, ys), True{}, iy), seg), {==})
    case 1n+(+n):
      {==}

law leaf_view:
  for +q: Nat
  for +d: Nat
  for +ks: Nat
  for +k: Nat
  for +a: Nat
  for +ts: +List<Core.Tree>
  for +set: +List<Core.Bsr>
  for +h: {Core.allIn(Core.own(q, Core.Leaf{a} <> ts, d, ks, k), set) == True{} : Bool}
  {Core.allIn(Core.Bsr{q, 1n+d, ks, k, 1n+k} <> Core.own(q, ts, 1n+d, ks, 1n+k), set) == True{} : Bool}

def leaf_view(q, d, ks, k, a, ts, set, h):
  %Lemma.add_one_right(k) : {Core.allIn(Core.Bsr{q, 1n+d, ks, k, _} <> Core.own(q, ts, 1n+d, ks, _), set) == True{} : Bool}
  h

law leaf_back:
  for +q: Nat
  for +d: Nat
  for +ks: Nat
  for +k: Nat
  for +a: Nat
  for +ts: +List<Core.Tree>
  for +set: +List<Core.Bsr>
  for +h: {Core.allIn(Core.Bsr{q, 1n+d, ks, k, 1n+k} <> Core.own(q, ts, 1n+d, ks, 1n+k), set) == True{} : Bool}
  {Core.allIn(Core.own(q, Core.Leaf{a} <> ts, d, ks, k), set) == True{} : Bool}

def leaf_back(q, d, ks, k, a, ts, set, h):
  %Equal.sym(Nat, Nat.add(k, 1n), 1n+k, Lemma.add_one_right(k)) : {Core.allIn(Core.Bsr{q, 1n+d, ks, k, _} <> Core.own(q, ts, 1n+d, ks, _), set) == True{} : Bool}
  h

# After the rest of the forest: the leaf's step completes the needed segment there.
def leaf_after(+grammar: +List<Core.Production>, +ys: +List<Core.Bsr>, +ns: +List<Prune.Seg>,
  +ok: {Prune.allStepsOk(ys, grammar, ns) == True{} : Bool},
  +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +a: Nat, +ts: +List<Core.Tree>,
  +iyh: {Core.member(Core.Bsr{q, 1n+d, ks, k, 1n+k}, ys) == True{} : Bool},
  rest: Pruned(ns, Prune.keep(ys, ns), q, ks, ts, 1n+d, 1n+k)) -> Pruned(ns, Prune.keep(ys, ns), q, ks, Core.Leaf{a} <> ts, d, k):
  match rest:
    case (s0, (o1, st1)):
      +s1 = s0
      +x = {Core.Bsr{q, 1n+d, ks, k, 1n+k} : Core.Bsr}
      +kept = Prune.keep(ys, ns)
      +mk = kept_member(ys, ns, x, iyh, s1)
      +needs = kept_needs(ys, grammar, ns, x, ok, iyh, s1)
      +before = Lemma.and_true_left(Prune.segIn(Prune.Seg{q, ks, d, k}, ns), Prune.allSegsIn(Prune.itemNeeds(Gll.nthSym(Core.rhsOf(grammar, q), d), grammar, k, 1n+k), ns), needs)
      +own = leaf_back(q, d, ks, k, a, ts, kept, Lemma.and_true_intro(Core.member(x, kept), Core.allIn(Core.own(q, ts, 1n+d, ks, 1n+k), kept), mk, o1))
      {(before, (own, st1)) : Pruned(ns, kept, q, ks, Core.Leaf{a} <> ts, d, k)}

law item_segs:
  for +grammar: +List<Core.Production>
  for +q: Nat
  for +d: Nat
  for +x: Nat
  for +need: Core.Need
  for +rest: +List<Core.Sym>
  for +k: Nat
  for +j: Nat
  for +ns: +List<Prune.Seg>
  for +ie: {G.dropFrom(d, Core.rhsOf(grammar, q)) == Core.Nonterminal{x, need} <> rest : +List<Core.Sym>}
  for +h: {Prune.allSegsIn(Prune.itemNeeds(Gll.nthSym(Core.rhsOf(grammar, q), d), grammar, k, j), ns) == True{} : Bool}
  {Prune.allSegsIn(Prune.prodSegs(grammar, x, 0n, k, j), ns) == True{} : Bool}

def item_segs(grammar, q, d, x, need, rest, k, j, ns, ie, h):
  %G.nth_drop(Core.rhsOf(grammar, q), d, Core.Nonterminal{x, need}, rest, ie) : {Prune.allSegsIn(Prune.itemNeeds(_, grammar, k, j), ns) == True{} : Bool}
  h

law child_seg:
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +q2: Nat
  for +ch: +List<Core.Tree>
  for +k: Nat
  for +ns: +List<Prune.Seg>
  for +rc: {Core.reads(ch, grammar, Core.rhsOf(grammar, q2), input, k) == True{} : Bool}
  for +h: {Prune.segIn(Prune.Seg{q2, k, List.length(&2, Core.Sym, Core.rhsOf(grammar, q2)), Nat.add(k, Core.width(Core.Node{q2, ch}))}, ns) == True{} : Bool}
  {Prune.segIn(Prune.Seg{q2, k, Nat.add(0n, List.length(&2, Core.Tree, ch)), G.endOf(ch, k)}, ns) == True{} : Bool}

def child_seg(grammar, input, q2, ch, k, ns, rc, h):
  %Equal.sym(Nat, List.length(&2, Core.Tree, ch), List.length(&2, Core.Sym, Core.rhsOf(grammar, q2)), reads_length(ch, Core.rhsOf(grammar, q2), grammar, input, k, rc)) : {Prune.segIn(Prune.Seg{q2, k, _, G.endOf(ch, k)}, ns) == True{} : Bool}
  %Equal.sym(Nat, G.endOf(ch, k), Nat.add(k, Core.width(Core.Node{q2, ch})), G.end_node(q2, ch, k)) : {Prune.segIn(Prune.Seg{q2, k, List.length(&2, Core.Sym, Core.rhsOf(grammar, q2)), _}, ns) == True{} : Bool}
  h

law all_in_app_g:
  for xs: +List<Core.Bsr>
  for +ys: +List<Core.Bsr>
  for +set: +List<Core.Bsr>
  for +hx: {Core.allIn(xs, set) == True{} : Bool}
  for +hy: {Core.allIn(ys, set) == True{} : Bool}
  {Core.allIn(List.append(&2, Core.Bsr, xs, ys), set) == True{} : Bool}

def all_in_app_g(xs, ys, set, hx, hy):
  G.all_in_app(xs, ys, set, hx, hy)

def node_join(+ys: +List<Core.Bsr>, +ns: +List<Prune.Seg>, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +q2: Nat, +ch: +List<Core.Tree>, +ts: +List<Core.Tree>,
  +before: {Prune.segIn(Prune.Seg{q, ks, d, k}, ns) == True{} : Bool},
  +own: {Core.allIn(Core.own(q, Core.Node{q2, ch} <> ts, d, ks, k), Prune.keep(ys, ns)) == True{} : Bool},
  +st1: {Core.allIn(Core.steps(ts, Nat.add(k, Core.width(Core.Node{q2, ch}))), Prune.keep(ys, ns)) == True{} : Bool},
  below: Pruned(ns, Prune.keep(ys, ns), q2, k, ch, 0n, k)) -> Pruned(ns, Prune.keep(ys, ns), q, ks, Core.Node{q2, ch} <> ts, d, k):
  match below:
    case (s0, (oc, sc)):
      +kept = Prune.keep(ys, ns)
      +far = {Nat.add(k, Core.width(Core.Node{q2, ch})) : Nat}
      +all = all_in_app_g(Core.own(q2, ch, 0n, k, k), List.append(&2, Core.Bsr, Core.steps(ch, k), Core.steps(ts, far)), kept, oc, all_in_app_g(Core.steps(ch, k), Core.steps(ts, far), kept, sc, st1))
      {(before, (own, all)) : Pruned(ns, kept, q, ks, Core.Node{q2, ch} <> ts, d, k)}

# After the rest of the forest: the node's step completes the needed segment there, so it
# is kept, and it needs the segment before it and the whole of its child's production.
def node_after(+grammar: +List<Core.Production>, +input: +List<Nat>, +ys: +List<Core.Bsr>, +ns: +List<Prune.Seg>,
  +ok: {Prune.allStepsOk(ys, grammar, ns) == True{} : Bool},
  +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +q2: Nat, +ch: +List<Core.Tree>, +ts: +List<Core.Tree>, +x: Nat, +need: Core.Need, +rest: +List<Core.Sym>,
  +ie: {G.dropFrom(d, Core.rhsOf(grammar, q)) == Core.Nonterminal{x, need} <> rest : +List<Core.Sym>},
  +lhs: {Core.lhsIs(grammar, q2, x) == True{} : Bool},
  +rc: {Core.reads(ch, grammar, Core.rhsOf(grammar, q2), input, k) == True{} : Bool},
  +iyh: {Core.member(Core.Bsr{q, 1n+d, ks, k, Nat.add(k, Core.width(Core.Node{q2, ch}))}, ys) == True{} : Bool},
  rest1: Pruned(ns, Prune.keep(ys, ns), q, ks, ts, 1n+d, Nat.add(k, Core.width(Core.Node{q2, ch}))),
  recCh: {Prune.segIn(Prune.Seg{q2, k, Nat.add(0n, List.length(&2, Core.Tree, ch)), G.endOf(ch, k)}, ns) == True{} : Bool} -> Pruned(ns, Prune.keep(ys, ns), q2, k, ch, 0n, k))
  -> Pruned(ns, Prune.keep(ys, ns), q, ks, Core.Node{q2, ch} <> ts, d, k):
  match rest1:
    case (s0, (o1, st1)):
      +s1 = s0
      +far = {Nat.add(k, Core.width(Core.Node{q2, ch})) : Nat}
      +step = {Core.Bsr{q, 1n+d, ks, k, far} : Core.Bsr}
      +kept = Prune.keep(ys, ns)
      +mk = kept_member(ys, ns, step, iyh, s1)
      +needs = kept_needs(ys, grammar, ns, step, ok, iyh, s1)
      +here = {Prune.segIn(Prune.Seg{q, ks, d, k}, ns) : Bool}
      +item = {Prune.allSegsIn(Prune.itemNeeds(Gll.nthSym(Core.rhsOf(grammar, q), d), grammar, k, far), ns) : Bool}
      +before = Lemma.and_true_left(here, item, needs)
      +prods = item_segs(grammar, q, d, x, need, rest, k, far, ns, ie, Lemma.and_true_right_side(here, item, needs))
      +child = child_seg(grammar, input, q2, ch, k, ns, rc, prod_seg_in(grammar, q2, x, 0n, k, far, ns, lhs, prods))
      +own = Lemma.and_true_intro(Core.member(step, kept), Core.allIn(Core.own(q, ts, 1n+d, ks, far), kept), mk, o1)
      node_join(ys, ns, q, ks, d, k, q2, ch, ts, before, own, st1, recCh(child))

law pwalk:
  for f: +List<Core.Tree>
  for items: +List<Core.Sym>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +ys: +List<Core.Bsr>
  for +ns: +List<Prune.Seg>
  for +ok: {Prune.allStepsOk(ys, grammar, ns) == True{} : Bool}
  for +q: Nat
  for +ks: Nat
  for +d: Nat
  for +k: Nat
  for +ie: {G.dropFrom(d, Core.rhsOf(grammar, q)) == items : +List<Core.Sym>}
  for +r: {Core.reads(f, grammar, items, input, k) == True{} : Bool}
  for +iy: {Core.allIn(Core.own(q, f, d, ks, k), ys) == True{} : Bool}
  for +sy: {Core.allIn(Core.steps(f, k), ys) == True{} : Bool}
  for +en: {Prune.segIn(Prune.Seg{q, ks, Nat.add(d, List.length(&2, Core.Tree, f)), G.endOf(f, k)}, ns) == True{} : Bool}
  Pruned(ns, Prune.keep(ys, ns), q, ks, f, d, k)

def pwalk(f, items, grammar, input, ys, ns, ok, q, ks, d, k, ie, r, iy, sy, en):
  match f items:
    case Nil{} Nil{}:
      +seg = seg_start(q, ks, d, k, ns, en)
      +own = empty_kept(d, q, ks, k, ys, ns, iy, seg)
      {(seg, (own, {==})) : Pruned(ns, Prune.keep(ys, ns), q, ks, [], d, k)}
    case Nil{} Con{+y, +yr}:
      Empty.absurd(Pruned(ns, Prune.keep(ys, ns), q, ks, [], d, k), Lemma.false_is_not_true(r))
    case Con{Core.Leaf{+a}, +ts} Nil{}:
      Empty.absurd(Pruned(ns, Prune.keep(ys, ns), q, ks, Core.Leaf{a} <> ts, d, k), Lemma.false_is_not_true(r))
    case Con{Core.Leaf{+a}, +ts} Con{Core.Nonterminal{+x, +need}, +rest}:
      Empty.absurd(Pruned(ns, Prune.keep(ys, ns), q, ks, Core.Leaf{a} <> ts, d, k), Lemma.false_is_not_true(r))
    case Con{Core.Leaf{+a}, +ts} Con{Core.Terminal{+t}, +rest}:
      +more = {Bool.and(Core.tokIs(Core.tokAt(input, k), a), Core.reads(ts, grammar, rest, input, 1n+k)) : Bool}
      +rt = Lemma.and_true_right_side(Core.tokIs(Core.tokAt(input, k), a), Core.reads(ts, grammar, rest, input, 1n+k), Lemma.and_true_right_side(Nat.is_eq(a, t), more, r))
      +view = leaf_view(q, d, ks, k, a, ts, ys, iy)
      +x = {Core.Bsr{q, 1n+d, ks, k, 1n+k} : Core.Bsr}
      +iyh = Lemma.and_true_left(Core.member(x, ys), Core.allIn(Core.own(q, ts, 1n+d, ks, 1n+k), ys), view)
      +iyt = Lemma.and_true_right_side(Core.member(x, ys), Core.allIn(Core.own(q, ts, 1n+d, ks, 1n+k), ys), view)
      +en2 = seg_next(q, ks, d, List.length(&2, Core.Tree, ts), G.endOf(ts, 1n+k), ns, en)
      leaf_after(grammar, ys, ns, ok, q, ks, d, k, a, ts, iyh,
        pwalk(ts, rest, grammar, input, ys, ns, ok, q, ks, 1n+d, 1n+k, G.drop_next(Core.rhsOf(grammar, q), d, Core.Terminal{t}, rest, ie), rt, iyt, sy, en2))
    case Con{Core.Node{+q2, +ch}, +ts} Nil{}:
      Empty.absurd(Pruned(ns, Prune.keep(ys, ns), q, ks, Core.Node{q2, ch} <> ts, d, k), Lemma.false_is_not_true(r))
    case Con{Core.Node{+q2, +ch}, +ts} Con{Core.Terminal{+t}, +rest}:
      Empty.absurd(Pruned(ns, Prune.keep(ys, ns), q, ks, Core.Node{q2, ch} <> ts, d, k), Lemma.false_is_not_true(r))
    case Con{Core.Node{+q2, +ch}, +ts} Con{Core.Nonterminal{+x, +need}, +rest}:
      +far = {Nat.add(k, Core.width(Core.Node{q2, ch})) : Nat}
      +head = {Bool.and(Core.lhsIs(grammar, q2, x), Core.needOk(need, Core.width(Core.Node{q2, ch}))) : Bool}
      +own = {Bool.and(head, Core.reads(ch, grammar, Core.rhsOf(grammar, q2), input, k)) : Bool}
      +left = Lemma.and_true_left(own, Core.reads(ts, grammar, rest, input, far), r)
      +lhs = Lemma.and_true_left(Core.lhsIs(grammar, q2, x), Core.needOk(need, Core.width(Core.Node{q2, ch})), Lemma.and_true_left(head, Core.reads(ch, grammar, Core.rhsOf(grammar, q2), input, k), left))
      +rc = Lemma.and_true_right_side(head, Core.reads(ch, grammar, Core.rhsOf(grammar, q2), input, k), left)
      +rt = Lemma.and_true_right_side(own, Core.reads(ts, grammar, rest, input, far), r)
      +step = {Core.Bsr{q, 1n+d, ks, k, far} : Core.Bsr}
      +iyh = Lemma.and_true_left(Core.member(step, ys), Core.allIn(Core.own(q, ts, 1n+d, ks, far), ys), iy)
      +iyt = Lemma.and_true_right_side(Core.member(step, ys), Core.allIn(Core.own(q, ts, 1n+d, ks, far), ys), iy)
      +below = {List.append(&2, Core.Bsr, Core.steps(ch, k), Core.steps(ts, far)) : +List<Core.Bsr>}
      +syo = in_app_left(Core.own(q2, ch, 0n, k, k), below, ys, sy)
      +syr = in_app_right(Core.own(q2, ch, 0n, k, k), below, ys, sy)
      +syc = in_app_left(Core.steps(ch, k), Core.steps(ts, far), ys, syr)
      +syt = in_app_right(Core.steps(ch, k), Core.steps(ts, far), ys, syr)
      +en2 = seg_next(q, ks, d, List.length(&2, Core.Tree, ts), G.endOf(ts, far), ns, en)
      node_after(grammar, input, ys, ns, ok, q, ks, d, k, q2, ch, ts, x, need, rest, ie, lhs, rc, iyh,
        pwalk(ts, rest, grammar, input, ys, ns, ok, q, ks, 1n+d, far, G.drop_next(Core.rhsOf(grammar, q), d, Core.Nonterminal{x, need}, rest, ie), rt, iyt, syt, en2),
        enc => pwalk(ch, Core.rhsOf(grammar, q2), grammar, input, ys, ns, ok, q2, k, 0n, k, {==}, rc, syo, syc, enc))

# ======== THE THEOREM ========

# Every step of a parse tree is in the checked parser's set.
def state_steps(b: Bool, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +s: Gll.GState, +ys: +List<Core.Bsr>,
  +eb: {b == Bool.and(Check.closed(grammar, input, s), Gll.keyIn(Gll.CKey{start, 0n}, Check.clustersOf(s))) : Bool},
  +e: {Check.checkPick(b, s) == Some{ys} : Maybe<&2, +List<Core.Bsr>>},
  +tree: Core.Tree,
  +rr: {Core.reads([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool})
  -> {Core.allIn(Core.steps([tree], 0n), ys) == True{} : Bool}:
  match b:
    case True{}:
      +both = Equal.sym(Bool, True{}, Bool.and(Check.closed(grammar, input, s), Gll.keyIn(Gll.CKey{start, 0n}, Check.clustersOf(s))), eb)
      +hc = Lemma.and_true_left(Check.closed(grammar, input, s), Gll.keyIn(Gll.CKey{start, 0n}, Check.clustersOf(s)), both)
      +root = Lemma.and_true_right_side(Check.closed(grammar, input, s), Gll.keyIn(Gll.CKey{start, 0n}, Check.clustersOf(s)), both)
      +es = Equal.cong(Maybe<&2, +List<Core.Bsr>>, +List<Core.Bsr>, v => G.setOr(v, []), Some{Check.stepsOf(s)}, Some{ys}, e)
      %es : {Core.allIn(Core.steps([tree], 0n), _) == True{} : Bool}
      G.tree_steps(tree, grammar, start, input, s, hc, root, rr)
    case False{}:
      Empty.absurd({Core.allIn(Core.steps([tree], 0n), ys) == True{} : Bool}, G.none_not_some(ys, e))

def run_steps(r: Gll.GRun, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +ys: +List<Core.Bsr>,
  +e: {Check.runChecked(r, grammar, start, input) == Some{ys} : Maybe<&2, +List<Core.Bsr>>},
  +tree: Core.Tree,
  +rr: {Core.reads([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool})
  -> {Core.allIn(Core.steps([tree], 0n), ys) == True{} : Bool}:
  match r:
    case Gll.GDone{+s}:
      state_steps(Bool.and(Check.closed(grammar, input, s), Gll.keyIn(Gll.CKey{start, 0n}, Check.clustersOf(s))), grammar, start, input, s, ys, {==}, e, tree, rr)
    case Gll.OutOfFuel{+s}:
      Empty.absurd({Core.allIn(Core.steps([tree], 0n), ys) == True{} : Bool}, G.none_not_some(ys, e))

law leaves_end:
  for +q: Nat
  for +ch: +List<Core.Tree>
  for +input: +List<Nat>
  for +rl: {List.length(&2, Nat, Core.leaves([Core.Node{q, ch}])) == List.length(&2, Nat, input) : Nat}
  {G.endOf(ch, 0n) == List.length(&2, Nat, input) : Nat}

def leaves_end(q, ch, input, rl):
  Equal.trans(Nat, G.endOf(ch, 0n), List.length(&2, Nat, Core.leaves(ch)), List.length(&2, Nat, input), G.end_eq(ch, 0n),
    Equal.trans(Nat, List.length(&2, Nat, Core.leaves(ch)), List.length(&2, Nat, List.append(&2, Nat, Core.leaves(ch), [])), List.length(&2, Nat, input),
      Equal.cong(+List<Nat>, Nat, v => List.length(&2, Nat, v), Core.leaves(ch), List.append(&2, Nat, Core.leaves(ch), []), Equal.sym(+List<Nat>, List.append(&2, Nat, Core.leaves(ch), []), Core.leaves(ch), Lemma.append_nil_right(Core.leaves(ch)))),
      rl))

law root_seg:
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +q: Nat
  for +ch: +List<Core.Tree>
  for +ns: +List<Prune.Seg>
  for +rc: {Core.reads(ch, grammar, Core.rhsOf(grammar, q), input, 0n) == True{} : Bool}
  for +rl: {List.length(&2, Nat, Core.leaves([Core.Node{q, ch}])) == List.length(&2, Nat, input) : Nat}
  for +h: {Prune.segIn(Prune.Seg{q, 0n, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), List.length(&2, Nat, input)}, ns) == True{} : Bool}
  {Prune.segIn(Prune.Seg{q, 0n, Nat.add(0n, List.length(&2, Core.Tree, ch)), G.endOf(ch, 0n)}, ns) == True{} : Bool}

def root_seg(grammar, input, q, ch, ns, rc, rl, h):
  %Equal.sym(Nat, List.length(&2, Core.Tree, ch), List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), reads_length(ch, Core.rhsOf(grammar, q), grammar, input, 0n, rc)) : {Prune.segIn(Prune.Seg{q, 0n, _, G.endOf(ch, 0n)}, ns) == True{} : Bool}
  %Equal.sym(Nat, G.endOf(ch, 0n), List.length(&2, Nat, input), leaves_end(q, ch, input, rl)) : {Prune.segIn(Prune.Seg{q, 0n, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), _}, ns) == True{} : Bool}
  h

def root_join(+ys: +List<Core.Bsr>, +ns: +List<Prune.Seg>, +q: Nat, +ch: +List<Core.Tree>, p: Pruned(ns, Prune.keep(ys, ns), q, 0n, ch, 0n, 0n))
  -> {Core.allIn(Core.steps([Core.Node{q, ch}], 0n), Prune.keep(ys, ns)) == True{} : Bool}:
  match p:
    case (s0, (o, st)):
      +kept = Prune.keep(ys, ns)
      G.all_in_app(Core.own(q, ch, 0n, 0n, 0n), List.append(&2, Core.Bsr, Core.steps(ch, 0n), []), kept, o, G.all_in_app(Core.steps(ch, 0n), [], kept, st, {==}))

# Every step of a parse tree is kept.
law tree_kept:
  for tree: Core.Tree
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +ys: +List<Core.Bsr>
  for +ns: +List<Prune.Seg>
  for +ok: {Prune.allStepsOk(ys, grammar, ns) == True{} : Bool}
  for +roots: {Prune.allSegsIn(Prune.rootSegs(grammar, start, List.length(&2, Nat, input)), ns) == True{} : Bool}
  for +inYs: {Core.allIn(Core.steps([tree], 0n), ys) == True{} : Bool}
  for +rr: {Core.reads([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool}
  for +rl: {List.length(&2, Nat, Core.leaves([tree])) == List.length(&2, Nat, input) : Nat}
  {Core.allIn(Core.steps([tree], 0n), Prune.keep(ys, ns)) == True{} : Bool}

def tree_kept(tree, grammar, start, input, ys, ns, ok, roots, inYs, rr, rl):
  match tree:
    case Core.Leaf{+a}:
      Empty.absurd({Core.allIn(Core.steps([Core.Leaf{a}], 0n), Prune.keep(ys, ns)) == True{} : Bool}, Lemma.false_is_not_true(rr))
    case Core.Node{+q, +ch}:
      +w = {Core.width(Core.Node{q, ch}) : Nat}
      +head = {Bool.and(Core.lhsIs(grammar, q, start), True{}) : Bool}
      +own = {Bool.and(head, Core.reads(ch, grammar, Core.rhsOf(grammar, q), input, 0n)) : Bool}
      +left = Lemma.and_true_left(own, Core.reads([], grammar, [], input, Nat.add(0n, w)), rr)
      +lhs = Lemma.and_true_left(Core.lhsIs(grammar, q, start), True{}, Lemma.and_true_left(head, Core.reads(ch, grammar, Core.rhsOf(grammar, q), input, 0n), left))
      +rc = Lemma.and_true_right_side(head, Core.reads(ch, grammar, Core.rhsOf(grammar, q), input, 0n), left)
      +below = {List.append(&2, Core.Bsr, Core.steps(ch, 0n), []) : +List<Core.Bsr>}
      +iyo = in_app_left(Core.own(q, ch, 0n, 0n, 0n), below, ys, inYs)
      +syc = in_app_left(Core.steps(ch, 0n), [], ys, in_app_right(Core.own(q, ch, 0n, 0n, 0n), below, ys, inYs))
      +en = root_seg(grammar, input, q, ch, ns, rc, rl, prod_seg_in(grammar, q, start, 0n, 0n, List.length(&2, Nat, input), ns, lhs, roots))
      root_join(ys, ns, q, ch, pwalk(ch, Core.rhsOf(grammar, q), grammar, input, ys, ns, ok, q, 0n, 0n, 0n, {==}, rc, iyo, syc, en))

def from_tree(+fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +ys: +List<Core.Bsr>, +ns: +List<Prune.Seg>, +set: +List<Core.Bsr>,
  +ec: {Check.checkedSteps(fuel, grammar, start, input) == Some{ys} : Maybe<&2, +List<Core.Bsr>>},
  +ok: {Prune.allStepsOk(ys, grammar, ns) == True{} : Bool},
  +roots: {Prune.allSegsIn(Prune.rootSegs(grammar, start, List.length(&2, Nat, input)), ns) == True{} : Bool},
  +es: {Prune.keep(ys, ns) == set : +List<Core.Bsr>},
  +tree: Core.Tree, +x: Core.Bsr, pt: Core.ParseTree(grammar, start, input, tree),
  +m: {Core.member(x, Core.steps([tree], 0n)) == True{} : Bool}) -> {Core.member(x, set) == True{} : Bool}:
  match pt:
    case (rr0, rl0):
      +rr = rr0
      +rl = rl0
      +inYs = run_steps(Gll.parse(fuel, grammar, start, input), grammar, start, input, ys, ec, tree, rr)
      %es : {Core.member(x, _) == True{} : Bool}
      G.all_in_member(Core.steps([tree], 0n), Prune.keep(ys, ns), x, tree_kept(tree, grammar, start, input, ys, ns, ok, roots, inYs, rr, rl), m)

def pick_parts(b: Bool, +fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +ys: +List<Core.Bsr>, +ns: +List<Prune.Seg>, +set: +List<Core.Bsr>,
  +ec: {Check.checkedSteps(fuel, grammar, start, input) == Some{ys} : Maybe<&2, +List<Core.Bsr>>},
  +eb: {b == Prune.needsClosed(grammar, start, List.length(&2, Nat, input), ys, ns) : Bool},
  +e: {Prune.prunePick(b, ys, ns) == Some{set} : Maybe<&2, +List<Core.Bsr>>}) -> Core.EveryParseStep(grammar, start, input, set):
  match b:
    case True{}:
      +n = List.length(&2, Nat, input)
      +hn = Equal.sym(Bool, True{}, Prune.needsClosed(grammar, start, n, ys, ns), eb)
      +roots = Lemma.and_true_left(Prune.allSegsIn(Prune.rootSegs(grammar, start, n), ns), Prune.allStepsOk(ys, grammar, ns), hn)
      +ok = Lemma.and_true_right_side(Prune.allSegsIn(Prune.rootSegs(grammar, start, n), ns), Prune.allStepsOk(ys, grammar, ns), hn)
      +es = Equal.cong(Maybe<&2, +List<Core.Bsr>>, +List<Core.Bsr>, v => G.setOr(v, []), Some{Prune.keep(ys, ns)}, Some{set}, e)
      tree => x => pt => m => from_tree(fuel, grammar, start, input, ys, ns, set, ec, ok, roots, es, tree, x, pt, m)
    case False{}:
      Empty.absurd(Core.EveryParseStep(grammar, start, input, set), G.none_not_some(set, e))

def needs_parts(nm: Maybe<&2, +List<Prune.Seg>>, +fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +ys: +List<Core.Bsr>, +set: +List<Core.Bsr>,
  +ec: {Check.checkedSteps(fuel, grammar, start, input) == Some{ys} : Maybe<&2, +List<Core.Bsr>>},
  +e: {Prune.pruneChecked(nm, grammar, start, List.length(&2, Nat, input), ys) == Some{set} : Maybe<&2, +List<Core.Bsr>>}) -> Core.EveryParseStep(grammar, start, input, set):
  match nm:
    case Some{+ns}:
      pick_parts(Prune.needsClosed(grammar, start, List.length(&2, Nat, input), ys, ns), fuel, grammar, start, input, ys, ns, set, ec, {==}, e)
    case None{}:
      Empty.absurd(Core.EveryParseStep(grammar, start, input, set), G.none_not_some(set, e))

def checked_parts(m: Maybe<&2, +List<Core.Bsr>>, +fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>,
  +em: {Check.checkedSteps(fuel, grammar, start, input) == m : Maybe<&2, +List<Core.Bsr>>},
  +e: {Prune.pruneSteps(m, fuel, grammar, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>}) -> Core.EveryParseStep(grammar, start, input, set):
  match m:
    case Some{+ys}:
      needs_parts(Prune.needsOf(fuel, grammar, start, List.length(&2, Nat, input), ys), fuel, grammar, start, input, ys, set, em, e)
    case None{}:
      Empty.absurd(Core.EveryParseStep(grammar, start, input, set), G.none_not_some(set, e))

# PRUNING KEEPS EVERY STEP OF EVERY PARSE TREE: whenever the pruned parser hands out a set,
# every step of every parse tree of the input is in it.
law prune_every_parse_step:
  for fuel: Nat
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Core.Bsr>
  for +got: {Prune.prunedSteps(fuel, grammar, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>}
  Core.EveryParseStep(grammar, start, input, set)

def prune_every_parse_step(fuel, grammar, start, input, set, got):
  +f = fuel
  checked_parts(Check.checkedSteps(f, grammar, start, input), f, grammar, start, input, set, {==}, got)

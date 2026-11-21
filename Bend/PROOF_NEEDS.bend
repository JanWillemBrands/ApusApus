import Base
import ./LEMMAS.bend as Lemma
import ./CORE.bend as Core
import ./GLL.bend as Gll
import ./CHECK.bend as Check
import ./PRUNE.bend as Prune
import ./RUN.bend as Run
import ./PROOF_GLL.bend as G
import ./PROOF_COUNT.bend as C

# THE NEEDS LOOP ANSWERS: pruning's loop (PRUNE.bend), run on steps that lie within bounds,
# finishes with fuel 1 + the size of the descriptor universe, and its needs are closed, so
# pruning hands out its steps (`pruned_answers`).
#
# A segment Seg{q, ks, dot, end} is counted as the descriptor Desc{q, dot, ks, end}, so the
# universe and the counting of RUN.bend serve. The invariant, while the needs `rem` of one
# segment are being added: every seen segment is still to do or has its needs in
# rem ++ seen; the to-do list is seen; seen and rem lie within bounds; the root segments lie
# in rem ++ seen. With rem empty and nothing to do, the needs are closed.

# ======== SEGMENT LISTS ========

law seg_eq_sound:
  for a: Prune.Seg
  for b: Prune.Seg
  for +e: {Prune.segEq(a, b) == True{} : Bool}
  {a == b : Prune.Seg}

def seg_eq_sound(a, b, e):
  match a b:
    case Prune.Seg{+q1, +d1, +k1, +i1} Prune.Seg{+q2, +d2, +k2, +i2}:
      +r1 = {Bool.and(Nat.is_eq(d1, d2), Bool.and(Nat.is_eq(k1, k2), Nat.is_eq(i1, i2))) : Bool}
      +r2 = {Bool.and(Nat.is_eq(k1, k2), Nat.is_eq(i1, i2)) : Bool}
      +e1 = Lemma.and_true_right_side(Nat.is_eq(q1, q2), r1, e)
      +e2 = Lemma.and_true_right_side(Nat.is_eq(d1, d2), r2, e1)
      +eq = Lemma.nat_eq_sound(q1, q2, Lemma.and_true_left(Nat.is_eq(q1, q2), r1, e))
      +ed = Lemma.nat_eq_sound(d1, d2, Lemma.and_true_left(Nat.is_eq(d1, d2), r2, e1))
      +ek = Lemma.nat_eq_sound(k1, k2, Lemma.and_true_left(Nat.is_eq(k1, k2), Nat.is_eq(i1, i2), e2))
      +ei = Lemma.nat_eq_sound(i1, i2, Lemma.and_true_right_side(Nat.is_eq(k1, k2), Nat.is_eq(i1, i2), e2))
      %eq : {Prune.Seg{q1, d1, k1, i1} == Prune.Seg{_, d2, k2, i2} : Prune.Seg}
      %ed : {Prune.Seg{q1, d1, k1, i1} == Prune.Seg{q1, _, k2, i2} : Prune.Seg}
      %ek : {Prune.Seg{q1, d1, k1, i1} == Prune.Seg{q1, d1, _, i2} : Prune.Seg}
      %ei : {Prune.Seg{q1, d1, k1, i1} == Prune.Seg{q1, d1, k1, _} : Prune.Seg}
      {==}


def seg_eq_refl(d: Prune.Seg) -> {Prune.segEq(d, d) == True{} : Bool}:
  match d:
    case Prune.Seg{+q, +dt, +k, +i}:
      Lemma.and_true_intro(Nat.is_eq(q, q), Bool.and(Nat.is_eq(dt, dt), Bool.and(Nat.is_eq(k, k), Nat.is_eq(i, i))), Lemma.nat_eq_refl(q),
        Lemma.and_true_intro(Nat.is_eq(dt, dt), Bool.and(Nat.is_eq(k, k), Nat.is_eq(i, i)), Lemma.nat_eq_refl(dt),
          Lemma.and_true_intro(Nat.is_eq(k, k), Nat.is_eq(i, i), Lemma.nat_eq_refl(k), Lemma.nat_eq_refl(i))))

def seg_pick(+x: Prune.Seg, +y: Prune.Seg, +rest: +List<Prune.Seg>, +ys: +List<Prune.Seg>,
  +hy: {Prune.segIn(y, ys) == True{} : Bool},
  cases: Either<{Prune.segEq(x, y) == True{} : Bool}, {Prune.segIn(x, rest) == True{} : Bool}>,
  later: {Prune.segIn(x, rest) == True{} : Bool} -> {Prune.segIn(x, ys) == True{} : Bool}) -> {Prune.segIn(x, ys) == True{} : Bool}:
  match cases:
    case Inl{e}:
      %Equal.sym(Prune.Seg, x, y, seg_eq_sound(x, y, e)) : {Prune.segIn(_, ys) == True{} : Bool}
      hy
    case Inr{m}:
      later(m)

law seg_sub:
  for xs: +List<Prune.Seg>
  for +x: Prune.Seg
  for +ys: +List<Prune.Seg>
  for +m: {Prune.segIn(x, xs) == True{} : Bool}
  for +h: {Prune.allSegsIn(xs, ys) == True{} : Bool}
  {Prune.segIn(x, ys) == True{} : Bool}

def seg_sub(xs, x, ys, m, h):
  match xs:
    case Nil{}:
      Empty.absurd({Prune.segIn(x, ys) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{+y, +rest}:
      seg_pick(x, y, rest, ys, Lemma.and_true_left(Prune.segIn(y, ys), Prune.allSegsIn(rest, ys), h), Lemma.or_true_cases(Prune.segEq(x, y), Prune.segIn(x, rest), m),
        m2 => seg_sub(rest, x, ys, m2, Lemma.and_true_right_side(Prune.segIn(y, ys), Prune.allSegsIn(rest, ys), h)))

def seg_app_left_pick(+x: Prune.Seg, +y: Prune.Seg, +rest: +List<Prune.Seg>, +c: +List<Prune.Seg>,
  cases: Either<{Prune.segEq(x, y) == True{} : Bool}, {Prune.segIn(x, rest) == True{} : Bool}>,
  later: {Prune.segIn(x, rest) == True{} : Bool} -> {Prune.segIn(x, List.append(&2, Prune.Seg, rest, c)) == True{} : Bool})
  -> {Prune.segIn(x, y <> List.append(&2, Prune.Seg, rest, c)) == True{} : Bool}:
  match cases:
    case Inl{e}:
      Lemma.or_true_left_intro(Prune.segEq(x, y), Prune.segIn(x, List.append(&2, Prune.Seg, rest, c)), e)
    case Inr{m}:
      Lemma.or_true_right_intro(Prune.segEq(x, y), Prune.segIn(x, List.append(&2, Prune.Seg, rest, c)), later(m))

law seg_in_app_left:
  for a: +List<Prune.Seg>
  for +c: +List<Prune.Seg>
  for +x: Prune.Seg
  for +m: {Prune.segIn(x, a) == True{} : Bool}
  {Prune.segIn(x, List.append(&2, Prune.Seg, a, c)) == True{} : Bool}

def seg_in_app_left(a, c, x, m):
  match a:
    case Nil{}:
      Empty.absurd({Prune.segIn(x, c) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{+y, +rest}:
      seg_app_left_pick(x, y, rest, c, Lemma.or_true_cases(Prune.segEq(x, y), Prune.segIn(x, rest), m), m2 => seg_in_app_left(rest, c, x, m2))

law seg_in_app_right:
  for a: +List<Prune.Seg>
  for +c: +List<Prune.Seg>
  for +x: Prune.Seg
  for +m: {Prune.segIn(x, c) == True{} : Bool}
  {Prune.segIn(x, List.append(&2, Prune.Seg, a, c)) == True{} : Bool}

def seg_in_app_right(a, c, x, m):
  match a:
    case Nil{}:
      m
    case Con{+y, +rest}:
      Lemma.or_true_right_intro(Prune.segEq(x, y), Prune.segIn(x, List.append(&2, Prune.Seg, rest, c)), seg_in_app_right(rest, c, x, m))

law seg_weaken:
  for xs: +List<Prune.Seg>
  for +y: Prune.Seg
  for +ys: +List<Prune.Seg>
  for +h: {Prune.allSegsIn(xs, ys) == True{} : Bool}
  {Prune.allSegsIn(xs, y <> ys) == True{} : Bool}

def seg_weaken(xs, y, ys, h):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Lemma.and_true_intro(Prune.segIn(x, y <> ys), Prune.allSegsIn(rest, y <> ys),
        Lemma.or_true_right_intro(Prune.segEq(x, y), Prune.segIn(x, ys), Lemma.and_true_left(Prune.segIn(x, ys), Prune.allSegsIn(rest, ys), h)),
        seg_weaken(rest, y, ys, Lemma.and_true_right_side(Prune.segIn(x, ys), Prune.allSegsIn(rest, ys), h)))

law seg_refl:
  for xs: +List<Prune.Seg>
  {Prune.allSegsIn(xs, xs) == True{} : Bool}

def seg_refl(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Lemma.and_true_intro(Prune.segIn(x, x <> rest), Prune.allSegsIn(rest, x <> rest), Lemma.or_true_left_intro(Prune.segEq(x, x), Prune.segIn(x, rest), seg_eq_refl(x)),
        seg_weaken(rest, x, rest, seg_refl(rest)))


law segs_trans:
  for xs: +List<Prune.Seg>
  for +ys: +List<Prune.Seg>
  for +zs: +List<Prune.Seg>
  for +h1: {Prune.allSegsIn(xs, ys) == True{} : Bool}
  for +h2: {Prune.allSegsIn(ys, zs) == True{} : Bool}
  {Prune.allSegsIn(xs, zs) == True{} : Bool}

def segs_trans(xs, ys, zs, h1, h2):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Lemma.and_true_intro(Prune.segIn(x, zs), Prune.allSegsIn(rest, zs), seg_sub(ys, x, zs, Lemma.and_true_left(Prune.segIn(x, ys), Prune.allSegsIn(rest, ys), h1), h2),
        segs_trans(rest, ys, zs, Lemma.and_true_right_side(Prune.segIn(x, ys), Prune.allSegsIn(rest, ys), h1), h2))

law segs_app_left:
  for xs: +List<Prune.Seg>
  for +a: +List<Prune.Seg>
  for +c: +List<Prune.Seg>
  for +h: {Prune.allSegsIn(xs, a) == True{} : Bool}
  {Prune.allSegsIn(xs, List.append(&2, Prune.Seg, a, c)) == True{} : Bool}

def segs_app_left(xs, a, c, h):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Lemma.and_true_intro(Prune.segIn(x, List.append(&2, Prune.Seg, a, c)), Prune.allSegsIn(rest, List.append(&2, Prune.Seg, a, c)),
        seg_in_app_left(a, c, x, Lemma.and_true_left(Prune.segIn(x, a), Prune.allSegsIn(rest, a), h)),
        segs_app_left(rest, a, c, Lemma.and_true_right_side(Prune.segIn(x, a), Prune.allSegsIn(rest, a), h)))

law segs_app_right:
  for xs: +List<Prune.Seg>
  for +a: +List<Prune.Seg>
  for +c: +List<Prune.Seg>
  for +h: {Prune.allSegsIn(xs, c) == True{} : Bool}
  {Prune.allSegsIn(xs, List.append(&2, Prune.Seg, a, c)) == True{} : Bool}

def segs_app_right(xs, a, c, h):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Lemma.and_true_intro(Prune.segIn(x, List.append(&2, Prune.Seg, a, c)), Prune.allSegsIn(rest, List.append(&2, Prune.Seg, a, c)),
        seg_in_app_right(a, c, x, Lemma.and_true_left(Prune.segIn(x, c), Prune.allSegsIn(rest, c), h)),
        segs_app_right(rest, a, c, Lemma.and_true_right_side(Prune.segIn(x, c), Prune.allSegsIn(rest, c), h)))

law segs_app:
  for xs: +List<Prune.Seg>
  for +ys: +List<Prune.Seg>
  for +set: +List<Prune.Seg>
  for +hx: {Prune.allSegsIn(xs, set) == True{} : Bool}
  for +hy: {Prune.allSegsIn(ys, set) == True{} : Bool}
  {Prune.allSegsIn(List.append(&2, Prune.Seg, xs, ys), set) == True{} : Bool}

def segs_app(xs, ys, set, hx, hy):
  match xs:
    case Nil{}:
      hy
    case Con{+x, +rest}:
      Lemma.and_true_intro(Prune.segIn(x, set), Prune.allSegsIn(List.append(&2, Prune.Seg, rest, ys), set), Lemma.and_true_left(Prune.segIn(x, set), Prune.allSegsIn(rest, set), hx),
        segs_app(rest, ys, set, Lemma.and_true_right_side(Prune.segIn(x, set), Prune.allSegsIn(rest, set), hx), hy))

def seg_in_head(+x: Prune.Seg, +rest: +List<Prune.Seg>) -> {Prune.segIn(x, x <> rest) == True{} : Bool}:
  Lemma.or_true_left_intro(Prune.segEq(x, x), Prune.segIn(x, rest), seg_eq_refl(x))

# ======== SEGMENTS COUNTED AS DESCRIPTORS ========

def toDesc(x: Prune.Seg) -> Gll.Desc:
  match x:
    case Prune.Seg{+q, +ks, +dot, +end}:
      Gll.Desc{q, dot, ks, end}

def descsOf(xs: +List<Prune.Seg>) -> +List<Gll.Desc>:
  match xs:
    case Nil{}:
      []
    case Con{+x, rest}:
      toDesc(x) <> descsOf(rest)

def segBound(x: Prune.Seg, +grammar: +List<Core.Production>, +input: +List<Nat>) -> Bool:
  Run.descBound(toDesc(x), grammar, input)

def segsBounded(xs: +List<Prune.Seg>, +grammar: +List<Core.Production>, +input: +List<Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, rest}:
      Bool.and(segBound(x, grammar, input), segsBounded(rest, grammar, input))

def nSeen(s: Prune.NeedState) -> +List<Prune.Seg>:
  match s:
    case Prune.NeedState{+seen, +todo}:
      seen

def nTodo(s: Prune.NeedState) -> +List<Prune.Seg>:
  match s:
    case Prune.NeedState{+seen, +todo}:
      todo

# The measure: segments within bounds not yet seen, plus the to-do list.
def nMeas(+grammar: +List<Core.Production>, +input: +List<Nat>, +s: Prune.NeedState) -> Nat:
  Nat.add(Run.countNot(Run.univ(grammar, input), descsOf(nSeen(s))), List.length(&2, Prune.Seg, nTodo(s)))

def and_swap(a: Bool, b: Bool, c: Bool, d: Bool) -> {Bool.and(a, Bool.and(b, Bool.and(c, d))) == Bool.and(a, Bool.and(c, Bool.and(b, d))) : Bool}:
  match b c:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

law seg_desc_eq:
  for x: Prune.Seg
  for y: Prune.Seg
  {Gll.descEq(toDesc(x), toDesc(y)) == Prune.segEq(x, y) : Bool}

def seg_desc_eq(x, y):
  match x y:
    case Prune.Seg{+q1, +s1, +d1, +e1} Prune.Seg{+q2, +s2, +d2, +e2}:
      and_swap(Nat.is_eq(q1, q2), Nat.is_eq(d1, d2), Nat.is_eq(s1, s2), Nat.is_eq(e1, e2))

law seg_in_desc:
  for +x: Prune.Seg
  for seen: +List<Prune.Seg>
  {Gll.descIn(toDesc(x), descsOf(seen)) == Prune.segIn(x, seen) : Bool}

def seg_in_desc(x, seen):
  match seen:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      %Equal.sym(Bool, Gll.descEq(toDesc(x), toDesc(y)), Prune.segEq(x, y), seg_desc_eq(x, y)) : {Bool.or(_, Gll.descIn(toDesc(x), descsOf(rest))) == Bool.or(Prune.segEq(x, y), Prune.segIn(x, rest)) : Bool}
      %Equal.sym(Bool, Gll.descIn(toDesc(x), descsOf(rest)), Prune.segIn(x, rest), seg_in_desc(x, rest)) : {Bool.or(Prune.segEq(x, y), _) == Bool.or(Prune.segEq(x, y), Prune.segIn(x, rest)) : Bool}
      {==}

# A new segment within bounds: one fewer unseen, one more to do.
def meas_add(+grammar: +List<Core.Production>, +input: +List<Nat>, +x: Prune.Seg, +seen: +List<Prune.Seg>, +todo: +List<Prune.Seg>,
  +out: {Prune.segIn(x, seen) == False{} : Bool}, +bx: {segBound(x, grammar, input) == True{} : Bool})
  -> {Nat.is_le(nMeas(grammar, input, Prune.NeedState{x <> seen, x <> todo}), nMeas(grammar, input, Prune.NeedState{seen, todo})) == True{} : Bool}:
  +U = Run.univ(grammar, input)
  +c2 = Run.countNot(U, descsOf(x <> seen))
  +T = List.length(&2, Prune.Seg, todo)
  %Equal.sym(Nat, Nat.add(c2, 1n+T), 1n+Nat.add(c2, T), Lemma.add_succ_right(c2, T)) : {Nat.is_le(_, Nat.add(Run.countNot(U, descsOf(seen)), T)) == True{} : Bool}
  C.le_add_l(1n+c2, Run.countNot(U, descsOf(seen)), T, C.count_drop(U, descsOf(seen), toDesc(x), C.bound_mem(toDesc(x), grammar, input, bx),
    Equal.trans(Bool, Gll.descIn(toDesc(x), descsOf(seen)), Prune.segIn(x, seen), False{}, seg_in_desc(x, seen), out)))

# ======== NEEDS LIE WITHIN BOUNDS ========

law drop_rhs:
  for n: Nat
  for grammar: +List<Core.Production>
  for +l: Nat
  for +r: +List<Core.Sym>
  for +rest: +List<Core.Production>
  for +e: {G.dropProds(n, grammar) == Core.Production{l, r} <> rest : +List<Core.Production>}
  {Core.rhsOf(grammar, n) == r : +List<Core.Sym>}

def drop_rhs(n, grammar, l, r, rest, e):
  match n grammar:
    case 0n +g:
      %Equal.sym(+List<Core.Production>, g, Core.Production{l, r} <> rest, e) : {Core.rhsOf(_, 0n) == r : +List<Core.Sym>}
      {==}
    case 1n+(+m) Nil{}:
      Empty.absurd({Core.rhsOf([], 1n+m) == r : +List<Core.Sym>},
        Lemma.true_is_not_false(Equal.cong(+List<Core.Production>, Bool, v => G.isNilProds(v), [], Core.Production{l, r} <> rest, e)))
    case 1n+(+m) Con{Core.Production{+l2, +r2}, +rest2}:
      drop_rhs(m, rest2, l, r, rest, e)

law drop_lt:
  for n: Nat
  for grammar: +List<Core.Production>
  for +l: Nat
  for +r: +List<Core.Sym>
  for +rest: +List<Core.Production>
  for +e: {G.dropProds(n, grammar) == Core.Production{l, r} <> rest : +List<Core.Production>}
  {Nat.is_le(1n+n, List.length(&2, Core.Production, grammar)) == True{} : Bool}

def drop_lt(n, grammar, l, r, rest, e):
  match n grammar:
    case 0n +g:
      %Equal.sym(+List<Core.Production>, g, Core.Production{l, r} <> rest, e) : {Nat.is_le(1n, List.length(&2, Core.Production, _)) == True{} : Bool}
      Lemma.zero_le(List.length(&2, Core.Production, rest))
    case 1n+(+m) Nil{}:
      Empty.absurd({Nat.is_le(2n+m, 0n) == True{} : Bool},
        Lemma.true_is_not_false(Equal.cong(+List<Core.Production>, Bool, v => G.isNilProds(v), [], Core.Production{l, r} <> rest, e)))
    case 1n+(+m) Con{Core.Production{+l2, +r2}, +rest2}:
      drop_lt(m, rest2, l, r, rest, e)

def rhs_len_le(+grammar: +List<Core.Production>, +base: Nat, +lhs: Nat, +rhs: +List<Core.Sym>, +rest: +List<Core.Production>,
  +hg: {G.dropProds(base, grammar) == Core.Production{lhs, rhs} <> rest : +List<Core.Production>})
  -> {Nat.is_le(List.length(&2, Core.Sym, rhs), List.length(&2, Core.Sym, Core.rhsOf(grammar, base))) == True{} : Bool}:
  %Equal.sym(+List<Core.Sym>, Core.rhsOf(grammar, base), rhs, drop_rhs(base, grammar, lhs, rhs, rest, hg)) : {Nat.is_le(List.length(&2, Core.Sym, rhs), List.length(&2, Core.Sym, _)) == True{} : Bool}
  Lemma.le_refl(List.length(&2, Core.Sym, rhs))

def prod_seg_bound(+grammar: +List<Core.Production>, +input: +List<Nat>, +base: Nat, +lhs: Nat, +rhs: +List<Core.Sym>, +rest: +List<Core.Production>, +k: Nat, +j: Nat,
  +hg: {G.dropProds(base, grammar) == Core.Production{lhs, rhs} <> rest : +List<Core.Production>},
  +hk: {Nat.is_le(k, List.length(&2, Nat, input)) == True{} : Bool}, +hj: {Nat.is_le(j, List.length(&2, Nat, input)) == True{} : Bool})
  -> {segBound(Prune.Seg{base, k, List.length(&2, Core.Sym, rhs), j}, grammar, input) == True{} : Bool}:
  +n = List.length(&2, Nat, input)
  +B = {Nat.is_le(List.length(&2, Core.Sym, rhs), List.length(&2, Core.Sym, Core.rhsOf(grammar, base))) : Bool}
  Lemma.and_true_intro(Nat.is_le(1n+base, List.length(&2, Core.Production, grammar)), Bool.and(B, Bool.and(Nat.is_le(k, n), Nat.is_le(j, n))), drop_lt(base, grammar, lhs, rhs, rest, hg),
    Lemma.and_true_intro(B, Bool.and(Nat.is_le(k, n), Nat.is_le(j, n)), rhs_len_le(grammar, base, lhs, rhs, rest, hg), Lemma.and_true_intro(Nat.is_le(k, n), Nat.is_le(j, n), hk, hj)))

def keep_bounded(b: Bool, +s: Prune.Seg, +ss: +List<Prune.Seg>, +grammar: +List<Core.Production>, +input: +List<Nat>,
  +hs: {segBound(s, grammar, input) == True{} : Bool}, +hr: {segsBounded(ss, grammar, input) == True{} : Bool})
  -> {segsBounded(Prune.keepSeg(b, s, ss), grammar, input) == True{} : Bool}:
  match b:
    case True{}:
      Lemma.and_true_intro(segBound(s, grammar, input), segsBounded(ss, grammar, input), hs, hr)
    case False{}:
      hr

law prod_bounded:
  for g: +List<Core.Production>
  for +x: Nat
  for +base: Nat
  for +k: Nat
  for +j: Nat
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +hg: {G.dropProds(base, grammar) == g : +List<Core.Production>}
  for +hk: {Nat.is_le(k, List.length(&2, Nat, input)) == True{} : Bool}
  for +hj: {Nat.is_le(j, List.length(&2, Nat, input)) == True{} : Bool}
  {segsBounded(Prune.prodSegs(g, x, base, k, j), grammar, input) == True{} : Bool}

def prod_bounded(g, x, base, k, j, grammar, input, hg, hk, hj):
  match g:
    case Nil{}:
      {==}
    case Con{Core.Production{+lhs, +rhs}, +rest}:
      keep_bounded(Nat.is_eq(lhs, x), Prune.Seg{base, k, List.length(&2, Core.Sym, rhs), j}, Prune.prodSegs(rest, x, 1n+base, k, j), grammar, input,
        prod_seg_bound(grammar, input, base, lhs, rhs, rest, k, j, hg, hk, hj),
        prod_bounded(rest, x, 1n+base, k, j, grammar, input, G.drop_step(base, grammar, lhs, rhs, rest, hg), hk, hj))

def item_bounded(item: Maybe<&2, Core.Sym>, +grammar: +List<Core.Production>, +input: +List<Nat>, +k: Nat, +j: Nat,
  +hk: {Nat.is_le(k, List.length(&2, Nat, input)) == True{} : Bool}, +hj: {Nat.is_le(j, List.length(&2, Nat, input)) == True{} : Bool})
  -> {segsBounded(Prune.itemNeeds(item, grammar, k, j), grammar, input) == True{} : Bool}:
  match item:
    case Some{Core.Nonterminal{+x, +need}}:
      prod_bounded(grammar, x, 0n, k, j, grammar, input, {==}, hk, hj)
    case Some{Core.Terminal{+t}}:
      {==}
    case None{}:
      {==}

def step_needs_bounded(+grammar: +List<Core.Production>, +input: +List<Nat>, e: Core.Bsr, +hb: {Run.stepBound(e, grammar, input) == True{} : Bool})
  -> {segsBounded(Prune.stepNeeds(grammar, e), grammar, input) == True{} : Bool}:
  match e:
    case Core.Bsr{+q, 0n, +i, +k, +j}:
      {==}
    case Core.Bsr{+q, 1n+(+d), +i, +k, +j}:
      +n = List.length(&2, Nat, input)
      +len = List.length(&2, Core.Sym, Core.rhsOf(grammar, q))
      +A = {Nat.is_le(1n+q, List.length(&2, Core.Production, grammar)) : Bool}
      +Dd = {Nat.is_le(1n+d, len) : Bool}
      +I = {Nat.is_le(i, n) : Bool}
      +Jn = {Nat.is_le(j, n) : Bool}
      +K = {Nat.is_le(k, n) : Bool}
      +DB = {Bool.and(A, Bool.and(Dd, Bool.and(I, Jn))) : Bool}
      +hdb = Lemma.and_true_left(DB, K, hb)
      +hK = Lemma.and_true_right_side(DB, K, hb)
      +hA = Lemma.and_true_left(A, Bool.and(Dd, Bool.and(I, Jn)), hdb)
      +r1 = Lemma.and_true_right_side(A, Bool.and(Dd, Bool.and(I, Jn)), hdb)
      +hD = Lemma.and_true_left(Dd, Bool.and(I, Jn), r1)
      +r2 = Lemma.and_true_right_side(Dd, Bool.and(I, Jn), r1)
      +hI = Lemma.and_true_left(I, Jn, r2)
      +hJ = Lemma.and_true_right_side(I, Jn, r2)
      +D0 = {Nat.is_le(d, len) : Bool}
      +head = Lemma.and_true_intro(A, Bool.and(D0, Bool.and(I, K)), hA, Lemma.and_true_intro(D0, Bool.and(I, K), Lemma.le_of_succ_le(d, len, hD), Lemma.and_true_intro(I, K, hI, hK)))
      Lemma.and_true_intro(segBound(Prune.Seg{q, i, d, k}, grammar, input), segsBounded(Prune.itemNeeds(Gll.nthSym(Core.rhsOf(grammar, q), d), grammar, k, j), grammar, input), head,
        item_bounded(Gll.nthSym(Core.rhsOf(grammar, q), d), grammar, input, k, j, hK, hJ))

def pick_bounded(b: Bool, +grammar: +List<Core.Production>, +input: +List<Nat>, +e: Core.Bsr, +hb: {Run.stepBound(e, grammar, input) == True{} : Bool})
  -> {segsBounded(Prune.stepPick(b, grammar, e), grammar, input) == True{} : Bool}:
  match b:
    case True{}:
      step_needs_bounded(grammar, input, e, hb)
    case False{}:
      {==}

law bounded_app:
  for xs: +List<Prune.Seg>
  for +ys: +List<Prune.Seg>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +hx: {segsBounded(xs, grammar, input) == True{} : Bool}
  for +hy: {segsBounded(ys, grammar, input) == True{} : Bool}
  {segsBounded(List.append(&2, Prune.Seg, xs, ys), grammar, input) == True{} : Bool}

def bounded_app(xs, ys, grammar, input, hx, hy):
  match xs:
    case Nil{}:
      hy
    case Con{+x, +rest}:
      Lemma.and_true_intro(segBound(x, grammar, input), segsBounded(List.append(&2, Prune.Seg, rest, ys), grammar, input), Lemma.and_true_left(segBound(x, grammar, input), segsBounded(rest, grammar, input), hx),
        bounded_app(rest, ys, grammar, input, Lemma.and_true_right_side(segBound(x, grammar, input), segsBounded(rest, grammar, input), hx), hy))

# What a segment needs lies within bounds, when the steps do.
law needs_bounded:
  for ys: +List<Core.Bsr>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +seg: Prune.Seg
  for +hy: {Run.stepsBounded(ys, grammar, input) == True{} : Bool}
  {segsBounded(Prune.segNeeds(ys, grammar, seg), grammar, input) == True{} : Bool}

def needs_bounded(ys, grammar, input, seg, hy):
  match ys:
    case Nil{}:
      {==}
    case Con{+e, +rest}:
      bounded_app(Prune.stepPick(Prune.segEq(Prune.segOf(e), seg), grammar, e), Prune.segNeeds(rest, grammar, seg), grammar, input,
        pick_bounded(Prune.segEq(Prune.segOf(e), seg), grammar, input, e, Lemma.and_true_left(Run.stepBound(e, grammar, input), Run.stepsBounded(rest, grammar, input), hy)),
        needs_bounded(rest, grammar, input, seg, Lemma.and_true_right_side(Run.stepBound(e, grammar, input), Run.stepsBounded(rest, grammar, input), hy)))

def roots_bounded(+grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>) -> {segsBounded(Prune.rootSegs(grammar, start, List.length(&2, Nat, input)), grammar, input) == True{} : Bool}:
  prod_bounded(grammar, start, 0n, 0n, List.length(&2, Nat, input), grammar, input, {==}, Lemma.zero_le(List.length(&2, Nat, input)), Lemma.le_refl(List.length(&2, Nat, input)))

# ======== THE INVARIANT ========

# ---- Every needed segment is reached from the root, in the loop's order ----

def anyNeed(+x: Prune.Seg, older: +List<Prune.Seg>, +ys: +List<Core.Bsr>, +grammar: +List<Core.Production>) -> Bool:
  match older:
    case Nil{}:
      False{}
    case Con{+y, rest}:
      Bool.or(Prune.segIn(x, Prune.segNeeds(ys, grammar, y)), anyNeed(x, rest, ys, grammar))

# x is a root segment, or a need of an older segment.
def justBy(+x: Prune.Seg, +older: +List<Prune.Seg>, +ys: +List<Core.Bsr>, +grammar: +List<Core.Production>, +roots: +List<Prune.Seg>) -> Bool:
  Bool.or(Prune.segIn(x, roots), anyNeed(x, older, ys, grammar))

def seenJust(seen: +List<Prune.Seg>, +ys: +List<Core.Bsr>, +grammar: +List<Core.Production>, +roots: +List<Prune.Seg>) -> Bool:
  match seen:
    case Nil{}:
      True{}
    case Con{+x, +older}:
      Bool.and(justBy(x, older, ys, grammar, roots), seenJust(older, ys, grammar, roots))

def remJust(rem: +List<Prune.Seg>, +seen: +List<Prune.Seg>, +ys: +List<Core.Bsr>, +grammar: +List<Core.Production>, +roots: +List<Prune.Seg>) -> Bool:
  match rem:
    case Nil{}:
      True{}
    case Con{+x, rest}:
      Bool.and(justBy(x, seen, ys, grammar, roots), remJust(rest, seen, ys, grammar, roots))

def just_pick(+x: Prune.Seg, +older: +List<Prune.Seg>, +y: Prune.Seg, +ys: +List<Core.Bsr>, +grammar: +List<Core.Production>, +roots: +List<Prune.Seg>,
  c: Either<{Prune.segIn(x, roots) == True{} : Bool}, {anyNeed(x, older, ys, grammar) == True{} : Bool}>) -> {justBy(x, y <> older, ys, grammar, roots) == True{} : Bool}:
  match c:
    case Inl{r}:
      Lemma.or_true_left_intro(Prune.segIn(x, roots), anyNeed(x, y <> older, ys, grammar), r)
    case Inr{a}:
      Lemma.or_true_right_intro(Prune.segIn(x, roots), anyNeed(x, y <> older, ys, grammar),
        Lemma.or_true_right_intro(Prune.segIn(x, Prune.segNeeds(ys, grammar, y)), anyNeed(x, older, ys, grammar), a))

def just_mono(+x: Prune.Seg, +older: +List<Prune.Seg>, +y: Prune.Seg, +ys: +List<Core.Bsr>, +grammar: +List<Core.Production>, +roots: +List<Prune.Seg>,
  +h: {justBy(x, older, ys, grammar, roots) == True{} : Bool}) -> {justBy(x, y <> older, ys, grammar, roots) == True{} : Bool}:
  just_pick(x, older, y, ys, grammar, roots, Lemma.or_true_cases(Prune.segIn(x, roots), anyNeed(x, older, ys, grammar), h))

law rem_mono:
  for rem: +List<Prune.Seg>
  for +seen: +List<Prune.Seg>
  for +y: Prune.Seg
  for +ys: +List<Core.Bsr>
  for +grammar: +List<Core.Production>
  for +roots: +List<Prune.Seg>
  for +h: {remJust(rem, seen, ys, grammar, roots) == True{} : Bool}
  {remJust(rem, y <> seen, ys, grammar, roots) == True{} : Bool}

def rem_mono(rem, seen, y, ys, grammar, roots, h):
  match rem:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +j = {justBy(x, seen, ys, grammar, roots) : Bool}
      Lemma.and_true_intro(justBy(x, y <> seen, ys, grammar, roots), remJust(rest, y <> seen, ys, grammar, roots),
        just_mono(x, seen, y, ys, grammar, roots, Lemma.and_true_left(j, remJust(rest, seen, ys, grammar, roots), h)),
        rem_mono(rest, seen, y, ys, grammar, roots, Lemma.and_true_right_side(j, remJust(rest, seen, ys, grammar, roots), h)))

def need_move(+x: Prune.Seg, +seg: Prune.Seg, +y: Prune.Seg, +ys: +List<Core.Bsr>, +grammar: +List<Core.Production>, +eq: {seg == y : Prune.Seg},
  +h: {Prune.segIn(x, Prune.segNeeds(ys, grammar, seg)) == True{} : Bool}) -> {Prune.segIn(x, Prune.segNeeds(ys, grammar, y)) == True{} : Bool}:
  %eq : {Prune.segIn(x, Prune.segNeeds(ys, grammar, _)) == True{} : Bool}
  h

def reach_pick(+x: Prune.Seg, +seg: Prune.Seg, +y: Prune.Seg, +rest: +List<Prune.Seg>, +ys: +List<Core.Bsr>, +grammar: +List<Core.Production>,
  +hx: {Prune.segIn(x, Prune.segNeeds(ys, grammar, seg)) == True{} : Bool},
  cases: Either<{Prune.segEq(seg, y) == True{} : Bool}, {Prune.segIn(seg, rest) == True{} : Bool}>,
  later: {Prune.segIn(seg, rest) == True{} : Bool} -> {anyNeed(x, rest, ys, grammar) == True{} : Bool}) -> {anyNeed(x, y <> rest, ys, grammar) == True{} : Bool}:
  match cases:
    case Inl{e}:
      +eq = seg_eq_sound(seg, y, e)
      Lemma.or_true_left_intro(Prune.segIn(x, Prune.segNeeds(ys, grammar, y)), anyNeed(x, rest, ys, grammar), need_move(x, seg, y, ys, grammar, eq, hx))
    case Inr{m}:
      Lemma.or_true_right_intro(Prune.segIn(x, Prune.segNeeds(ys, grammar, y)), anyNeed(x, rest, ys, grammar), later(m))

law any_need:
  for seen: +List<Prune.Seg>
  for +seg: Prune.Seg
  for +x: Prune.Seg
  for +ys: +List<Core.Bsr>
  for +grammar: +List<Core.Production>
  for +hs: {Prune.segIn(seg, seen) == True{} : Bool}
  for +hx: {Prune.segIn(x, Prune.segNeeds(ys, grammar, seg)) == True{} : Bool}
  {anyNeed(x, seen, ys, grammar) == True{} : Bool}

def any_need(seen, seg, x, ys, grammar, hs, hx):
  match seen:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(hs))
    case Con{+y, +rest}:
      reach_pick(x, seg, y, rest, ys, grammar, hx, Lemma.or_true_cases(Prune.segEq(seg, y), Prune.segIn(seg, rest), hs), m => any_need(rest, seg, x, ys, grammar, m, hx))

# The needs of a seen segment are reached.
law needs_just:
  for xs: +List<Prune.Seg>
  for +seg: Prune.Seg
  for +seen: +List<Prune.Seg>
  for +ys: +List<Core.Bsr>
  for +grammar: +List<Core.Production>
  for +roots: +List<Prune.Seg>
  for +sub: {Prune.allSegsIn(xs, Prune.segNeeds(ys, grammar, seg)) == True{} : Bool}
  for +hs: {Prune.segIn(seg, seen) == True{} : Bool}
  {remJust(xs, seen, ys, grammar, roots) == True{} : Bool}

def needs_just(xs, seg, seen, ys, grammar, roots, sub, hs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +N = Prune.segNeeds(ys, grammar, seg)
      Lemma.and_true_intro(justBy(x, seen, ys, grammar, roots), remJust(rest, seen, ys, grammar, roots),
        Lemma.or_true_right_intro(Prune.segIn(x, roots), anyNeed(x, seen, ys, grammar), any_need(seen, seg, x, ys, grammar, hs, Lemma.and_true_left(Prune.segIn(x, N), Prune.allSegsIn(rest, N), sub))),
        needs_just(rest, seg, seen, ys, grammar, roots, Lemma.and_true_right_side(Prune.segIn(x, N), Prune.allSegsIn(rest, N), sub), hs))

law roots_just:
  for xs: +List<Prune.Seg>
  for +roots: +List<Prune.Seg>
  for +ys: +List<Core.Bsr>
  for +grammar: +List<Core.Production>
  for +sub: {Prune.allSegsIn(xs, roots) == True{} : Bool}
  {remJust(xs, [], ys, grammar, roots) == True{} : Bool}

def roots_just(xs, roots, ys, grammar, sub):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Lemma.and_true_intro(justBy(x, [], ys, grammar, roots), remJust(rest, [], ys, grammar, roots),
        Lemma.or_true_left_intro(Prune.segIn(x, roots), False{}, Lemma.and_true_left(Prune.segIn(x, roots), Prune.allSegsIn(rest, roots), sub)),
        roots_just(rest, roots, ys, grammar, Lemma.and_true_right_side(Prune.segIn(x, roots), Prune.allSegsIn(rest, roots), sub)))

# Every segment of xs is still to do, or what it needs lies in tgt.
def queuedJ(xs: +List<Prune.Seg>, +todo: +List<Prune.Seg>, +tgt: +List<Prune.Seg>, +ys: +List<Core.Bsr>, +grammar: +List<Core.Production>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, rest}:
      Bool.and(Bool.or(Prune.segIn(x, todo), Prune.allSegsIn(Prune.segNeeds(ys, grammar, x), tgt)), queuedJ(rest, todo, tgt, ys, grammar))

def needJ(+rem: +List<Prune.Seg>, +seen: +List<Prune.Seg>, +todo: +List<Prune.Seg>, +ys: +List<Core.Bsr>, +grammar: +List<Core.Production>, +input: +List<Nat>, +start: Nat) -> Bool:
  Bool.and(queuedJ(seen, todo, List.append(&2, Prune.Seg, rem, seen), ys, grammar), Bool.and(Prune.allSegsIn(todo, seen), Bool.and(segsBounded(seen, grammar, input), Bool.and(Prune.allSegsIn(Prune.rootSegs(grammar, start, List.length(&2, Nat, input)), List.append(&2, Prune.Seg, rem, seen)), Bool.and(segsBounded(rem, grammar, input), Bool.and(seenJust(seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))), remJust(rem, seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input)))))))))

def JParts(+rem: +List<Prune.Seg>, +seen: +List<Prune.Seg>, +todo: +List<Prune.Seg>, +ys: +List<Core.Bsr>, +grammar: +List<Core.Production>, +input: +List<Nat>, +start: Nat) -> Type:
  {queuedJ(seen, todo, List.append(&2, Prune.Seg, rem, seen), ys, grammar) == True{} : Bool} &
  {Prune.allSegsIn(todo, seen) == True{} : Bool} &
  {segsBounded(seen, grammar, input) == True{} : Bool} &
  {Prune.allSegsIn(Prune.rootSegs(grammar, start, List.length(&2, Nat, input)), List.append(&2, Prune.Seg, rem, seen)) == True{} : Bool} &
  {segsBounded(rem, grammar, input) == True{} : Bool} &
  {seenJust(seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))) == True{} : Bool} &
  {remJust(rem, seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))) == True{} : Bool}

def j_split(+rem: +List<Prune.Seg>, +seen: +List<Prune.Seg>, +todo: +List<Prune.Seg>, +ys: +List<Core.Bsr>, +grammar: +List<Core.Production>, +input: +List<Nat>, +start: Nat,
  +h: {needJ(rem, seen, todo, ys, grammar, input, start) == True{} : Bool}) -> JParts(rem, seen, todo, ys, grammar, input, start):
  +r1 = Lemma.and_true_right_side(queuedJ(seen, todo, List.append(&2, Prune.Seg, rem, seen), ys, grammar), Bool.and(Prune.allSegsIn(todo, seen), Bool.and(segsBounded(seen, grammar, input), Bool.and(Prune.allSegsIn(Prune.rootSegs(grammar, start, List.length(&2, Nat, input)), List.append(&2, Prune.Seg, rem, seen)), Bool.and(segsBounded(rem, grammar, input), Bool.and(seenJust(seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))), remJust(rem, seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input)))))))), h)
  +r2 = Lemma.and_true_right_side(Prune.allSegsIn(todo, seen), Bool.and(segsBounded(seen, grammar, input), Bool.and(Prune.allSegsIn(Prune.rootSegs(grammar, start, List.length(&2, Nat, input)), List.append(&2, Prune.Seg, rem, seen)), Bool.and(segsBounded(rem, grammar, input), Bool.and(seenJust(seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))), remJust(rem, seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))))))), r1)
  +r3 = Lemma.and_true_right_side(segsBounded(seen, grammar, input), Bool.and(Prune.allSegsIn(Prune.rootSegs(grammar, start, List.length(&2, Nat, input)), List.append(&2, Prune.Seg, rem, seen)), Bool.and(segsBounded(rem, grammar, input), Bool.and(seenJust(seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))), remJust(rem, seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input)))))), r2)
  +r4 = Lemma.and_true_right_side(Prune.allSegsIn(Prune.rootSegs(grammar, start, List.length(&2, Nat, input)), List.append(&2, Prune.Seg, rem, seen)), Bool.and(segsBounded(rem, grammar, input), Bool.and(seenJust(seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))), remJust(rem, seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))))), r3)
  +r5 = Lemma.and_true_right_side(segsBounded(rem, grammar, input), Bool.and(seenJust(seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))), remJust(rem, seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input)))), r4)
  (Lemma.and_true_left(queuedJ(seen, todo, List.append(&2, Prune.Seg, rem, seen), ys, grammar), Bool.and(Prune.allSegsIn(todo, seen), Bool.and(segsBounded(seen, grammar, input), Bool.and(Prune.allSegsIn(Prune.rootSegs(grammar, start, List.length(&2, Nat, input)), List.append(&2, Prune.Seg, rem, seen)), Bool.and(segsBounded(rem, grammar, input), Bool.and(seenJust(seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))), remJust(rem, seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input)))))))), h), (Lemma.and_true_left(Prune.allSegsIn(todo, seen), Bool.and(segsBounded(seen, grammar, input), Bool.and(Prune.allSegsIn(Prune.rootSegs(grammar, start, List.length(&2, Nat, input)), List.append(&2, Prune.Seg, rem, seen)), Bool.and(segsBounded(rem, grammar, input), Bool.and(seenJust(seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))), remJust(rem, seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))))))), r1), (Lemma.and_true_left(segsBounded(seen, grammar, input), Bool.and(Prune.allSegsIn(Prune.rootSegs(grammar, start, List.length(&2, Nat, input)), List.append(&2, Prune.Seg, rem, seen)), Bool.and(segsBounded(rem, grammar, input), Bool.and(seenJust(seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))), remJust(rem, seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input)))))), r2), (Lemma.and_true_left(Prune.allSegsIn(Prune.rootSegs(grammar, start, List.length(&2, Nat, input)), List.append(&2, Prune.Seg, rem, seen)), Bool.and(segsBounded(rem, grammar, input), Bool.and(seenJust(seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))), remJust(rem, seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))))), r3), (Lemma.and_true_left(segsBounded(rem, grammar, input), Bool.and(seenJust(seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))), remJust(rem, seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input)))), r4), (Lemma.and_true_left(seenJust(seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))), remJust(rem, seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))), r5), Lemma.and_true_right_side(seenJust(seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))), remJust(rem, seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))), r5)))))))

def j_join(+rem: +List<Prune.Seg>, +seen: +List<Prune.Seg>, +todo: +List<Prune.Seg>, +ys: +List<Core.Bsr>, +grammar: +List<Core.Production>, +input: +List<Nat>, +start: Nat,
  +j1: {queuedJ(seen, todo, List.append(&2, Prune.Seg, rem, seen), ys, grammar) == True{} : Bool},
  +j2: {Prune.allSegsIn(todo, seen) == True{} : Bool},
  +j3: {segsBounded(seen, grammar, input) == True{} : Bool},
  +j4: {Prune.allSegsIn(Prune.rootSegs(grammar, start, List.length(&2, Nat, input)), List.append(&2, Prune.Seg, rem, seen)) == True{} : Bool},
  +j5: {segsBounded(rem, grammar, input) == True{} : Bool},
  +j6: {seenJust(seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))) == True{} : Bool},
  +j7: {remJust(rem, seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))) == True{} : Bool}) -> {needJ(rem, seen, todo, ys, grammar, input, start) == True{} : Bool}:
  Lemma.and_true_intro(queuedJ(seen, todo, List.append(&2, Prune.Seg, rem, seen), ys, grammar), Bool.and(Prune.allSegsIn(todo, seen), Bool.and(segsBounded(seen, grammar, input), Bool.and(Prune.allSegsIn(Prune.rootSegs(grammar, start, List.length(&2, Nat, input)), List.append(&2, Prune.Seg, rem, seen)), Bool.and(segsBounded(rem, grammar, input), Bool.and(seenJust(seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))), remJust(rem, seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input)))))))), j1, Lemma.and_true_intro(Prune.allSegsIn(todo, seen), Bool.and(segsBounded(seen, grammar, input), Bool.and(Prune.allSegsIn(Prune.rootSegs(grammar, start, List.length(&2, Nat, input)), List.append(&2, Prune.Seg, rem, seen)), Bool.and(segsBounded(rem, grammar, input), Bool.and(seenJust(seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))), remJust(rem, seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))))))), j2, Lemma.and_true_intro(segsBounded(seen, grammar, input), Bool.and(Prune.allSegsIn(Prune.rootSegs(grammar, start, List.length(&2, Nat, input)), List.append(&2, Prune.Seg, rem, seen)), Bool.and(segsBounded(rem, grammar, input), Bool.and(seenJust(seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))), remJust(rem, seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input)))))), j3, Lemma.and_true_intro(Prune.allSegsIn(Prune.rootSegs(grammar, start, List.length(&2, Nat, input)), List.append(&2, Prune.Seg, rem, seen)), Bool.and(segsBounded(rem, grammar, input), Bool.and(seenJust(seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))), remJust(rem, seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))))), j4, Lemma.and_true_intro(segsBounded(rem, grammar, input), Bool.and(seenJust(seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))), remJust(rem, seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input)))), j5, Lemma.and_true_intro(seenJust(seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))), remJust(rem, seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))), j6, j7))))))

# ======== ADDING THE NEEDS OF ONE SEGMENT ========

law queued_shift:
  for xs: +List<Prune.Seg>
  for +todo: +List<Prune.Seg>
  for +todo2: +List<Prune.Seg>
  for +tgt: +List<Prune.Seg>
  for +tgt2: +List<Prune.Seg>
  for +ys: +List<Core.Bsr>
  for +grammar: +List<Core.Production>
  for +st: {Prune.allSegsIn(todo, todo2) == True{} : Bool}
  for +sg: {Prune.allSegsIn(tgt, tgt2) == True{} : Bool}
  for +h: {queuedJ(xs, todo, tgt, ys, grammar) == True{} : Bool}
  {queuedJ(xs, todo2, tgt2, ys, grammar) == True{} : Bool}

def shift_one(+x: Prune.Seg, +todo: +List<Prune.Seg>, +todo2: +List<Prune.Seg>, +tgt: +List<Prune.Seg>, +tgt2: +List<Prune.Seg>, +ys: +List<Core.Bsr>, +grammar: +List<Core.Production>,
  +st: {Prune.allSegsIn(todo, todo2) == True{} : Bool}, +sg: {Prune.allSegsIn(tgt, tgt2) == True{} : Bool},
  cases: Either<{Prune.segIn(x, todo) == True{} : Bool}, {Prune.allSegsIn(Prune.segNeeds(ys, grammar, x), tgt) == True{} : Bool}>)
  -> {Bool.or(Prune.segIn(x, todo2), Prune.allSegsIn(Prune.segNeeds(ys, grammar, x), tgt2)) == True{} : Bool}:
  match cases:
    case Inl{m}:
      Lemma.or_true_left_intro(Prune.segIn(x, todo2), Prune.allSegsIn(Prune.segNeeds(ys, grammar, x), tgt2), seg_sub(todo, x, todo2, m, st))
    case Inr{d}:
      Lemma.or_true_right_intro(Prune.segIn(x, todo2), Prune.allSegsIn(Prune.segNeeds(ys, grammar, x), tgt2), segs_trans(Prune.segNeeds(ys, grammar, x), tgt, tgt2, d, sg))

def queued_shift(xs, todo, todo2, tgt, tgt2, ys, grammar, st, sg, h):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +hx = {Bool.or(Prune.segIn(x, todo), Prune.allSegsIn(Prune.segNeeds(ys, grammar, x), tgt)) : Bool}
      Lemma.and_true_intro(Bool.or(Prune.segIn(x, todo2), Prune.allSegsIn(Prune.segNeeds(ys, grammar, x), tgt2)), queuedJ(rest, todo2, tgt2, ys, grammar),
        shift_one(x, todo, todo2, tgt, tgt2, ys, grammar, st, sg, Lemma.or_true_cases(Prune.segIn(x, todo), Prune.allSegsIn(Prune.segNeeds(ys, grammar, x), tgt), Lemma.and_true_left(hx, queuedJ(rest, todo, tgt, ys, grammar), h))),
        queued_shift(rest, todo, todo2, tgt, tgt2, ys, grammar, st, sg, Lemma.and_true_right_side(hx, queuedJ(rest, todo, tgt, ys, grammar), h)))

# Taking r off the needs still to add keeps everything in reach, once r is seen.
def rem_sub(+r: Prune.Seg, +rest: +List<Prune.Seg>, +seen: +List<Prune.Seg>, +seen1: +List<Prune.Seg>,
  +hr: {Prune.segIn(r, seen1) == True{} : Bool}, +hs: {Prune.allSegsIn(seen, seen1) == True{} : Bool})
  -> {Prune.allSegsIn(List.append(&2, Prune.Seg, r <> rest, seen), List.append(&2, Prune.Seg, rest, seen1)) == True{} : Bool}:
  Lemma.and_true_intro(Prune.segIn(r, List.append(&2, Prune.Seg, rest, seen1)), Prune.allSegsIn(List.append(&2, Prune.Seg, rest, seen), List.append(&2, Prune.Seg, rest, seen1)), seg_in_app_right(rest, seen1, r, hr),
    segs_app(rest, seen, List.append(&2, Prune.Seg, rest, seen1), segs_app_left(rest, rest, seen1, seg_refl(rest)), segs_app_right(seen, rest, seen1, hs)))

def fold_case(known: Bool, +r: Prune.Seg, +rest: +List<Prune.Seg>, +seen: +List<Prune.Seg>, +todo: +List<Prune.Seg>, +ys: +List<Core.Bsr>, +grammar: +List<Core.Production>, +input: +List<Nat>, +start: Nat,
  +ek: {Prune.segIn(r, seen) == known : Bool},
  +h1: {queuedJ(seen, todo, List.append(&2, Prune.Seg, r <> rest, seen), ys, grammar) == True{} : Bool},
  +h2: {Prune.allSegsIn(todo, seen) == True{} : Bool},
  +h3: {segsBounded(seen, grammar, input) == True{} : Bool},
  +h4: {Prune.allSegsIn(Prune.rootSegs(grammar, start, List.length(&2, Nat, input)), List.append(&2, Prune.Seg, r <> rest, seen)) == True{} : Bool},
  +hb: {segsBounded(r <> rest, grammar, input) == True{} : Bool},
  +h6: {seenJust(seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))) == True{} : Bool},
  +h7: {remJust(r <> rest, seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))) == True{} : Bool})
  -> {needJ(rest, Prune.addIf(known, r, seen), Prune.addIf(known, r, todo), ys, grammar, input, start) == True{} : Bool} &
     {Nat.is_le(nMeas(grammar, input, Prune.NeedState{Prune.addIf(known, r, seen), Prune.addIf(known, r, todo)}), nMeas(grammar, input, Prune.NeedState{seen, todo})) == True{} : Bool}:
  match known:
    case True{}:
      +hbr = Lemma.and_true_left(segBound(r, grammar, input), segsBounded(rest, grammar, input), hb)
      +h5 = Lemma.and_true_right_side(segBound(r, grammar, input), segsBounded(rest, grammar, input), hb)
      +sub = rem_sub(r, rest, seen, seen, ek, seg_refl(seen))
      (j_join(rest, seen, todo, ys, grammar, input, start,
         queued_shift(seen, todo, todo, List.append(&2, Prune.Seg, r <> rest, seen), List.append(&2, Prune.Seg, rest, seen), ys, grammar, seg_refl(todo), sub, h1), h2, h3,
         segs_trans(Prune.rootSegs(grammar, start, List.length(&2, Nat, input)), List.append(&2, Prune.Seg, r <> rest, seen), List.append(&2, Prune.Seg, rest, seen), h4, sub), h5, h6, Lemma.and_true_right_side(justBy(r, seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))), remJust(rest, seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))), h7)),
       Lemma.le_refl(nMeas(grammar, input, Prune.NeedState{seen, todo})))
    case False{}:
      +hbr = Lemma.and_true_left(segBound(r, grammar, input), segsBounded(rest, grammar, input), hb)
      +h5 = Lemma.and_true_right_side(segBound(r, grammar, input), segsBounded(rest, grammar, input), hb)
      +seen1 = {r <> seen : +List<Prune.Seg>}
      +sub = rem_sub(r, rest, seen, seen1, seg_in_head(r, seen), seg_weaken(seen, r, seen, seg_refl(seen)))
      +q1 = Lemma.and_true_intro(Bool.or(Prune.segIn(r, r <> todo), Prune.allSegsIn(Prune.segNeeds(ys, grammar, r), List.append(&2, Prune.Seg, rest, seen1))), queuedJ(seen, r <> todo, List.append(&2, Prune.Seg, rest, seen1), ys, grammar),
        Lemma.or_true_left_intro(Prune.segIn(r, r <> todo), Prune.allSegsIn(Prune.segNeeds(ys, grammar, r), List.append(&2, Prune.Seg, rest, seen1)), seg_in_head(r, todo)),
        queued_shift(seen, todo, r <> todo, List.append(&2, Prune.Seg, r <> rest, seen), List.append(&2, Prune.Seg, rest, seen1), ys, grammar, seg_weaken(todo, r, todo, seg_refl(todo)), sub, h1))
      (j_join(rest, seen1, r <> todo, ys, grammar, input, start, q1,
         Lemma.and_true_intro(Prune.segIn(r, seen1), Prune.allSegsIn(todo, seen1), seg_in_head(r, seen), seg_weaken(todo, r, seen, h2)),
         Lemma.and_true_intro(segBound(r, grammar, input), segsBounded(seen, grammar, input), hbr, h3),
         segs_trans(Prune.rootSegs(grammar, start, List.length(&2, Nat, input)), List.append(&2, Prune.Seg, r <> rest, seen), List.append(&2, Prune.Seg, rest, seen1), h4, sub), h5,
         Lemma.and_true_intro(justBy(r, seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))), seenJust(seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))), Lemma.and_true_left(justBy(r, seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))), remJust(rest, seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))), h7), h6),
         rem_mono(rest, seen, r, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input)), Lemma.and_true_right_side(justBy(r, seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))), remJust(rest, seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))), h7))),
       meas_add(grammar, input, r, seen, todo, ek, hbr))

def fold_pick(known: Bool, +r: Prune.Seg, +rest: +List<Prune.Seg>, +seen: +List<Prune.Seg>, +todo: +List<Prune.Seg>, +ys: +List<Core.Bsr>, +grammar: +List<Core.Production>, +input: +List<Nat>, +start: Nat,
  +ek: {Prune.segIn(r, seen) == known : Bool},
  p: JParts(r <> rest, seen, todo, ys, grammar, input, start))
  -> {needJ(rest, Prune.addIf(known, r, seen), Prune.addIf(known, r, todo), ys, grammar, input, start) == True{} : Bool} &
     {Nat.is_le(nMeas(grammar, input, Prune.NeedState{Prune.addIf(known, r, seen), Prune.addIf(known, r, todo)}), nMeas(grammar, input, Prune.NeedState{seen, todo})) == True{} : Bool}:
  match p:
    case (+h1, (+h2, (+h3, (+h4, (+h5, (+h6, h7)))))):
      fold_case(known, r, rest, seen, todo, ys, grammar, input, start, ek, h1, h2, h3, h4, h5, h6, h7)

def fold_join(+t: Prune.NeedState, +s1: Prune.NeedState, +s0: Prune.NeedState, +ys: +List<Core.Bsr>, +grammar: +List<Core.Production>, +input: +List<Nat>, +start: Nat,
  q: {needJ([], nSeen(t), nTodo(t), ys, grammar, input, start) == True{} : Bool} & {Nat.is_le(nMeas(grammar, input, t), nMeas(grammar, input, s1)) == True{} : Bool},
  +m1: {Nat.is_le(nMeas(grammar, input, s1), nMeas(grammar, input, s0)) == True{} : Bool})
  -> {needJ([], nSeen(t), nTodo(t), ys, grammar, input, start) == True{} : Bool} & {Nat.is_le(nMeas(grammar, input, t), nMeas(grammar, input, s0)) == True{} : Bool}:
  match q:
    case (+hj, m2):
      (hj, Lemma.le_trans(nMeas(grammar, input, t), nMeas(grammar, input, s1), nMeas(grammar, input, s0), m2, m1))

# Adding a list of needs ends with none left to add, and never raises the measure.
law fold_inv:
  for rem: +List<Prune.Seg>
  for +seen: +List<Prune.Seg>
  for +todo: +List<Prune.Seg>
  for +ys: +List<Core.Bsr>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +start: Nat
  for +h: {needJ(rem, seen, todo, ys, grammar, input, start) == True{} : Bool}
  {needJ([], nSeen(Prune.addSegs(rem, seen, todo)), nTodo(Prune.addSegs(rem, seen, todo)), ys, grammar, input, start) == True{} : Bool} &
  {Nat.is_le(nMeas(grammar, input, Prune.addSegs(rem, seen, todo)), nMeas(grammar, input, Prune.NeedState{seen, todo})) == True{} : Bool}

def fold_next(+r: Prune.Seg, +rest: +List<Prune.Seg>, +seen: +List<Prune.Seg>, +todo: +List<Prune.Seg>, +ys: +List<Core.Bsr>, +grammar: +List<Core.Production>, +input: +List<Nat>, +start: Nat,
  p: {needJ(rest, Prune.addIf(Prune.segIn(r, seen), r, seen), Prune.addIf(Prune.segIn(r, seen), r, todo), ys, grammar, input, start) == True{} : Bool} &
     {Nat.is_le(nMeas(grammar, input, Prune.NeedState{Prune.addIf(Prune.segIn(r, seen), r, seen), Prune.addIf(Prune.segIn(r, seen), r, todo)}), nMeas(grammar, input, Prune.NeedState{seen, todo})) == True{} : Bool},
  later: {needJ(rest, Prune.addIf(Prune.segIn(r, seen), r, seen), Prune.addIf(Prune.segIn(r, seen), r, todo), ys, grammar, input, start) == True{} : Bool} ->
    {needJ([], nSeen(Prune.addSegs(rest, Prune.addIf(Prune.segIn(r, seen), r, seen), Prune.addIf(Prune.segIn(r, seen), r, todo))), nTodo(Prune.addSegs(rest, Prune.addIf(Prune.segIn(r, seen), r, seen), Prune.addIf(Prune.segIn(r, seen), r, todo))), ys, grammar, input, start) == True{} : Bool} &
    {Nat.is_le(nMeas(grammar, input, Prune.addSegs(rest, Prune.addIf(Prune.segIn(r, seen), r, seen), Prune.addIf(Prune.segIn(r, seen), r, todo))), nMeas(grammar, input, Prune.NeedState{Prune.addIf(Prune.segIn(r, seen), r, seen), Prune.addIf(Prune.segIn(r, seen), r, todo)})) == True{} : Bool})
  -> {needJ([], nSeen(Prune.addSegs(r <> rest, seen, todo)), nTodo(Prune.addSegs(r <> rest, seen, todo)), ys, grammar, input, start) == True{} : Bool} &
     {Nat.is_le(nMeas(grammar, input, Prune.addSegs(r <> rest, seen, todo)), nMeas(grammar, input, Prune.NeedState{seen, todo})) == True{} : Bool}:
  match p:
    case (+hj, m1):
      +s1 = Prune.addIf(Prune.segIn(r, seen), r, seen)
      +t1 = Prune.addIf(Prune.segIn(r, seen), r, todo)
      fold_join(Prune.addSegs(rest, s1, t1), Prune.NeedState{s1, t1}, Prune.NeedState{seen, todo}, ys, grammar, input, start,
        later(hj), m1)

def fold_inv(rem, seen, todo, ys, grammar, input, start, h):
  match rem:
    case Nil{}:
      (h, Lemma.le_refl(nMeas(grammar, input, Prune.NeedState{seen, todo})))
    case Con{+r, +rest}:
      fold_next(r, rest, seen, todo, ys, grammar, input, start,
        fold_pick(Prune.segIn(r, seen), r, rest, seen, todo, ys, grammar, input, start, {==}, j_split(r <> rest, seen, todo, ys, grammar, input, start, h)),
        hj => fold_inv(rest, Prune.addIf(Prune.segIn(r, seen), r, seen), Prune.addIf(Prune.segIn(r, seen), r, todo), ys, grammar, input, start, hj))

# ======== ONE ITERATION ========

def requeue_in(+x: Prune.Seg, +seg: Prune.Seg, +rest: +List<Prune.Seg>, +seen: +List<Prune.Seg>, +ys: +List<Core.Bsr>, +grammar: +List<Core.Production>,
  cases: Either<{Prune.segEq(x, seg) == True{} : Bool}, {Prune.segIn(x, rest) == True{} : Bool}>)
  -> {Bool.or(Prune.segIn(x, rest), Prune.allSegsIn(Prune.segNeeds(ys, grammar, x), List.append(&2, Prune.Seg, Prune.segNeeds(ys, grammar, seg), seen))) == True{} : Bool}:
  match cases:
    case Inl{e}:
      %Equal.sym(Prune.Seg, x, seg, seg_eq_sound(x, seg, e)) : {Bool.or(Prune.segIn(_, rest), Prune.allSegsIn(Prune.segNeeds(ys, grammar, _), List.append(&2, Prune.Seg, Prune.segNeeds(ys, grammar, seg), seen))) == True{} : Bool}
      Lemma.or_true_right_intro(Prune.segIn(seg, rest), Prune.allSegsIn(Prune.segNeeds(ys, grammar, seg), List.append(&2, Prune.Seg, Prune.segNeeds(ys, grammar, seg), seen)),
        segs_app_left(Prune.segNeeds(ys, grammar, seg), Prune.segNeeds(ys, grammar, seg), seen, seg_refl(Prune.segNeeds(ys, grammar, seg))))
    case Inr{m}:
      Lemma.or_true_left_intro(Prune.segIn(x, rest), Prune.allSegsIn(Prune.segNeeds(ys, grammar, x), List.append(&2, Prune.Seg, Prune.segNeeds(ys, grammar, seg), seen)), m)

def requeue_one(+x: Prune.Seg, +seg: Prune.Seg, +rest: +List<Prune.Seg>, +seen: +List<Prune.Seg>, +ys: +List<Core.Bsr>, +grammar: +List<Core.Production>,
  cases: Either<{Prune.segIn(x, seg <> rest) == True{} : Bool}, {Prune.allSegsIn(Prune.segNeeds(ys, grammar, x), seen) == True{} : Bool}>)
  -> {Bool.or(Prune.segIn(x, rest), Prune.allSegsIn(Prune.segNeeds(ys, grammar, x), List.append(&2, Prune.Seg, Prune.segNeeds(ys, grammar, seg), seen))) == True{} : Bool}:
  match cases:
    case Inl{m}:
      requeue_in(x, seg, rest, seen, ys, grammar, Lemma.or_true_cases(Prune.segEq(x, seg), Prune.segIn(x, rest), m))
    case Inr{d}:
      Lemma.or_true_right_intro(Prune.segIn(x, rest), Prune.allSegsIn(Prune.segNeeds(ys, grammar, x), List.append(&2, Prune.Seg, Prune.segNeeds(ys, grammar, seg), seen)),
        segs_app_right(Prune.segNeeds(ys, grammar, x), Prune.segNeeds(ys, grammar, seg), seen, d))

# Taking seg off the to-do list: its needs are now the ones still to add.
law requeue:
  for xs: +List<Prune.Seg>
  for +seg: Prune.Seg
  for +rest: +List<Prune.Seg>
  for +seen: +List<Prune.Seg>
  for +ys: +List<Core.Bsr>
  for +grammar: +List<Core.Production>
  for +h: {queuedJ(xs, seg <> rest, seen, ys, grammar) == True{} : Bool}
  {queuedJ(xs, rest, List.append(&2, Prune.Seg, Prune.segNeeds(ys, grammar, seg), seen), ys, grammar) == True{} : Bool}

def requeue(xs, seg, rest, seen, ys, grammar, h):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest2}:
      +hx = {Bool.or(Prune.segIn(x, seg <> rest), Prune.allSegsIn(Prune.segNeeds(ys, grammar, x), seen)) : Bool}
      +N = Prune.segNeeds(ys, grammar, seg)
      Lemma.and_true_intro(Bool.or(Prune.segIn(x, rest), Prune.allSegsIn(Prune.segNeeds(ys, grammar, x), List.append(&2, Prune.Seg, N, seen))), queuedJ(rest2, rest, List.append(&2, Prune.Seg, N, seen), ys, grammar),
        requeue_one(x, seg, rest, seen, ys, grammar, Lemma.or_true_cases(Prune.segIn(x, seg <> rest), Prune.allSegsIn(Prune.segNeeds(ys, grammar, x), seen), Lemma.and_true_left(hx, queuedJ(rest2, seg <> rest, seen, ys, grammar), h))),
        requeue(rest2, seg, rest, seen, ys, grammar, Lemma.and_true_right_side(hx, queuedJ(rest2, seg <> rest, seen, ys, grammar), h)))

# ======== THE LOOP ENDS CLOSED ========

def need_here(b: Bool, +e: Core.Bsr, +grammar: +List<Core.Production>, +more: +List<Prune.Seg>, +eb: {b == True{} : Bool})
  -> {Prune.allSegsIn(Prune.stepNeeds(grammar, e), List.append(&2, Prune.Seg, Prune.stepPick(b, grammar, e), more)) == True{} : Bool}:
  match b:
    case True{}:
      segs_app_left(Prune.stepNeeds(grammar, e), Prune.stepNeeds(grammar, e), more, seg_refl(Prune.stepNeeds(grammar, e)))
    case False{}:
      Empty.absurd({Prune.allSegsIn(Prune.stepNeeds(grammar, e), more) == True{} : Bool}, Lemma.false_is_not_true(eb))

def need_head(+e: Core.Bsr, +y: Core.Bsr, +grammar: +List<Core.Production>, +more: +List<Prune.Seg>, +eq: {e == y : Core.Bsr})
  -> {Prune.allSegsIn(Prune.stepNeeds(grammar, e), List.append(&2, Prune.Seg, Prune.stepPick(Prune.segEq(Prune.segOf(y), Prune.segOf(e)), grammar, y), more)) == True{} : Bool}:
  %eq : {Prune.allSegsIn(Prune.stepNeeds(grammar, e), List.append(&2, Prune.Seg, Prune.stepPick(Prune.segEq(Prune.segOf(_), Prune.segOf(e)), grammar, _), more)) == True{} : Bool}
  need_here(Prune.segEq(Prune.segOf(e), Prune.segOf(e)), e, grammar, more, seg_eq_refl(Prune.segOf(e)))

def need_pick(+e: Core.Bsr, +y: Core.Bsr, +rest: +List<Core.Bsr>, +grammar: +List<Core.Production>,
  cases: Either<{Core.bsrEq(e, y) == True{} : Bool}, {Core.member(e, rest) == True{} : Bool}>,
  later: {Core.member(e, rest) == True{} : Bool} -> {Prune.allSegsIn(Prune.stepNeeds(grammar, e), Prune.segNeeds(rest, grammar, Prune.segOf(e))) == True{} : Bool})
  -> {Prune.allSegsIn(Prune.stepNeeds(grammar, e), Prune.segNeeds(y <> rest, grammar, Prune.segOf(e))) == True{} : Bool}:
  match cases:
    case Inl{q}:
      need_head(e, y, grammar, Prune.segNeeds(rest, grammar, Prune.segOf(e)), G.bsr_eq_sound(e, y, q))
    case Inr{m}:
      segs_app_right(Prune.stepNeeds(grammar, e), Prune.stepPick(Prune.segEq(Prune.segOf(y), Prune.segOf(e)), grammar, y), Prune.segNeeds(rest, grammar, Prune.segOf(e)), later(m))

# A step's needs are among the needs of its segment.
law need_in:
  for ys: +List<Core.Bsr>
  for +grammar: +List<Core.Production>
  for +e: Core.Bsr
  for +m: {Core.member(e, ys) == True{} : Bool}
  {Prune.allSegsIn(Prune.stepNeeds(grammar, e), Prune.segNeeds(ys, grammar, Prune.segOf(e))) == True{} : Bool}

def need_in(ys, grammar, e, m):
  match ys:
    case Nil{}:
      Empty.absurd({Prune.allSegsIn(Prune.stepNeeds(grammar, e), []) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{+y, +rest}:
      need_pick(e, y, rest, grammar, Lemma.or_true_cases(Core.bsrEq(e, y), Core.member(e, rest), m), m2 => need_in(rest, grammar, e, m2))

def queued_pick(+x: Prune.Seg, +y: Prune.Seg, +rest: +List<Prune.Seg>, +tgt: +List<Prune.Seg>, +ys: +List<Core.Bsr>, +grammar: +List<Core.Production>,
  +hy: {Prune.allSegsIn(Prune.segNeeds(ys, grammar, y), tgt) == True{} : Bool},
  cases: Either<{Prune.segEq(x, y) == True{} : Bool}, {Prune.segIn(x, rest) == True{} : Bool}>,
  later: {Prune.segIn(x, rest) == True{} : Bool} -> {Prune.allSegsIn(Prune.segNeeds(ys, grammar, x), tgt) == True{} : Bool})
  -> {Prune.allSegsIn(Prune.segNeeds(ys, grammar, x), tgt) == True{} : Bool}:
  match cases:
    case Inl{e}:
      %Equal.sym(Prune.Seg, x, y, seg_eq_sound(x, y, e)) : {Prune.allSegsIn(Prune.segNeeds(ys, grammar, _), tgt) == True{} : Bool}
      hy
    case Inr{m}:
      later(m)

# With nothing left to do, a seen segment has its needs seen.
law queued_at:
  for xs: +List<Prune.Seg>
  for +x: Prune.Seg
  for +tgt: +List<Prune.Seg>
  for +ys: +List<Core.Bsr>
  for +grammar: +List<Core.Production>
  for +m: {Prune.segIn(x, xs) == True{} : Bool}
  for +h: {queuedJ(xs, [], tgt, ys, grammar) == True{} : Bool}
  {Prune.allSegsIn(Prune.segNeeds(ys, grammar, x), tgt) == True{} : Bool}

def queued_at(xs, x, tgt, ys, grammar, m, h):
  match xs:
    case Nil{}:
      Empty.absurd({Prune.allSegsIn(Prune.segNeeds(ys, grammar, x), tgt) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{+y, +rest}:
      +hy = {Prune.allSegsIn(Prune.segNeeds(ys, grammar, y), tgt) : Bool}
      queued_pick(x, y, rest, tgt, ys, grammar, Lemma.and_true_left(hy, queuedJ(rest, [], tgt, ys, grammar), h), Lemma.or_true_cases(Prune.segEq(x, y), Prune.segIn(x, rest), m),
        m2 => queued_at(rest, x, tgt, ys, grammar, m2, Lemma.and_true_right_side(hy, queuedJ(rest, [], tgt, ys, grammar), h)))

def ok_pick(b: Bool, +e: Core.Bsr, +ys: +List<Core.Bsr>, +grammar: +List<Core.Production>, +seen: +List<Prune.Seg>,
  +eb: {Prune.segIn(Prune.segOf(e), seen) == b : Bool},
  +m: {Core.member(e, ys) == True{} : Bool},
  +h1: {queuedJ(seen, [], seen, ys, grammar) == True{} : Bool})
  -> {Bool.or(Bool.not(b), Prune.allSegsIn(Prune.stepNeeds(grammar, e), seen)) == True{} : Bool}:
  match b:
    case True{}:
      segs_trans(Prune.stepNeeds(grammar, e), Prune.segNeeds(ys, grammar, Prune.segOf(e)), seen, need_in(ys, grammar, e, m), queued_at(seen, Prune.segOf(e), seen, ys, grammar, eb, h1))
    case False{}:
      {==}

law steps_ok:
  for zs: +List<Core.Bsr>
  for +ys: +List<Core.Bsr>
  for +grammar: +List<Core.Production>
  for +seen: +List<Prune.Seg>
  for +sub: {Core.allIn(zs, ys) == True{} : Bool}
  for +h1: {queuedJ(seen, [], seen, ys, grammar) == True{} : Bool}
  {Prune.allStepsOk(zs, grammar, seen) == True{} : Bool}

def steps_ok(zs, ys, grammar, seen, sub, h1):
  match zs:
    case Nil{}:
      {==}
    case Con{+e, +rest}:
      Lemma.and_true_intro(Prune.stepOk(grammar, seen, e), Prune.allStepsOk(rest, grammar, seen),
        ok_pick(Prune.segIn(Prune.segOf(e), seen), e, ys, grammar, seen, {==}, Lemma.and_true_left(Core.member(e, ys), Core.allIn(rest, ys), sub), h1),
        steps_ok(rest, ys, grammar, seen, Lemma.and_true_right_side(Core.member(e, ys), Core.allIn(rest, ys), sub), h1))

def closedPick(m: Maybe<&2, +List<Prune.Seg>>, +grammar: +List<Core.Production>, +start: Nat, +n: Nat, +ys: +List<Core.Bsr>) -> Bool:
  match m:
    case Some{+ns}:
      Bool.and(Prune.needsClosed(grammar, start, n, ys, ns), seenJust(ns, ys, grammar, Prune.rootSegs(grammar, start, n)))
    case None{}:
      False{}

def end_closed(+seen: +List<Prune.Seg>, +ys: +List<Core.Bsr>, +grammar: +List<Core.Production>, +input: +List<Nat>, +start: Nat, p: JParts([], seen, [], ys, grammar, input, start))
  -> {Bool.and(Prune.needsClosed(grammar, start, List.length(&2, Nat, input), ys, seen), seenJust(seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input)))) == True{} : Bool}:
  match p:
    case (+h1, (+h2, (+h3, (+h4, (+h5, (+h6, h7)))))):
      Lemma.and_true_intro(Prune.needsClosed(grammar, start, List.length(&2, Nat, input), ys, seen), seenJust(seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))),
        Lemma.and_true_intro(Prune.allSegsIn(Prune.rootSegs(grammar, start, List.length(&2, Nat, input)), seen), Prune.allStepsOk(ys, grammar, seen), h4, steps_ok(ys, ys, grammar, seen, C.step_refl(ys), h1)), h6)

def loop_more(+f: Nat, +t: Prune.NeedState, +s0: Prune.NeedState, +ys: +List<Core.Bsr>, +grammar: +List<Core.Production>, +input: +List<Nat>, +start: Nat,
  +hy: {Run.stepsBounded(ys, grammar, input) == True{} : Bool},
  q: {needJ([], nSeen(t), nTodo(t), ys, grammar, input, start) == True{} : Bool} & {Nat.is_le(nMeas(grammar, input, t), nMeas(grammar, input, s0)) == True{} : Bool},
  +hf: {Nat.is_le(1n+nMeas(grammar, input, s0), f) == True{} : Bool},
  later: {needJ([], nSeen(t), nTodo(t), ys, grammar, input, start) == True{} : Bool} -> {Nat.is_le(1n+nMeas(grammar, input, t), f) == True{} : Bool} -> {closedPick(Prune.needLoop(f, ys, grammar, t), grammar, start, List.length(&2, Nat, input), ys) == True{} : Bool})
  -> {closedPick(Prune.needLoop(f, ys, grammar, t), grammar, start, List.length(&2, Nat, input), ys) == True{} : Bool}:
  match q:
    case (+hj, m):
      later(hj, Lemma.le_trans(1n+nMeas(grammar, input, t), 1n+nMeas(grammar, input, s0), f, m, hf))

def pop_meas(+grammar: +List<Core.Production>, +input: +List<Nat>, +seen: +List<Prune.Seg>, +rest: +List<Prune.Seg>, +f: Nat,
  +hf: {Nat.is_le(Nat.add(Run.countNot(Run.univ(grammar, input), descsOf(seen)), 1n+List.length(&2, Prune.Seg, rest)), f) == True{} : Bool})
  -> {Nat.is_le(1n+Nat.add(Run.countNot(Run.univ(grammar, input), descsOf(seen)), List.length(&2, Prune.Seg, rest)), f) == True{} : Bool}:
  %Lemma.add_succ_right(Run.countNot(Run.univ(grammar, input), descsOf(seen)), List.length(&2, Prune.Seg, rest)) : {Nat.is_le(_, f) == True{} : Bool}
  hf

def loop_next(+f: Nat, +seg: Prune.Seg, +rest: +List<Prune.Seg>, +seen: +List<Prune.Seg>, +ys: +List<Core.Bsr>, +grammar: +List<Core.Production>, +input: +List<Nat>, +start: Nat,
  +hy: {Run.stepsBounded(ys, grammar, input) == True{} : Bool},
  p: JParts([], seen, seg <> rest, ys, grammar, input, start),
  +hf: {Nat.is_le(Nat.add(Run.countNot(Run.univ(grammar, input), descsOf(seen)), 1n+List.length(&2, Prune.Seg, rest)), f) == True{} : Bool},
  later: {needJ([], nSeen(Prune.addSegs(Prune.segNeeds(ys, grammar, seg), seen, rest)), nTodo(Prune.addSegs(Prune.segNeeds(ys, grammar, seg), seen, rest)), ys, grammar, input, start) == True{} : Bool} -> {Nat.is_le(1n+nMeas(grammar, input, Prune.addSegs(Prune.segNeeds(ys, grammar, seg), seen, rest)), f) == True{} : Bool} -> {closedPick(Prune.needLoop(f, ys, grammar, Prune.addSegs(Prune.segNeeds(ys, grammar, seg), seen, rest)), grammar, start, List.length(&2, Nat, input), ys) == True{} : Bool})
  -> {closedPick(Prune.needLoop(f, ys, grammar, Prune.addSegs(Prune.segNeeds(ys, grammar, seg), seen, rest)), grammar, start, List.length(&2, Nat, input), ys) == True{} : Bool}:
  match p:
    case (+h1, (+h2, (+h3, (+h4, (+h5, (+h6, h7)))))):
      +N = Prune.segNeeds(ys, grammar, seg)
      +J = j_join(N, seen, rest, ys, grammar, input, start, requeue(seen, seg, rest, seen, ys, grammar, h1),
        Lemma.and_true_right_side(Prune.segIn(seg, seen), Prune.allSegsIn(rest, seen), h2), h3,
        segs_app_right(Prune.rootSegs(grammar, start, List.length(&2, Nat, input)), N, seen, h4), needs_bounded(ys, grammar, input, seg, hy), h6,
        needs_just(N, seg, seen, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input)), seg_refl(N), Lemma.and_true_left(Prune.segIn(seg, seen), Prune.allSegsIn(rest, seen), h2)))
      loop_more(f, Prune.addSegs(N, seen, rest), Prune.NeedState{seen, rest}, ys, grammar, input, start, hy,
        fold_inv(N, seen, rest, ys, grammar, input, start, J), pop_meas(grammar, input, seen, rest, f, hf), later)

# With more fuel than the measure, the loop ends with closed needs.
law loop_closed:
  for fuel: Nat
  for +ys: +List<Core.Bsr>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +start: Nat
  for s: Prune.NeedState
  for +hy: {Run.stepsBounded(ys, grammar, input) == True{} : Bool}
  for +h: {needJ([], nSeen(s), nTodo(s), ys, grammar, input, start) == True{} : Bool}
  for +hf: {Nat.is_le(1n+nMeas(grammar, input, s), fuel) == True{} : Bool}
  {closedPick(Prune.needLoop(fuel, ys, grammar, s), grammar, start, List.length(&2, Nat, input), ys) == True{} : Bool}

def loop_closed(fuel, ys, grammar, input, start, s, hy, h, hf):
  match fuel s:
    case 0n +st:
      Empty.absurd({closedPick(Prune.needLoop(0n, ys, grammar, st), grammar, start, List.length(&2, Nat, input), ys) == True{} : Bool}, Lemma.false_is_not_true(hf))
    case 1n+(+f) Prune.NeedState{+seen, Nil{}}:
      end_closed(seen, ys, grammar, input, start, j_split([], seen, [], ys, grammar, input, start, h))
    case 1n+(+f) Prune.NeedState{+seen, Con{+seg, +rest}}:
      loop_next(f, seg, rest, seen, ys, grammar, input, start, hy, j_split([], seen, seg <> rest, ys, grammar, input, start, h), hf,
        hj => hf2 => loop_closed(f, ys, grammar, input, start, Prune.addSegs(Prune.segNeeds(ys, grammar, seg), seen, rest), hy, hj, hf2))

# ======== THE LAW ========

def start_more(+fuel: Nat, +ys: +List<Core.Bsr>, +grammar: +List<Core.Production>, +input: +List<Nat>, +start: Nat, +hy: {Run.stepsBounded(ys, grammar, input) == True{} : Bool},
  q: {needJ([], nSeen(Prune.addSegs(Prune.rootSegs(grammar, start, List.length(&2, Nat, input)), [], [])), nTodo(Prune.addSegs(Prune.rootSegs(grammar, start, List.length(&2, Nat, input)), [], [])), ys, grammar, input, start) == True{} : Bool} &
     {Nat.is_le(nMeas(grammar, input, Prune.addSegs(Prune.rootSegs(grammar, start, List.length(&2, Nat, input)), [], [])), nMeas(grammar, input, Prune.NeedState{[], []})) == True{} : Bool},
  +hf: {Nat.is_le(1n+List.length(&2, Gll.Desc, Run.univ(grammar, input)), fuel) == True{} : Bool})
  -> {closedPick(Prune.needsOf(fuel, grammar, start, List.length(&2, Nat, input), ys), grammar, start, List.length(&2, Nat, input), ys) == True{} : Bool}:
  match q:
    case (+hj, m):
      +t = Prune.addSegs(Prune.rootSegs(grammar, start, List.length(&2, Nat, input)), [], [])
      +U = Run.univ(grammar, input)
      +h0 = Lemma.le_trans(1n+nMeas(grammar, input, Prune.NeedState{[], []}), 1n+List.length(&2, Gll.Desc, U), fuel, C.count_start(U), hf)
      loop_closed(fuel, ys, grammar, input, start, t, hy, hj, Lemma.le_trans(1n+nMeas(grammar, input, t), 1n+nMeas(grammar, input, Prune.NeedState{[], []}), fuel, m, h0))

# THE NEEDS ARE CLOSED: on steps within bounds, with fuel 1 + the size of the descriptor
# universe, the needs loop finishes and its needs pass `needsClosed`.
law needs_closed:
  for fuel: Nat
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +ys: +List<Core.Bsr>
  for +hy: {Run.stepsBounded(ys, grammar, input) == True{} : Bool}
  for +hf: {Nat.is_le(1n+List.length(&2, Gll.Desc, Run.univ(grammar, input)), fuel) == True{} : Bool}
  {closedPick(Prune.needsOf(fuel, grammar, start, List.length(&2, Nat, input), ys), grammar, start, List.length(&2, Nat, input), ys) == True{} : Bool}

def needs_closed(fuel, grammar, start, input, ys, hy, hf):
  +R = Prune.rootSegs(grammar, start, List.length(&2, Nat, input))
  start_more(fuel, ys, grammar, input, start, hy,
    fold_inv(R, [], [], ys, grammar, input, start, j_join(R, [], [], ys, grammar, input, start, {==}, {==}, {==}, segs_app_left(R, R, [], seg_refl(R)), roots_bounded(grammar, start, input), {==}, roots_just(R, R, ys, grammar, seg_refl(R)))), hf)

def isSteps(m: Maybe<&2, +List<Core.Bsr>>) -> Bool:
  match m:
    case Some{ys}:
      True{}
    case None{}:
      False{}

def prune_pick(b: Bool, +ys: +List<Core.Bsr>, +ns: +List<Prune.Seg>, +h: {b == True{} : Bool}) -> {isSteps(Prune.prunePick(b, ys, ns)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({isSteps(None{}) == True{} : Bool}, Lemma.false_is_not_true(h))

def prune_from(m: Maybe<&2, +List<Prune.Seg>>, +grammar: +List<Core.Production>, +start: Nat, +n: Nat, +ys: +List<Core.Bsr>, +h: {closedPick(m, grammar, start, n, ys) == True{} : Bool})
  -> {isSteps(Prune.pruneChecked(m, grammar, start, n, ys)) == True{} : Bool}:
  match m:
    case Some{+ns}:
      prune_pick(Prune.needsClosed(grammar, start, n, ys, ns), ys, ns, Lemma.and_true_left(Prune.needsClosed(grammar, start, n, ys, ns), seenJust(ns, ys, grammar, Prune.rootSegs(grammar, start, n)), h))
    case None{}:
      Empty.absurd({isSteps(None{}) == True{} : Bool}, Lemma.false_is_not_true(h))

# PRUNING ANSWERS: on steps within bounds, with that fuel, pruning hands out its steps.
law pruned_answers:
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +ys: +List<Core.Bsr>
  for +hy: {Run.stepsBounded(ys, grammar, input) == True{} : Bool}
  for +hf: {Nat.is_le(1n+List.length(&2, Gll.Desc, Run.univ(grammar, input)), fuel) == True{} : Bool}
  {isSteps(Prune.pruneSteps(Some{ys}, fuel, grammar, start, input)) == True{} : Bool}

def pruned_answers(fuel, grammar, start, input, ys, hy, hf):
  +n = List.length(&2, Nat, input)
  prune_from(Prune.needsOf(fuel, grammar, start, n, ys), grammar, start, n, ys, needs_closed(fuel, grammar, start, input, ys, hy, hf))


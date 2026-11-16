import Base
import ../LEMMAS.bend as Lemma
import ./PROOF_BASICS.bend as B
import ./CORE.bend as Core
import ./SETS.bend as Sets
import ./GLL.bend as Gll
import ./LL1.bend as LL
import ./TABLES.bend as T
import ./PROOF_GLL.bend as G
import ./PROOF_PRUNE.bend as P
import ./PROOF_DECIDE.bend as D
import ./PROOF_RULE.bend as Rule
import ./PROOF_LL1.bend as L

# LL(1) BY THE TABLES IS LL(1). Whatever production q can begin with is in its predict set
# by the tables: a first token is in FIRST (a walk over the forest that reads it, using
# that FIRST is closed), and a token that follows q in a parse tree is in FOLLOW of q's
# nonterminal (a walk down the tree, using that FOLLOW is closed). The check finds no
# token in two predict sets of one nonterminal, so no two productions can predict the same.

# ======== SMALL FACTS ========

law maybe_eq_sound:
  for a: Maybe<&2, Nat>
  for b: Maybe<&2, Nat>
  for +e: {T.maybeEq(a, b) == True{} : Bool}
  {a == b : Maybe<&2, Nat>}

def maybe_eq_sound(a, b, e):
  match a b:
    case None{} None{}:
      {==}
    case Some{+x} Some{+y}:
      Equal.cong(Nat, Maybe<&2, Nat>, v => Some{v}, x, y, Lemma.nat_eq_sound(x, y, e))
    case None{} Some{+y}:
      Empty.absurd({None{} == Some{y} : Maybe<&2, Nat>}, Lemma.false_is_not_true(e))
    case Some{+x} None{}:
      Empty.absurd({Some{x} == None{} : Maybe<&2, Nat>}, Lemma.false_is_not_true(e))

law maybe_eq_refl:
  for a: Maybe<&2, Nat>
  {T.maybeEq(a, a) == True{} : Bool}

def maybe_eq_refl(a):
  match a:
    case None{}:
      {==}
    case Some{+x}:
      Lemma.nat_eq_refl(x)

def join_pick(+x: Maybe<&2, Nat>, +rest: +List<Maybe<&2, Nat>>, +b: +List<Maybe<&2, Nat>>, +n: Maybe<&2, Nat>,
  cases: Either<{T.maybeEq(n, x) == True{} : Bool}, {T.maybeIn(n, rest) == True{} : Bool}>,
  later: {T.maybeIn(n, rest) == True{} : Bool} -> {T.maybeIn(n, T.joinMaybes(rest, b)) == True{} : Bool}) -> {T.maybeIn(n, x <> T.joinMaybes(rest, b)) == True{} : Bool}:
  match cases:
    case Inl{e}:
      Lemma.or_true_left_intro(T.maybeEq(n, x), T.maybeIn(n, T.joinMaybes(rest, b)), e)
    case Inr{m}:
      Lemma.or_true_right_intro(T.maybeEq(n, x), T.maybeIn(n, T.joinMaybes(rest, b)), later(m))

law maybe_join_left:
  for a: +List<Maybe<&2, Nat>>
  for +b: +List<Maybe<&2, Nat>>
  for +n: Maybe<&2, Nat>
  for +h: {T.maybeIn(n, a) == True{} : Bool}
  {T.maybeIn(n, T.joinMaybes(a, b)) == True{} : Bool}

def maybe_join_left(a, b, n, h):
  match a:
    case Nil{}:
      Empty.absurd({T.maybeIn(n, b) == True{} : Bool}, Lemma.false_is_not_true(h))
    case Con{+x, +rest}:
      join_pick(x, rest, b, n, Lemma.or_true_cases(T.maybeEq(n, x), T.maybeIn(n, rest), h), m => maybe_join_left(rest, b, n, m))

law maybe_join_right:
  for a: +List<Maybe<&2, Nat>>
  for +b: +List<Maybe<&2, Nat>>
  for +n: Maybe<&2, Nat>
  for +h: {T.maybeIn(n, b) == True{} : Bool}
  {T.maybeIn(n, T.joinMaybes(a, b)) == True{} : Bool}

def maybe_join_right(a, b, n, h):
  match a:
    case Nil{}:
      h
    case Con{+x, +rest}:
      Lemma.or_true_right_intro(T.maybeEq(n, x), T.maybeIn(n, T.joinMaybes(rest, b)), maybe_join_right(rest, b, n, h))

def nat_join_pick(+x: Nat, +rest: +List<Nat>, +b: +List<Nat>, +t: Nat,
  cases: Either<{Nat.is_eq(t, x) == True{} : Bool}, {Sets.natIn(t, rest) == True{} : Bool}>,
  later: {Sets.natIn(t, rest) == True{} : Bool} -> {Sets.natIn(t, Sets.joinNats(rest, b)) == True{} : Bool}) -> {Sets.natIn(t, x <> Sets.joinNats(rest, b)) == True{} : Bool}:
  match cases:
    case Inl{e}:
      Lemma.or_true_left_intro(Nat.is_eq(t, x), Sets.natIn(t, Sets.joinNats(rest, b)), e)
    case Inr{m}:
      Lemma.or_true_right_intro(Nat.is_eq(t, x), Sets.natIn(t, Sets.joinNats(rest, b)), later(m))

law nat_in_join_left:
  for a: +List<Nat>
  for +b: +List<Nat>
  for +t: Nat
  for +h: {Sets.natIn(t, a) == True{} : Bool}
  {Sets.natIn(t, Sets.joinNats(a, b)) == True{} : Bool}

def nat_in_join_left(a, b, t, h):
  match a:
    case Nil{}:
      Empty.absurd({Sets.natIn(t, b) == True{} : Bool}, Lemma.false_is_not_true(h))
    case Con{+x, +rest}:
      nat_join_pick(x, rest, b, t, Lemma.or_true_cases(Nat.is_eq(t, x), Sets.natIn(t, rest), h), m => nat_in_join_left(rest, b, t, m))

law nat_in_join_right:
  for a: +List<Nat>
  for +b: +List<Nat>
  for +t: Nat
  for +h: {Sets.natIn(t, b) == True{} : Bool}
  {Sets.natIn(t, Sets.joinNats(a, b)) == True{} : Bool}

def nat_in_join_right(a, b, t, h):
  match a:
    case Nil{}:
      h
    case Con{+x, +rest}:
      Lemma.or_true_right_intro(Nat.is_eq(t, x), Sets.natIn(t, Sets.joinNats(rest, b)), nat_in_join_right(rest, b, t, h))

def some_pick(+x: Nat, +rest: +List<Nat>, +t: Nat,
  cases: Either<{Nat.is_eq(t, x) == True{} : Bool}, {Sets.natIn(t, rest) == True{} : Bool}>,
  later: {Sets.natIn(t, rest) == True{} : Bool} -> {T.maybeIn(Some{t}, T.someAll(rest)) == True{} : Bool}) -> {T.maybeIn(Some{t}, Some{x} <> T.someAll(rest)) == True{} : Bool}:
  match cases:
    case Inl{e}:
      Lemma.or_true_left_intro(Nat.is_eq(t, x), T.maybeIn(Some{t}, T.someAll(rest)), e)
    case Inr{m}:
      Lemma.or_true_right_intro(Nat.is_eq(t, x), T.maybeIn(Some{t}, T.someAll(rest)), later(m))

law some_in:
  for ts: +List<Nat>
  for +t: Nat
  for +h: {Sets.natIn(t, ts) == True{} : Bool}
  {T.maybeIn(Some{t}, T.someAll(ts)) == True{} : Bool}

def some_in(ts, t, h):
  match ts:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(h))
    case Con{+x, +rest}:
      some_pick(x, rest, t, Lemma.or_true_cases(Nat.is_eq(t, x), Sets.natIn(t, rest), h), m => some_in(rest, t, m))

def nat_all_pick(+x: Nat, +rest: +List<Nat>, +c: +List<Nat>, +t: Nat, +hx: {Sets.natIn(x, c) == True{} : Bool},
  cases: Either<{Nat.is_eq(t, x) == True{} : Bool}, {Sets.natIn(t, rest) == True{} : Bool}>,
  later: {Sets.natIn(t, rest) == True{} : Bool} -> {Sets.natIn(t, c) == True{} : Bool}) -> {Sets.natIn(t, c) == True{} : Bool}:
  match cases:
    case Inl{e}:
      %Equal.sym(Nat, t, x, Lemma.nat_eq_sound(t, x, e)) : {Sets.natIn(_, c) == True{} : Bool}
      hx
    case Inr{m}:
      later(m)

law nat_all_member:
  for xs: +List<Nat>
  for +c: +List<Nat>
  for +t: Nat
  for +all: {Sets.allNatIn(xs, c) == True{} : Bool}
  for +m: {Sets.natIn(t, xs) == True{} : Bool}
  {Sets.natIn(t, c) == True{} : Bool}

def nat_all_member(xs, c, t, all, m):
  match xs:
    case Nil{}:
      Empty.absurd({Sets.natIn(t, c) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{+x, +rest}:
      nat_all_pick(x, rest, c, t, Lemma.and_true_left(Sets.natIn(x, c), Sets.allNatIn(rest, c), all), Lemma.or_true_cases(Nat.is_eq(t, x), Sets.natIn(t, rest), m),
        m2 => nat_all_member(rest, c, t, Lemma.and_true_right_side(Sets.natIn(x, c), Sets.allNatIn(rest, c), all), m2))

def maybe_all_pick(+x: Maybe<&2, Nat>, +rest: +List<Maybe<&2, Nat>>, +ys: +List<Maybe<&2, Nat>>, +n: Maybe<&2, Nat>, +hx: {T.maybeIn(x, ys) == True{} : Bool},
  cases: Either<{T.maybeEq(n, x) == True{} : Bool}, {T.maybeIn(n, rest) == True{} : Bool}>,
  later: {T.maybeIn(n, rest) == True{} : Bool} -> {T.maybeIn(n, ys) == True{} : Bool}) -> {T.maybeIn(n, ys) == True{} : Bool}:
  match cases:
    case Inl{e}:
      %Equal.sym(Maybe<&2, Nat>, n, x, maybe_eq_sound(n, x, e)) : {T.maybeIn(_, ys) == True{} : Bool}
      hx
    case Inr{m}:
      later(m)

law maybe_all_member:
  for xs: +List<Maybe<&2, Nat>>
  for +ys: +List<Maybe<&2, Nat>>
  for +n: Maybe<&2, Nat>
  for +all: {T.allMaybeIn(xs, ys) == True{} : Bool}
  for +m: {T.maybeIn(n, xs) == True{} : Bool}
  {T.maybeIn(n, ys) == True{} : Bool}

def maybe_all_member(xs, ys, n, all, m):
  match xs:
    case Nil{}:
      Empty.absurd({T.maybeIn(n, ys) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{+x, +rest}:
      maybe_all_pick(x, rest, ys, n, Lemma.and_true_left(T.maybeIn(x, ys), T.allMaybeIn(rest, ys), all), Lemma.or_true_cases(T.maybeEq(n, x), T.maybeIn(n, rest), m),
        m2 => maybe_all_member(rest, ys, n, Lemma.and_true_right_side(T.maybeIn(x, ys), T.allMaybeIn(rest, ys), all), m2))

def follow_pick(+x: Nat, +rest: +List<Nat>, +y: Nat, +follows: +List<T.FollowFact>, +t: Nat, +hx: {T.followHas(y, Some{x}, follows) == True{} : Bool},
  cases: Either<{Nat.is_eq(t, x) == True{} : Bool}, {Sets.natIn(t, rest) == True{} : Bool}>,
  later: {Sets.natIn(t, rest) == True{} : Bool} -> {T.followHas(y, Some{t}, follows) == True{} : Bool}) -> {T.followHas(y, Some{t}, follows) == True{} : Bool}:
  match cases:
    case Inl{e}:
      %Equal.sym(Nat, t, x, Lemma.nat_eq_sound(t, x, e)) : {T.followHas(y, Some{_}, follows) == True{} : Bool}
      hx
    case Inr{m}:
      later(m)

law all_follow_member:
  for ts: +List<Nat>
  for +y: Nat
  for +follows: +List<T.FollowFact>
  for +t: Nat
  for +all: {T.allFollow(ts, y, follows) == True{} : Bool}
  for +m: {Sets.natIn(t, ts) == True{} : Bool}
  {T.followHas(y, Some{t}, follows) == True{} : Bool}

def all_follow_member(ts, y, follows, t, all, m):
  match ts:
    case Nil{}:
      Empty.absurd({T.followHas(y, Some{t}, follows) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{+x, +rest}:
      follow_pick(x, rest, y, follows, t, Lemma.and_true_left(T.followHas(y, Some{x}, follows), T.allFollow(rest, y, follows), all), Lemma.or_true_cases(Nat.is_eq(t, x), Sets.natIn(t, rest), m),
        m2 => all_follow_member(rest, y, follows, t, Lemma.and_true_right_side(T.followHas(y, Some{x}, follows), T.allFollow(rest, y, follows), all), m2))

def disjoint_pick(+x: Maybe<&2, Nat>, +rest: +List<Maybe<&2, Nat>>, +ys: +List<Maybe<&2, Nat>>, +n: Maybe<&2, Nat>,
  +hx: {Bool.not(T.maybeIn(x, ys)) == True{} : Bool}, +m2: {T.maybeIn(n, ys) == True{} : Bool},
  cases: Either<{T.maybeEq(n, x) == True{} : Bool}, {T.maybeIn(n, rest) == True{} : Bool}>,
  later: {T.maybeIn(n, rest) == True{} : Bool} -> Empty) -> Empty:
  match cases:
    case Inl{e}:
      +mx = {(%maybe_eq_sound(n, x, e) : {T.maybeIn(_, ys) == True{} : Bool}
        m2) : {T.maybeIn(x, ys) == True{} : Bool}}
      B.not_both(T.maybeIn(x, ys), mx, hx)
    case Inr{m}:
      later(m)

law disjoint_no:
  for xs: +List<Maybe<&2, Nat>>
  for +ys: +List<Maybe<&2, Nat>>
  for +n: Maybe<&2, Nat>
  for +d: {T.disjoint(xs, ys) == True{} : Bool}
  for +m1: {T.maybeIn(n, xs) == True{} : Bool}
  for +m2: {T.maybeIn(n, ys) == True{} : Bool}
  Empty

def disjoint_no(xs, ys, n, d, m1, m2):
  match xs:
    case Nil{}:
      Lemma.false_is_not_true(m1)
    case Con{+x, +rest}:
      disjoint_pick(x, rest, ys, n, Lemma.and_true_left(Bool.not(T.maybeIn(x, ys)), T.disjoint(rest, ys), d), m2, Lemma.or_true_cases(T.maybeEq(n, x), T.maybeIn(n, rest), m1),
        m3 => disjoint_no(rest, ys, n, Lemma.and_true_right_side(Bool.not(T.maybeIn(x, ys)), T.disjoint(rest, ys), d), m3, m2))

law nats_if_true:
  for b: Bool
  for +xs: +List<Nat>
  for +t: Nat
  for +hb: {b == True{} : Bool}
  for +h: {Sets.natIn(t, xs) == True{} : Bool}
  {Sets.natIn(t, T.natsIf(b, xs)) == True{} : Bool}

def nats_if_true(b, xs, t, hb, h):
  match b:
    case True{}:
      h
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(hb))

law maybes_if_true:
  for b: Bool
  for +xs: +List<Maybe<&2, Nat>>
  for +n: Maybe<&2, Nat>
  for +hb: {b == True{} : Bool}
  for +h: {T.maybeIn(n, xs) == True{} : Bool}
  {T.maybeIn(n, T.maybesIf(b, xs)) == True{} : Bool}

def maybes_if_true(b, xs, n, hb, h):
  match b:
    case True{}:
      h
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(hb))

law tok_end:
  for input: +List<Nat>
  {Core.tokAt(input, List.length(&2, Nat, input)) == None{} : Maybe<&2, Nat>}

def tok_end(input):
  match input:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      tok_end(rest)

law first_closed_at:
  for g: +List<Core.Production>
  for p: Nat
  for +y: Nat
  for +firsts: +List<T.FirstFact>
  for +nulls: +List<Nat>
  for +cf: {T.firstsClosed(g, firsts, nulls) == True{} : Bool}
  for +hl: {Core.lhsIs(g, p, y) == True{} : Bool}
  {Sets.allNatIn(T.firstOfItems(Core.rhsOf(g, p), firsts, nulls), T.firstsOf(y, firsts)) == True{} : Bool}

def first_closed_at(g, p, y, firsts, nulls, cf, hl):
  match g p:
    case Nil{} +p0:
      Empty.absurd({True{} == True{} : Bool}, Lemma.false_is_not_true(hl))
    case Con{Core.Production{+lhs, +rhs}, +rest} 0n:
      +here = {Sets.allNatIn(T.firstOfItems(rhs, firsts, nulls), T.firstsOf(lhs, firsts)) : Bool}
      %Lemma.nat_eq_sound(lhs, y, hl) : {Sets.allNatIn(T.firstOfItems(rhs, firsts, nulls), T.firstsOf(_, firsts)) == True{} : Bool}
      Lemma.and_true_left(here, T.firstsClosed(rest, firsts, nulls), cf)
    case Con{Core.Production{+lhs, +rhs}, +rest} 1n+(+n):
      +here = {Sets.allNatIn(T.firstOfItems(rhs, firsts, nulls), T.firstsOf(lhs, firsts)) : Bool}
      first_closed_at(rest, n, y, firsts, nulls, Lemma.and_true_right_side(here, T.firstsClosed(rest, firsts, nulls), cf), hl)

law follow_closed_at:
  for g: +List<Core.Production>
  for p: Nat
  for +y: Nat
  for +firsts: +List<T.FirstFact>
  for +follows: +List<T.FollowFact>
  for +nulls: +List<Nat>
  for +cfo: {T.followsClosed(g, firsts, follows, nulls) == True{} : Bool}
  for +hl: {Core.lhsIs(g, p, y) == True{} : Bool}
  {T.suffixOk(Core.rhsOf(g, p), y, firsts, follows, nulls) == True{} : Bool}

def follow_closed_at(g, p, y, firsts, follows, nulls, cfo, hl):
  match g p:
    case Nil{} +p0:
      Empty.absurd({True{} == True{} : Bool}, Lemma.false_is_not_true(hl))
    case Con{Core.Production{+lhs, +rhs}, +rest} 0n:
      +here = {T.suffixOk(rhs, lhs, firsts, follows, nulls) : Bool}
      %Lemma.nat_eq_sound(lhs, y, hl) : {T.suffixOk(rhs, _, firsts, follows, nulls) == True{} : Bool}
      Lemma.and_true_left(here, T.followsClosed(rest, firsts, follows, nulls), cfo)
    case Con{Core.Production{+lhs, +rhs}, +rest} 1n+(+n):
      +here = {T.suffixOk(rhs, lhs, firsts, follows, nulls) : Bool}
      follow_closed_at(rest, n, y, firsts, follows, nulls, Lemma.and_true_right_side(here, T.followsClosed(rest, firsts, follows, nulls), cfo), hl)

# ======== A FIRST TOKEN IS IN FIRST ========

def first_node(w: +List<Nat>, +p: Nat, +cs: +List<Core.Tree>, +ts: +List<Core.Tree>, +y: Nat, +need: Core.Need, +rest: +List<Core.Sym>,
  +grammar: +List<Core.Production>, +firsts: +List<T.FirstFact>, +nulls: +List<Nat>, +t: Nat, +r: +List<Nat>,
  +cn: {Sets.nullsClosed(grammar, nulls) == True{} : Bool},
  +cf: {T.firstsClosed(grammar, firsts, nulls) == True{} : Bool},
  +hl: {Core.lhsIs(grammar, p, y) == True{} : Bool},
  +hd: {Bool.and(Bool.and(Core.lhsIs(grammar, p, y), Core.needOk(need, Core.width(Core.Node{p, cs}))), Core.fits(cs, grammar, Core.rhsOf(grammar, p))) == True{} : Bool},
  +ew: {Core.leaves(cs) == w : +List<Nat>},
  +e: {List.append(&2, Nat, Core.leaves(cs), Core.leaves(ts)) == t <> r : +List<Nat>},
  inCs: @t2: Nat -> @r2: +List<Nat> -> {Core.leaves(cs) == t2 <> r2 : +List<Nat>} -> {Sets.natIn(t2, T.firstOfItems(Core.rhsOf(grammar, p), firsts, nulls)) == True{} : Bool},
  inTs: {Core.leaves(ts) == t <> r : +List<Nat>} -> {Sets.natIn(t, T.firstOfItems(rest, firsts, nulls)) == True{} : Bool})
  -> {Sets.natIn(t, T.firstOfItems(Core.Nonterminal{y, need} <> rest, firsts, nulls)) == True{} : Bool}:
  match w:
    case Nil{}:
      +s = {Core.Nonterminal{y, need} : Core.Sym}
      +e2 = Equal.trans(+List<Nat>, Core.leaves(ts), List.append(&2, Nat, Core.leaves(cs), Core.leaves(ts)), t <> r,
        Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, Core.leaves(ts)), [], Core.leaves(cs), Equal.sym(+List<Nat>, Core.leaves(cs), [], ew)), e)
      +zh = Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, []), Core.leaves(cs), [], ew)
      +one = Lemma.and_true_intro(Bool.and(Bool.and(Core.lhsIs(grammar, p, y), Core.needOk(need, Core.width(Core.Node{p, cs}))), Core.fits(cs, grammar, Core.rhsOf(grammar, p))), True{}, hd, {==})
      +sn = Lemma.and_true_left(Sets.itemNull(s, nulls), True{}, Rule.zero_nulls([Core.Node{p, cs}], [s], grammar, nulls, cn, one, zh))
      nat_in_join_right(T.firstsOf(y, firsts), T.natsIf(Sets.itemNull(s, nulls), T.firstOfItems(rest, firsts, nulls)), t,
        nats_if_true(Sets.itemNull(s, nulls), T.firstOfItems(rest, firsts, nulls), t, sn, inTs(e2)))
    case Con{+t2, +r2}:
      +e2 = Equal.trans(+List<Nat>, t2 <> List.append(&2, Nat, r2, Core.leaves(ts)), List.append(&2, Nat, Core.leaves(cs), Core.leaves(ts)), t <> r,
        Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, Core.leaves(ts)), t2 <> r2, Core.leaves(cs), Equal.sym(+List<Nat>, Core.leaves(cs), t2 <> r2, ew)), e)
      +same = L.cons_head(t2, t, List.append(&2, Nat, r2, Core.leaves(ts)), r, e2)
      +in2 = nat_all_member(T.firstOfItems(Core.rhsOf(grammar, p), firsts, nulls), T.firstsOf(y, firsts), t2, first_closed_at(grammar, p, y, firsts, nulls, cf, hl), inCs(t2, r2, ew))
      +inT = {(%same : {Sets.natIn(_, T.firstsOf(y, firsts)) == True{} : Bool}
        in2) : {Sets.natIn(t, T.firstsOf(y, firsts)) == True{} : Bool}}
      nat_in_join_left(T.firstsOf(y, firsts), T.natsIf(Sets.itemNull(Core.Nonterminal{y, need}, nulls), T.firstOfItems(rest, firsts, nulls)), t, inT)

law first_in:
  for fs: +List<Core.Tree>
  for items: +List<Core.Sym>
  for +grammar: +List<Core.Production>
  for +firsts: +List<T.FirstFact>
  for +nulls: +List<Nat>
  for +cn: {Sets.nullsClosed(grammar, nulls) == True{} : Bool}
  for +cf: {T.firstsClosed(grammar, firsts, nulls) == True{} : Bool}
  for +t: Nat
  for +r: +List<Nat>
  for +fit: {Core.fits(fs, grammar, items) == True{} : Bool}
  for +lv: {Core.leaves(fs) == t <> r : +List<Nat>}
  {Sets.natIn(t, T.firstOfItems(items, firsts, nulls)) == True{} : Bool}

def first_in(fs, items, grammar, firsts, nulls, cn, cf, t, r, fit, lv):
  match fs items:
    case Nil{} +its:
      Empty.absurd({Sets.natIn(t, T.firstOfItems(its, firsts, nulls)) == True{} : Bool}, L.cons_not_nil(t, r, Equal.sym(+List<Nat>, [], t <> r, lv)))
    case Con{Core.Leaf{+a}, +ts} Con{Core.Terminal{+k}, +rest}:
      +ak = Lemma.nat_eq_sound(a, k, Lemma.and_true_left(Nat.is_eq(a, k), Core.fits(ts, grammar, rest), fit))
      +ta = Equal.sym(Nat, a, t, L.cons_head(a, t, Core.leaves(ts), r, lv))
      Lemma.or_true_left_intro(Nat.is_eq(t, k), False{}, B.eq_is_eq(t, k, Equal.trans(Nat, t, a, k, ta, ak)))
    case Con{Core.Leaf{+a}, +ts} Nil{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Core.Leaf{+a}, +ts} Con{Core.Nonterminal{+y, +need}, +rest}:
      Empty.absurd({Sets.natIn(t, T.firstOfItems(Core.Nonterminal{y, need} <> rest, firsts, nulls)) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Core.Node{+p, +cs}, +ts} Nil{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Core.Node{+p, +cs}, +ts} Con{Core.Terminal{+k}, +rest}:
      Empty.absurd({Sets.natIn(t, [k]) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Core.Node{+p, +cs}, +ts} Con{Core.Nonterminal{+y, +need}, +rest}:
      +lh = {Core.lhsIs(grammar, p, y) : Bool}
      +nd = {Core.needOk(need, Core.width(Core.Node{p, cs})) : Bool}
      +fc = {Core.fits(cs, grammar, Core.rhsOf(grammar, p)) : Bool}
      +ft = {Core.fits(ts, grammar, rest) : Bool}
      +hd = Lemma.and_true_left(Bool.and(Bool.and(lh, nd), fc), ft, fit)
      +hl = Lemma.and_true_left(lh, nd, Lemma.and_true_left(Bool.and(lh, nd), fc, hd))
      +hc = Lemma.and_true_right_side(Bool.and(lh, nd), fc, hd)
      +htt = Lemma.and_true_right_side(Bool.and(Bool.and(lh, nd), fc), ft, fit)
      first_node(Core.leaves(cs), p, cs, ts, y, need, rest, grammar, firsts, nulls, t, r, cn, cf, hl, hd, {==}, lv,
        t2 => r2 => h => first_in(cs, Core.rhsOf(grammar, p), grammar, firsts, nulls, cn, cf, t2, r2, hc, h),
        h => first_in(ts, rest, grammar, firsts, nulls, cn, cf, t, r, htt, h))

# ======== A NODE'S LAST STEP ========

def bIndex(b: Core.Bsr) -> Nat:
  match b:
    case Core.Bsr{+q, d, i, k, j}:
      q

def bDot(b: Core.Bsr) -> Nat:
  match b:
    case Core.Bsr{q, +d, i, k, j}:
      d

def bEnd(b: Core.Bsr) -> Nat:
  match b:
    case Core.Bsr{q, d, i, k, +j}:
      j

def lift_split(+y: Core.Bsr, +rest: +List<Core.Bsr>, +b: +List<Core.Bsr>, +x: Core.Bsr,
  c: Either<{Core.member(x, rest) == True{} : Bool}, {Core.member(x, b) == True{} : Bool}>)
  -> Either<{Core.member(x, y <> rest) == True{} : Bool}, {Core.member(x, b) == True{} : Bool}>:
  match c:
    case Inl{m}:
      Inl{Lemma.or_true_right_intro(Core.bsrEq(x, y), Core.member(x, rest), m)}
    case Inr{m}:
      Inr{m}

def split_pick(+y: Core.Bsr, +rest: +List<Core.Bsr>, +b: +List<Core.Bsr>, +x: Core.Bsr,
  cases: Either<{Core.bsrEq(x, y) == True{} : Bool}, {Core.member(x, List.append(&2, Core.Bsr, rest, b)) == True{} : Bool}>,
  later: {Core.member(x, List.append(&2, Core.Bsr, rest, b)) == True{} : Bool} -> Either<{Core.member(x, rest) == True{} : Bool}, {Core.member(x, b) == True{} : Bool}>)
  -> Either<{Core.member(x, y <> rest) == True{} : Bool}, {Core.member(x, b) == True{} : Bool}>:
  match cases:
    case Inl{e}:
      Inl{Lemma.or_true_left_intro(Core.bsrEq(x, y), Core.member(x, rest), e)}
    case Inr{m}:
      lift_split(y, rest, b, x, later(m))

law member_split:
  for a: +List<Core.Bsr>
  for +b: +List<Core.Bsr>
  for +x: Core.Bsr
  for +m: {Core.member(x, List.append(&2, Core.Bsr, a, b)) == True{} : Bool}
  Either<{Core.member(x, a) == True{} : Bool}, {Core.member(x, b) == True{} : Bool}>

def member_split(a, b, x, m):
  match a:
    case Nil{}:
      Inr{m}
    case Con{+y, +rest}:
      split_pick(y, rest, b, x, Lemma.or_true_cases(Core.bsrEq(x, y), Core.member(x, List.append(&2, Core.Bsr, rest, b)), m), m2 => member_split(rest, b, x, m2))

def head_pick(+hd: Core.Bsr, +tail: +List<Core.Bsr>, +x: Core.Bsr, +p: Nat, +he: {bIndex(hd) == p : Nat},
  cases: Either<{Core.bsrEq(x, hd) == True{} : Bool}, {Core.member(x, tail) == True{} : Bool}>,
  later: {Core.member(x, tail) == True{} : Bool} -> {bIndex(x) == p : Nat}) -> {bIndex(x) == p : Nat}:
  match cases:
    case Inl{e}:
      Equal.trans(Nat, bIndex(x), bIndex(hd), p, Equal.cong(Core.Bsr, Nat, v => bIndex(v), x, hd, G.bsr_eq_sound(x, hd, e)), he)
    case Inr{m}:
      later(m)

def empty_index(d0: Nat, +p: Nat, +i: Nat, +k: Nat, +x: Core.Bsr, +m: {Core.member(x, Core.emptyAt(d0, p, i, k)) == True{} : Bool}) -> {bIndex(x) == p : Nat}:
  match d0:
    case 0n:
      +hd = {Core.Bsr{p, 0n, i, k, k} : Core.Bsr}
      head_pick(hd, [], x, p, {==}, Lemma.or_true_cases(Core.bsrEq(x, hd), False{}, m), m2 => Empty.absurd({bIndex(x) == p : Nat}, Lemma.false_is_not_true(m2)))
    case 1n+(+e):
      Empty.absurd({bIndex(x) == p : Nat}, Lemma.false_is_not_true(m))

# Every own step of a node of p is a step of p.
law own_index:
  for cs: +List<Core.Tree>
  for +p: Nat
  for +d0: Nat
  for +i: Nat
  for +k: Nat
  for +x: Core.Bsr
  for +m: {Core.member(x, Core.own(p, cs, d0, i, k)) == True{} : Bool}
  {bIndex(x) == p : Nat}

def own_index(cs, p, d0, i, k, x, m):
  match cs:
    case Nil{}:
      empty_index(d0, p, i, k, x, m)
    case Con{+t, +rest}:
      +far = Nat.add(k, Core.width(t))
      +hd = {Core.Bsr{p, 1n+d0, i, k, far} : Core.Bsr}
      +tail = Core.own(p, rest, 1n+d0, i, far)
      head_pick(hd, tail, x, p, {==}, Lemma.or_true_cases(Core.bsrEq(x, hd), Core.member(x, tail), m), m2 => own_index(rest, p, 1n+d0, i, far, x, m2))

law dot_len:
  for +d0: Nat
  for +len: Nat
  for +e: {1n+d0 == Nat.add(d0, 1n+len) : Nat}
  {len == 0n : Nat}

def dot_len(d0, len, e):
  +e1 = Equal.trans(Nat, 1n+d0, Nat.add(d0, 1n+len), 1n+Nat.add(d0, len), e, Lemma.add_succ_right(d0, len))
  +e2 = B.succ_inj(d0, Nat.add(d0, len), e1)
  +e3 = Equal.trans(Nat, Nat.add(d0, 0n), d0, Nat.add(d0, len), Lemma.add_zero_right(d0), e2)
  Equal.sym(Nat, 0n, len, Lemma.add_cancel_left(d0, 0n, len, e3))

def last_pick(+hd: Core.Bsr, +tail: +List<Core.Bsr>, +x: Core.Bsr, +d0: Nat, +len: Nat, +far: Nat, +endHere: Nat,
  +hdot: {bDot(hd) == 1n+d0 : Nat}, +hend: {bEnd(hd) == far : Nat},
  +xd: {bDot(x) == Nat.add(d0, 1n+len) : Nat},
  zeroEnd: {len == 0n : Nat} -> {far == endHere : Nat},
  cases: Either<{Core.bsrEq(x, hd) == True{} : Bool}, {Core.member(x, tail) == True{} : Bool}>,
  later: {Core.member(x, tail) == True{} : Bool} -> {bEnd(x) == endHere : Nat}) -> {bEnd(x) == endHere : Nat}:
  match cases:
    case Inl{e}:
      +same = G.bsr_eq_sound(x, hd, e)
      +dx = Equal.trans(Nat, bDot(x), bDot(hd), 1n+d0, Equal.cong(Core.Bsr, Nat, v => bDot(v), x, hd, same), hdot)
      +lz = dot_len(d0, len, Equal.trans(Nat, 1n+d0, bDot(x), Nat.add(d0, 1n+len), Equal.sym(Nat, bDot(x), 1n+d0, dx), xd))
      Equal.trans(Nat, bEnd(x), far, endHere, Equal.trans(Nat, bEnd(x), bEnd(hd), far, Equal.cong(Core.Bsr, Nat, v => bEnd(v), x, hd, same), hend), zeroEnd(lz))
    case Inr{m}:
      later(m)

def end_head(+hd: Core.Bsr, +x: Core.Bsr, +k: Nat, +he: {bEnd(hd) == k : Nat},
  cases: Either<{Core.bsrEq(x, hd) == True{} : Bool}, {False{} == True{} : Bool}>) -> {bEnd(x) == k : Nat}:
  match cases:
    case Inl{e}:
      Equal.trans(Nat, bEnd(x), bEnd(hd), k, Equal.cong(Core.Bsr, Nat, v => bEnd(v), x, hd, G.bsr_eq_sound(x, hd, e)), he)
    case Inr{m}:
      Empty.absurd({bEnd(x) == k : Nat}, Lemma.false_is_not_true(m))

def empty_end(d0: Nat, +p: Nat, +i: Nat, +k: Nat, +x: Core.Bsr, +m: {Core.member(x, Core.emptyAt(d0, p, i, k)) == True{} : Bool}) -> {bEnd(x) == k : Nat}:
  match d0:
    case 0n:
      +hd = {Core.Bsr{p, 0n, i, k, k} : Core.Bsr}
      end_head(hd, x, k, {==}, Lemma.or_true_cases(Core.bsrEq(x, hd), False{}, m))
    case 1n+(+e):
      Empty.absurd({bEnd(x) == k : Nat}, Lemma.false_is_not_true(m))

def leaf_zero(rest: +List<Core.Tree>, +a: Nat, +k: Nat, +lz: {List.length(&2, Core.Tree, rest) == 0n : Nat}) -> {Nat.add(k, 1n) == G.endOf(Core.Leaf{a} <> rest, k) : Nat}:
  match rest:
    case Nil{}:
      Lemma.add_one_right(k)
    case Con{+t, +r}:
      Empty.absurd({Nat.add(k, 1n) == G.endOf(Core.Leaf{a} <> t <> r, k) : Nat}, B.succ_not_zero(List.length(&2, Core.Tree, r), lz))

def node_zero(rest: +List<Core.Tree>, +q: Nat, +ch: +List<Core.Tree>, +k: Nat, +lz: {List.length(&2, Core.Tree, rest) == 0n : Nat}) -> {Nat.add(k, Core.width(Core.Node{q, ch})) == G.endOf(Core.Node{q, ch} <> rest, k) : Nat}:
  match rest:
    case Nil{}:
      {==}
    case Con{+t, +r}:
      Empty.absurd({Nat.add(k, Core.width(Core.Node{q, ch})) == G.endOf(Core.Node{q, ch} <> t <> r, k) : Nat}, B.succ_not_zero(List.length(&2, Core.Tree, r), lz))

# The own step after the last item of a node ends where the node ends.
law own_last:
  for cs: +List<Core.Tree>
  for +p: Nat
  for +d0: Nat
  for +i: Nat
  for +k: Nat
  for +x: Core.Bsr
  for +m: {Core.member(x, Core.own(p, cs, d0, i, k)) == True{} : Bool}
  for +xd: {bDot(x) == Nat.add(d0, List.length(&2, Core.Tree, cs)) : Nat}
  {bEnd(x) == G.endOf(cs, k) : Nat}

def own_last(cs, p, d0, i, k, x, m, xd):
  match cs:
    case Nil{}:
      empty_end(d0, p, i, k, x, m)
    case Con{Core.Leaf{+a}, +rest}:
      +far = Nat.add(k, 1n)
      +hd = {Core.Bsr{p, 1n+d0, i, k, far} : Core.Bsr}
      +tail = Core.own(p, rest, 1n+d0, i, far)
      +xd2 = Equal.trans(Nat, bDot(x), Nat.add(d0, 1n+List.length(&2, Core.Tree, rest)), Nat.add(1n+d0, List.length(&2, Core.Tree, rest)), xd, Lemma.add_succ_right(d0, List.length(&2, Core.Tree, rest)))
      last_pick(hd, tail, x, d0, List.length(&2, Core.Tree, rest), far, G.endOf(Core.Leaf{a} <> rest, k), {==}, {==}, xd,
        lz => leaf_zero(rest, a, k, lz),
        Lemma.or_true_cases(Core.bsrEq(x, hd), Core.member(x, tail), m),
        m2 => Equal.trans(Nat, bEnd(x), G.endOf(rest, far), G.endOf(rest, 1n+k), own_last(rest, p, 1n+d0, i, far, x, m2, xd2),
          Equal.cong(Nat, Nat, v => G.endOf(rest, v), far, 1n+k, Lemma.add_one_right(k))))
    case Con{Core.Node{+q, +ch}, +rest}:
      +far = Nat.add(k, Core.width(Core.Node{q, ch}))
      +hd = {Core.Bsr{p, 1n+d0, i, k, far} : Core.Bsr}
      +tail = Core.own(p, rest, 1n+d0, i, far)
      +xd2 = Equal.trans(Nat, bDot(x), Nat.add(d0, 1n+List.length(&2, Core.Tree, rest)), Nat.add(1n+d0, List.length(&2, Core.Tree, rest)), xd, Lemma.add_succ_right(d0, List.length(&2, Core.Tree, rest)))
      last_pick(hd, tail, x, d0, List.length(&2, Core.Tree, rest), far, G.endOf(Core.Node{q, ch} <> rest, k), {==}, {==}, xd,
        lz => node_zero(rest, q, ch, k, lz),
        Lemma.or_true_cases(Core.bsrEq(x, hd), Core.member(x, tail), m),
        m2 => own_last(rest, p, 1n+d0, i, far, x, m2, xd2))

# ======== A FOLLOWING TOKEN IS IN FOLLOW ========

# The token after a child of a node of y, at item z, is in FOLLOW of z: what begins the
# items after it, or, when they read nothing, what follows y.
def child_cases(w: +List<Nat>, +ts: +List<Core.Tree>, +rest: +List<Core.Sym>, +z: Nat, +y: Nat, +far: Nat,
  +grammar: +List<Core.Production>, +input: +List<Nat>, +firsts: +List<T.FirstFact>, +follows: +List<T.FollowFact>, +nulls: +List<Nat>,
  +cn: {Sets.nullsClosed(grammar, nulls) == True{} : Bool},
  +cf: {T.firstsClosed(grammar, firsts, nulls) == True{} : Bool},
  +ew: {Core.leaves(ts) == w : +List<Nat>},
  +rt: {Core.reads(ts, grammar, rest, input, far) == True{} : Bool},
  +ftt: {Core.fits(ts, grammar, rest) == True{} : Bool},
  +allF: {T.allFollow(T.firstOfItems(rest, firsts, nulls), z, follows) == True{} : Bool},
  +orP: {Bool.or(Bool.not(Sets.allNull(rest, nulls)), T.allMaybeIn(T.followsOf(y, follows), T.followsOf(z, follows))) == True{} : Bool},
  +pf: {T.followHas(y, Core.tokAt(input, G.endOf(ts, far)), follows) == True{} : Bool})
  -> {T.followHas(z, Core.tokAt(input, far), follows) == True{} : Bool}:
  match w:
    case Nil{}:
      +an = Rule.zero_nulls(ts, rest, grammar, nulls, cn, ftt, ew)
      +sub = B.or_not_true(Sets.allNull(rest, nulls), T.allMaybeIn(T.followsOf(y, follows), T.followsOf(z, follows)), an, orP)
      +endEq = Equal.trans(Nat, G.endOf(ts, far), Nat.add(far, List.length(&2, Nat, Core.leaves(ts))), far, G.end_eq(ts, far),
        Equal.trans(Nat, Nat.add(far, List.length(&2, Nat, Core.leaves(ts))), Nat.add(far, 0n), far,
          Equal.cong(+List<Nat>, Nat, v => Nat.add(far, List.length(&2, Nat, v)), Core.leaves(ts), [], ew), Lemma.add_zero_right(far)))
      +pf2 = {(%endEq : {T.followHas(y, Core.tokAt(input, _), follows) == True{} : Bool}
        pf) : {T.followHas(y, Core.tokAt(input, far), follows) == True{} : Bool}}
      maybe_all_member(T.followsOf(y, follows), T.followsOf(z, follows), Core.tokAt(input, far), sub, pf2)
    case Con{+t, +r}:
      +tok = L.reads_head(ts, rest, grammar, input, far, t, r, rt, ew)
      +ft = first_in(ts, rest, grammar, firsts, nulls, cn, cf, t, r, ftt, ew)
      +fh = all_follow_member(T.firstOfItems(rest, firsts, nulls), z, follows, t, allF, ft)
      %Equal.sym(Maybe<&2, Nat>, Core.tokAt(input, far), Some{t}, tok) : {T.followHas(z, _, follows) == True{} : Bool}
      fh

def child_follow(w: +List<Nat>, +ts: +List<Core.Tree>, +rest: +List<Core.Sym>, +z: Nat, +y: Nat, +far: Nat,
  +grammar: +List<Core.Production>, +input: +List<Nat>, +firsts: +List<T.FirstFact>, +follows: +List<T.FollowFact>, +nulls: +List<Nat>,
  +cn: {Sets.nullsClosed(grammar, nulls) == True{} : Bool},
  +cf: {T.firstsClosed(grammar, firsts, nulls) == True{} : Bool},
  +ew: {Core.leaves(ts) == w : +List<Nat>},
  +rt: {Core.reads(ts, grammar, rest, input, far) == True{} : Bool},
  +item: {Bool.and(T.allFollow(T.firstOfItems(rest, firsts, nulls), z, follows), Bool.or(Bool.not(Sets.allNull(rest, nulls)), T.allMaybeIn(T.followsOf(y, follows), T.followsOf(z, follows)))) == True{} : Bool},
  +pf: {T.followHas(y, Core.tokAt(input, G.endOf(ts, far)), follows) == True{} : Bool})
  -> {T.followHas(z, Core.tokAt(input, far), follows) == True{} : Bool}:
  +allF = {T.allFollow(T.firstOfItems(rest, firsts, nulls), z, follows) : Bool}
  +orP = {Bool.or(Bool.not(Sets.allNull(rest, nulls)), T.allMaybeIn(T.followsOf(y, follows), T.followsOf(z, follows))) : Bool}
  +ftt = D.reads_fits(ts, rest, grammar, input, far, rt)
  child_cases(w, ts, rest, z, y, far, grammar, input, firsts, follows, nulls, cn, cf, ew, rt, ftt, Lemma.and_true_left(allF, orP, item), Lemma.and_true_right_side(allF, orP, item), pf)

def own_follow(+cs: +List<Core.Tree>, +p: Nat, +z: Nat, +k: Nat, +x: Core.Bsr,
  +grammar: +List<Core.Production>, +input: +List<Nat>, +follows: +List<T.FollowFact>,
  +hl: {Core.lhsIs(grammar, p, z) == True{} : Bool},
  +hn: {bDot(x) == List.length(&2, Core.Sym, Core.rhsOf(grammar, bIndex(x))) : Nat},
  +rc: {Core.reads(cs, grammar, Core.rhsOf(grammar, p), input, k) == True{} : Bool},
  +mo: {Core.member(x, Core.own(p, cs, 0n, k, k)) == True{} : Bool},
  +ec: {G.endOf(cs, k) == Nat.add(k, Core.width(Core.Node{p, cs})) : Nat},
  +childFol: {T.followHas(z, Core.tokAt(input, Nat.add(k, Core.width(Core.Node{p, cs}))), follows) == True{} : Bool})
  -> {T.followHas(Gll.lhsOf(grammar, bIndex(x)), Core.tokAt(input, bEnd(x)), follows) == True{} : Bool}:
  +ip = own_index(cs, p, 0n, k, k, x, mo)
  +hn2 = Equal.trans(Nat, bDot(x), List.length(&2, Core.Sym, Core.rhsOf(grammar, bIndex(x))), List.length(&2, Core.Sym, Core.rhsOf(grammar, p)), hn,
    Equal.cong(Nat, Nat, v => List.length(&2, Core.Sym, Core.rhsOf(grammar, v)), bIndex(x), p, ip))
  +xd = Equal.trans(Nat, bDot(x), List.length(&2, Core.Sym, Core.rhsOf(grammar, p)), List.length(&2, Core.Tree, cs), hn2, Equal.sym(Nat, List.length(&2, Core.Tree, cs), List.length(&2, Core.Sym, Core.rhsOf(grammar, p)), P.reads_length(cs, Core.rhsOf(grammar, p), grammar, input, k, rc)))
  +eE = Equal.trans(Nat, bEnd(x), G.endOf(cs, k), Nat.add(k, Core.width(Core.Node{p, cs})), own_last(cs, p, 0n, k, k, x, mo, xd), ec)
  +eL = Equal.trans(Nat, Gll.lhsOf(grammar, bIndex(x)), Gll.lhsOf(grammar, p), z, Equal.cong(Nat, Nat, v => Gll.lhsOf(grammar, v), bIndex(x), p, ip), G.lhs_of(grammar, p, z, hl))
  %Equal.sym(Nat, Gll.lhsOf(grammar, bIndex(x)), z, eL) : {T.followHas(_, Core.tokAt(input, bEnd(x)), follows) == True{} : Bool}
  %Equal.sym(Nat, bEnd(x), Nat.add(k, Core.width(Core.Node{p, cs})), eE) : {T.followHas(z, Core.tokAt(input, _), follows) == True{} : Bool}
  childFol

def inner_split(+cs: +List<Core.Tree>, +ts: +List<Core.Tree>, +p: Nat, +k: Nat, +x: Core.Bsr,
  +grammar: +List<Core.Production>, +input: +List<Nat>, +follows: +List<T.FollowFact>,
  cases: Either<{Core.member(x, Core.steps(cs, k)) == True{} : Bool}, {Core.member(x, Core.steps(ts, Nat.add(k, Core.width(Core.Node{p, cs})))) == True{} : Bool}>,
  down: {Core.member(x, Core.steps(cs, k)) == True{} : Bool} -> {T.followHas(Gll.lhsOf(grammar, bIndex(x)), Core.tokAt(input, bEnd(x)), follows) == True{} : Bool},
  along: {Core.member(x, Core.steps(ts, Nat.add(k, Core.width(Core.Node{p, cs})))) == True{} : Bool} -> {T.followHas(Gll.lhsOf(grammar, bIndex(x)), Core.tokAt(input, bEnd(x)), follows) == True{} : Bool})
  -> {T.followHas(Gll.lhsOf(grammar, bIndex(x)), Core.tokAt(input, bEnd(x)), follows) == True{} : Bool}:
  match cases:
    case Inl{m}:
      down(m)
    case Inr{m}:
      along(m)

def node_split(+cs: +List<Core.Tree>, +ts: +List<Core.Tree>, +p: Nat, +z: Nat, +k: Nat, +x: Core.Bsr,
  +grammar: +List<Core.Production>, +input: +List<Nat>, +follows: +List<T.FollowFact>,
  +hl: {Core.lhsIs(grammar, p, z) == True{} : Bool},
  +hn: {bDot(x) == List.length(&2, Core.Sym, Core.rhsOf(grammar, bIndex(x))) : Nat},
  +rc: {Core.reads(cs, grammar, Core.rhsOf(grammar, p), input, k) == True{} : Bool},
  +ec: {G.endOf(cs, k) == Nat.add(k, Core.width(Core.Node{p, cs})) : Nat},
  +childFol: {T.followHas(z, Core.tokAt(input, Nat.add(k, Core.width(Core.Node{p, cs}))), follows) == True{} : Bool},
  cases: Either<{Core.member(x, Core.own(p, cs, 0n, k, k)) == True{} : Bool}, {Core.member(x, List.append(&2, Core.Bsr, Core.steps(cs, k), Core.steps(ts, Nat.add(k, Core.width(Core.Node{p, cs}))))) == True{} : Bool}>,
  down: {Core.member(x, Core.steps(cs, k)) == True{} : Bool} -> {T.followHas(Gll.lhsOf(grammar, bIndex(x)), Core.tokAt(input, bEnd(x)), follows) == True{} : Bool},
  along: {Core.member(x, Core.steps(ts, Nat.add(k, Core.width(Core.Node{p, cs})))) == True{} : Bool} -> {T.followHas(Gll.lhsOf(grammar, bIndex(x)), Core.tokAt(input, bEnd(x)), follows) == True{} : Bool})
  -> {T.followHas(Gll.lhsOf(grammar, bIndex(x)), Core.tokAt(input, bEnd(x)), follows) == True{} : Bool}:
  match cases:
    case Inl{+mo}:
      own_follow(cs, p, z, k, x, grammar, input, follows, hl, hn, rc, mo, ec, childFol)
    case Inr{+mr}:
      inner_split(cs, ts, p, k, x, grammar, input, follows, member_split(Core.steps(cs, k), Core.steps(ts, Nat.add(k, Core.width(Core.Node{p, cs}))), x, mr), down, along)

# Walking down a parse tree: every node's last step is followed by a token of FOLLOW of
# its nonterminal.
law follow_walk:
  for fs: +List<Core.Tree>
  for items: +List<Core.Sym>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +firsts: +List<T.FirstFact>
  for +follows: +List<T.FollowFact>
  for +nulls: +List<Nat>
  for +k: Nat
  for +y: Nat
  for +x: Core.Bsr
  for +cn: {Sets.nullsClosed(grammar, nulls) == True{} : Bool}
  for +cf: {T.firstsClosed(grammar, firsts, nulls) == True{} : Bool}
  for +cfo: {T.followsClosed(grammar, firsts, follows, nulls) == True{} : Bool}
  for +hn: {bDot(x) == List.length(&2, Core.Sym, Core.rhsOf(grammar, bIndex(x))) : Nat}
  for +rd: {Core.reads(fs, grammar, items, input, k) == True{} : Bool}
  for +pf: {T.followHas(y, Core.tokAt(input, G.endOf(fs, k)), follows) == True{} : Bool}
  for +sk: {T.suffixOk(items, y, firsts, follows, nulls) == True{} : Bool}
  for +m: {Core.member(x, Core.steps(fs, k)) == True{} : Bool}
  {T.followHas(Gll.lhsOf(grammar, bIndex(x)), Core.tokAt(input, bEnd(x)), follows) == True{} : Bool}

def follow_walk(fs, items, grammar, input, firsts, follows, nulls, k, y, x, cn, cf, cfo, hn, rd, pf, sk, m):
  match fs items:
    case Nil{} +its:
      Empty.absurd({T.followHas(Gll.lhsOf(grammar, bIndex(x)), Core.tokAt(input, bEnd(x)), follows) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{Core.Leaf{+a}, +ts} Con{Core.Terminal{+tk}, +rest}:
      +more = {Bool.and(Core.tokIs(Core.tokAt(input, k), a), Core.reads(ts, grammar, rest, input, 1n+k)) : Bool}
      +rt = Lemma.and_true_right_side(Core.tokIs(Core.tokAt(input, k), a), Core.reads(ts, grammar, rest, input, 1n+k), Lemma.and_true_right_side(Nat.is_eq(a, tk), more, rd))
      follow_walk(ts, rest, grammar, input, firsts, follows, nulls, 1n+k, y, x, cn, cf, cfo, hn, rt, pf, Lemma.and_true_right_side(True{}, T.suffixOk(rest, y, firsts, follows, nulls), sk), m)
    case Con{Core.Leaf{+a}, +ts} Nil{}:
      Empty.absurd({T.followHas(Gll.lhsOf(grammar, bIndex(x)), Core.tokAt(input, bEnd(x)), follows) == True{} : Bool}, Lemma.false_is_not_true(rd))
    case Con{Core.Leaf{+a}, +ts} Con{Core.Nonterminal{+z, +need}, +rest}:
      Empty.absurd({T.followHas(Gll.lhsOf(grammar, bIndex(x)), Core.tokAt(input, bEnd(x)), follows) == True{} : Bool}, Lemma.false_is_not_true(rd))
    case Con{Core.Node{+p, +cs}, +ts} Nil{}:
      Empty.absurd({T.followHas(Gll.lhsOf(grammar, bIndex(x)), Core.tokAt(input, bEnd(x)), follows) == True{} : Bool}, Lemma.false_is_not_true(rd))
    case Con{Core.Node{+p, +cs}, +ts} Con{Core.Terminal{+tk}, +rest}:
      Empty.absurd({T.followHas(Gll.lhsOf(grammar, bIndex(x)), Core.tokAt(input, bEnd(x)), follows) == True{} : Bool}, Lemma.false_is_not_true(rd))
    case Con{Core.Node{+p, +cs}, +ts} Con{Core.Nonterminal{+z, +need}, +rest}:
      +far = Nat.add(k, Core.width(Core.Node{p, cs}))
      +head = {Bool.and(Core.lhsIs(grammar, p, z), Core.needOk(need, Core.width(Core.Node{p, cs}))) : Bool}
      +own = {Bool.and(head, Core.reads(cs, grammar, Core.rhsOf(grammar, p), input, k)) : Bool}
      +after = {Core.reads(ts, grammar, rest, input, far) : Bool}
      +left = Lemma.and_true_left(own, after, rd)
      +hl = Lemma.and_true_left(Core.lhsIs(grammar, p, z), Core.needOk(need, Core.width(Core.Node{p, cs})), Lemma.and_true_left(head, Core.reads(cs, grammar, Core.rhsOf(grammar, p), input, k), left))
      +rc = Lemma.and_true_right_side(head, Core.reads(cs, grammar, Core.rhsOf(grammar, p), input, k), left)
      +rt = Lemma.and_true_right_side(own, after, rd)
      +item = {T.itemOk(Core.Nonterminal{z, need}, rest, y, firsts, follows, nulls) : Bool}
      +skt = Lemma.and_true_right_side(item, T.suffixOk(rest, y, firsts, follows, nulls), sk)
      +hi = Lemma.and_true_left(item, T.suffixOk(rest, y, firsts, follows, nulls), sk)
      +childFol = child_follow(Core.leaves(ts), ts, rest, z, y, far, grammar, input, firsts, follows, nulls, cn, cf, {==}, rt, hi, pf)
      +ec = Equal.trans(Nat, G.endOf(cs, k), Nat.add(k, List.length(&2, Nat, Core.leaves(cs))), far, G.end_eq(cs, k),
        Equal.cong(+List<Nat>, Nat, v => Nat.add(k, List.length(&2, Nat, v)), Core.leaves(cs), List.append(&2, Nat, Core.leaves(cs), []), Equal.sym(+List<Nat>, List.append(&2, Nat, Core.leaves(cs), []), Core.leaves(cs), Lemma.append_nil_right(Core.leaves(cs)))))
      +pfc = {(%Equal.sym(Nat, G.endOf(cs, k), far, ec) : {T.followHas(z, Core.tokAt(input, _), follows) == True{} : Bool}
        childFol) : {T.followHas(z, Core.tokAt(input, G.endOf(cs, k)), follows) == True{} : Bool}}
      +skc = follow_closed_at(grammar, p, z, firsts, follows, nulls, cfo, hl)
      node_split(cs, ts, p, z, k, x, grammar, input, follows, hl, hn, rc, ec, childFol,
        member_split(Core.own(p, cs, 0n, k, k), List.append(&2, Core.Bsr, Core.steps(cs, k), Core.steps(ts, far)), x, m),
        mc => follow_walk(cs, Core.rhsOf(grammar, p), grammar, input, firsts, follows, nulls, k, z, x, cn, cf, cfo, hn, rc, pfc, skc, mc),
        mt => follow_walk(ts, rest, grammar, input, firsts, follows, nulls, far, y, x, cn, cf, cfo, hn, rt, pf, skt, mt))

# ======== WHAT A PRODUCTION PREDICTS IS IN ITS PREDICT SET ========

def first_branch(+grammar: +List<Core.Production>, +firsts: +List<T.FirstFact>, +follows: +List<T.FollowFact>, +nulls: +List<Nat>, +q: Nat, +next: Maybe<&2, Nat>,
  +cn: {Sets.nullsClosed(grammar, nulls) == True{} : Bool},
  +cf: {T.firstsClosed(grammar, firsts, nulls) == True{} : Bool},
  fi: LL.FirstIs(grammar, Core.rhsOf(grammar, q), next))
  -> {T.maybeIn(next, T.predictOf(Gll.lhsOf(grammar, q), Core.rhsOf(grammar, q), firsts, follows, nulls)) == True{} : Bool}:
  match fi:
    case (f0, (t0, (r0, (fit0, (lv0, ne0))))):
      +f = f0
      +t = t0
      +r = r0
      +fit = {fit0 : {Core.fits(f, grammar, Core.rhsOf(grammar, q)) == True{} : Bool}}
      +lv = {lv0 : {Core.leaves(f) == t <> r : +List<Nat>}}
      +ne = {ne0 : {next == Some{t} : Maybe<&2, Nat>}}
      +rhs = Core.rhsOf(grammar, q)
      +inF = some_in(T.firstOfItems(rhs, firsts, nulls), t, first_in(f, rhs, grammar, firsts, nulls, cn, cf, t, r, fit, lv))
      %Equal.sym(Maybe<&2, Nat>, next, Some{t}, ne) : {T.maybeIn(_, T.predictOf(Gll.lhsOf(grammar, q), rhs, firsts, follows, nulls)) == True{} : Bool}
      maybe_join_left(T.someAll(T.firstOfItems(rhs, firsts, nulls)), T.maybesIf(Sets.allNull(rhs, nulls), T.followsOf(Gll.lhsOf(grammar, q), follows)), Some{t}, inF)

def follow_pt(+grammar: +List<Core.Production>, +start: Nat, +firsts: +List<T.FirstFact>, +follows: +List<T.FollowFact>, +nulls: +List<Nat>, +q: Nat, +next: Maybe<&2, Nat>,
  +input: +List<Nat>, +tree: Core.Tree, +i: Nat, +k: Nat, +j: Nat,
  +cn: {Sets.nullsClosed(grammar, nulls) == True{} : Bool},
  +cf: {T.firstsClosed(grammar, firsts, nulls) == True{} : Bool},
  +cfo: {T.followsClosed(grammar, firsts, follows, nulls) == True{} : Bool},
  +cs: {T.followHas(start, None{}, follows) == True{} : Bool},
  +cr: {T.suffixOk([Core.Nonterminal{start, Core.Anything{}}], start, firsts, follows, nulls) == True{} : Bool},
  +mm: {Core.member(Core.Bsr{q, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), i, k, j}, Core.steps([tree], 0n)) == True{} : Bool},
  +tk: {Core.tokAt(input, j) == next : Maybe<&2, Nat>},
  pt: Core.ParseTree(grammar, start, input, tree)) -> {T.followHas(Gll.lhsOf(grammar, q), next, follows) == True{} : Bool}:
  match pt:
    case (rr0, rl0):
      +rr = rr0
      +rl = {rl0 : {List.length(&2, Nat, Core.leaves([tree])) == List.length(&2, Nat, input) : Nat}}
      +e1 = Equal.trans(Nat, G.endOf([tree], 0n), List.length(&2, Nat, Core.leaves([tree])), List.length(&2, Nat, input), G.end_eq([tree], 0n), rl)
      +te = Equal.trans(Maybe<&2, Nat>, Core.tokAt(input, G.endOf([tree], 0n)), Core.tokAt(input, List.length(&2, Nat, input)), None{},
        Equal.cong(Nat, Maybe<&2, Nat>, v => Core.tokAt(input, v), G.endOf([tree], 0n), List.length(&2, Nat, input), e1), tok_end(input))
      +pf0 = {(%Equal.sym(Maybe<&2, Nat>, Core.tokAt(input, G.endOf([tree], 0n)), None{}, te) : {T.followHas(start, _, follows) == True{} : Bool}
        cs) : {T.followHas(start, Core.tokAt(input, G.endOf([tree], 0n)), follows) == True{} : Bool}}
      +x = {Core.Bsr{q, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), i, k, j} : Core.Bsr}
      +fw = follow_walk([tree], [Core.Nonterminal{start, Core.Anything{}}], grammar, input, firsts, follows, nulls, 0n, start, x, cn, cf, cfo, {==}, rr, pf0, cr, mm)
      %tk : {T.followHas(Gll.lhsOf(grammar, q), _, follows) == True{} : Bool}
      fw

def follow_tree(+grammar: +List<Core.Production>, +start: Nat, +firsts: +List<T.FirstFact>, +follows: +List<T.FollowFact>, +nulls: +List<Nat>, +q: Nat, +next: Maybe<&2, Nat>,
  +cn: {Sets.nullsClosed(grammar, nulls) == True{} : Bool},
  +cf: {T.firstsClosed(grammar, firsts, nulls) == True{} : Bool},
  +cfo: {T.followsClosed(grammar, firsts, follows, nulls) == True{} : Bool},
  +cs: {T.followHas(start, None{}, follows) == True{} : Bool},
  +cr: {T.suffixOk([Core.Nonterminal{start, Core.Anything{}}], start, firsts, follows, nulls) == True{} : Bool},
  fol: LL.FollowIs(grammar, start, q, next)) -> {T.followHas(Gll.lhsOf(grammar, q), next, follows) == True{} : Bool}:
  match fol:
    case (input0, (tree0, (i0, (k0, (j0, (pt, (mm0, tk0))))))):
      follow_pt(grammar, start, firsts, follows, nulls, q, next, input0, tree0, i0, k0, j0, cn, cf, cfo, cs, cr, mm0, tk0, pt)

def null_branch(+grammar: +List<Core.Production>, +firsts: +List<T.FirstFact>, +follows: +List<T.FollowFact>, +nulls: +List<Nat>, +q: Nat, +next: Maybe<&2, Nat>,
  +cn: {Sets.nullsClosed(grammar, nulls) == True{} : Bool},
  +fh: {T.followHas(Gll.lhsOf(grammar, q), next, follows) == True{} : Bool},
  nul: LL.Nullable(grammar, Core.rhsOf(grammar, q)))
  -> {T.maybeIn(next, T.predictOf(Gll.lhsOf(grammar, q), Core.rhsOf(grammar, q), firsts, follows, nulls)) == True{} : Bool}:
  match nul:
    case (f0, (fit0, lv0)):
      +rhs = Core.rhsOf(grammar, q)
      +an = Rule.zero_nulls(f0, rhs, grammar, nulls, cn, fit0, lv0)
      maybe_join_right(T.someAll(T.firstOfItems(rhs, firsts, nulls)), T.maybesIf(Sets.allNull(rhs, nulls), T.followsOf(Gll.lhsOf(grammar, q), follows)), next,
        maybes_if_true(Sets.allNull(rhs, nulls), T.followsOf(Gll.lhsOf(grammar, q), follows), next, an, fh))

def follow_branch(+grammar: +List<Core.Production>, +start: Nat, +firsts: +List<T.FirstFact>, +follows: +List<T.FollowFact>, +nulls: +List<Nat>, +q: Nat, +next: Maybe<&2, Nat>,
  +cn: {Sets.nullsClosed(grammar, nulls) == True{} : Bool},
  +cf: {T.firstsClosed(grammar, firsts, nulls) == True{} : Bool},
  +cfo: {T.followsClosed(grammar, firsts, follows, nulls) == True{} : Bool},
  +cs: {T.followHas(start, None{}, follows) == True{} : Bool},
  +cr: {T.suffixOk([Core.Nonterminal{start, Core.Anything{}}], start, firsts, follows, nulls) == True{} : Bool},
  nf: LL.Nullable(grammar, Core.rhsOf(grammar, q)) & LL.FollowIs(grammar, start, q, next))
  -> {T.maybeIn(next, T.predictOf(Gll.lhsOf(grammar, q), Core.rhsOf(grammar, q), firsts, follows, nulls)) == True{} : Bool}:
  match nf:
    case (nul, fol):
      +fh = follow_tree(grammar, start, firsts, follows, nulls, q, next, cn, cf, cfo, cs, cr, fol)
      null_branch(grammar, firsts, follows, nulls, q, next, cn, fh, nul)

law predicts_in:
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +firsts: +List<T.FirstFact>
  for +follows: +List<T.FollowFact>
  for +nulls: +List<Nat>
  for +q: Nat
  for +next: Maybe<&2, Nat>
  for +cn: {Sets.nullsClosed(grammar, nulls) == True{} : Bool}
  for +cf: {T.firstsClosed(grammar, firsts, nulls) == True{} : Bool}
  for +cfo: {T.followsClosed(grammar, firsts, follows, nulls) == True{} : Bool}
  for +cs: {T.followHas(start, None{}, follows) == True{} : Bool}
  for +cr: {T.suffixOk([Core.Nonterminal{start, Core.Anything{}}], start, firsts, follows, nulls) == True{} : Bool}
  for p: LL.Predicts(grammar, start, q, next)
  {T.maybeIn(next, T.predictOf(Gll.lhsOf(grammar, q), Core.rhsOf(grammar, q), firsts, follows, nulls)) == True{} : Bool}

def predicts_in(grammar, start, firsts, follows, nulls, q, next, cn, cf, cfo, cs, cr, p):
  match p:
    case Inl{fi}:
      first_branch(grammar, firsts, follows, nulls, q, next, cn, cf, fi)
    case Inr{nf}:
      follow_branch(grammar, start, firsts, follows, nulls, q, next, cn, cf, cfo, cs, cr, nf)

# ======== THE PAIRS ========

def Pred(+g: +List<Core.Production>, +q: Nat, +firsts: +List<T.FirstFact>, +follows: +List<T.FollowFact>, +nulls: +List<Nat>) -> +List<Maybe<&2, Nat>>:
  T.predictOf(Gll.lhsOf(g, q), Core.rhsOf(g, q), firsts, follows, nulls)

law later_at:
  for prods: +List<Core.Production>
  for m: Nat
  for +x: Nat
  for +rhs: +List<Core.Sym>
  for +firsts: +List<T.FirstFact>
  for +follows: +List<T.FollowFact>
  for +nulls: +List<Nat>
  for +al: {T.againstLater(prods, x, rhs, firsts, follows, nulls) == True{} : Bool}
  for +hl: {Core.lhsIs(prods, m, x) == True{} : Bool}
  {T.disjoint(T.predictOf(x, rhs, firsts, follows, nulls), Pred(prods, m, firsts, follows, nulls)) == True{} : Bool}

def later_at(prods, m, x, rhs, firsts, follows, nulls, al, hl):
  match prods m:
    case Nil{} +m0:
      Empty.absurd({T.disjoint(T.predictOf(x, rhs, firsts, follows, nulls), Pred([], m0, firsts, follows, nulls)) == True{} : Bool}, Lemma.false_is_not_true(hl))
    case Con{Core.Production{+l2, +r2}, +rest} 0n:
      +d = {T.disjoint(T.predictOf(x, rhs, firsts, follows, nulls), T.predictOf(l2, r2, firsts, follows, nulls)) : Bool}
      B.or_not_true(Nat.is_eq(l2, x), d, hl, Lemma.and_true_left(Bool.or(Bool.not(Nat.is_eq(l2, x)), d), T.againstLater(rest, x, rhs, firsts, follows, nulls), al))
    case Con{Core.Production{+l2, +r2}, +rest} 1n+(+m2):
      +d = {T.disjoint(T.predictOf(x, rhs, firsts, follows, nulls), T.predictOf(l2, r2, firsts, follows, nulls)) : Bool}
      later_at(rest, m2, x, rhs, firsts, follows, nulls, Lemma.and_true_right_side(Bool.or(Bool.not(Nat.is_eq(l2, x)), d), T.againstLater(rest, x, rhs, firsts, follows, nulls), al), hl)

def Apart(+g: +List<Core.Production>, +q1: Nat, +q2: Nat, +firsts: +List<T.FirstFact>, +follows: +List<T.FollowFact>, +nulls: +List<Nat>) -> Type:
  Either<{T.disjoint(Pred(g, q1, firsts, follows, nulls), Pred(g, q2, firsts, follows, nulls)) == True{} : Bool}, {T.disjoint(Pred(g, q2, firsts, follows, nulls), Pred(g, q1, firsts, follows, nulls)) == True{} : Bool}>

law pairs_at:
  for g: +List<Core.Production>
  for q1: Nat
  for q2: Nat
  for +x: Nat
  for +firsts: +List<T.FirstFact>
  for +follows: +List<T.FollowFact>
  for +nulls: +List<Nat>
  for +po: {T.pairsOk(g, firsts, follows, nulls) == True{} : Bool}
  for +h1: {Core.lhsIs(g, q1, x) == True{} : Bool}
  for +h2: {Core.lhsIs(g, q2, x) == True{} : Bool}
  for +neq: {Nat.is_eq(q1, q2) == False{} : Bool}
  Apart(g, q1, q2, firsts, follows, nulls)

def pairs_at(g, q1, q2, x, firsts, follows, nulls, po, h1, h2, neq):
  match g q1 q2:
    case Nil{} +a +b:
      Empty.absurd(Apart([], a, b, firsts, follows, nulls), Lemma.false_is_not_true(h1))
    case Con{Core.Production{+l, +r}, +rest} 0n 0n:
      Empty.absurd(Apart(Core.Production{l, r} <> rest, 0n, 0n, firsts, follows, nulls), Lemma.true_is_not_false(neq))
    case Con{Core.Production{+l, +r}, +rest} 0n 1n+(+m):
      +al = Lemma.and_true_left(T.againstLater(rest, l, r, firsts, follows, nulls), T.pairsOk(rest, firsts, follows, nulls), po)
      +lx = Lemma.nat_eq_sound(l, x, h1)
      +h2l = {(%Equal.sym(Nat, l, x, lx) : {Core.lhsIs(rest, m, _) == True{} : Bool}
        h2) : {Core.lhsIs(rest, m, l) == True{} : Bool}}
      Inl{later_at(rest, m, l, r, firsts, follows, nulls, al, h2l)}
    case Con{Core.Production{+l, +r}, +rest} 1n+(+m) 0n:
      +al = Lemma.and_true_left(T.againstLater(rest, l, r, firsts, follows, nulls), T.pairsOk(rest, firsts, follows, nulls), po)
      +lx = Lemma.nat_eq_sound(l, x, h2)
      +h1l = {(%Equal.sym(Nat, l, x, lx) : {Core.lhsIs(rest, m, _) == True{} : Bool}
        h1) : {Core.lhsIs(rest, m, l) == True{} : Bool}}
      Inr{later_at(rest, m, l, r, firsts, follows, nulls, al, h1l)}
    case Con{Core.Production{+l, +r}, +rest} 1n+(+m1) 1n+(+m2):
      pairs_at(rest, m1, m2, x, firsts, follows, nulls, Lemma.and_true_right_side(T.againstLater(rest, l, r, firsts, follows, nulls), T.pairsOk(rest, firsts, follows, nulls), po), h1, h2, neq)

# ======== THE LAW ========

def apart_no(+g: +List<Core.Production>, +q1: Nat, +q2: Nat, +firsts: +List<T.FirstFact>, +follows: +List<T.FollowFact>, +nulls: +List<Nat>, +next: Maybe<&2, Nat>,
  ap: Apart(g, q1, q2, firsts, follows, nulls),
  +m1: {T.maybeIn(next, Pred(g, q1, firsts, follows, nulls)) == True{} : Bool},
  +m2: {T.maybeIn(next, Pred(g, q2, firsts, follows, nulls)) == True{} : Bool}) -> Empty:
  match ap:
    case Inl{d}:
      disjoint_no(Pred(g, q1, firsts, follows, nulls), Pred(g, q2, firsts, follows, nulls), next, d, m1, m2)
    case Inr{d}:
      disjoint_no(Pred(g, q2, firsts, follows, nulls), Pred(g, q1, firsts, follows, nulls), next, d, m2, m1)

def sound_pair(+grammar: +List<Core.Production>, +start: Nat, +nulls: +List<Nat>, +firsts: +List<T.FirstFact>, +follows: +List<T.FollowFact>,
  +x: Nat, +q1: Nat, +q2: Nat, +next: Maybe<&2, Nat>,
  +ok: {T.checkWith(grammar, start, nulls, firsts, follows) == True{} : Bool},
  +neq: {Nat.is_eq(q1, q2) == False{} : Bool},
  +l1: {Core.lhsIs(grammar, q1, x) == True{} : Bool},
  +l2: {Core.lhsIs(grammar, q2, x) == True{} : Bool},
  p1: LL.Predicts(grammar, start, q1, next),
  p2: LL.Predicts(grammar, start, q2, next)) -> Empty:
  +a1 = {Sets.nullsClosed(grammar, nulls) : Bool}
  +a2 = {T.firstsClosed(grammar, firsts, nulls) : Bool}
  +a3 = {T.followsClosed(grammar, firsts, follows, nulls) : Bool}
  +a4 = {T.followHas(start, None{}, follows) : Bool}
  +a5 = {T.suffixOk([Core.Nonterminal{start, Core.Anything{}}], start, firsts, follows, nulls) : Bool}
  +a6 = {T.pairsOk(grammar, firsts, follows, nulls) : Bool}
  +r1 = Lemma.and_true_right_side(a1, Bool.and(a2, Bool.and(a3, Bool.and(a4, Bool.and(a5, a6)))), ok)
  +r2 = Lemma.and_true_right_side(a2, Bool.and(a3, Bool.and(a4, Bool.and(a5, a6))), r1)
  +r3 = Lemma.and_true_right_side(a3, Bool.and(a4, Bool.and(a5, a6)), r2)
  +r4 = Lemma.and_true_right_side(a4, Bool.and(a5, a6), r3)
  +cn = Lemma.and_true_left(a1, Bool.and(a2, Bool.and(a3, Bool.and(a4, Bool.and(a5, a6)))), ok)
  +cf = Lemma.and_true_left(a2, Bool.and(a3, Bool.and(a4, Bool.and(a5, a6))), r1)
  +cfo = Lemma.and_true_left(a3, Bool.and(a4, Bool.and(a5, a6)), r2)
  +cs = Lemma.and_true_left(a4, Bool.and(a5, a6), r3)
  +cr = Lemma.and_true_left(a5, a6, r4)
  +po = Lemma.and_true_right_side(a5, a6, r4)
  +m1 = predicts_in(grammar, start, firsts, follows, nulls, q1, next, cn, cf, cfo, cs, cr, p1)
  +m2 = predicts_in(grammar, start, firsts, follows, nulls, q2, next, cn, cf, cfo, cs, cr, p2)
  apart_no(grammar, q1, q2, firsts, follows, nulls, next, pairs_at(grammar, q1, q2, x, firsts, follows, nulls, po, l1, l2, neq), m1, m2)

def sound_with(+grammar: +List<Core.Production>, +start: Nat, +nulls: +List<Nat>, +firsts: +List<T.FirstFact>, +follows: +List<T.FollowFact>,
  +ok: {T.checkWith(grammar, start, nulls, firsts, follows) == True{} : Bool}) -> LL.LL1(grammar, start):
  x => q1 => q2 => next => neq => l1 => l2 => p1 => p2 => sound_pair(grammar, start, nulls, firsts, follows, x, q1, q2, next, ok, neq, l1, l2, p1, p2)

# LL(1) BY THE TABLES IS LL(1): when the check finds no conflict in the tables, no two
# productions of one nonterminal can begin with the same next token.
law tables_ll1_sound:
  for fuel: Nat
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +ok: {T.ll1ByTables(fuel, grammar, start) == True{} : Bool}
  LL.LL1(grammar, start)

def tables_ll1_sound(fuel, grammar, start, ok):
  +f = fuel
  +nulls = Sets.growNulls(f, grammar, [])
  +firsts = T.growFirsts(f, grammar, nulls, [])
  +follows = T.growFollows(f, grammar, firsts, nulls, [T.FollowFact{start, None{}}])
  sound_with(grammar, start, nulls, firsts, follows, ok)

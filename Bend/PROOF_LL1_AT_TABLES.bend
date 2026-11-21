import Base
import ./LEMMAS.bend as Lemma
import ./PROOF_BASICS.bend as B
import ./CORE.bend as Core
import ./GLL.bend as Gll
import ./SETS.bend as Sets
import ./LL1.bend as LL
import ./TABLES.bend as T
import ./PREDICT.bend as Pr
import ./PROOF_TABLES.bend as PT
import ./PROOF_PREDICT.bend as PP

# LL(1) AT ONE NONTERMINAL, FOR PARTIALLY LL(1) GRAMMARS (TABLES.bend, `ll1AtByTables`).
# When the tables are closed and no two productions of x predict a common token, x is LL(1)
# (`tables_ll1_at`); and prediction with those tables admits at most one production of x
# for any next token, so at most one is seeded per cluster of x (`seeds_one_at`).

# ======== THE PAIRS OF x ========

law pairs_at_x:
  for g: +List<Core.Production>
  for q1: Nat
  for q2: Nat
  for +x: Nat
  for +firsts: +List<T.FirstFact>
  for +follows: +List<T.FollowFact>
  for +nulls: +List<Nat>
  for +pa: {T.pairsAt(g, x, firsts, follows, nulls) == True{} : Bool}
  for +h1: {Core.lhsIs(g, q1, x) == True{} : Bool}
  for +h2: {Core.lhsIs(g, q2, x) == True{} : Bool}
  for +neq: {Nat.is_eq(q1, q2) == False{} : Bool}
  PT.Apart(g, q1, q2, firsts, follows, nulls)

def pairs_at_x(g, q1, q2, x, firsts, follows, nulls, pa, h1, h2, neq):
  match g q1 q2:
    case Nil{} +a +b:
      Empty.absurd(PT.Apart([], a, b, firsts, follows, nulls), Lemma.false_is_not_true(h1))
    case Con{Core.Production{+l, +r}, +rest} 0n 0n:
      Empty.absurd(PT.Apart(Core.Production{l, r} <> rest, 0n, 0n, firsts, follows, nulls), Lemma.true_is_not_false(neq))
    case Con{Core.Production{+l, +r}, +rest} 0n 1n+(+m):
      +AL = {T.againstLater(rest, l, r, firsts, follows, nulls) : Bool}
      +al = B.or_not_true(Nat.is_eq(l, x), AL, h1, Lemma.and_true_left(Bool.or(Bool.not(Nat.is_eq(l, x)), AL), T.pairsAt(rest, x, firsts, follows, nulls), pa))
      +lx = Lemma.nat_eq_sound(l, x, h1)
      +h2l = {(%Equal.sym(Nat, l, x, lx) : {Core.lhsIs(rest, m, _) == True{} : Bool}
        h2) : {Core.lhsIs(rest, m, l) == True{} : Bool}}
      Inl{PT.later_at(rest, m, l, r, firsts, follows, nulls, al, h2l)}
    case Con{Core.Production{+l, +r}, +rest} 1n+(+m) 0n:
      +AL = {T.againstLater(rest, l, r, firsts, follows, nulls) : Bool}
      +al = B.or_not_true(Nat.is_eq(l, x), AL, h2, Lemma.and_true_left(Bool.or(Bool.not(Nat.is_eq(l, x)), AL), T.pairsAt(rest, x, firsts, follows, nulls), pa))
      +lx = Lemma.nat_eq_sound(l, x, h2)
      +h1l = {(%Equal.sym(Nat, l, x, lx) : {Core.lhsIs(rest, m, _) == True{} : Bool}
        h1) : {Core.lhsIs(rest, m, l) == True{} : Bool}}
      Inr{PT.later_at(rest, m, l, r, firsts, follows, nulls, al, h1l)}
    case Con{Core.Production{+l, +r}, +rest} 1n+(+m1) 1n+(+m2):
      +AL = {T.againstLater(rest, l, r, firsts, follows, nulls) : Bool}
      pairs_at_x(rest, m1, m2, x, firsts, follows, nulls, Lemma.and_true_right_side(Bool.or(Bool.not(Nat.is_eq(l, x)), AL), T.pairsAt(rest, x, firsts, follows, nulls), pa), h1, h2, neq)

# ======== LL(1) AT x ========

def sound_pair_at(+grammar: +List<Core.Production>, +start: Nat, +nulls: +List<Nat>, +firsts: +List<T.FirstFact>, +follows: +List<T.FollowFact>,
  +x: Nat, +q1: Nat, +q2: Nat, +next: Maybe<&2, Nat>,
  +ok: {T.checkAt(grammar, start, nulls, firsts, follows, x) == True{} : Bool},
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
  +a6 = {T.pairsAt(grammar, x, firsts, follows, nulls) : Bool}
  +r1 = Lemma.and_true_right_side(a1, Bool.and(a2, Bool.and(a3, Bool.and(a4, Bool.and(a5, a6)))), ok)
  +r2 = Lemma.and_true_right_side(a2, Bool.and(a3, Bool.and(a4, Bool.and(a5, a6))), r1)
  +r3 = Lemma.and_true_right_side(a3, Bool.and(a4, Bool.and(a5, a6)), r2)
  +r4 = Lemma.and_true_right_side(a4, Bool.and(a5, a6), r3)
  +cn = Lemma.and_true_left(a1, Bool.and(a2, Bool.and(a3, Bool.and(a4, Bool.and(a5, a6)))), ok)
  +cf = Lemma.and_true_left(a2, Bool.and(a3, Bool.and(a4, Bool.and(a5, a6))), r1)
  +cfo = Lemma.and_true_left(a3, Bool.and(a4, Bool.and(a5, a6)), r2)
  +cs = Lemma.and_true_left(a4, Bool.and(a5, a6), r3)
  +cr = Lemma.and_true_left(a5, a6, r4)
  +pa = Lemma.and_true_right_side(a5, a6, r4)
  +m1 = PT.predicts_in(grammar, start, firsts, follows, nulls, q1, next, cn, cf, cfo, cs, cr, p1)
  +m2 = PT.predicts_in(grammar, start, firsts, follows, nulls, q2, next, cn, cf, cfo, cs, cr, p2)
  PT.apart_no(grammar, q1, q2, firsts, follows, nulls, next, pairs_at_x(grammar, q1, q2, x, firsts, follows, nulls, pa, l1, l2, neq), m1, m2)

def sound_at(+grammar: +List<Core.Production>, +start: Nat, +nulls: +List<Nat>, +firsts: +List<T.FirstFact>, +follows: +List<T.FollowFact>, +x: Nat,
  +ok: {T.checkAt(grammar, start, nulls, firsts, follows, x) == True{} : Bool}) -> LL.LL1At(grammar, start, x):
  q1 => q2 => next => neq => l1 => l2 => p1 => p2 => sound_pair_at(grammar, start, nulls, firsts, follows, x, q1, q2, next, ok, neq, l1, l2, p1, p2)

# LL(1) AT x BY THE TABLES IS LL(1) AT x: when the check finds no conflict among x's
# productions in closed tables, no two of them can begin with the same next token, whatever
# the rest of the grammar does.
law tables_ll1_at:
  for fuel: Nat
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +x: Nat
  for +ok: {T.ll1AtByTables(fuel, grammar, start, x) == True{} : Bool}
  LL.LL1At(grammar, start, x)

def tables_ll1_at(fuel, grammar, start, x, ok):
  +f = fuel
  +nulls = Sets.growNulls(f, grammar, [])
  +firsts = T.growFirsts(f, grammar, nulls, [])
  +follows = T.growFollows(f, grammar, firsts, nulls, [T.FollowFact{start, None{}}])
  sound_at(grammar, start, nulls, firsts, follows, x, ok)

# ======== PREDICTION SEEDS AT MOST ONE PRODUCTION OF x ========

def maybe_eq_of(a: Maybe<&2, Nat>, b: Maybe<&2, Nat>, +h: {Gll.tokEq(a, b) == True{} : Bool}) -> {T.maybeEq(a, b) == True{} : Bool}:
  match a b:
    case None{} None{}:
      {==}
    case Some{+x} Some{+y}:
      h
    case None{} Some{+y}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(h))
    case Some{+x} None{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(h))

def mpick(+y: Maybe<&2, Nat>, +rest: +List<Maybe<&2, Nat>>, +n: Maybe<&2, Nat>,
  cases: Either<{Gll.tokEq(n, y) == True{} : Bool}, {Gll.tokIn(n, rest) == True{} : Bool}>,
  later: {Gll.tokIn(n, rest) == True{} : Bool} -> {T.maybeIn(n, rest) == True{} : Bool}) -> {T.maybeIn(n, y <> rest) == True{} : Bool}:
  match cases:
    case Inl{e}:
      Lemma.or_true_left_intro(T.maybeEq(n, y), T.maybeIn(n, rest), maybe_eq_of(n, y, e))
    case Inr{m}:
      Lemma.or_true_right_intro(T.maybeEq(n, y), T.maybeIn(n, rest), later(m))

law maybe_in_of:
  for xs: +List<Maybe<&2, Nat>>
  for +n: Maybe<&2, Nat>
  for +h: {Gll.tokIn(n, xs) == True{} : Bool}
  {T.maybeIn(n, xs) == True{} : Bool}

def maybe_in_of(xs, n, h):
  match xs:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(h))
    case Con{+y, +rest}:
      mpick(y, rest, n, Lemma.or_true_cases(Gll.tokEq(n, y), Gll.tokIn(n, rest), h), m => maybe_in_of(rest, n, m))

def set_to(+tok: Maybe<&2, Nat>, +xs: +List<Maybe<&2, Nat>>, +ys: +List<Maybe<&2, Nat>>, +e: {xs == ys : +List<Maybe<&2, Nat>>},
  +h: {T.maybeIn(tok, xs) == True{} : Bool}) -> {T.maybeIn(tok, ys) == True{} : Bool}:
  %e : {T.maybeIn(tok, _) == True{} : Bool}
  h

# An admitted production of x has the token in its predict set.
def admitted_in(+grammar: +List<Core.Production>, +firsts: +List<T.FirstFact>, +follows: +List<T.FollowFact>, +nulls: +List<Nat>, +q: Nat, +x: Nat, +tok: Maybe<&2, Nat>,
  +hl: {Core.lhsIs(grammar, q, x) == True{} : Bool},
  +ha: {Gll.admits(Gll.Allowed{Pr.predictSets(grammar, firsts, follows, nulls)}, q, tok) == True{} : Bool})
  -> {T.maybeIn(tok, PT.Pred(grammar, q, firsts, follows, nulls)) == True{} : Bool}:
  set_to(tok, Gll.setAt(Pr.predictSets(grammar, firsts, follows, nulls), q), PT.Pred(grammar, q, firsts, follows, nulls), PP.set_at(grammar, q, x, firsts, follows, nulls, hl),
    maybe_in_of(Gll.setAt(Pr.predictSets(grammar, firsts, follows, nulls), q), tok, ha))

def seeds_with(+grammar: +List<Core.Production>, +start: Nat, +nulls: +List<Nat>, +firsts: +List<T.FirstFact>, +follows: +List<T.FollowFact>, +x: Nat,
  +q1: Nat, +q2: Nat, +tok: Maybe<&2, Nat>,
  +ok: {T.checkAt(grammar, start, nulls, firsts, follows, x) == True{} : Bool},
  +neq: {Nat.is_eq(q1, q2) == False{} : Bool},
  +l1: {Core.lhsIs(grammar, q1, x) == True{} : Bool},
  +l2: {Core.lhsIs(grammar, q2, x) == True{} : Bool},
  +a1: {Gll.admits(Gll.Allowed{Pr.predictSets(grammar, firsts, follows, nulls)}, q1, tok) == True{} : Bool},
  +a2: {Gll.admits(Gll.Allowed{Pr.predictSets(grammar, firsts, follows, nulls)}, q2, tok) == True{} : Bool}) -> Empty:
  +a1b = {Sets.nullsClosed(grammar, nulls) : Bool}
  +a2b = {T.firstsClosed(grammar, firsts, nulls) : Bool}
  +a3b = {T.followsClosed(grammar, firsts, follows, nulls) : Bool}
  +a4b = {T.followHas(start, None{}, follows) : Bool}
  +a5b = {T.suffixOk([Core.Nonterminal{start, Core.Anything{}}], start, firsts, follows, nulls) : Bool}
  +a6b = {T.pairsAt(grammar, x, firsts, follows, nulls) : Bool}
  +r1 = Lemma.and_true_right_side(a1b, Bool.and(a2b, Bool.and(a3b, Bool.and(a4b, Bool.and(a5b, a6b)))), ok)
  +r2 = Lemma.and_true_right_side(a2b, Bool.and(a3b, Bool.and(a4b, Bool.and(a5b, a6b))), r1)
  +r3 = Lemma.and_true_right_side(a3b, Bool.and(a4b, Bool.and(a5b, a6b)), r2)
  +r4 = Lemma.and_true_right_side(a4b, Bool.and(a5b, a6b), r3)
  +pa = Lemma.and_true_right_side(a5b, a6b, r4)
  PT.apart_no(grammar, q1, q2, firsts, follows, nulls, tok, pairs_at_x(grammar, q1, q2, x, firsts, follows, nulls, pa, l1, l2, neq),
    admitted_in(grammar, firsts, follows, nulls, q1, x, tok, l1, a1), admitted_in(grammar, firsts, follows, nulls, q2, x, tok, l2, a2))

# PREDICTION SEEDS AT MOST ONE PRODUCTION OF x: when x passes the check, the predicting
# parser (PREDICT.bend) admits no two productions of x for the same next token, so a
# cluster of x starts at most one of them.
law seeds_one_at:
  for fuel: Nat
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +x: Nat
  for +q1: Nat
  for +q2: Nat
  for +tok: Maybe<&2, Nat>
  for +ok: {T.ll1AtByTables(fuel, grammar, start, x) == True{} : Bool}
  for +neq: {Nat.is_eq(q1, q2) == False{} : Bool}
  for +l1: {Core.lhsIs(grammar, q1, x) == True{} : Bool}
  for +l2: {Core.lhsIs(grammar, q2, x) == True{} : Bool}
  for +a1: {Gll.admits(Gll.Allowed{Pr.predictSets(grammar, T.growFirsts(fuel, grammar, Sets.growNulls(fuel, grammar, []), []), T.growFollows(fuel, grammar, T.growFirsts(fuel, grammar, Sets.growNulls(fuel, grammar, []), []), Sets.growNulls(fuel, grammar, []), [T.FollowFact{start, None{}}]), Sets.growNulls(fuel, grammar, []))}, q1, tok) == True{} : Bool}
  for +a2: {Gll.admits(Gll.Allowed{Pr.predictSets(grammar, T.growFirsts(fuel, grammar, Sets.growNulls(fuel, grammar, []), []), T.growFollows(fuel, grammar, T.growFirsts(fuel, grammar, Sets.growNulls(fuel, grammar, []), []), Sets.growNulls(fuel, grammar, []), [T.FollowFact{start, None{}}]), Sets.growNulls(fuel, grammar, []))}, q2, tok) == True{} : Bool}
  Empty

def seeds_one_at(fuel, grammar, start, x, q1, q2, tok, ok, neq, l1, l2, a1, a2):
  +f = fuel
  +nulls = Sets.growNulls(f, grammar, [])
  +firsts = T.growFirsts(f, grammar, nulls, [])
  +follows = T.growFollows(f, grammar, firsts, nulls, [T.FollowFact{start, None{}}])
  seeds_with(grammar, start, nulls, firsts, follows, x, q1, q2, tok, ok, neq, l1, l2, a1, a2)
